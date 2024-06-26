package alpine
package evaluation

import alpine.ast
import alpine.symbols
import alpine.symbols.{Entity, EntityReference, Type}
import alpine.util.FatalError

import java.io.OutputStream
import java.nio.charset.StandardCharsets.UTF_8

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.control.NoStackTrace
import alpine.symbols.Type.Bool
import scala.collection.View.Empty
import alpine.ast.Tree.walkRoots
import alpine.evaluation.Value.BuiltinFunction
import alpine.evaluation.Value.Builtin
import alpine.evaluation.Value.Record
import alpine.evaluation.Value.Lambda
import alpine.evaluation.Value.Unevaluated
import alpine.evaluation.Value.Poison
import alpine.ast.Typecast

/** The evaluation of an Alpine program.
 *
 *  @param syntax The program being evaluated.
 *  @param standardOutput The standard output of the interpreter.
 *  @param standardError The standard output of the interpreter.
 */
final class Interpreter(
    syntax: TypedProgram,
    standardOutput: OutputStream,
    standardError: OutputStream
) extends ast.TreeVisitor[Interpreter.Context, Value]:

  import Interpreter.Context

  /** The program being evaluated. */
  private given TypedProgram = syntax

  /** A map from global entity to its declaration. */
  private val globals: mutable.HashMap[symbols.Entity, Value] =
    val partialResult = mutable.HashMap[symbols.Entity, Value]()
    for d <- syntax.declarations do
      partialResult.put(d.entityDeclared, Value.Unevaluated(d, d.tpe))
    partialResult

  /** Evaluates the entry point of the program. */
  def run(): Int =
    val e = syntax.entry.getOrElse(throw Panic("no entry point"))
    try
      e.visit(this)(using Context())
      0
    catch case e: Interpreter.Exit =>
      e.status

  def visitLabeled[T <: ast.Tree](n: ast.Labeled[T])(using context: Context): Value =
    unexpectedVisit(n)

  def visitBinding(n: ast.Binding)(using context: Context): Value =
    unexpectedVisit(n)

  def visitTypeDeclaration(n: ast.TypeDeclaration)(using context: Context): Value =
    unexpectedVisit(n)

  def visitFunction(n: ast.Function)(using context: Context): Value =
    unexpectedVisit(n)

  def visitParameter(n: ast.Parameter)(using context: Context): Value =
    unexpectedVisit(n)

  def visitIdentifier(n: ast.Identifier)(using context: Context): Value =
    val r = n.referredEntity.get
    r.entity match
      case e: Entity.Builtin =>
        builtin(e)
      case e =>
        context.getLocal(e.name).getOrElse(getGlobal(e).get)

  def visitBooleanLiteral(n: ast.BooleanLiteral)(using context: Context): Value =
    Value.Builtin(n.value == "true", Type.Bool)

  def visitIntegerLiteral(n: ast.IntegerLiteral)(using context: Context): Value =
    Value.Builtin(n.value.toInt, Type.Int)

  def visitFloatLiteral(n: ast.FloatLiteral)(using context: Context): Value =
    Value.Builtin(n.value.toFloat, Type.Float)

  def visitStringLiteral(n: ast.StringLiteral)(using context: Context): Value =
    Value.Builtin(n.value, Type.String)

  def visitRecord(n: ast.Record)(using context: Context): Value =
    val fieldValues = n.fields.map(_.value.visit(this))
    val fieldTypes = fieldValues.map(_.dynamicType)
    val fieldLabels = n.fields.map(_.label)
    val labeledTypes = (fieldLabels zip fieldTypes).map((l, t) => Type.Labeled(l, t))
    val dynamicType = Type.Record(n.identifier, labeledTypes)
    Value.Record(n.identifier, fieldValues, dynamicType)

  def visitSelection(n: ast.Selection)(using context: Context): Value =
    n.qualification.visit(this) match
      case q: Value.Record => syntax.treeToReferredEntity.get(n) match
        case Some(symbols.EntityReference(Entity.Field(_, i), _)) =>
          q.fields(i)
        case r =>
          throw Panic(s"unexpected entity reference '${r}'")
      case q =>
        throw Panic(s"unexpected qualification of type '${q.dynamicType}'")

  def visitApplication(n: ast.Application)(using context: Context): Value =
    val funcNode = n.function.visit(this) // function node in AST
    val args = n.arguments.map(_.value.visit(this)) // visit argument expressions
    call(funcNode, args)

  def visitPrefixApplication(n: ast.PrefixApplication)(using context: Context): Value =
    val argument = n.argument.visit(this) // evaluate argument
    val funcNode = n.function.visit(this) // get funcNode
    call(funcNode, List(argument))        // Call requires a `Seq type, hence `List`

  def visitInfixApplication(n: ast.InfixApplication)(using context: Context): Value =
    // visit left-hand and right-hand sides of infix operator
    val leftValue = n.lhs.visit(this)
    val rightValue = n.rhs.visit(this)
    // get function node from AST
    val funcNode = n.function.visit(this)
    // call on function node and sequence (Array) of values 
    call(funcNode, List(leftValue, rightValue))

  def visitConditional(n: ast.Conditional)(using context: Context): Value =
    val condition = n.condition.visit(this)
    val Value.Builtin(value: Boolean, _) = condition : @unchecked // magic
    if value then n.successCase.visit(this) else n.failureCase.visit(this) 

  def visitMatch(n: ast.Match)(using context: Context): Value =
    val scrutineeValue = n.scrutinee.visit(this)
    val matchingCases = n.cases.filter(c => matches(scrutineeValue, c.pattern).exists(_ => true)) 
    matchingCases match
      case Nil => throw Panic("No matching case !")
      case _ =>  
        val bindings = matches(scrutineeValue, matchingCases.head.pattern)
        bindings match
          case None => throw Panic("No matching case !")
          case Some(bindings) => 
            matchingCases.head.body.visit(this)(using context.pushing(bindings))

  def visitMatchCase(n: ast.Match.Case)(using context: Context): Value =
    unexpectedVisit(n)

  def visitLet(n: ast.Let)(using context: Context): Value =
    n.binding.initializer match
      case Some(bindingInitializer) =>
        val bindingValue = bindingInitializer.visit(this) 
        val newBindingFrame = Map.from(List((n.binding.nameDeclared, bindingValue)))
        n.body.visit(this)(using context.pushing(newBindingFrame))
      case None => throw Panic("No biding initializer !")

  def visitLambda(n: ast.Lambda)(using context: Context): Value =
    Value.Lambda(n.body, n.inputs, context.flattened, n.tpe)
  

  def visitParenthesizedExpression(n: ast.ParenthesizedExpression)(using context: Context): Value =
    n.inner.visit(this)

  def visitAscribedExpression(n: ast.AscribedExpression)(using context: Context): Value =
    val e = n.inner.visit(this)
    n.operation match
      case Typecast.Widen => e
      case Typecast.Narrow => if e.dynamicType.isSubtypeOf(n.ascription.tpe) then Value.some(e) else Value.none
      case Typecast.NarrowUnconditionally =>
        if e.dynamicType.isSubtypeOf(n.ascription.tpe) then e
        else throw Panic(s"cannot cast '${e.dynamicType}' to '${n.ascription.tpe}'")

  def visitTypeIdentifier(n: ast.TypeIdentifier)(using context: Context): Value =
    unexpectedVisit(n)

  def visitRecordType(n: ast.RecordType)(using context: Context): Value =
    unexpectedVisit(n)

  def visitTypeApplication(n: ast.TypeApplication)(using context: Context): Value =
    unexpectedVisit(n)

  def visitArrow(n: ast.Arrow)(using context: Context): Value =
    unexpectedVisit(n)

  def visitSum(n: ast.Sum)(using context: Context): Value =
    unexpectedVisit(n)

  def visitParenthesizedType(n: ast.ParenthesizedType)(using context: Context): Value =
    unexpectedVisit(n)

  def visitValuePattern(n: ast.ValuePattern)(using context: Context): Value =
    unexpectedVisit(n)

  def visitRecordPattern(n: ast.RecordPattern)(using context: Context): Value =
    unexpectedVisit(n)

  def visitWildcard(n: ast.Wildcard)(using context: Context): Value =
    unexpectedVisit(n)

  def visitError(n: ast.ErrorTree)(using context: Context): Value =
    unexpectedVisit(n)

  /** Returns the built-in function or value corresponding to `e`. */
  private def builtin(e: Entity.Builtin): Value =
    Type.Arrow.from(e.tpe) match
      case Some(a) => Value.BuiltinFunction(e.name.identifier, a)
      case _ => throw Panic(s"undefined built-in entity '${e.name}'")

  /** Returns the value of the global entity `e`. */
  private def getGlobal(e: Entity): Option[Value] =
    globals.get(e) match
      case Some(v: Value.Unevaluated) =>
        v.declaration match
          case d: ast.Binding =>
            globals.put(e, Value.Poison)
            val computed = d.initializer.get.visit(this)(using Context())
            globals.put(e, computed)
            Some(computed)

          case d: ast.Function =>
            val computed = Value.Function(d, Type.Arrow.from(d.tpe).get)
            globals.put(e, computed)
            Some(computed)

          case _ => ???

      case Some(Value.Poison) => throw Panic("initialization cycle")
      case v => v

  /** Returns the result of applying `f` on arguments `a`. */
  private def call(f: Value, a: Seq[Value])(using context: Context): Value =
    f match
      case Value.Function(d, _) =>
        // get input names
        val inputNames = d.inputs.map(_.nameDeclared)
        // create a frame from input names and input values `a`
        val newFrame: Interpreter.Frame = inputNames.zip(a).toMap
        // visit the function body using the next context
        d.body.visit(this)(using context.pushing(newFrame))

      case l: Value.Lambda =>
        // get input names
        val inputNames = l.inputs.map(_.nameDeclared)
        // create a frame from input names and input values `a` and captures
        val newFrame: Interpreter.Frame = inputNames.zip(a).toMap ++ l.captures
        // we visit the body with the updated context
        l.body.visit(this)(using context.pushing(newFrame))

      case Value.BuiltinFunction("exit", _) =>
        val Value.Builtin(status, _) = a.head : @unchecked
        throw Interpreter.Exit(status.asInstanceOf)

      case Value.BuiltinFunction("print", _) =>
        val text = a.head match
          case Value.Builtin(s : String, _) => s.substring(1, s.length - 1) // Remove quotes
          case v => v.toString
        standardOutput.write(text.getBytes(UTF_8))
        Value.unit

      case Value.BuiltinFunction("equality", _) =>
        Value.Builtin(a(0) == a(1), Type.Bool)
      case Value.BuiltinFunction("inequality", _) =>
        Value.Builtin(a(0) != a(1), Type.Bool)
      case Value.BuiltinFunction("lnot", _) =>
        applyBuiltinUnary[Boolean](a, Type.Bool)((b) => !b)
      case Value.BuiltinFunction("land", _) =>
        applyBuiltinBinary[Boolean](a, Type.Bool)((l, r) => l && r)
      case Value.BuiltinFunction("lor", _) =>
        applyBuiltinBinary[Boolean](a, Type.Bool)((l, r) => l || r)
      case Value.BuiltinFunction("ineg", _) =>
        applyBuiltinUnary[Int](a, Type.Int)((n) => -n)
      case Value.BuiltinFunction("iadd", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l + r)
      case Value.BuiltinFunction("isub", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l - r)
      case Value.BuiltinFunction("imul", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l * r)
      case Value.BuiltinFunction("idiv", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l / r)
      case Value.BuiltinFunction("irem", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l % r)
      case Value.BuiltinFunction("ishl", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l << r)
      case Value.BuiltinFunction("ishr", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l >> r)
      case Value.BuiltinFunction("ilt", _) =>
        applyBuiltinComparison[Int](a)((l, r) => l < r)
      case Value.BuiltinFunction("ile", _) =>
        applyBuiltinComparison[Int](a)((l, r) => l <= r)
      case Value.BuiltinFunction("igt", _) =>
        applyBuiltinComparison[Int](a)((l, r) => l > r)
      case Value.BuiltinFunction("ige", _) =>
        applyBuiltinComparison[Int](a)((l, r) => l >= r)
      case Value.BuiltinFunction("iinv", _) =>
        applyBuiltinUnary[Int](a, Type.Int)((n) => ~n)
      case Value.BuiltinFunction("iand", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l & r)
      case Value.BuiltinFunction("ior", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l | r)
      case Value.BuiltinFunction("ixor", _) =>
        applyBuiltinBinary[Int](a, Type.Int)((l, r) => l ^ r)
      case Value.BuiltinFunction("fneg", _) =>
        applyBuiltinUnary[Float](a, Type.Float)((n) => -n)
      case Value.BuiltinFunction("fadd", _) =>
        applyBuiltinBinary[Float](a, Type.Float)((l, r) => l + r)
      case Value.BuiltinFunction("fsub", _) =>
        applyBuiltinBinary[Float](a, Type.Float)((l, r) => l - r)
      case Value.BuiltinFunction("fmul", _) =>
        applyBuiltinBinary[Float](a, Type.Float)((l, r) => l * r)
      case Value.BuiltinFunction("fdiv", _) =>
        applyBuiltinBinary[Float](a, Type.Float)((l, r) => l / r)
      case Value.BuiltinFunction("flt", _) =>
        applyBuiltinComparison[Float](a)((l, r) => l < r)
      case Value.BuiltinFunction("fle", _) =>
        applyBuiltinComparison[Float](a)((l, r) => l <= r)
      case Value.BuiltinFunction("fgt", _) =>
        applyBuiltinComparison[Float](a)((l, r) => l > r)
      case Value.BuiltinFunction("fge", _) =>
        applyBuiltinComparison[Float](a)((l, r) => l >= r)
      case _ =>
        throw Panic(s"value of type '${f.dynamicType}' is not a function")

  private def applyBuiltinUnary[T](
      a: Seq[Value], r: Type.Builtin
  )(f: T => T): Value.Builtin[T] =
    val Value.Builtin(b, _) = a.head : @unchecked
    Value.Builtin(f(b.asInstanceOf[T]), r)

  private def applyBuiltinBinary[T](
      a: Seq[Value], r: Type.Builtin
  )(f: (T, T) => T): Value.Builtin[T] =
    val Value.Builtin(lhs, _) = a(0) : @unchecked
    val Value.Builtin(rhs, _) = a(1) : @unchecked
    Value.Builtin(f(lhs.asInstanceOf[T], rhs.asInstanceOf[T]), r)

  private def applyBuiltinComparison[T](
      a: Seq[Value])(f: (T, T) => Boolean
  ): Value.Builtin[Boolean] =
    val Value.Builtin(lhs, _) = a(0) : @unchecked
    val Value.Builtin(rhs, _) = a(1) : @unchecked
    Value.Builtin(f(lhs.asInstanceOf[T], rhs.asInstanceOf[T]), Type.Bool)

  /** Returns a map from binding in `pattern` to its value iff `scrutinee` matches `pattern`.  */
  private def matches(
      scrutinee: Value, pattern: ast.Pattern
  )(using context: Context): Option[Interpreter.Frame] =
    pattern match
      case p: ast.Wildcard =>
        matchesWildcard(scrutinee, p)
      case p: ast.ValuePattern =>
        matchesValue(scrutinee, p)
      case p: ast.RecordPattern =>
        matchesRecord(scrutinee, p)
      case p: ast.Binding =>
        matchesBinding(scrutinee, p)
      case p: ast.ErrorTree =>
        unexpectedVisit(p)

  /** Returns a map from binding in `pattern` to its value iff `scrutinee` matches `pattern`.  */
  private def matchesWildcard(
      scrutinee: Value, pattern: ast.Wildcard
  )(using context: Context): Option[Interpreter.Frame] =
    Some(Map.empty[symbols.Name, Value])

  /** Returns a map from binding in `pattern` to its value iff `scrutinee` matches `pattern`.  */
  private def matchesValue(
      scrutinee: Value, pattern: ast.ValuePattern
  )(using context: Context): Option[Interpreter.Frame] =
    val patternValue = pattern.value.visit(this)
    if patternValue == scrutinee then Some(Map.empty[symbols.Name, Value]) else None


  /** Returns a map from binding in `pattern` to its value iff `scrutinee` matches `pattern`.  */
  private def matchesRecord(
      scrutinee: Value, pattern: ast.RecordPattern
  )(using context: Context): Option[Interpreter.Frame] =
    import Interpreter.Frame
    scrutinee match
      case s: Value.Record =>
       val patternTypeRecord = Type.Record.from(pattern.tpe)
       patternTypeRecord match
        case None => None
        case Some(ptr) =>
          if ptr.structurallyMatches(s.dynamicType) && s.fields.length == pattern.fields.length then 
            var FrameAcc = Map.empty[symbols.Name, Value]
            var flag = true 
            (s.fields zip pattern.fields).foreach {
              case (v, p) =>
                matches(v, p.value) match {
                  case Some(m) => FrameAcc = FrameAcc ++ m
                  case _       => flag = false
                }
            }
            if flag then Some(FrameAcc) else None
          else None  
       
      case _ => None

  /** Returns a map from binding in `pattern` to its value iff `scrutinee` matches `pattern`.  */
  private def matchesBinding(
      scrutinee: Value, pattern: ast.Binding
  )(using context: Context): Option[Interpreter.Frame] =  
    val frame = Map((pattern.nameDeclared, scrutinee))
    pattern.ascription match
      case None => if scrutinee.dynamicType == pattern.tpe then Some(frame) else None
      case Some(asc) => if scrutinee.dynamicType.isSubtypeOf(asc.tpe) then Some(frame) else None

end Interpreter

object Interpreter:

  /** A map from local symbol to its value. */
  type Frame = Map[symbols.Name, Value]

  /** The local state of an Alpine interpreter.
   *
   *  @param locals A stack of maps from local symbol to its value.
   */
  final class Context(val locals: List[Frame] = List()):

    /** Returns a copy of `this` in which a frame with the given local mapping has been pushed. */
    def defining(m: (symbols.Name, Value)): Context =
      pushing(Map(m))

    /** Returns a copy of `this` in which `f` has been pushed on the top of the locals. */
    def pushing(f: Frame): Context =
      Context(locals.prepended(f))

    /** Returns the value of `n` iff it is defined in the context's locals. */
    def getLocal(n: symbols.Name): Option[Value] =
      @tailrec def loop(frames: List[Interpreter.Frame]): Option[Value] =
        frames match
          case Nil => None
          case local :: fs => local.get(n) match
            case Some(d) => Some(d)
            case _ => loop(fs)
      loop(locals)

    /** A map from visible local symbol to its value. */
    def flattened: Frame =
      val partialResult = mutable.HashMap[symbols.Name, Value]()
      for
        frame <- locals
        (n, v) <- frame if !partialResult.isDefinedAt(n)
      do
        partialResult.put(n, v)
      partialResult.toMap

  end Context

  /** An exception thrown when the interpreter evaluated a call to `Builtin.exit`. */
  private final class Exit(val status: Int) extends Exception with NoStackTrace

end Interpreter
