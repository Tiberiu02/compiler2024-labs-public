package alpine
package codegen

import alpine.symbols
import alpine.wasm.WasmTree._
import alpine.ast._
import alpine.wasm.Wasm
import scala.collection.mutable
import scala.collection.mutable.Stack
import alpine.wasm.WasmTree
import scala.collection.mutable.ListBuffer

/** The transpilation of an Alpine program to Scala. */
final class CodeGenerator(syntax: TypedProgram)
    extends ast.TreeVisitor[CodeGenerator.Context, Unit]:
  import CodeGenerator._

  val imports = List(
    ImportFromModule("api", "print", "print", List(I32), None),
    ImportFromModule("api", "print", "fprint", List(F32), None),
    ImportFromModule("api", "print-char", "print-char", List(I32), None),
    ImportFromModule("api", "show-memory", "show-memory", List(I32), None),
    ImportMemory("api", "mem", 100)
  )

  // context used for evaluation
  val a = CodeGenerator.Context(imports)

  /** The program being evaluated. */
  private given TypedProgram = syntax
  syntax.declarations.foreach(_.visit(this)(using a))

  /** Returns a WebAssembly program equivalent to `syntax`. */
  def compile(): Module = a.toModule

  // Tree visitor methods

  /** Visits `n` with state `a`. */
  def visitLabeled[T <: Tree](n: Labeled[T])(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitBinding(n: Binding)(using a: Context): Unit =
    if n.identifier == "main" then
      n.initializer.get.visit(this)
      a.addFunction(MainFunction(a.popInstructions.toList.reverse, None))
    else
      a.inTopLevelValueDef = true
      val instruction = n.initializer match
        case Some(expr) => 
          n.initializer.get.visit(this)
          Some(a.popOneInstruction)
        case _ => None

      a.addTopLevelMapping(n.identifier, instruction)
      a.inTopLevelValueDef = false

  /** Visits `n` with state `a`. */
  def visitTypeDeclaration(n: TypeDeclaration)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitFunction(n: ast.Function)(using a: Context): Unit = 
    a.inFunctionDef = true // we are now in a function
    n.output match
      case Some(tpe) => tpe.visit(this)
      case None => a.pushType(None)

    n.inputs.foreach(_.visit(this)) // pushes input types to stack

    val all = a.popTypes.toList.reverse

    // last elements on the stack
    val inputs = all match
      case x :: xs => xs.filter(_.isDefined).map(_.get)
      case _ => ???
    // first element on stack
    val output = all match 
      case x :: xs => x
      case _ => ???

    n.body.visit(this)

    a.addFunction(FunctionDefinition(
      name = n.identifier, 
      params = inputs,
      returnType = output,
      body = a.popInstructions.reverse.toList)
    )
    a.inFunctionDef = false

  /** Visits `n` with state `a`. */
  def visitParameter(n: Parameter)(using a: Context): Unit =
    a.addParameterToMap(n.identifier)
    if n.ascription.isDefined then
      n.ascription.get.visit(this)

  /** Visits `n` with state `a`. */
  def visitIdentifier(n: Identifier)(using a: Context): Unit = 
    if a.inFunctionDef then
      a.getParameterNum(n.value) match
        case Some(int) => a.pushInstruction(LocalGet(int)) // named argument
        case None => a.pushInstruction(Call(n.value))
    else if !a.inTopLevelValueDef then
      a.getTopLevelMapping(n.value) match
        case Some(instructionOpt) => 
          instructionOpt match
            case Some(instruction) => a.pushInstruction(instruction)
            case None => ???
        case None => a.pushInstruction(Call(n.value))

  /** Visits `n` with state `a`. */
  def visitBooleanLiteral(n: BooleanLiteral)(using a: Context): Unit =
    if n.value.toBoolean then a.pushInstruction(IConst(1))
    else a.pushInstruction(IConst(0))

  /** Visits `n` with state `a`. */
  def visitIntegerLiteral(n: IntegerLiteral)(using a: Context): Unit =
    a.pushInstruction(IConst(n.value.toInt)) 

  /** Visits `n` with state `a`. */
  def visitFloatLiteral(n: FloatLiteral)(using a: Context): Unit =
    a.pushInstruction(FConst(n.value.toFloat))

  /** Visits `n` with state `a`. */
  def visitStringLiteral(n: StringLiteral)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitRecord(n: Record)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitSelection(n: Selection)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitApplication(n: Application)(using a: Context): Unit =
    println(n.function)
    n.function match
      case Identifier("print", _) =>
        println(n.arguments.head.value.tpe)
        if n.arguments.head.value.tpe == symbols.Type.Int then
          n.arguments.head.value.visit(this)
          a.pushInstruction(Call("print"))
        else if n.arguments.head.value.tpe == symbols.Type.Float then
          n.arguments.head.value.visit(this)
          a.pushInstruction(Call("fprint"))
        else ??? // error
      case Identifier(s, _) =>
        n.arguments.foreach(_.value.visit(this))
        n.function.visit(this)
      case _ => ??? // error

  /** Visits `n` with state `a`. */
  def visitPrefixApplication(n: PrefixApplication)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitInfixApplication(n: InfixApplication)(using a: Context): Unit =
    n.lhs.visit(this)
    n.rhs.visit(this)
    if n.lhs.tpe == symbols.Type.Int && n.rhs.tpe == symbols.Type.Int then
      n.function.value match
        case "+"  => a.pushInstruction(IAdd)
        case "-"  => a.pushInstruction(ISub)
        case "*"  => a.pushInstruction(IMul)
        case "/"  => a.pushInstruction(IDiv)
        case "%"  => a.pushInstruction(IRem)
        case "&"  => a.pushInstruction(IAnd)
        case "|"  => a.pushInstruction(IOr)
        case "==" => a.pushInstruction(IEq)
        case "<"  => a.pushInstruction(ILt_s)
        case "<=" => a.pushInstruction(ILe_s)
    else if n.lhs.tpe == symbols.Type.Float && n.rhs.tpe == symbols.Type.Float
    then
      n.function.value match
        case "+"  => a.pushInstruction(FAdd)
        case "-"  => a.pushInstruction(FSub)
        case "*"  => a.pushInstruction(FMul)
        case "/"  => a.pushInstruction(FDiv)
        case "="  => a.pushInstruction(FEq)
        case "<"  => a.pushInstruction(FLt)
        case "<=" => a.pushInstruction(FLe)
    else ??? // error

  /** Visits `n` with state `a`. */
  def visitConditional(n: Conditional)(using a: Context): Unit =
    // get all the relevant instructions
    n.successCase.visit(this)
    val successInstructions = a.popInstructions.toList.reverse
    n.failureCase.visit(this)
    val failureInstructions = a.popInstructions.toList.reverse
    n.condition.visit(this)

    n.successCase.tpe match
      case symbols.Type.Int =>
        a.pushInstruction(If_i32(successInstructions, Some(failureInstructions)))
      case symbols.Type.Unit  =>
        a.pushInstruction(If_void(successInstructions, Some(failureInstructions)))
      case _ => ??? // error

  /** Visits `n` with state `a`. */
  def visitMatch(n: Match)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitMatchCase(n: Match.Case)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitLet(n: Let)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitLambda(n: Lambda)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitParenthesizedExpression(n: ParenthesizedExpression)(using
      a: Context
  ): Unit = 
    n.inner.visit(this)

  /** Visits `n` with state `a`. */
  def visitAscribedExpression(n: AscribedExpression)(using a: Context): Unit =
    ???

  /** Visits `n` with state `a`. */
  def visitTypeIdentifier(n: TypeIdentifier)(using a: Context): Unit =
    a.pushType(
      n.value match
        case "Int" =>
          Some(I32)
        case "Float" =>
          Some(F32)
        case _ => ???
    )

  /** Visits `n` with state `a`. */
  def visitRecordType(n: RecordType)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitTypeApplication(n: TypeApplication)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitArrow(n: Arrow)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitSum(n: Sum)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitParenthesizedType(n: ParenthesizedType)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitValuePattern(n: ValuePattern)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitRecordPattern(n: RecordPattern)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitWildcard(n: Wildcard)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitError(n: ErrorTree)(using a: Context): Unit = ???

object CodeGenerator:

  /** The local state of a transpilation to Scala.
    *
    * @param indentation
    *   The current identation to add before newlines.
    */
  final class Context(imports: List[Import]):
    var inFunctionDef = false

    // list of functions (including main function)
    private var functions = ListBuffer[WasmTree.Function]()

    // stack of instructions used for evaluating functions
    private var instructionsStack = Stack[WasmTree.Instruction]()

    def pushInstruction(instruction: Instruction) =
      instructionsStack.push(instruction)

    def popInstructions = instructionsStack.popAll()

    def popOneInstruction = instructionsStack.pop()

    var typesStack = Stack[Option[WasmTree.WasmType]]()

    def pushType(t: Option[WasmTree.WasmType]) =
      typesStack.push(t)

    def popTypes = typesStack.popAll()

    /* adds a function to the list of function */
    def addFunction(f: WasmTree.Function) =
      functions += f

    private var ctr = 0
    /* maps identifiers to numbers */
    private var functionParameterMappings = Map[String, Int]()

    /* adds a parameter to the parameter mappings */
    def addParameterToMap(identifier: String) =
      functionParameterMappings += (identifier -> ctr)
      ctr += 1

    /* gets the corresponding number (for example for Local.get(0)) */
    def getParameterNum(identifier: String) =
      functionParameterMappings.get(identifier)

    def clearFunctionParameterMappings =
      functionParameterMappings = Map[String, Int]()

    var inTopLevelValueDef = false
    private var topLevelMappings = Map[String, Option[Instruction]]()

    def addTopLevelMapping(identifier: String, value: Option[Instruction]) =
      topLevelMappings += (identifier -> value)

    def getTopLevelMapping(identifier: String) =
      topLevelMappings.get(identifier)

    def clearTopLevelMappings =
      topLevelMappings = Map[String, Option[Instruction]]()

    /* returns a wasm module representing the program */
    def toModule: Module = Module(imports, functions.toList)
