package alpine
package codegen

import alpine.symbols
import alpine.wasm.WasmTree._
import alpine.ast._
import alpine.wasm.Wasm
import scala.collection.mutable
import scala.collection.mutable.Stack
import alpine.wasm.WasmTree

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
  def visitBinding(n: Binding)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitTypeDeclaration(n: TypeDeclaration)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitFunction(n: ast.Function)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitParameter(n: Parameter)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitIdentifier(n: Identifier)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitBooleanLiteral(n: BooleanLiteral)(using a: Context): Unit =
    if n.value.toBoolean then
      a.pushInstruction(IConst(1))
    else
      a.pushInstruction(IConst(0))

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
  def visitApplication(n: Application)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitPrefixApplication(n: PrefixApplication)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitInfixApplication(n: InfixApplication)(using a: Context): Unit = ???

  /** Visits `n` with state `a`. */
  def visitConditional(n: Conditional)(using a: Context): Unit = ???

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
  ): Unit = ???

  /** Visits `n` with state `a`. */
  def visitAscribedExpression(n: AscribedExpression)(using a: Context): Unit =
    ???

  /** Visits `n` with state `a`. */
  def visitTypeIdentifier(n: TypeIdentifier)(using a: Context): Unit = ???

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
    // list of functions (including main function)
    private var functions: List[WasmTree.Function] = Nil

    // stack of instructions used for evaluating functions
    private var instructionsStack = Stack[WasmTree.Instruction]()

    def pushInstruction(instruction: Instruction) = 
      instructionsStack.push(instruction)

    def clearStack() =
      instructionsStack = Stack[Instruction]()

    def toModule: Module = Module(imports, functions)

    /** The types that must be emitted in the program. */
    private var _typesToEmit = mutable.Set[symbols.Type.Record]()

    /** The types that must be emitted in the program. */
    def typesToEmit: Set[symbols.Type.Record] = _typesToEmit.toSet

    /** The (partial) result of the transpilation. */
    private var _output = StringBuilder()

    /** `true` iff the transpiler is processing top-level symbols. */
    private var _isTopLevel = true

    /** `true` iff the transpiler is processing top-level symbols. */
    def isTopLevel: Boolean = _isTopLevel

    /** Adds `t` to the set of types that are used by the transpiled program. */
    def registerUse(t: symbols.Type.Record): Unit =
      if t != symbols.Type.Unit then _typesToEmit.add(t)

    /** Returns `action` applied on `this` where `output` has been exchanged
      * with `o`.
      */
    def swappingOutputBuffer[R](o: StringBuilder)(action: Context => R): R =
      val old = _output
      _output = o
      try action(this)
      finally _output = old

    /** Returns `action` applied on `this` where `isTopLevel` is `false`. */
    def inScope[R](action: Context => R): R =
      var tl = _isTopLevel
      _isTopLevel = false
      try action(this)
      finally _isTopLevel = tl
