package alpine
package parsing

import alpine.ast
import alpine.util.FatalError

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.SeqView.Reverse
import alpine.evaluation.Panic

import alpine.ast
import alpine.util.FatalError
import alpine.evaluation.Panic

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.SeqView.Reverse
import scala.util.Try
import scala.util.Failure
import scala.util.Success

class Parser(val source: SourceFile):

  import ast.*
  import Token.Kind as K

  /** The token stream. */
  private var tokens = Lexer(source)

  /** The boundary of the last consumed token. */
  private var lastBoundary = 0

  /** The next token in the stream if it has already been produced. */
  private var lookahead: Option[Token] = None

  /** The errors collected by the parser. */
  private var errors = mutable.ListBuffer[SyntaxError]()

  /** A stack of predicates identifying tokens suitable for error recovery. */
  private var recoveryPredicates = mutable.ListBuffer[Token => Boolean]()

  /** The diagnostics collected by the parser. */
  def diagnostics: DiagnosticSet =
    DiagnosticSet(errors)

  // --- Declarations ---------------------------------------------------------

  /** Parses and returns a program. */
  def program(): alpine.Program =
    @tailrec def loop(partialResult: List[Declaration]): IArray[Declaration] =
      if peek != None then
        loop(partialResult :+ topLevel())
      else
        IArray.from(partialResult)
    Program(loop(List()))

  /** Parses and returns a top-level declaration. */
  def topLevel(): Declaration =
    peek match
      case Some(Token(K.Let, _)) =>
        binding()
      case Some(Token(K.Fun, _)) =>
        function()
      case Some(Token(K.Type, _)) =>
        typeDeclaration()
      case _ =>
        recover(ExpectedTree("top-level declaration", emptySiteAtLastBoundary), ErrorTree.apply)

  /** Parses and returns a binding declaration. */
  private[parsing] def binding(initializerIsExpected: Boolean = true): Binding =
    val let = expect(K.Let)
    val id = identifier()
    val ascr = peek match
      case Some(Token(K.Colon, _)) =>
        val col = take()
        Some(tpe())
      case _ =>
        None
    val init = peek match
      case Some(Token(K.Eq, _)) =>
        if initializerIsExpected then
          val eq = expect(K.Eq)
          Some(expression())
        else
          report(ExpectedTree("assertion", emptySiteAtLastBoundary))
          None
      case _ =>
        if initializerIsExpected then
          report(ExpectedTree("assertion", emptySiteAtLastBoundary))
          None
        else
          None
    val site = if init.isDefined then
      let.site.extendedToCover(init.get.site)
    else if ascr.isDefined then
      let.site.extendedToCover(ascr.get.site)
    else
      let.site.extendedToCover(id.site)
    Binding(id.value, ascr, init, site)

  /** Parses and returns a function declaration. */
  private[parsing] def function(): Function =
    val fun = expect(K.Fun)
    val id = functionIdentifier()
    val inputs = valueParameterList()
    val output = peek match 
      case Some(Token(K.Arrow, _)) =>
        val arrow = expect(K.Arrow)
        Some(tpe())
      case _ =>
        None 
    val body = inBraces(expression)
    Function(id, Nil, inputs, output, body, fun.site.extendedToCover(body.site))

  /** Parses and returns the identifier of a function. */
  private def functionIdentifier(): String =
    take(K.Identifier) match
      case Some(s) =>
        s.site.text.toString
      case _ if peek.map((t) => t.kind.isOperatorPart).getOrElse(false) =>
        operatorIdentifier()(1).text.toString
      case _ =>
        missingName

  /** Parses and returns a list of parameter declarations in parentheses. */
  private[parsing] def valueParameterList(): List[Parameter] =
    val isTerminator = (token: Token) => token.kind == K.RParen
    val onlyParam = () => parameter() match
      case p: Parameter => 
        p
      case _ =>
        throw Panic("not a valid parameter")
    val element = () => commaSeparatedList(isTerminator, onlyParam)
    inParentheses(element)

  /** Parses and returns a parameter declaration. */
  private[parsing] def parameter(): Declaration =
    val lab = peek match
      case Some(Token(K.Identifier, _)) =>
        val l = identifier()
        Some((l.value, l.site))
      case Some(t) if t.kind.isKeyword =>
        take()
        Some((t.site.text.toString, t.site))
      case Some(Token(K.Underscore, _)) =>
        val underscore = expect(K.Underscore)
        None
      case _ =>
        throw Panic("no valid label for parameter")
    val id = identifier()
    val ascr = peek match 
      case Some(Token(K.Colon, _)) =>
        val col = expect(K.Colon)
        Some(tpe())
      case _ =>
        None
    val siteStart = if lab.isDefined then
      lab.get._2
    else 
      id.site
    val siteEnd = if ascr.isDefined then
      ascr.get.site
    else
      id.site
    val site = siteStart.extendedTo(siteEnd.end)
    Parameter(lab.map(_._1), id.value, ascr, site)

  /** Parses and returns a type declaration. */
  private[parsing] def typeDeclaration(): TypeDeclaration =
    val tpeTok = expect(K.Type)
    val id = identifier()
    val eq = expect(K.Eq)
    val tpeDeclared = tpe()
    TypeDeclaration(id.value, Nil, tpeDeclared, tpeTok.site.extendedToCover(tpeDeclared.site))

  /** Parses and returns a list of parameter declarations in angle brackets. */
  //--- This is intentionally left in the handout /*+++ +++*/
  private def typeParameterList(): List[Parameter] =
    inAngles(() => commaSeparatedList(K.RAngle.matches, parameter))
      .collect({ case p: Parameter => p })

  // --- Expressions ----------------------------------------------------------

  /** Parses and returns a term-level expression. */
  def expression(): Expression =
    infixExpression()

  /** Parses and returns an infix expression. */
  private[parsing] def infixExpression(precedence: Int = ast.OperatorPrecedence.min): Expression =
    def rec(lhs: Expression, prec: Int): Expression =
      peek match
        case Some(t) if t.kind.isOperatorPart =>
          val opid1 = operatorIdentifier()
          val op1 = opid1._1.get
          val rhs = ascribed()
          val id1 = Identifier(op1.toString, opid1._2)
          if op1.precedence >= prec then
            peek match
              case Some(Token(K.Operator, _)) =>
                val snap = snapshot()
                val opid2 = operatorIdentifier()
                restore(snap)
                val op2 = opid2._1.get
                if op2.precedence > op1.precedence then
                  val updatedrhs = rec(rhs, op2.precedence)
                  InfixApplication(id1, lhs, updatedrhs, lhs.site.extendedToCover(updatedrhs.site))
                else
                  val updatedlhs = InfixApplication(id1, lhs, rhs, lhs.site.extendedToCover(rhs.site))
                  rec(updatedlhs, op2.precedence)
              case _ =>
                InfixApplication(id1, lhs, rhs, lhs.site.extendedToCover(rhs.site))
          else 
            val updatedlhs = InfixApplication(id1, lhs, rhs, lhs.site.extendedToCover(rhs.site))
            rec(updatedlhs, op1.precedence)

        case _ =>
          lhs
            
    rec(ascribed(), precedence)

  /** Parses and returns an expression with an optional ascription. */
  private[parsing] def ascribed(): Expression =
    val prefExpr = prefixExpression()
    takeIf(t => t.kind == K.At || t.kind == K.AtBang || t.kind == K.AtQuery) match
      case Some(t) =>
        val ascrTpe = tpe()
        t.kind match 
          case K.At =>
            AscribedExpression(prefExpr, Typecast.Widen, ascrTpe, prefExpr.site.extendedToCover(ascrTpe.site))
          case K.AtBang => 
            AscribedExpression(prefExpr, Typecast.NarrowUnconditionally, ascrTpe, prefExpr.site.extendedToCover(ascrTpe.site))
          case K.AtQuery =>
            AscribedExpression(prefExpr, Typecast.Narrow, ascrTpe, prefExpr.site.extendedToCover(ascrTpe.site))
          case _ =>
            throw Panic("not an ascription")
      case _ => 
        prefExpr
    
  /** Parses and returns a prefix application. */
  private[parsing] def prefixExpression(): Expression =
    peek match
      case Some(Token(K.Operator, s)) =>
        operator() match
          case id: Identifier =>
            if noWhitespaceBeforeNextToken then
              val cpdExprTok = peek.get
              PrefixApplication(id, compoundExpression(), s.extendedToCover(cpdExprTok.site))
            else
              id
          case errTree: ErrorTree =>
            errTree
          case _ => 
            throw Panic("An error occured in prefixExpression()")
      case Some(_) =>
        compoundExpression()
      case None =>
        throw Panic("No next token in prefixExpression()")

  /** Parses and returns a compound expression. */
  private[parsing] def compoundExpression(): Expression =
    def compoundExpression2(expr: Expression): Expression =
      if !noWhitespaceBeforeNextToken then
        expr
      else
        peek match
          case Some(Token(K.Dot, _)) =>
            val dot = take()
            val select = peek match
              case Some(Token(K.Integer | K.Identifier | K.Operator, _)) =>
                primaryExpression().asInstanceOf[Selectee]
              case _ => 
                throw Panic("not a valid selection")
            compoundExpression2(Selection(expr, select, expr.site.extendedTo(select.site.end)))
          case Some(Token(K.LParen, _)) =>
            val parList = parenthesizedLabeledList(expression)
            val site = parList match
              case Nil => 
                expr.site
              case _ =>
                expr.site.extendedToCover(parList.last.site)
            compoundExpression2(Application(expr, parList, site))
          case Some(t) =>
            expr
          case _ =>
            throw Panic("no more token")
    compoundExpression2(primaryExpression())

  /** Parses and returns a term-level primary exression.
   *
   *  primary-expression ::=
   *    | value-identifier
   *    | integer-literal
   *    | float-literal
   *    | string-literal
   */
  private[parsing] def primaryExpression(): Expression =
    peek match
      case Some(Token(K.Identifier, s)) =>
        identifier()
      case Some(Token(K.True, _)) =>
        booleanLiteral()
      case Some(Token(K.False, _)) =>
        booleanLiteral()
      case Some(Token(K.Integer, _)) =>
        integerLiteral()
      case Some(Token(K.Float, _)) =>
        floatLiteral()
      case Some(Token(K.String, _)) =>
        stringLiteral()
      case Some(Token(K.Label, _)) =>
        recordExpression()
      case Some(Token(K.If, _)) =>
        conditional()
      case Some(Token(K.Match, _)) =>
        mtch()
      case Some(Token(K.Let, _)) =>
        let()
      case Some(Token(K.LParen, _)) =>
        lambdaOrParenthesizedExpression()
      case Some(t) if t.kind.isOperatorPart =>
        operator()
      case _ =>
        recover(ExpectedTree("expression", emptySiteAtLastBoundary), ErrorTree.apply)
  
  /** Parses and returns an Boolean literal expression. */
  private[parsing] def booleanLiteral(): BooleanLiteral =
    val s = expect("Boolean literal", K.True | K.False)
    BooleanLiteral(s.site.text.toString, s.site)

  /** Parses and returns an integer literal expression. */
  private[parsing] def integerLiteral(): IntegerLiteral =
    val s = expect(K.Integer)
    IntegerLiteral(s.site.text.toString, s.site)

  /** Parses and returns a floating-point literal expression. */
  private[parsing] def floatLiteral(): FloatLiteral =
    val s = expect(K.Float)
    FloatLiteral(s.site.text.toString, s.site)
    

  /** Parses and returns a string literal expression. */
  private[parsing] def stringLiteral(): StringLiteral =
    val s = expect(K.String)
    StringLiteral(s.site.text.toString, s.site)
    

  /** Parses and returns a term-level record expression. */
  private def recordExpression(): Record =
    val make = (id: String, fields: List[Labeled[Expression]], site: SourceSpan) =>
      Record(id, fields, site)
    record(recordExpressionFields, make)

  /** Parses and returns the fields of a term-level record expression. */
  private def recordExpressionFields(): List[Labeled[Expression]] =
    peek match
      case Some(Token(K.LParen, _)) =>
        parenthesizedLabeledList(expression)
      case _ =>
        Nil

  /** Parses and returns a conditional expression. */
  private[parsing] def conditional(): Expression =
    val ifTok = expect(K.If)
    val cond = expression()
    val thenTok = expect(K.Then)
    val succ = expression()
    val elseTok = expect(K.Else)
    val fail = expression()
    val site = ifTok.site.extendedToCover(fail.site)
    Conditional(cond, succ, fail, site)

  /** Parses and returns a match expression. */
  private[parsing] def mtch(): Expression =
    val mtchTok = expect(K.Match)
    val scrutinee = expression()
    val cases = matchBody()
    Match(scrutinee, cases, scrutinee.site.extendedToCover(cases.last.body.site))

  /** Parses and returns a the cases of a match expression. */
  private def matchBody(): List[Match.Case] =
    @tailrec def loop(partialResult: List[Match.Case]): List[Match.Case] =
      peek match
        case Some(Token(K.RBrace, _)) =>
          partialResult
        case Some(Token(K.Case, _)) =>
          loop(partialResult :+ matchCase())
        case _ =>
          report(ExpectedTokenError(K.Case, emptySiteAtLastBoundary))
          discardUntilRecovery()
          if peek == None then partialResult else loop(partialResult)
    inBraces({ () => recovering(K.Case.matches, () => loop(List())) })

  /** Parses and returns a case in a match expression. */
  private def matchCase(): Match.Case =
    val s = peek.map((t) => t.site)
    if take(K.Case) == None then
      report(ExpectedTokenError(K.Case, emptySiteAtLastBoundary))
    val p = pattern()
    if take(K.Then) == None then
      recover(
        ExpectedTokenError(K.Then, emptySiteAtLastBoundary),
        (e) => Match.Case(p, ErrorTree(e), s.get.extendedTo(lastBoundary)))
    else
      val b = expression()
      Match.Case(p, b, s.get.extendedTo(lastBoundary))

  /** Parses and returns a let expression. */
  private[parsing] def let(): Let =
    val bind = binding()
    val body = inBraces(expression)
    Let(bind, body, bind.site.extendedToCover(body.site)) 

  /** Parses and returns a lambda or parenthesized term-level expression. */
  private def lambdaOrParenthesizedExpression(): Expression =
    def consumeParentheses(count: Int): Boolean = 
      if count < 0 then
        false
      else
        take() match 
          case Some(Token(K.LParen, _)) =>
            consumeParentheses(count + 1)
          case Some(Token(K.RParen, _)) =>
            if count - 1 == 0 then 
              true
            else
              consumeParentheses(count - 1)
          case Some(_) =>
            consumeParentheses(count)
          case None => 
            false

    def isLambda(): Boolean =
      val snap = snapshot()
      if !consumeParentheses(0) then
        restore(snap)
        throw Panic("# of lparen not matching # of rparen")
      else
        take() match
          case Some(Token(K.LBrace | K.Arrow, _)) =>
            restore(snap)
            true
          case _ =>
            restore(snap)
            false

    def lambda(): Lambda =
      val inputs = valueParameterList()
      val output = peek match
        case Some(Token(K.Arrow, _)) =>
          val arrow = expect(K.Arrow)
          Some(tpe())
        case _ =>
          None
      val body = inBraces(expression)
      val site = if !inputs.isEmpty then
        inputs.head.site.extendedToCover(body.site)
      else if output.isDefined then
        output.get.site.extendedToCover(body.site)
      else
        body.site
      Lambda(inputs, output, body, site)

    def parenthesizedExpression(): ParenthesizedExpression = 
      val expr = inParentheses(expression)
      ParenthesizedExpression(expr, expr.site)

    if isLambda() then
      val snap = snapshot()
      val res = Try(lambda())
      res match 
        case Success(l) => 
          l
        case Failure(e) =>  
          restore(snap)
          parenthesizedExpression()
    else
      parenthesizedExpression()

  /** Parses and returns an operator. */
  private def operator(): Expression =
    operatorIdentifier() match
      case (Some(o), p) => Identifier(p.text.toString, p)
      case (_, p) => ErrorTree(p)

  /** Parses and returns an operator identifier, along with its source positions.
   *
   *  If the the parsed operator is undefined, a diagnostic is reported and the returned identifier
   *  is `None`. In any case, the returned span represents the positions of the parsed identifier.
   */
  private def operatorIdentifier(): (Option[ast.OperatorIdentifier], SourceSpan) =
    import ast.OperatorIdentifier as O

    @tailrec def loop(start: Int, end: Int): (Option[ast.OperatorIdentifier], SourceSpan) =
      if takeIf((t) => t.isOperatorPartImmediatelyAfter(end)) != None then
        loop(start, lastBoundary)
      else
        val p = source.span(start, end)
        val s = p.text
        val o = if s == "||" then
          Some(O.LogicalOr)
        else if s == "&&" then
          Some(O.LogicalAnd)
        else if s == "<" then
          Some(O.LessThan)
        else if s == "<=" then
          Some(O.LessThanOrEqual)
        else if s == ">" then
          Some(O.GreaterThan)
        else if s == ">=" then
          Some(O.GreaterThanOrEqual)
        else if s == "==" then
          Some(O.Equal)
        else if s == "!=" then
          Some(O.NotEqual)
        else if s == "..." then
          Some(O.ClosedRange)
        else if s == "..<" then
          Some(O.HaflOpenRange)
        else if s == "+" then
          Some(O.Plus)
        else if s == "-" then
          Some(O.Minus)
        else if s == "|" then
          Some(O.BitwiseOr)
        else if s == "^" then
          Some(O.BitwiseXor)
        else if s == "*" then
          Some(O.Star)
        else if s == "/" then
          Some(O.Slash)
        else if s == "%" then
          Some(O.Percent)
        else if s == "&" then
          Some(O.Ampersand)
        else if s == "<<" then
          Some(O.LeftShift)
        else if s == ">>" then
          Some(O.RightShift)
        else if s == "~" then
          Some(O.Tilde)
        else if s == "!" then
          Some(O.Bang)
        else
          report(SyntaxError(s"undefined operator '${s}'", p))
          None
        (o, p)

    val h = expect("operator", (t) => t.kind.isOperatorPart)
    loop(h.site.start, h.site.end)

  /** Parses and returns a type cast operator. */
  private def typecast(): Typecast =
    peek match
      case Some(Token(K.At, _)) =>
        take(); Typecast.Widen
      case Some(Token(K.AtQuery, _)) =>
        take(); Typecast.Narrow
      case Some(Token(K.AtBang, _)) =>
        take(); Typecast.NarrowUnconditionally
      case _ =>
        throw FatalError("expected typecast operator", emptySiteAtLastBoundary)

  // --- Types ----------------------------------------------------------------

  /** Parses and returns a type-level expression. */
  private[parsing] def tpe(): Type =
    def rec(tpeList: List[Type]): List[Type] =
      peek match
        case Some(t: Token) if t.kind == K.Operator && t.site.text.toString == "|" => 
          expect(K.Operator)
          rec(tpeList :+ primaryType())
        case _ =>
          tpeList
    val firstTpe = primaryType()
    val tpeList = rec(List(firstTpe))
    tpeList match
      case head :: Nil =>
        head
      case head :: tail =>
        Sum(tpeList, firstTpe.site.extendedToCover(tpeList.last.site))
      case _ =>
        throw Panic("no type found")

  /** Parses and returns a type-level primary exression. */
  private def primaryType(): Type =
    peek match
      case Some(Token(K.Identifier, s)) =>
        typeIdentifier()
      case Some(Token(K.Label, _)) =>
        recordType()
      case Some(Token(K.LParen, _)) =>
        arrowOrParenthesizedType()
      case _ =>
        recover(ExpectedTree("type expression", emptySiteAtLastBoundary), ErrorTree.apply)

  /** Parses and returns a type identifier. */
  private def typeIdentifier(): Type =
    take(K.Identifier) match
      case Some(t) =>
        new TypeIdentifier(t)
      case _ => 
        throw Panic("no identifier token")

  /** Parses and returns a list of type arguments. */
  private def typeArguments(): List[Labeled[Type]] =
    parenthesizedLabeledList(tpe)

  /** Parses and returns a type-level record expressions. */
  private[parsing] def recordType(): RecordType =
    val make = (id: String, fields: List[Labeled[Type]], site: SourceSpan) =>
      RecordType(id, fields, site)
    record(recordTypeFields, make)

  /** Parses and returns the fields of a type-level record expression. */
  private def recordTypeFields(): List[Labeled[Type]] =
    peek match
      case Some(Token(K.LParen, _)) =>
        parenthesizedLabeledList(tpe)
      case _ =>
        Nil

  /** Parses and returns a arrow or parenthesized type-level expression. */
  private[parsing] def arrowOrParenthesizedType(): Type =
    typeArguments() match
      case list if peek.exists(_.kind == K.Arrow) =>
        val arrow = expect(K.Arrow)
        val outTpe = tpe()
        val site = list match
          case head :: tail =>
            list.head.site.extendedToCover(outTpe.site)
          case Nil => 
            arrow.site.extendedToCover(outTpe.site)
        Arrow(list, outTpe, site)
      case parenTpe :: Nil =>
        ParenthesizedType(parenTpe.value, parenTpe.value.site)
      case _ =>
        throw Panic("no type found")

  // --- Patterns -------------------------------------------------------------

  /** Parses and returns a pattern. */
  private[parsing] def pattern(): Pattern =
    peek match
      case Some(Token(K.Underscore, _)) =>
        wildcard()
      case Some(Token(K.Label, _)) =>
        recordPattern()
      case Some(Token(K.Let, _)) =>
        bindingPattern()
      case _ =>
        valuePattern()

  /** Parses and returns a wildcard pattern. */
  def wildcard(): Wildcard =
    val wc = expect(K.Underscore)
    Wildcard(wc.site)

  /** Parses and returns a record pattern. */
  private def recordPattern(): RecordPattern =
    val make = (id: String, fields: List[Labeled[Pattern]], site: SourceSpan) =>
      RecordPattern(id, fields, site)
    record(recordPatternFields, make)

  /** Parses and returns the fields of a record pattern. */
  private def recordPatternFields(): List[Labeled[Pattern]] =
    peek match
      case Some(Token(K.LParen, _)) =>
        parenthesizedLabeledList(pattern)
      case _ =>
        Nil

  /** Parses and returns a binding pattern. */
  private def bindingPattern(): Binding =
    binding(false)

  /** Parses and returns a value pattern. */
  private def valuePattern(): ValuePattern =
    val value = expression()
    ValuePattern(value, value.site)

  // --- Common trees ---------------------------------------------------------

  /** Parses and returns an identifier. */
  private def identifier(): Identifier =
    val s = expect(K.Identifier)
    Identifier(s.site.text.toString, s.site)

  // --- Combinators ----------------------------------------------------------

  /** Parses and returns a record.
   *
   *  @param fields A closure parsing the fields of the record.
   *  @param make A closure constructing a record tree from its name, fields, and site.
   */
  private def record[Field <: Labeled[Tree], T <: RecordPrototype[Field]](
      fields: () => List[Field],
      make: (String, List[Field], SourceSpan) => T
  ): T =
    val lab = expect(K.Label)
    val fieldList = fields()
    val site = if !fieldList.isEmpty then
      lab.site.extendedTo(fieldList.last.site.end + 1)
    else 
      lab.site.extendedToCover(lab.site)
    make(lab.site.text.toString, fieldList, site)

  /** Parses and returns a parenthesized list of labeled value.
   *
   *  See also [[this.labeledList]].
   *
   *  @param value A closure parsing a labeled value.
   */
  private[parsing] def parenthesizedLabeledList[T <: Tree](
      value: () => T
  ): List[Labeled[T]] =
    val isTerminator = (token: Token) => token.kind == K.RParen
    val element = () => commaSeparatedList(isTerminator, () => labeled(value))
    inParentheses(element)

  /** Parses and returns a value optionally prefixed by a label.
   *
   *  This combinator attempts to parse a label `n` followed by a colon and then applies `value`.
   *  If that succeeds, returned tree is the result of `value` labeled by `n`. If there is no label,
   *  the combinator backtracks, re-applies `value`, and returns its result sans label.
   *
   *  @param value A closure parsing a labeled value.
   */
  private[parsing] def labeled[T <: Tree](
      value: () => T
  ): Labeled[T] =
    peek match
      case Some(Token(K.Identifier, _)) =>
        val snap = snapshot()
        val id = identifier()
        take(K.Colon) match
          case Some(col) =>
            val labVal = value()
            Labeled(Some(id.value), labVal, id.site.extendedToCover(labVal.site)) 
          case None => 
            restore(snap)
            val labVal = value()
            Labeled(None, labVal, labVal.site)
      case Some(t: Token) if t.kind.isKeyword =>
        val snap = snapshot()
        val kw = take() match
          case Some(t) => 
            t
          case _ =>
            throw Panic("no next token")
          take(K.Colon) match
            case Some(col) =>
              val labVal = value()
              Labeled(Some(kw.site.text.toString), labVal, kw.site.extendedToCover(labVal.site))
            case None =>
              restore(snap)
              val labVal = value()
              Labeled(None, labVal, labVal.site)
      case Some(_) =>
        val labVal = value()
        Labeled(None, labVal, labVal.site)
      case _ =>
        throw Panic("not a valid label")

  /** Parses and returns a sequence of `element` separated by commas and delimited on the RHS  by a
   *  token satisfying `isTerminator`.
   */
  private[parsing] def commaSeparatedList[T](isTerminator: Token => Boolean, element: () => T): List[T] =
    @tailrec def loop(partialResult: List[T]): List[T] =
      if peek.map(isTerminator).getOrElse(false) then
        partialResult
      else
        val nextPartialResult = partialResult :+ recovering(K.Comma.matches, element)
        if peek.map(isTerminator).getOrElse(false) then
          nextPartialResult
        else if take(K.Comma) != None then
          loop(nextPartialResult)
        else
          report(ExpectedTokenError(K.Comma, emptySiteAtLastBoundary))
          loop(nextPartialResult)
    loop(List())

  /** Parses and returns `element` surrounded by a pair of parentheses. */
  private[parsing] def inParentheses[T](element: () => T): T =
    expect(K.LParen)
    val value = element()
    expect(K.RParen)
    value

  /** Parses and returns `element` surrounded by a pair of braces. */
  private[parsing] def inBraces[T](element: () => T): T =
    expect(K.LBrace)
    val value = element()
    expect(K.RBrace)
    value

  /** Parses and returns `element` surrounded by angle brackets. */
  private[parsing] def inAngles[T](element: () => T): T =
    expect(K.LAngle)
    val value = element()
    expect(K.RAngle)
    value

  /** Parses and returns `element` surrounded by a `left` and `right`. */
  private[parsing] def delimited[T](left: Token.Kind, right: Token.Kind, element: () => T): T =
    if take(left) == None then
      report(ExpectedTokenError(right, emptySiteAtLastBoundary))
    val contents = recovering(right.matches, element)
    if take(right) == None then
      report(ExpectedTokenError(right, emptySiteAtLastBoundary))
    contents

  /** Returns the result of `element` with `isRecoveryToken` added to the recovery predicates. */
  private def recovering[T](isRecoveryToken: Token => Boolean, element: () => T): T =
    recoveryPredicates += isRecoveryToken
    try
      element()
    finally
      recoveryPredicates.dropRightInPlace(1)

  // --- Utilities ------------------------------------------------------------

  /** Returns `true` iff there isn't any whitespace before the next token in the stream. */
  private def noWhitespaceBeforeNextToken: Boolean =
    peek.map((t) => lastBoundary == t.site.start).getOrElse(false)

  /** Reports a missing identifier and returns "_". */
  def missingName =
    report(ExpectedTokenError(K.Identifier, emptySiteAtLastBoundary))
    "_"

  /** Reports `error`, advances the stream to the next recovery token, and returns the result of
   *  calling `errorTree` on the skipped positions.
   */
  private def recover[T](error: SyntaxError, errorTree: SourceSpan => T): T =
    report(error)
    errorTree(discardUntilRecovery())

  /** Advances the stream to the next recovery token and returns the skipped positions. */
  private def discardUntilRecovery(): SourceSpan =
    @tailrec def loop(s: Int): SourceSpan =
      if !peek.isDefined || Reverse(recoveryPredicates).exists((p) => p(peek.get)) then
        source.span(s, lastBoundary)
      else
        take()
        loop(s)
    loop(lastBoundary)

  /** Consumes and returns the next token in the stream iff it has kind `k` or throw an exception
    * otherwise,
    */
  private def expect(construct: String, predicate: (Token) => Boolean): Token =
    takeIf(predicate) match
      case Some(next) => next
      case _ => throw FatalError(s"expected ${construct}", emptySiteAtLastBoundary)

  /** Consumes and returns the next token in the stream iff it has kind `k` or throw an exception
    * otherwise,
    */
  private def expect(k: Token.Kind): Token =
    take(k) match
      case Some(next) => next
      case _ => throw FatalError(s"expected ${k}", emptySiteAtLastBoundary)

  /** Returns the next token in the stream without consuming it. */
  private def peek: Option[Token] =
    if lookahead == None then
      lookahead = tokens.next()
    lookahead

  /** Consumes the next token in the stream iff it has kind `k` and returns the result of `action`
   *  applied on that token. */
  private def taking[T](k: Token.Kind, action: Token => T): Option[T] =
    take(k).map(action)

  /** Consumes and returns the next token in the stream. */
  private def take(): Option[Token] =
    peek.map({ (next) =>
      lastBoundary = next.site.end
      lookahead = None
      next
    })

  /** Consumes and returns the next token in the stream iff it has kind `k`. */
  private def take(k: Token.Kind): Option[Token] =
    takeIf(k.matches)

  /** Consumes and returns the next character in the stream iff it satisfies `predicate`. */
  private def takeIf(predicate: Token => Boolean): Option[Token] =
    if peek.map(predicate).getOrElse(false) then take() else None

  /** Returns an empty range at the position of the last consumed token. */
  private def emptySiteAtLastBoundary: SourceSpan =
    source.span(lastBoundary, lastBoundary)

  /** Reports the given diagnostic. */
  private def report(d: SyntaxError): Unit =
    errors += d

  /** Returns a backup of this instance's state. */
  private[parsing] def snapshot(): Parser.Snapshot =
    Parser.Snapshot(
      tokens.copy(), lastBoundary, lookahead, errors.length, recoveryPredicates.length)

  /** Restores this instance to state `s`. */
  private[parsing] def restore(s: Parser.Snapshot): Unit =
    tokens = s.tokens
    lastBoundary = s.lastBoundary
    lookahead = s.lookahead
    errors.dropRightInPlace(errors.length - s.errorCount)
    recoveryPredicates.dropRightInPlace(recoveryPredicates.length - s.recoveryPredicateCount)

end Parser

object Parser:

  /** The information necessary to restore the state of a parser instance. */
  private[parsing] final case class Snapshot(
      tokens: Lexer,
      lastBoundary: Int,
      lookahead: Option[Token],
      errorCount: Int,
      recoveryPredicateCount: Int)

end Parser

extension (self: Token.Kind) def | (other: Token.Kind): (Token) => Boolean =
  (t) => (t.kind == self) || (t.kind == other)

extension (self: Token => Boolean) def | (other: Token.Kind): (Token) => Boolean =
  (t) => self(t) || (t.kind == other)

