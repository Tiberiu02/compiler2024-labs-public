package alpine
package parsing

import alpine.ast
import alpine.util.FatalError

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.SeqView.Reverse
import alpine.evaluation.Panic

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
    expect(K.Let)
    val id = expect(K.Identifier)
    val binding_tp = if take(K.Colon) != None then Some(tpe()) else None
    val init = if take(K.Eq) != None then Some(expression()) else None
    if initializerIsExpected && init.isEmpty then
      report(ExpectedTokenError(K.Eq, emptySiteAtLastBoundary))
    Binding(id.site.text.toString, binding_tp, init, id.site.extendedTo(lastBoundary))



  /** Parses and returns a function declaration. */
  private[parsing] def function(): Function =
    expect(K.Fun)
    val name = expect(K.Identifier)
    // val typeParameters = typeParameterList() 
    val typeParameters = List() // Not sure why Function takes type parameters. This is not part of the grammar
    val valueParameters = valueParameterList()
    val returnType = if take(K.Arrow) != None then Some(tpe()) else None
    take(K.LBrace)
    val body = expression()
    take(K.RBrace)
    Function(name.site.text.toString, typeParameters, valueParameters, returnType, body, name.site.extendedTo(lastBoundary))

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
    inParentheses(() => commaSeparatedList(K.RParen.matches, parameter))
      .collect({ case p: Parameter => p })

  /** Parses and returns a parameter declaration. */
  private[parsing] def parameter(): Declaration =

    val s = take().get
    val label = if s.kind == K.Identifier || s.kind.isKeyword then Some(s.site.text.toString) else None
    println(s.kind)
    println(label)
    val name = expect(K.Identifier).site.text.toString
    val tp = if take(K.Colon) != None then Some(tpe()) else None
    Parameter(label, name, tp, s.site.extendedTo(lastBoundary))


  /** Parses and returns a type declaration. */
  private[parsing] def typeDeclaration(): TypeDeclaration =
    take(K.Type)
    val name = expect(K.Identifier)
    // val typeParameters = typeParameterList()
    val typeParameters = List() // Not sure why TypeDeclaration takes parameters. This is not part of the grammar
    take(K.Eq)
    val body = tpe()
    TypeDeclaration(name.site.text.toString, typeParameters, body, name.site.extendedTo(lastBoundary))

  /** Parses and returns a list of parameter declarations in angle brackets. */
  //--- This is intentionally left in the handout /*+++ +++*/
  private def typeParameterList(): List[Parameter] =
    inAngles(() => commaSeparatedList(K.RAngle.matches, parameter))
      .collect({ case p: Parameter => p })

  // --- Expressions ----------------------------------------------------------

  /** Parses and returns a term-level expression. */
  def expression(): Expression =
    infixExpression()

  /** 
   * Parses and returns an infix expression. As we saw in the lecture, parsing expressions requires care because of the ambiguity introduced by precedence.
   * Notice that infixEpression takes a precendence as input: you may use it this parameter to factor out the parsing of all possible infix expressions with different precedence levels.
   * You may take inspiration from the precedence climbing algorithm to parse infix expressions.
   *  **/
  private[parsing] def infixExpression(precedence: Int = ast.OperatorPrecedence.min): Expression =
    // helper function for that algorithm on wiki
    def helper(preced: Int, lhs: Expression): Expression =
      peek match
        case Some(Token(K.Operator, _)) =>
          val opId1 = operatorIdentifier()
          val rhs = ascribed()
          if opId1._1.get.precedence >= preced then

            peek match
              case Some(Token(K.Operator, _)) =>
                val backupPoint = snapshot()
                val opId2 = operatorIdentifier()
                restore(backupPoint)

                if opId2._1.get.precedence > opId1._1.get.precedence then
                  val updatedrhs = helper(opId2._1.get.precedence, rhs)

                  InfixApplication(Identifier(opId1._1.get.toString, opId1._2), 
                    lhs, updatedrhs, lhs.site.extendedToCover(updatedrhs.site))
                else
                  val newLhs = InfixApplication(Identifier(opId1._1.get.toString, opId1._2), lhs, rhs, 
                    lhs.site.extendedToCover(rhs.site))
                  helper(opId2._1.get.precedence, newLhs)

              case _ =>
                InfixApplication(Identifier(opId1._1.get.toString, opId1._2), 
                  lhs, rhs, lhs.site.extendedToCover(rhs.site))

          else 
            val newLhs = InfixApplication(Identifier(opId1._1.get.toString, opId1._2), 
              lhs, rhs, lhs.site.extendedToCover(rhs.site))

            helper(opId1._1.get.precedence, newLhs)

        case _ =>
          lhs
            
    helper(precedence, ascribed())

  
     
  /** Parses and returns an expression with an optional ascription. */
  private[parsing] def ascribed(): Expression =
    val prefixExpresion = prefixExpression()
    peek match
      case Some(Token(K.AtBang, _)) | Some(Token(K.At, _)) | Some(Token(K.AtQuery, _)) =>
        val operation = typecast()
        val typeIdenfitier = typeIdentifier()

        AscribedExpression(prefixExpresion, operation, typeIdenfitier, 
          prefixExpresion.site.extendedTo(lastBoundary))
      case _ =>
        prefixExpresion

  /** Parses and returns a prefix application. */
  private[parsing] def prefixExpression(): Expression =
    peek match {
      case Some(Token(K.Operator, _)) =>
        val operator = take(K.Operator).get
        val ident = Identifier(operator.site.text.toString, operator.site.extendedTo(lastBoundary))
        if noWhitespaceBeforeNextToken then
          val compoundExpr = compoundExpression()
          PrefixApplication(ident, compoundExpr, ident.site.extendedTo(lastBoundary))
        else
          ident
      case _ =>
        compoundExpression()
    }

  /** Parses and returns a compound expression. */
  // CompoundExpression -> PrimaryExpression ['.' Integer | '.' Identifier | '.' InfixOp | '(' LabeledExpressionList ')']
  private[parsing] def compoundExpression(): Expression =
    val e = primaryExpression()
    peek match
      case Some(Token(K.Dot, _)) =>
        take()
        val s = peek match {
          case Some(Token(K.Integer, _)) => integerLiteral()
          case Some(Token(K.Identifier, _)) => identifier()
          case Some(Token(K.Operator, _)) => operator()
          case _ => throw FatalError("expected integer, identifier, or operator", emptySiteAtLastBoundary)
        }
        Selection(e, s.asInstanceOf[ast.Selectee], e.site.extendedTo(lastBoundary))
      case Some(Token(K.LParen, _)) =>
        val l = parenthesizedLabeledList(() => expression())
        Application(e, l, e.site.extendedTo(lastBoundary))
      case _ =>
        e

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
    record(() => recordExpressionFields(), Record.apply)

  /** Parses and returns the fields of a term-level record expression. */
  private def recordExpressionFields(): List[Labeled[Expression]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(expression)))

  /** Parses and returns a conditional expression. */
  private[parsing] def conditional(): Expression =
    take(K.If)
    val c = expression()
    take(K.Then)
    val t = expression()
    take(K.Else)
    val e = expression()
    Conditional(c, t, e, c.site.extendedTo(lastBoundary))

  /** Parses and returns a match expression. */
  private[parsing] def mtch(): Expression =
    take(K.Match)
    val matchExpression = expression()
    val body = matchBody()
    Match(matchExpression, body, matchExpression.site.extendedTo(lastBoundary))

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
    val b = binding()
    val body = inBraces(() => expression())
    Let(b, body, b.site.extendedTo(lastBoundary))

  /** Parses and returns a lambda or parenthesized term-level expression. */
  private def lambdaOrParenthesizedExpression(): Expression =
    val backupPoint = snapshot()
    inParentheses(() => ()) // skip parentheses

    peek match 
      case Some(Token(K.Arrow, _)) | Some(Token(K.LBrace, _)) =>
        restore(backupPoint)
        val inputs = valueParameterList()
        val output = peek match
          case Some(Token(K.Arrow, _)) =>
            Some(tpe())
          case _ => None
        val token = take(K.LBrace)
        val innerExpr = expression()
        take(K.RBrace)
        Lambda(inputs, output, innerExpr, token.get.site.extendedTo(lastBoundary))

      case _ =>
        restore(backupPoint)
        val token = take(K.LParen)
        ParenthesizedExpression(expression(), 
          token.get.site.extendedTo(lastBoundary))

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
    val t = primaryType()
    def isTypeUnionOperator(t: Token): Boolean =
      t.site.text == "|"
    if peek.map(isTypeUnionOperator).getOrElse(false) then
      @tailrec def loop(partialResult: List[Type]): List[Type] =
        if !peek.map(isTypeUnionOperator).getOrElse(false) then
          partialResult
        else
          take(K.Operator)
          val nextPartialResult = partialResult :+ primaryType()
          if !peek.map(isTypeUnionOperator).getOrElse(false) then
            nextPartialResult
          else if take(K.Comma) != None then
            loop(nextPartialResult)
          else
            report(ExpectedTokenError(K.Comma, emptySiteAtLastBoundary))
            loop(nextPartialResult)
      
      Sum(loop(List(t)), t.site.extendedTo(lastBoundary))
    else
      t


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
    val id = expect(K.Identifier)
    TypeIdentifier(id.site.text.toString, id.site.extendedTo(lastBoundary))

  /** Parses and returns a list of type arguments. */
  private def typeArguments(): List[Labeled[Type]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(tpe)))

  /** Parses and returns a type-level record expressions. */
  private[parsing] def recordType(): RecordType =
    val label = expect(K.Label)
    val fields = if peek.map(K.LParen.matches).getOrElse(false) then inParentheses(() => recordTypeFields()) else List()
    RecordType(label.site.text.toString, fields, label.site.extendedTo(lastBoundary))

  /** Parses and returns the fields of a type-level record expression. */
  private def recordTypeFields(): List[Labeled[Type]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(() => tpe())))


  /** Parses and returns a arrow or parenthesized type-level expression. */
  private[parsing] def arrowOrParenthesizedType(): Type =
    val paren = take(K.LParen)
    val backupPoint = snapshot()
    val inTypes = typeArguments()
    take(K.RParen)
    peek match
      case Some(Token(K.Arrow, _)) =>
        val arrowToken = take(K.Arrow).get
        val outType = tpe()
        Arrow(inTypes, outType, arrowToken.site.extendedTo(lastBoundary))
      case _ =>
        restore(backupPoint)
        ParenthesizedType(tpe(), paren.get.site.extendedTo(lastBoundary))

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
    val s = take(K.Underscore).get
    Wildcard(s.site.extendedTo(lastBoundary))

  /** Parses and returns a record pattern. */
  private def recordPattern(): RecordPattern =
    val label = expect(K.Label)
    peek match
      case Some(Token(K.LParen, _)) =>
        val fields = inParentheses(() => recordPatternFields())
        RecordPattern(label.site.text.toString, fields, label.site.extendedTo(lastBoundary))
      case _ =>
        RecordPattern(label.site.text.toString, List(), label.site.extendedTo(lastBoundary))

  /** Parses and returns the fields of a record pattern. */
  private def recordPatternFields(): List[Labeled[Pattern]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(pattern)))

  /** Parses and returns a binding pattern. */
  private def bindingPattern(): Binding =
    take(K.Let)
    val id = expect(K.Identifier)
    val tp = if take(K.Colon) != None then Some(tpe()) else None
    val hasInit = take(K.Eq)
    if !hasInit.isEmpty then
      report(ExpectedTokenError(K.Eq, emptySiteAtLastBoundary))
      Binding(id.site.text.toString, tp, None, id.site.extendedTo(lastBoundary))
    else
      Binding(id.site.text.toString, tp, None, id.site.extendedTo(lastBoundary))

  /** Parses and returns a value pattern. */
  private def valuePattern(): ValuePattern =
    val e = expression()
    ValuePattern(e, e.site)

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
    val label = expect(K.Label)
    peek match
      case Some(Token(K.LParen, _)) =>
        val fs = inParentheses(fields)
        make(label.site.text.toString, fs, label.site.extendedTo(lastBoundary))
      case _ =>
        make(label.site.text.toString, List(), label.site.extendedTo(lastBoundary))
  
  /** Parses and returns a parenthesized list of labeled value.
   *
   *  See also [[this.labeledList]].
   *
   *  @param value A closure parsing a labeled value.
   */
  private[parsing] def parenthesizedLabeledList[T <: Tree](
      value: () => T
  ): List[Labeled[T]] =
    inParentheses(() => commaSeparatedList(K.RParen.matches, () => labeled(value)))



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
      // use the functions restore and snapshot
      // may want to backtrack using restore with the snapshot if the combinator fails 

      val stateBeforeAttempt = snapshot()

      peek match
        case Some(t) =>
          if t.kind.isKeyword || t.kind == K.Identifier then
            val n = take().get
            take(K.Colon) match
              case Some(_) =>
                val v = value()
                Labeled(Some(n.site.text.toString), v, n.site.extendedTo(lastBoundary))
              case None =>
                restore(stateBeforeAttempt)
                val v = value()
                Labeled(None, v, v.site.extendedTo(lastBoundary))
          else
            val v = value()
            Labeled(None, v, v.site.extendedTo(lastBoundary))

        case None => 
          throw new IllegalStateException("peek should not return None")
          val v = value() // report an error
          Labeled(None, v, v.site.extendedTo(lastBoundary))

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
    take(K.LParen)
    val parsedExpression = element()
    take(K.RParen)
    parsedExpression

  /** Parses and returns `element` surrounded by a pair of braces. */
  private[parsing] def inBraces[T](element: () => T): T =
    take(K.LBrace)
    val parsedExpression = element()
    take(K.RBrace)
    parsedExpression

  /** Parses and returns `element` surrounded by angle brackets. */
  private[parsing] def inAngles[T](element: () => T): T =
    take(K.LAngle)
    val parsedExpression = element()
    take(K.RAngle)
    parsedExpression
    

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
