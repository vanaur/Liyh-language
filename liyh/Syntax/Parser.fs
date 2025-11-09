#nowarn "25"
namespace Liyh.Syntax

module Parser =
    open FParsec
    open Liyh.Utils.ErrorReporter
    open Indentation
    open SyntaxTree
    open MixFix
    open MixFixPattern

    let private pipe6 p1 p2 p3 p4 p5 p6 action =
        parse {
            let! a = p1
            let! b = p2
            let! c = p3
            let! d = p4
            let! e = p5
            let! f = p6

            return action a b c d e f
        }

    let private pipe7 p1 p2 p3 p4 p5 p6 p7 action =
        parse {
            let! a = p1
            let! b = p2
            let! c = p3
            let! d = p4
            let! e = p5
            let! f = p6
            let! g = p7

            return action a b c d e f g
        }

    // Notation state type that manages mixfix operators
    type public NotationState = 
        { MixfixOperators: MixfixOperator list }

    // Default notation state with basic operators
    let private defaultNotationState =
        { MixfixOperators = [] }

    let private emptyNotationState =
        { MixfixOperators = [] }

    // Utilities to work with notation state
    let private getMixfixOperators: Parser<MixfixOperator list, NotationState IndentState> =
        fun stream -> Reply stream.UserState.UserState.MixfixOperators
    
    let private addMixfixOperator (op: MixfixOperator): Parser<unit, NotationState IndentState> =
        fun stream ->
            stream.UserState <-
                { stream.UserState with
                    UserState =
                        { stream.UserState.UserState with
                            MixfixOperators = op :: stream.UserState.UserState.MixfixOperators } }

            Reply Unchecked.defaultof<unit>

    // Forward reference to resolve recursion
    let private parseExpressionRefHolder = createParserForwardedToRef<ExpressionWithPos, NotationState IndentState>()
    let private parseExpressionRef = fst parseExpressionRefHolder
    let private parseExpressionImpl = snd parseExpressionRefHolder

    /// Reserved names and symbols for the language.
    let private reserved =
        [ "for"; "in"; "let"; "var"; "while"; "do"; "match"; "is"; "as"; "_"; "->"; "["; "match"; "|>";
          "if"; "then"; "else"; "("; "{"; "}"; ")"; "]"; "<-"; "with"; "handle"; "export"; "effect"; "=";
          "notation"; "using"; "use"; "innermost"; "outermost"; "unreachable"; "--"; "to"; "downto"; "type";
          "type-alias"; "."; ]

    /// Retrieves operator parts defined by user custom notations.
    let private reservedByUser (id: string) (operators: MixfixOperator list) =
        operators
        |> List.map (fun { Pattern = pattern; Name = name } ->
            pattern
            |> List.filter _.IsFixed
            |> List.map (function Fixed s -> s), name)
        |> List.tryPick (fun (parts, opName) -> if List.contains id parts then Some opName else None)

    let private spacesOrComment =
        spaces >>. optional (skipString "--" <?> "" >>. skipRestOfLine true) >>. spaces

    module private NameParser =

        /// Parses a valid name according to the Liyh specification and returns it as a character string.
        /// This parser may fail in a definition context if the name is already defined in a custom notation.
        /// The `export` parameter disables this failure if set to `true`.
        let public parseName (export: bool) =
            let parseUsualName =
                regex @"[_\p{L}][_\p{L}\p{N}]*"
                <?> "valid name (unicode string that does not begin with a number or '_')"

            let parsePlainName =
                between
                    (pchar '`')
                    (pchar '`')
                    (many1
                        (satisfy (fun c -> c <> '`' && c <> '\n' && c <> '\r'))
                        |>> fun cs -> System.String.Join("", cs))

            choice [ parseUsualName; parsePlainName ]
            >>= fun name ->
                parse {
                    let! operators = getMixfixOperators
                    match reservedByUser name operators with
                    | None ->
                        if List.contains name reserved
                        then return! fail (sprintf "'%s' is a reserved symbol by the language" name)
                        else return name

                    | Some userReservedIn ->
                        if export then return name
                        else
                            return! fail
                                (sprintf "'%s' is reserved by the user/lib-defined notation '%s' and cannot be used as a name"
                                    name
                                    userReservedIn)
                }

        /// Parses a valid name according to the Liyh specification and returns it as a character string.
        /// This parser may fail in a definition context if the name is already defined in a custom notation.
        let public parseIdentifierName =
            parseName false <?> "valid name" >>= fun name ->
                if List.contains name reserved
                then fail (sprintf "reserved identifier '%s'" name)
                else preturn name

        /// Parses a valid identifier according to the Liyh specification (names separated by dots).
        /// This parser may fail in a definition context if the name is already defined in a custom notation.
        let public parseIdentifier =
            parseWithPos parseIdentifierName >>= fun firstName ->
                let rec parseQualifiers acc =
                    choice [
                        attempt
                            (pchar '.'
                                >>. lookAhead (parseWithPos parseIdentifierName)
                                >>. parseWithPos parseIdentifierName)
                            >>= fun nextName -> parseQualifiers (nextName :: acc)

                        preturn acc
                    ]

                parseQualifiers [] |>> fun qualifierParts ->
                    match List.rev qualifierParts with
                    | [] -> { Qualifier = []; Name = firstName }
                    | qualifiers ->
                        { Qualifier = firstName :: List.take (List.length qualifiers - 1) qualifiers
                          Name = List.last qualifiers }

    module private LiteralParser =

        let private parseDigitsWithUnderscores: Parser<string, _ IndentState> =
            let digitGroup = many1Chars (digit <?> "")
            let underscore = skipChar '_' <?> ""

            pipe2
                digitGroup
                (many (underscore >>. digitGroup))
                (fun firstGroup restGroup -> firstGroup :: restGroup |> String.concat "")

        let private parseNumberParts: Parser<string * string option * string option, _ IndentState> =
            let sign =
                opt (pchar '+' <|> pchar '-') |>>
                    function
                    | Some c -> string c
                    | None -> ""

            let intPart = parseDigitsWithUnderscores
            let floatPart = opt (skipChar '.' <?> "decimal part" >>. parseDigitsWithUnderscores)
            let expPart =
                opt ((skipChar 'e' <|> skipChar 'E') <?> ""
                    >>. pipe2
                            (opt (pchar '+' <|> pchar '-') |>>
                                function
                                | Some c -> string c
                                | None -> "")
                            parseDigitsWithUnderscores
                            ( + ))

            pipe3
                (pipe2 sign intPart ( + ))
                floatPart
                expPart
                (fun intPart floatPart expPart -> (intPart, floatPart, expPart))

        let private parseInteger: Parser<int64, _ IndentState> =
            parse {
                let! (intPart, floatPart, expPart) = parseNumberParts

                if floatPart.IsSome || expPart.IsSome then
                    return! fail "Not an integer"
                else
                    let sign = if intPart.StartsWith "-" then -1L else 1L
                    let absValue =
                        if intPart.StartsWith "-" || intPart.StartsWith "+"
                        then intPart.Substring 1
                        else intPart

                    return sign * int64 absValue
            }

        let private parseFloat: Parser<double, _ IndentState> =
            parse {
                let! (intPart, floatPart, expPart) = parseNumberParts

                if floatPart.IsSome || expPart.IsSome then
                    let fracStr =
                        match floatPart with
                        | Some f -> "." + f
                        | None -> ""

                    let expStr =
                        match expPart with
                        | Some e -> "e" + e
                        | None -> ""

                    return double (intPart + fracStr + expStr)
                else
                    return! fail "Not a float"
            }

        let private parseStringInterpolation parseExpr =
            let escapedChar =
                pchar '\\' <?> "" >>.
                    choice [
                        pchar '{' >>% "{"
                        pchar '}' >>% "}"
                        pchar '"' >>% "\""
                        pchar '\\' >>% "\\"
                        pchar 'n' >>% "\n"
                        pchar 't' >>% "\t" ]

            let normalChar = satisfy (fun c -> c <> '{' && c <> '"' && c <> '\\') |>> string
            let textFragment =
                many1 (attempt escapedChar <|> normalChar)
                |>> fun strs -> InterpolatedPart.Str (String.concat "" strs)

            let interpolationFragment =
                between (pchar '{' <?> "") (pchar '}' <?> "") (parseExpr |>> InterpolatedPart.Interpolation)

            let fragment = choice [ attempt interpolationFragment; textFragment ]

            parse {
                let! content = between (skipChar '"') (skipChar '"' <?> "closing string or valid string or valid interpolated string") (many fragment)
                match content |> List.tryFind _.IsInterpolation with
                | Some _ -> return Literal.InterpolatedString content
                | None ->
                    let strContent =
                        content |> List.fold (fun acc frag ->
                            match frag with
                            | InterpolatedPart.Str s -> acc + s
                            | _ -> acc) ""
                    return Literal.String strContent
            }

        let private parseChar =
            let octalDigit = satisfy (fun c -> c >= '0' && c <= '7')

            let parseOctal =
                pipe2 octalDigit (manyMinMaxSatisfy 0 2 (fun c -> c >= '0' && c <= '7'))
                    (fun first rest ->
                        let digits = first :: (List.ofSeq rest)
                        let value = List.fold (fun acc d -> acc * 8 + (int d - int '0')) 0 digits
                        char value)

            let escapedChar =
                pchar '\\' >>.
                    choice [
                        pchar 'n' >>% '\n'
                        pchar 't' >>% '\t'
                        pchar 'r' >>% '\r'
                        pchar '\\' >>% '\\'
                        pchar ''' >>% '''
                        pchar '"' >>% '"'
                        parseOctal  // Séquences octales flexibles
                    ]

            let simpleChar = satisfy (fun c -> c <> ''' && c <> '\\')
            between (pchar ''') (pchar ''') (escapedChar <|> simpleChar)
            |>> Literal.Char

        let public parseLiteral (parseExpr: _ option) =
            let literalParsers =
                [ attempt parseFloat |>> Literal.Float
                  parseInteger |>> Literal.Integer
                  parseChar ]
                @ match parseExpr with
                   | Some p -> [ parseStringInterpolation p ]
                   | None -> []

            let wp = List.map parseWithPos literalParsers
            choice wp <?> "literal"

    module private TypeParser =
        let private typeRefHolder = createParserForwardedToRef()
        let public parseType = fst typeRefHolder
        let private parseTypeRef = snd typeRefHolder

        // 't, 'myVarType
        let private parseVariableType =
            parseWithPos (
                skipChar '\'' >>. NameParser.parseName false
                |>> Type.VariableType
            )

        // _
        let private parseWildcardType =
            parseWithPos (skipChar '_' >>% Type.WildcardType)

        // Int, Bool, MyType, Option['t]
        let private parseNamedType =
            let parseElementAfterComma =
                spaces >>. (parseType <?> "other elements in the parametrized's type") .>> spaces

            parseWithPos (
                parseWithPos NameParser.parseIdentifier
                .>>. opt (
                    skipChar '[' >>. spaces >>.
                    sepBy1 parseElementAfterComma (skipChar ',' <?> "other types") .>>
                    spaces .>> (skipChar ']' <?> "closing ']' to end the parametrized type")
                )
                |>> fun (id, argsOpt) ->
                    match argsOpt with
                    | Some args -> Type.ParametrizedType(id, args)
                    | None -> Type.NamedType(id)
            )

        // (Int, String, Bool)
        let private parseTupleType =
            let comma = skipChar ',' <?> "comma ',' between types"
            let parseElementAfterComma =
                spaces >>. (parseType <?> "other elements in the tuple's type") .>> spaces

            parseWithPos (
                between
                    (skipChar '(' >>. spaces)
                    (spaces >>. skipChar ')' <?> "closing ')' to end tuple")
                    (sepBy1 parseElementAfterComma comma)

                |>> fun types ->
                    match types with
                    | [{ Node = single }] -> single
                    | lst -> Type.TupleType(lst)
            )

        // { a: Int, b: String }
        let private parseRowRecordType =
            let fieldName = NameParser.parseIdentifierName
            let colon = spaces >>. (skipChar ':' >>. spaces <?> "':' after field name")
            let comma = skipChar ',' <?> "comma ',' between fields or closing '}'"
            let closingBrace = skipChar '}' <?> "closing '}' to end record type"

            let field =
                fieldName .>> colon .>>. parseType <?> "other elements in the record"

            let parseFields =
                sepBy1 field (spaces >>. comma >>. spaces)

            parseWithPos (
                skipChar '{' >>. spaces >>.
                parseFields .>>
                spaces .>> closingBrace
                |>> Type.RowRecordType
            )

        // [Int, Int] -> Int
        let private parseRuleType =
            let openBracket = skipChar '['
            let closeBracket = skipChar ']' <?> "closing ']' after function arguments"
            let arrow = skipString "->" <?> "arrow '->' after function arguments"
            let comma = skipChar ',' <?> "comma ',' between arguments"

            let parseElementAfterComma =
                spaces >>. (parseType <?> "other elements in the function type parameters") .>> spaces

            let args =
                openBracket >>. spaces >>.
                sepBy parseElementAfterComma comma .>>
                spaces .>> closeBracket

            parseWithPos (
                pipe2
                    (args .>> spaces .>> arrow .>> spaces)
                    (parseType <?> "return type (the function must return something after '->')")
                    (fun args ret ->
                        let argsList = match args with | [] -> [] | xs -> xs
                        Type.RuleType(argsList, ret)
                    )
            )

        // t1 % { eff₁, eff₂, ..., effₙ }
        let private parseModuloEffectType =
            pipe2
                (spaces >>? skipChar '%' <?> "")
                (spaces >>.
                    between
                        (spaces >>. (skipChar '{' <?> "some effects"))
                        (spaces >>. (skipChar '}' <?> "closing '}'"))
                        (sepBy
                            (spaces >>? (parseWithPos NameParser.parseIdentifier <?> "effect name"))
                            (spaces >>? skipChar ',')))
                (fun _ xs -> xs)

        let private parseTypeWithContext =
            let parsers =
                choice [
                    parseWildcardType
                    parseRuleType
                    parseVariableType
                    parseTupleType
                    parseRowRecordType
                    parseNamedType ] <?> "valid type"

            parsers .>>. opt (parseWithPos parseModuloEffectType)
            |>> function
                | t1, None -> t1
                | t1, Some { Node = effects; Pos = pos; Pos' = pos' } ->
                    { Node = Type.ModuloEffectType(t1, effects); Pos = pos; Pos' = pos' }

        do parseTypeRef.Value <-
            spaces >>. parseTypeWithContext .>> spaces

    module private PatternParser =
        // Forward reference to resolve recursion
        let private parsePatternRefHolder = createParserForwardedToRef<PatternWithPos, NotationState IndentState>()
        let private parsePatternRef = fst parsePatternRefHolder
        let private parsePatternImpl = snd parsePatternRefHolder

        // 'x, 'myVar
        let private parseVariablePattern =
            skipChar '\'' >>. NameParser.parseName false
            |>> Pattern.VariablePattern

        // none, some, zero
        let private parseSymbolPattern =
            NameParser.parseIdentifier
            |>> Pattern.SymbolPattern

        // 8, "hello", true
        let private parseLiteralPattern =
            LiteralParser.parseLiteral (Some parseExpressionRef)
            |>> Pattern.LiteralPattern

        // _
        let private parseWildcard =
            skipChar '_' >>% Pattern.Wildcard

        // (1, 2, 3)
        let private parseTuplePattern =
            between
                (skipChar '(' >>. spaces)
                (spaces >>. skipChar ')' <?> "closing tuple pattern")
                (sepBy1 (spaces >>. parsePatternRef) (spaces >>. skipChar ',' <?> "other elements in the tuple pattern"))

            >>= function
                | [] -> fail "Tuple cannot be empty"
                | [ { Node = x } ] -> preturn x
                | xs -> preturn (Pattern.TuplePattern xs)

        // { 1, 2, 3 }
        let private parseListPattern =
            between
                (skipChar '{' >>. spaces)
                (spaces >>. skipChar '}' <?> "closing list pattern")
                (sepBy parsePatternRef (spaces >>. skipChar ',' <?> "other elements in the list pattern"))
            |>> Pattern.ListPattern

        // { a₁ = ..., a₂ = ..., ..., aₙ = ... }
        let private parseRecordPattern =
            let parseRecordField =
                pipe3
                    (spaces >>. NameParser.parseIdentifierName)
                    (spaces >>. skipChar '=')
                    (spaces >>. parsePatternRef)
                    (fun name _ pattern -> (name, pattern))

            spaces >>.
                between
                    (spaces >>. skipChar '{')
                    (spaces >>. skipChar '}')
                    (spaces >>. sepBy1 parseRecordField (spaces >>. skipChar ','))
            |>> Pattern.RecordPattern

        let private parseAtomicPattern =
            choice [
                attempt (parseWithPos parseVariablePattern)
                attempt (parseWithPos parseWildcard)
                attempt (parseWithPos parseLiteralPattern)
                attempt (parseWithPos parseSymbolPattern)
                attempt (parseWithPos parseTuplePattern)
                attempt (parseWithPos parseListPattern)
                attempt (parseWithPos parseRecordPattern)
                attempt (between (skipChar '(') (spaces >>. skipChar ')') parsePatternRef)
            ] <?> "atomic pattern" .>> spacesOrComment

        let private parsePatternWithMixfixInternal () =
            fun stream ->
                let currentParser = parse {
                    let! operators = getMixfixOperators
                    // Create a temporary mixfix parser with the current operators
                    let tempParserRef = { MixfixPatternParserRef.Operators = operators; CurrentParser = None }
                    let mixfixParser = MixfixPatternParser(tempParserRef)
                    // Create the expression parser using the mixfix parser
                    let expressionParser = mixfixParser.CreateParser parseAtomicPattern
                    return! expressionParser
                }
                currentParser stream

        let private parsePatternWithPostfixInternal () =
            parsePatternWithMixfixInternal ()
            .>>. many (
                between (skipChar '[' >>. spaces) (spaces >>. skipChar ']')
                    (sepBy parsePatternRef (spaces >>. skipChar ',' >>. spaces))
            )
            |>> fun (basePattern, postfixesList) ->
                List.fold (fun pattern args ->
                    { Node = Pattern.ApplyPattern(pattern, args)
                      Pos = pattern.Pos
                      Pos' = pattern.Pos' }) basePattern postfixesList

        // as, when, `x : Type`
        let private parsePatternWithModifiersInternal () =
            let parseAs (basePattern: WithPos<_>) =
                spaces >>. skipString "as" >>. spaces >>. parsePatternRef
                |>> fun asPattern ->
                    { Node = Pattern.AsPattern(basePattern, asPattern)
                      Pos = basePattern.Pos
                      Pos' = basePattern.Pos' }

            let parseWhen (basePattern: WithPos<_>) =
                spaces >>. skipString "when" >>. spaces >>. parseExpressionRef
                |>> fun condition ->
                    { Node = Pattern.WhenPattern(basePattern, condition)
                      Pos = basePattern.Pos
                      Pos' = basePattern.Pos' }

            let parseTyped (basePattern: WithPos<_>) =
                spaces >>. skipChar ':' >>. spaces >>. TypeParser.parseType
                |>> fun typeAnnotation ->
                    { Node = Pattern.TypedPattern(basePattern, typeAnnotation)
                      Pos = basePattern.Pos
                      Pos' = basePattern.Pos' }

            parsePatternWithPostfixInternal ()
            >>= fun basePattern ->
                choice [
                    attempt (parseAs basePattern)
                    attempt (parseWhen basePattern)
                    attempt (parseTyped basePattern)
                    preturn basePattern ]

        // 1 | 2 | 3 | 4 (for literals only)
        let private parseAlternativePatternInternal () =
            attempt (
                sepBy1 (LiteralParser.parseLiteral (Some parseExpressionRef)) (spaces >>. skipChar '|' >>. spaces)
                |>> fun literals ->
                    match literals with
                    | [single] -> Pattern.LiteralPattern single
                    | multiple -> Pattern.AlternativePattern multiple
            )
            <|>
            (parsePatternWithModifiersInternal () |>> fun pattern -> pattern.Node)

        let public createPatternParser () =
            parsePatternImpl.Value <-
                spaces >>. parseWithPos (parseAlternativePatternInternal ()) .>> spaces

            parsePatternRef

        let public parsePattern = parsePatternRef


    //                                   //
    // ------- Expression parser ------- //
    //                                   //


    // 'x, 'myVar
    let private parseBindingVariable =
        pipe2
            (skipChar '\'')
            (NameParser.parseName false
            )
            (fun _ name ->
                if List.contains name reserved then
                    fail (sprintf "reserved identifier '%s'" name)
                else
                    preturn (Expression.BindingVariable name))
            |> fun p -> p >>= id

    // 17, -0.2, 10_000, "hello", "hello, {4 + 2}!"
    let private parseLiteral =
        LiteralParser.parseLiteral (Some parseExpressionRef)
        |>> Expression.Literal

    // ( ... )
    let private parseBetweenParens =
        between (pchar '(' >>. spaces) (spaces >>. pchar ')') parseExpressionRef

    // Unicode identifier starting with a letter or '_'
    let private parseIdentifier =
        parseWithPos NameParser.parseIdentifier
        |>> Expression.Identifier

    // x <- y
    let private parseReAssign =
        pipe2
            //(spaces >>. NameParser.parseIdentifierName)
            //(spaces >>. skipChar ''' >>. NameParser.parseIdentifierName)
            (spaces >>. choice [ NameParser.parseIdentifierName; skipChar ''' >>. NameParser.parseIdentifierName ])
            (spaces >>. skipString "<-" >>. spaces >>. parseExpressionRef)
            (fun var value -> Expression.ReAssign(var, value))

    // (a, b, c)
    let private parseTuple =
        between
            (skipChar '(')
            (skipChar ')' <?> "closing tuple")
            (sepBy (spaces >>. parseExpressionRef) (spaces >>. skipChar ',' <?> "other elements in the tuple"))
        |> parseWithPos
        |>> function
            | { Node = []; Pos = pos; Pos' = pos' } -> { Node = Expression.Literal { Node = Literal.Unit; Pos = pos; Pos' = pos' }; Pos = pos; Pos' = pos' }
            | { Node = [ x ] } -> x
            | { Node = content; Pos = pos; Pos' = pos' } -> { Node = Expression.Tuple content; Pos = pos; Pos' = pos' }

    // { a = 3, b = "hello" }, { 0 .. 10 }, { 0 .. 0.1 .. 10 }, { 1, 2, 3, 4, 5 }
    // { k for k in { 0 .. 10_000 } if k % 2 = 0 }, { myRecord with a = 0 }
    let private parseBracedExpression =
        let sep = spaces >>. skipChar ',' <?> "other items before '}'" >>. spaces

        let parseRecordField =
            pipe3
                NameParser.parseIdentifierName
                (spaces >>. skipChar '=' >>. spaces)
                parseExpressionRef
                (fun name _ expr -> (name, expr))

        let parseRecord =
            sepBy1 parseRecordField sep
            |>> Expression.Record

        let parseRecordUsing =
            pipe3
                //NameParser.parseIdentifierName
                (spaces >>? parseExpressionRef)
                (spaces >>. skipString "using" >>. spaces)  // It clashes with "ResumeWith" using `with`
                (sepBy1 parseRecordField sep)
                (fun recordName _ fields -> Expression.RecordUsing(recordName, fields))

        let parseRangeWithStep =
            pipe3
                parseExpressionRef
                (spaces >>. skipString ".." >>. spaces >>. parseExpressionRef)
                (spaces >>. skipString ".." >>. spaces >>. parseExpressionRef)
                (fun start step endExpr -> Expression.Range { RangeStart = start; RangeStep = Some step; RangeStop = endExpr })

        let parseRangeSimple =
            pipe2
                parseExpressionRef
                (spaces >>. skipString ".." >>. spaces >>. parseExpressionRef)
                (fun start endExpr -> Expression.Range { RangeStart = start; RangeStep = None; RangeStop = endExpr })

        let parseRange = attempt parseRangeWithStep <|> parseRangeSimple

        let parseListComprehension =
            pipe4
                parseExpressionRef
                (spaces >>. skipString "for" >>. spaces >>. NameParser.parseIdentifierName)
                (spaces >>. skipString "in" >>. spaces >>. parseExpressionRef)
                (opt (spaces >>. skipString "if" >>. spaces >>. parseExpressionRef))
                (fun expr var range condition ->
                    Expression.ListComprehension { ItemValue = expr; Pattern = var; ListExpr = range; IfPred = condition })

        let parseList =
            sepBy parseExpressionRef sep
            |>> Expression.List

        let parseContent =
            choice [
                attempt (parseWithPos parseListComprehension)
                attempt (parseWithPos parseRecordUsing)
                attempt (parseWithPos parseRecord)
                attempt (parseWithPos parseRange)
                parseWithPos parseList
            ]

        between
            (skipChar '{' >>. spaces)
            (spaces >>. skipChar '}' <?> "closing '{'")
            parseContent

    // while <PRED> do <EXPR>
    let private parseWhileDo =
        pipe2
            (skipString "while" >>. spaces >>. parseExpressionRef)
            (spaces >>. skipString "do" >>. parseExpressionRef)
            (fun cond content -> Expression.While { Predicate = cond; Body = content })

    // let x = y, var x = y
    let private parseLetVar =
        pipe4
            (spaces >>. choice [ pstring "let"; pstring "var" ])
            (spaces >>. PatternParser.parsePattern)
            (spaces >>. skipChar '=' >>. parseExpressionRef)
            (opt (spaces >>? skipString "in" >>. spaces >>. parseExpressionRef))
            (fun letVar p v in' ->
                let head =
                    if letVar = "let"
                    then Expression.Let(p, v)
                    else Expression.Var(p, v)
                match in' with
                | None -> head
                | Some tail ->
                    Expression.ExpressionSequence [ { Node = head; Pos = p.Pos; Pos' = p.Pos' }; tail ])

    // [a₁, a₂, ..., aₙ] -> ...
    let private parseLambdaRule =
        let parseLHS =
            between
                (spaces >>. skipChar '[')
                (spaces >>. skipChar ']')
                (sepBy (spaces >>. PatternParser.parsePattern) (spaces >>. skipChar ','))

        let parseRHS =
            spaces >>. skipString "->" >>. spaces >>. parseExpressionRef

        pipe2
            parseLHS
            parseRHS
            (fun a b -> Expression.Lambda { Patterns = a; Body = b })

    // using <HANDLER>(<STATE>) handle <TO HANDLE>
    let private parseHandleEffect =
        pipe3
            (spaces >>. skipString "using" >>. spaces >>. parseWithPos NameParser.parseIdentifier)
            (spaces >>. parseExpressionRef)
            (spaces >>. skipString "handle" >>. parseExpressionRef)
            (fun handler initState expr ->
                Expression.HandleEffect { Handler = handler; InitialState = initState; Body = expr })

    let private parseMatchingCases =
        blockOf
            (tuple2
                (spaces >>. optional (skipChar '|') >>. spaces >>. PatternParser.parsePattern)
                (spaces >>. skipString "->" >>. spaces >>. parseExpressionRef))

    // match cases
    let private parseMatch =
        pipe2
            (spaces >>. skipString "match" >>. spaces >>. parseExpressionRef .>> (spaces .>> skipString "with" <?> "'with' keyword"))
            (spaces >>. parseMatchingCases)
            (fun expr cases -> Expression.Match { ToMatch = expr; Cases = cases })

    let private parseIfThenElse =
        pipe3
            (skipString "if" >>. spaces >>. parseExpressionRef)
            (skipString "then" >>. spaces >>. parseExpressionRef)
            (opt (skipString "else" >>. spaces >>. parseExpressionRef))
            (fun condition thenBranch elseBranch ->
                IfThenElse { Condition = condition; ThenBranch = thenBranch; ElseBranch = elseBranch })

    // for <ITEM> in <COLLECTION> do <BODY>
    let private parseForIn =
        pipe3
            (spaces >>. skipString "for" >>. spaces >>. PatternParser.parsePattern)
            (spaces >>. skipString "in" >>. spaces >>. parseExpressionRef)
            (spaces >>. skipString "do" >>. spaces >>. parseExpressionRef)
            (fun pattern collection expression ->
                Expression.ForIn { Pattern = pattern; ListExpr = collection; Body = expression })

    // for <VAR> to <VAL> do <BODY>
    let private parseForTo =
        pipe4
            (spaces >>. skipString "for" >>. spaces >>. PatternParser.parsePattern)
            (spaces >>. skipChar '=' >>. spaces >>. parseExpressionRef)
            (spaces >>. (choice [ pstring "to" <|> pstring "downto" ] .>> spaces) .>>. parseExpressionRef)
            (spaces >>. skipString "do" >>. spaces >>. parseExpressionRef)
            (fun patt value (reachingMethod, toReach) expression ->
                if reachingMethod = "to"
                then Expression.ForTo { Pattern = patt; InitialValue = value; EndValue = toReach; Body = expression }
                else Expression.ForDownTo { Pattern = patt; InitialValue = value; EndValue = toReach; Body = expression })

    let private parseBasicExpression =

        let parsers =
            [ attempt (parseWithPos parseReAssign)
              attempt (parseWithPos parseIdentifier)
              attempt (parseWithPos parseLiteral)
              attempt parseBetweenParens
              parseWithPos parseBindingVariable
              parseTuple
              parseBracedExpression
              parseWithPos parseMatch
              parseWithPos parseIfThenElse
              parseWithPos parseWhileDo
              attempt (parseWithPos parseForIn)
              parseWithPos parseForTo
              parseWithPos parseLetVar
              parseWithPos parseLambdaRule
              parseWithPos parseHandleEffect ]

        choice parsers <?> "valid expression" .>> spacesOrComment

    do PatternParser.createPatternParser () |> ignore

    let private parseApplyArguments =
        sepBy parseExpressionRef (spaces >>. pchar ',' >>. spaces)

    let private parseTermRefHolder = createParserForwardedToRef<ExpressionWithPos, NotationState IndentState>()
    let private parseTerm = fst parseTermRefHolder
    let private parseTermRef = snd parseTermRefHolder

    let private parsePostfixNotations =
        let functionCall =
            parseWithPos (between (skipChar '[' <?> "" .>> spaces) (skipChar ']' <?> "closing '['") parseApplyArguments)
            |>> fun args expr ->
                { Pos = expr.Pos
                  Node = Expression.Apply { LHS = expr; Arguments = args.Node } //(expr, args)
                  Pos' = args.Pos' }

        let collectionAccess =
            spaces >>? skipChar '.' >>? notFollowedBy (skipChar '.') <?> "" >>. spaces >>. between
                (skipChar '[' <?> "collection access '.[ ... ]'" .>> spaces)
                (skipChar ']' <?> "closing '['")
                (spaces >>. sepBy1 parseExpressionRef (spaces >>. skipChar ',') .>> spaces)
            |> parseWithPos
            |>> fun indices expr ->
                { Pos = expr.Pos
                  Node = Expression.CollectionAccess { LHS = expr; Indices = indices.Node }
                  Pos' = indices.Pos' }

        let ufcs =
            spaces >>? skipString "|>" <?> "" >>. spaces >>. parseExpressionRef
            |>> fun b expr ->
                { Pos = expr.Pos
                  Node = Expression.UFCS { LHS = expr; RHS = b }
                  Pos' = b.Pos' }

        let resume =
            spaces >>? skipString "with" <?> "" >>? notFollowedBy parseMatchingCases >>. parseExpressionRef
            |>> fun state resume ->
                let node = { Value = resume; HandlerState = state }
                { Pos = resume.Pos
                  Node = Expression.ResumeWith { Pos = resume.Pos; Node = node; Pos' = resume.Pos' }
                  Pos' = resume.Pos' }

        let badFunctionCall =
            spaces >>? skipChar '(' <?> ""
            >>. fail "Function calls use square brackets [args], not parentheses (args)"

        choice [
            // function call
            functionCall
            // collection access
            collectionAccess
            // Unified Function Calling Syntax (UFCS) as a pipe "operator"
            ufcs
            // resume with (semantically valid only in handlers)
            resume
            // detect function call with parentheses instead of brackets, error
            // badFunctionCall // cause some errors for now
        ]

    /// Transforms a right-associative UFCS call chain (e.g., `a |> (b |> c)`)
    /// into a left-associative chain (e.g., `((a |> b) |> c)`).
    let rec private linearizeUfcsChain (expression: ExpressionWithPos) =

        let inline createUfcsNode (pos, pos') lhs rhs =
            { Node = UFCS { LHS = lhs; RHS = rhs }; Pos = pos; Pos' = pos' }

        let rec collectParts (currentExpr: ExpressionWithPos) =
            match removePos currentExpr with
            | UFCS { LHS = lhs; RHS = rhs } -> lhs :: collectParts rhs
            | _ -> [ currentExpr ]

        match expression.Node with
        | UFCS _ ->
            let parts = collectParts expression
            let leftAssociativeTree = List.reduce (createUfcsNode expression.PosTuple) parts
            leftAssociativeTree

        | _ -> expression

    let private parseMainExpression =
        parseTermRef.Value <-
            parseBasicExpression .>>. many parsePostfixNotations
            |>> fun (baseExpr, postfixes) ->
                List.fold (fun expr transf -> transf expr) baseExpr postfixes
                |> linearizeUfcsChain

        // Créer le parser mixfix AVANT le block handler
        fun (stream: CharStream<_>) ->
            let currentParser = parse {
                let! operators = getMixfixOperators
                let tempParserRef = { MixfixParserRef.Operators = operators; CurrentParser = None }
                let mixfixParser = MixfixParser(tempParserRef)

                let singleExprParser = mixfixParser.CreateParser parseTerm

                // Block handler parsing line by line
                let blockParser = parse {
                    do! spaces
                    let! pos = getPosition

                    let! head = singleExprParser .>>? spacesOrComment
                    let! tail = attempt (blockOf (singleExprParser .>>? spacesOrComment) |> exact pos) <|>% []

                    return
                        match head :: tail with
                        | [ x ] -> x
                        | xs -> { Pos = xs.Head.Pos
                                  Node = ExpressionSequence xs
                                  Pos' = (List.last xs).Pos' }
                }
                
                return! blockParser
            }
            currentParser stream

    do parseExpressionImpl.Value <- spaces >>. parseMainExpression



    //                                  //
    // ------- Top-level parser ------- //
    //                                  //


    let private parseStrategy =
        choice [
            skipString "innermost" >>% Innermost
            skipString "outermost" >>% Outermost
            skipString "invalid" >>% Invalid ] <?> "rewriting strategy (innermost, outermost or invalid)"

    let private parseUse =
        pipe3
            (spaces >>. skipString "use")
            (spaces >>. parseWithPos NameParser.parseIdentifier)
            (opt (attempt (spaces >>. skipString "as" >>. notFollowedBy letter >>. spaces >>. NameParser.parseName false)))
            (fun _ lib as' -> { Lib = lib; Qualifier = as' })
        |> parseWithPos
        |>> TopLevel.Use

    let private parseRule' =
        pipe6
            (spaces >>. parseWithPos (NameParser.parseName false))
            (spaces >>.
                choice [
                    between
                        (spaces >>. skipChar '[' <?> "parameters/patterns")
                        (spaces >>. skipChar ']' <?> "closing '['")
                        (sepBy (spaces >>. PatternParser.parsePattern) (spaces >>. skipChar ','));
                    preturn []
                ])
            (spaces >>. opt (skipString "when" <?> "when-clause" >>? spaces >>. parseExpressionRef))
            (spaces >>. opt (skipChar ':' <?> "rule's type" >>? spaces >>. TypeParser.parseType))
            (spaces >>. opt parseStrategy)
            (spaces >>. skipString "->" <?> "rewriting expression" >>. parseExpressionRef)
            (fun name pattern whenClause type' strategy rewriting ->
                TopLevel.Rule
                    { Name = name
                      Patterns = pattern
                      WhenClause = whenClause
                      Type = type'
                      Strategy = strategy
                      Body = rewriting })

    let private parseMixfixRule =
        fun stream ->
            let currentParser = parse {
                let! operators = getMixfixOperators
                let tempParserRef = { MixfixPatternParserRef.Operators = operators; CurrentParser = None }
                let mixfixParser = MixfixPatternParser(tempParserRef)
                
                let atomicPattern = PatternParser.parsePattern
                let mixfixPatternParser = mixfixParser.CreateParser atomicPattern

                return! pipe5
                    (spaces >>. between (skipChar '(') (skipChar ')') mixfixPatternParser)
                    (spaces >>. opt (skipString "when" <?> "when-clause" >>? spaces >>. parseExpressionRef))
                    (spaces >>. opt (skipChar ':' <?> "rule's type" >>? spaces >>. TypeParser.parseType))
                    (spaces >>. opt parseStrategy)
                    (spaces >>. skipString "->" <?> "rewriting expression" >>. parseExpressionRef)
                    (fun lhsPattern whenClause type' strategy rewriting ->
                        // Extract the head symbol and collect patterns
                        let rec findHeadAndPatterns p =
                            match p.Node with
                            | Pattern.SymbolPattern id -> (Some id, [])
                            | Pattern.MixfixOperatorPattern(a, b) ->
                                let op = operators |> List.find (fun x -> x.Name = a)

                                // Try to extract an IdentifierWithPos from op.RewritesTo.
                                // If none found, fallback to the operator name with lhsPattern positions.
                                let extractIdFromExpr (e: ExpressionWithPos) =
                                    let rec aux (ex: ExpressionWithPos) =
                                        match ex.Node with
                                        | Identifier id -> Some id
                                        | Apply app -> aux app.LHS
                                        | _ -> None
                                    aux e

                                let headId =
                                    match extractIdFromExpr op.RewritesTo with
                                    | Some id -> id.Node
                                    | None -> failwith "??"

                                (Some headId, b)
                            | Pattern.ApplyPattern (base', args) ->
                                let (headOpt, basePatterns) = findHeadAndPatterns base'
                                // collect patterns coming from each argument (ignore their head ids)
                                let argPatterns = args |> List.collect (fun arg -> snd (findHeadAndPatterns arg))
                                (headOpt, basePatterns @ argPatterns)
                            | _ -> (None, [ p ])
                        
                        let (headSymbolOpt, patterns) = findHeadAndPatterns lhsPattern

                        let name = 
                            match headSymbolOpt with
                            | Some id -> 
                                { Node = id.Name.Node
                                  Pos = id.Name.Pos
                                  Pos' = id.Name.Pos' }
                            | None -> 
                                { Node = "_mixfix_rule"
                                  Pos = lhsPattern.Pos
                                  Pos' = lhsPattern.Pos' }

                        TopLevel.Rule
                            { Name = name
                              Patterns = patterns
                              WhenClause = whenClause
                              Type = type'
                              Strategy = strategy
                              Body = rewriting })
            }
            currentParser stream

    let private parseRule = attempt parseMixfixRule <|> parseRule'

    let private parseExport =
        pipe2
            (spaces >>. skipString "export")
            (spaces >>. sepBy1 (spaces >>. NameParser.parseName true) (spaces >>? skipChar ',' <?> "other symbols to export (separated by a comma)"))
            (fun _ lst -> TopLevel.ModuleExport lst)

    let private parseSignature (mustIndicateRetType: bool) =
        let parseRetType = skipChar ':' >>. spaces >>. TypeParser.parseType

        pipe3
            (spaces >>. NameParser.parseName false)
            (spaces >>.
                choice [
                    between
                        (spaces >>. skipChar '[')
                        (spaces >>. skipChar ']')
                        (sepBy (spaces >>. TypeParser.parseType) (spaces >>. skipChar ','))
                    preturn []
                ])
            (if mustIndicateRetType then spaces >>. parseRetType |>> Some else opt (spaces >>? parseRetType))
            (fun name argsType retType -> { Name = name; ArgumentsType = argsType; ReturnType = retType })

    let private parseVariableTypes =
        choice [
            between
                (spaces >>. skipChar '[')
                (spaces >>. skipChar ']')
                (spaces >>.
                    sepBy1
                        (spaces >>. skipChar ''' >>. NameParser.parseName false)
                        (spaces >>. skipChar ','))
            preturn []]

    let private parseEffect =
        pipe3
            (spaces >>. skipString "effect" >>. spaces >>. NameParser.parseName false)
            (spaces >>. optional (skipChar '=') >>. spaces >>. parseVariableTypes)
            (spaces >>. blockOf (parseWithPos (parseSignature true)))
            (fun name varTypes operations -> TopLevel.Effect(name, varTypes, operations))

    let private parseTypeBody =
        let parseTypeConstructorWithPipe =
            parseWithPos (optional (skipChar '|') >>. spaces >>. parseSignature false)

        let format1 = 
            spaces >>. skipChar '=' >>. spaces >>. 
            sepBy1 parseTypeConstructorWithPipe (spaces >>. skipChar '|' >>. spaces)

        let format2 =
            spaces >>. skipChar '=' >>. spaces >>. 
            blockOf parseTypeConstructorWithPipe

        choice [ attempt format1; format2 ]

    let private parseType =
        pipe3
            (spaces >>. skipString "type" >>. spaces >>. NameParser.parseName false)
            (spaces >>. parseVariableTypes)
            parseTypeBody
            (fun name varTypes constructors ->
                TopLevel.Type { Name = name; VarTypes = varTypes; Constructors = constructors })

    let private parseTypeAlias =
        pipe3
            (spaces >>. skipString "type-alias" >>. spaces >>. NameParser.parseName false)
            (spaces >>. parseVariableTypes)
            (spaces >>. optional (skipChar '=') >>. spaces >>. TypeParser.parseType)
            (fun name varTypes alias -> TopLevel.TypeAlias(name, varTypes, alias))

    let private parseHandler =
        pipe7
            (spaces >>. NameParser.parseName false)
            (spaces >>.
                between
                    (spaces >>. skipChar '(')
                    (spaces >>. skipChar ')')
                    (spaces >>. PatternParser.parsePattern))
            (spaces >>.
                between
                    (spaces >>. skipChar '[')
                    (spaces >>. skipChar ']')
                    (spaces >>. PatternParser.parsePattern))
            (spaces >>. opt (skipString "when" >>? spaces >>. parseExpressionRef))
            (spaces >>. opt (skipChar ':' <?> "rule's type" >>? spaces >>. TypeParser.parseType))
            (spaces >>. opt parseStrategy)
            (spaces >>. skipString "->" >>. parseExpressionRef)
            (fun name state pattern whenClause type' strategy rewriting ->
                TopLevel.Handler
                    { Name = name
                      State = state
                      Pattern = pattern
                      WhenClause = whenClause
                      Strategy = strategy
                      Type = type'
                      Body = rewriting })

    type private NotationField =
        | Name of string
        | Assoc of Associativity
        | Prec of uint32

    let private parseNotation =

        let parseAnyNonSpace =
            many1Satisfy (fun c -> c <> ' ' && c <> '\n' && c <> '\r' && c <> ''' && c <> '"')

        let parseMixfixPattern =
            let validatedPatternPart =
                let parseHole =
                    skipChar ''' >>. NameParser.parseName false |>> HolePart <?> "hole"

                let parseFixedPart =
                    parseAnyNonSpace >>= fun fixedPart ->
                        if List.contains fixedPart reserved
                        then fail (sprintf "The symbol '%s' was used as a fixed part of a notation, but it is reserved by the language" fixedPart)
                        else preturn (FixedPart fixedPart)

                choiceL [
                    lookAhead (pchar ''') >>. parseHole;
                    parseFixedPart
                ] "hole or fixed part"

            let parseTerminator =
                attempt (spaces >>. (skipString "is" <|> skipString "->"))

            pipe2
                (spaces >>? validatedPatternPart) // Parse la première partie (pour simuler many1)
                (manyTill (spaces >>? validatedPatternPart) (lookAhead parseTerminator)) // Parse les suivantes
                (fun part parts -> part :: parts) // Combine les résultats

        let parseNotationName =
            pipe2
                (spaces >>. (skipStringCI "name" <?> "name"))
                (spaces >>. skipChar ':' >>. spaces >>. between (skipChar '"') (skipChar '"') parseAnyNonSpace)
                (fun _ name -> Name name)

        let parseNotationAssociativity =
            pipe2
                (spaces >>. (skipStringCI "associativity" <?> "associativity"))
                (spaces >>. skipChar ':' >>. spaces >>.
                    choice [
                        skipStringCI "left" >>% Associativity.Left
                        skipStringCI "right" >>% Associativity.Right
                        skipStringCI "none" >>% Associativity.None ])
                (fun _ assoc -> Assoc assoc)

        let parseNotationPrecedence =
            pipe2
                (spaces >>. (skipStringCI "precedence" <?> "precedence"))
                (spaces >>. skipChar ':' >>. spaces >>. puint32)
                (fun _ prec -> Prec prec)

        let parseField =
            choice [
                parseNotationName
                parseNotationAssociativity
                parseNotationPrecedence ]
            |> parseWithPos <?> ""

        let parseFields =
            many (parseField .>> spacesOrComment)
            >>= fun fields ->
                let names = fields |> List.choose (function { Node = Name _ } as f -> Some f | _ -> None)
                let assocs = fields |> List.choose (function { Node = Assoc _ } as f -> Some f | _ -> None)
                let precs = fields |> List.choose (function { Node = Prec _ } as f -> Some f | _ -> None)

                let errors = [
                    if names.Length = 0 then "The `name` field is missing in the notation definition"
                    elif names.Length > 1 then "The `name` field appears more than once in the notation definition"

                    if assocs.Length = 0 then "The `associativity` field is missing in the notation definition"
                    elif assocs.Length > 1 then "The `associativity` field appears more than once in the notation definition"

                    if precs.Length = 0 then "The `precedence` field is missing in the notation definition"
                    elif precs.Length > 1 then "The `precedence` field appears more than once in the notation definition"
                ]

                match errors with
                | [] -> preturn (names.Head, assocs.Head, precs.Head)
                | errors -> fail (String.concat "\n" errors)

        parse {
            let! pos = getPosition

            do! spaces >>. skipString "notation"
            let! pattern = spaces >>. parseMixfixPattern
            do! spaces >>. ((skipString "is" <|> skipString "->") <?> "rewriting the notation (`is/->`)")
            let! is = spaces >>. parseExpressionRef
            let! name, assoc, prec = greater pos parseFields

            let! pos' = getPosition

            let { Node = Name name; Pos = pos1; Pos' = pos1' } = name
            let { Node = Assoc assoc; Pos = pos2; Pos' = pos2' } = assoc
            let { Node = Prec prec; Pos = pos3; Pos' = pos3' } = prec

            let notation =
                { NotationName = { Node = name; Pos = pos1; Pos' = pos1' }
                  NotationPattern = { Node = pattern; Pos = pos; Pos' = pos' }
                  NotationPrecedence = { Node = prec; Pos = pos3; Pos' = pos3' }
                  NotationAssociativity = { Node = assoc; Pos = pos2; Pos' = pos2' }
                  NotationIs = is }

            do! addMixfixOperator (notationPatternToMixfixOperator notation)

            return notation
        }
        |>> TopLevel.Notation

    let private parseTopLevel =
        let topLevelParsers =
            [ parseWithPos parseUse
              parseWithPos parseExport
              parseWithPos parseEffect
              parseWithPos parseTypeAlias
              parseWithPos parseType
              parseWithPos parseNotation
              attempt (parseWithPos parseHandler)
              parseWithPos parseRule ]

        let parseStatement = 
            choice topLevelParsers |>> Some

        let parseComment = 
            attempt (spaces >>. skipString "--" <?> "" >>. skipRestOfLine true >>. spaces) >>% None

        let parseWhitespace = 
            attempt (skipMany1 (satisfy System.Char.IsWhiteSpace)) >>% None

        choice [
            parseStatement
            parseComment
            parseWhitespace ]

    let private parseTopLevelBlock =
        // For now, let's use the original implementation but with better error handling
        spaces >>. blockOf parseTopLevel
        |>> List.choose id

    let private parseModule =
        pipe2
            (spaces >>. many (spaces >>? skipString "--|" >>. restOfLine false))
            (parseTopLevelBlock)
            (fun description content ->
                let description =
                    match description with
                    | [] -> None
                    | xs -> System.String.Join("\n", xs |> List.map _.Trim()) |> Some

                { ModuleDescription = description; ModuleContent = content })


    //                              //
    // ------- Root parsing ------- //
    //                              //


    let private withStreamName (streamName: string) (p: Parser<_, _>) =
        fun (stream: CharStream<_>) ->
            stream.Name <- streamName
            p stream

    let private finalParser (streamName: string) (p: Parser<_, _>) =
        withStreamName streamName (opt (spacesOrComment >>? p .>> spaces .>> (eof <?> "")))
        //withStreamName streamName (opt (p .>> spaces .>> (eof <?> "")))

    let private extractErrorMessageText (errorMsg: ErrorMessage) =
        match errorMsg.Type with
        | ErrorMessageType.Expected ->
            (errorMsg :?> ErrorMessage.Expected).Label

        | ErrorMessageType.ExpectedString ->
            sprintf "\"%s\"" (errorMsg :?> ErrorMessage.ExpectedString).String

        | ErrorMessageType.Unexpected ->
            (errorMsg :?> ErrorMessage.Unexpected).Label

        | ErrorMessageType.UnexpectedString ->
            sprintf "\"%s\"" (errorMsg :?> ErrorMessage.UnexpectedString).String

        | ErrorMessageType.Message ->
            (errorMsg :?> ErrorMessage.Message).String

        | ErrorMessageType.NestedError ->
            let nested = errorMsg :?> ErrorMessage.NestedError
            sprintf "Nested error at line %d, column %d" nested.Position.Line nested.Position.Column

        | ErrorMessageType.CompoundError ->
            let compound = errorMsg :?> ErrorMessage.CompoundError
            sprintf "Compound error: %s" compound.LabelOfCompound

        | ErrorMessageType.Other ->
            sprintf "Other error: %A" (errorMsg :?> ErrorMessage.Other).Data

        | _ -> "Unknown error"

    let private processErrorMessages (messages: ErrorMessage[]) =
        let rec loop (msgs: ErrorMessage[]) =
            msgs
            |> Array.collect (fun msg ->
                match msg.Type with
                | ErrorMessageType.NestedError ->
                    let nestedError = msg :?> ErrorMessage.NestedError
                    ErrorMessageList.ToSortedArray nestedError.Messages |> loop
                | _ -> [| msg |])
        loop messages

    let private formatErrorType (errorType: ErrorMessageType) (joinedMessages: string) =
        match errorType with
        | ErrorMessageType.Expected ->
            sprintf "the parser expected %s" joinedMessages

        | ErrorMessageType.ExpectedString ->
            sprintf "the parser expected a %s" joinedMessages

        | ErrorMessageType.ExpectedCaseInsensitiveString ->
            sprintf "expected (case insensitive): %s" joinedMessages

        | ErrorMessageType.Unexpected ->
            sprintf "unexpected: %s" joinedMessages

        | ErrorMessageType.UnexpectedString ->
            sprintf "unexpected string: %s" joinedMessages

        | ErrorMessageType.UnexpectedCaseInsensitiveString ->
            sprintf "unexpected (case insensitive): %s" joinedMessages

        | ErrorMessageType.Message ->
            joinedMessages

        | ErrorMessageType.CompoundError ->
            sprintf "compound errors: %s" joinedMessages

        | ErrorMessageType.Other ->
            sprintf "other errors: %s" joinedMessages

        | _ ->
            sprintf "unknown errors: %s" joinedMessages

    let private groupAndFormatErrors (errorList: ErrorMessageList) =
        let allMessages = 
            ErrorMessageList.ToSortedArray errorList 
            |> processErrorMessages

        allMessages
        |> Array.groupBy _.Type
        |> Array.map (fun (errorType, messages) ->
            let joinedMessages =
                let alignmentPrefix = "the parser could expect alignment at column "
                let (alignment, others) =
                    messages
                    |> Array.map extractErrorMessageText
                    |> Array.distinct
                    |> Array.partition (fun msg -> msg.StartsWith alignmentPrefix)

                let alignmentColumns =
                    alignment
                    |> Array.collect (fun msg ->
                        msg.Substring(alignmentPrefix.Length).Split(" or ")
                        |> Array.map (fun part -> part.Trim().Split(' ').[0])
                    )
                    |> Array.distinct
                    |> Array.sortBy int

                let newAlignmentMessage =
                    if alignmentColumns.Length = 0 then None
                    else
                        let columnsStr =
                            match alignmentColumns.Length with
                            | 1 -> alignmentColumns.[0]
                            | 2 -> sprintf "%s or %s" alignmentColumns.[0] alignmentColumns.[1]
                            | _ ->
                                let allButLast = alignmentColumns.[..alignmentColumns.Length - 2]
                                let last = alignmentColumns.[alignmentColumns.Length - 1]
                                sprintf "%s or %s" (String.concat ", " allButLast) last
                        Some($"the parser could expect alignment at column {columnsStr} for indentation")

                Array.append
                    (match newAlignmentMessage with Some msg -> [| msg |] | None -> [||])
                    others
                |> Array.sort

            let joinedMessages =  String.concat " or " joinedMessages
            formatErrorType errorType joinedMessages)
        |> Array.filter (not << System.String.IsNullOrEmpty)
        |> Array.distinct
        |> Array.toList

    let private findRelevantPosition (errorList: ErrorMessageList) (defaultPosition: Position) =
        let rec findNestedPosition (messages: ErrorMessage[]) =
            messages
            |> Array.choose (fun msg ->
                match msg.Type with
                | ErrorMessageType.NestedError ->
                    let nested = msg :?> ErrorMessage.NestedError
                    Some nested.Position
                | _ -> None)
            |> Array.tryLast

        match ErrorMessageList.ToSortedArray errorList |> findNestedPosition with
        | Some pos -> pos
        | None -> defaultPosition

    let private formatErrorMessage (errors: string list) =
        let ensureDot (s: string) = 
            if s.EndsWith "." then s else s + "."

        match errors with
        | [] -> "Invalid syntax (unknown reason)"
        | xs ->
            xs
            |> List.map (fun (s: string) ->
                if System.String.IsNullOrWhiteSpace s then s
                else
                    let s = s.Trim()
                    let first = System.Char.ToUpper s.[0]
                    let rest = s.Substring(1)
                    string first + rest
            )
            |> List.map ensureDot
            |> String.concat " "
            //|> String.concat " Another possible error: "

    let private createErrorReport str originalPosition relevantPosition errorMessage =
        let informations =
            if originalPosition <> relevantPosition
            then [ "The parser backtracked several times, so the position indicated in the\nsnippet may not be at the actual source of the error." ]
            else []

        /// This hint is generic for parsing, so it is difficult to make it contextual.
        let hint =
            "Syntax errors may be due to syntactic ambiguity, try using parentheses if you think this is the case."

        { ErrorType = Liyh.Utils.ErrorReporter.Syntax
          ErrorCode = null // not for now, this is difficult to do
          EnclosingPosition = (relevantPosition, None)
          Description = errorMessage
          AllLines = NodeInfo.getLines str
          Informations = informations
          Hint = hint }

    let private handleParseFailure (str: string) (err: ParserError) (position: Position) =
        let relevantPosition = findRelevantPosition err.Messages position
        let formattedErrors = groupAndFormatErrors err.Messages
        let errorMessage = formatErrorMessage formattedErrors

        createErrorReport str (Some position) (Some relevantPosition) errorMessage

    /// Parses only 'use' statements from the text, ignoring everything else.
    let public parseUses (text: string) (streamName: string) (errorQueue: ErrorQueue) =

        let parseUsesOnly =
            let parseUseStatement = parseUse |>> Some
            let parseAnythingElse = 
                choice [
                    skipString "--" >>. skipRestOfLine true >>% None
                    newline >>% None
                    spaces1 >>% None
                    skipMany1 (noneOf [ '\n' ]) >>% None ]

            let parseItem = 
                choice [
                    attempt parseUseStatement
                    parseAnythingElse ]

            many parseItem .>> eof
            |>> List.choose id
            |>> List.map (function TopLevel.Use use' -> use')

        match runParser (finalParser streamName parseUsesOnly) emptyNotationState text with
        | Success(r, _, _) -> r
        | Failure(debugMsg, err, _) ->
            //printfn "FParsec debug message:\n%A" debugMsg
            let report = handleParseFailure text err err.Position
            errorQueue.AddError report
            None

    type public LiyhParsingResult =
        { Module: Module
          MixfixOperators: MixfixOperator list }

    /// Syntactically analyses the given text (which is supposed to be Liyh code) from the given stream name
    /// and reports parsing errors (which are always fatal) in `errorQueue`, returns the AST otherwise.
    let public parse (text: string) (streamName: string) (notations: MixfixOperator list) (errorQueue: ErrorQueue) =

        let notationState =
            { defaultNotationState with
                MixfixOperators = defaultNotationState.MixfixOperators @ notations }

        match runParser (finalParser streamName parseModule) notationState text with
        | Success(Some result, userState, _) ->
            Some { Module = result
                   MixfixOperators = userState.UserState.MixfixOperators }

        | Failure(debugMsg, err, _) ->
            //printfn "FParsec debug message:\n%A" debugMsg
            let report = handleParseFailure text err err.Position
            errorQueue.AddError report
            None

    let public testParse (text: string) =
        let tempErrorQueue = new ErrorQueue()

        match parse text null defaultNotationState.MixfixOperators tempErrorQueue with
        | Some result -> printfn "%A" result
        | None -> tempErrorQueue.ReportAll System.Console.Error true

    let public testTopLevelParse (text: string) =
        match runParser (finalParser null parseModule) defaultNotationState text with
        | Success(result, _, _) -> printfn "%A" result
        | Failure(debugMsg, _, _) -> printfn "%s" debugMsg

    let public test (text: string) =
        match runParser (finalParser null parseExpressionRef) defaultNotationState text with
        | Success(result, _, _) -> printfn "%A" result
        | Failure(debugMsg, _, _) -> printfn "%s" debugMsg


