#nowarn "25"
namespace Liyh.Syntax

module private ParsingErorr =
    open FParsec
    open Liyh.Utils.ErrorReporter
    open SyntaxTree


    // --- Building pleasant messages and reports --- //


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
            sprintf "unknown syntax errors: %s" joinedMessages

    let public groupAndFormatErrors (errorList: ErrorMessageList) =
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

                Array.append (match newAlignmentMessage with Some msg -> [| msg |] | None -> [||]) others
                |> Array.sort

            let joinedMessages =  String.concat " or " joinedMessages
            formatErrorType errorType joinedMessages)

        |> Array.filter (not << System.String.IsNullOrEmpty)
        |> Array.distinct
        |> Array.toList

    let public findRelevantPosition (errorList: ErrorMessageList) (defaultPosition: Position) =
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

    let public formatErrorMessage (errors: string list) =
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

    let public createErrorReport str originalPosition relevantPosition errorMessage =
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

    let public buildErrorReport (sourceCode: string) (startPos: Position) (endPos: Position) (errors: ErrorMessageList) =
        let formattedErrors = groupAndFormatErrors errors
        let description = formatErrorMessage formattedErrors
        let relevantPos = findRelevantPosition errors startPos

        let informations =
            if startPos <> relevantPos
            then [ "The parser backtracked, the error might be earlier." ]
            else []

        let hasExplicitMessage = 
            ErrorMessageList.ToSortedArray errors
            |> Array.exists (fun e -> e.Type = ErrorMessageType.Message)

        let hint = 
            if hasExplicitMessage then null 
            else "Syntax errors may be due to syntactic ambiguity, try using parentheses if you think this is the case."

        { ErrorType = Liyh.Utils.ErrorReporter.Syntax
          ErrorCode = null
          EnclosingPosition = (Some relevantPos, Some endPos)
          Description = description
          AllLines = NodeInfo.getLines sourceCode |> Seq.toList
          Informations = informations
          Hint = hint }


    // --- Retrieve error messages from the AST --- //


    let rec private collectParsingErrorsFromTopLevel (topLevel: TopLevelWithPos) =
        match topLevel.Node with
        | TopLevel.ParseError err -> [err]
        | Use _ -> []
        | Rule rule ->
            let patternErrors = List.collect collectParsingErrorsFromPattern rule.Patterns
            let whenErrors = defaultArg (rule.WhenClause |> Option.map collectParsingErrorsFromExpression) []
            let bodyErrors = collectParsingErrorsFromExpression rule.Body
            patternErrors @ whenErrors @ bodyErrors
        | Handler handler ->
            let stateErrors = collectParsingErrorsFromPattern handler.State
            let patternErrors = collectParsingErrorsFromPattern handler.Pattern
            let whenErrors = defaultArg (handler.WhenClause |> Option.map collectParsingErrorsFromExpression) []
            let bodyErrors = collectParsingErrorsFromExpression handler.Body
            stateErrors @ patternErrors @ whenErrors @ bodyErrors
        | Context { Content = content } ->
            List.collect collectParsingErrorsFromTopLevel content
        | Effect _ | Type _ | TypeAlias _ | Extern _ | Measure | Unit | UnitSystem | UnitConversion | ModuleExport _ -> []
        | Notation notation -> collectParsingErrorsFromExpression notation.NotationIs

    and private collectParsingErrorsFromExpression (expr: ExpressionWithPos) =
        match expr.Node with
        | Expression.ParseError err -> [err]
        | UFCS ufcs ->
            collectParsingErrorsFromExpression ufcs.LHS @ collectParsingErrorsFromExpression ufcs.RHS
        | Identifier _ | BindingVariable _ | Literal _ -> []
        | CollectionAccess ca ->
            collectParsingErrorsFromExpression ca.LHS @ List.collect collectParsingErrorsFromExpression ca.Indices
        | ExpressionSequence exprs -> List.collect collectParsingErrorsFromExpression exprs
        | Apply apply ->
            collectParsingErrorsFromExpression apply.LHS @ List.collect collectParsingErrorsFromExpression apply.Arguments
        | MixfixOperator op -> List.collect collectParsingErrorsFromExpression op.Arguments
        | Tuple exprs | List exprs -> List.collect collectParsingErrorsFromExpression exprs
        | Record fields -> List.collect (snd >> collectParsingErrorsFromExpression) fields
        | RecordUsing (baseExpr, fields) ->
            collectParsingErrorsFromExpression baseExpr @ List.collect (snd >> collectParsingErrorsFromExpression) fields
        | ListComprehension lc ->
            collectParsingErrorsFromExpression lc.ItemValue
            @ collectParsingErrorsFromPattern lc.Pattern
            @ collectParsingErrorsFromExpression lc.ListExpr
            @ defaultArg (lc.IfPred |> Option.map collectParsingErrorsFromExpression) []
        | Range range ->
            collectParsingErrorsFromExpression range.RangeStart
            @ defaultArg (range.RangeStep |> Option.map collectParsingErrorsFromExpression) []
            @ collectParsingErrorsFromExpression range.RangeStop
        | While w ->
            collectParsingErrorsFromExpression w.Predicate @ collectParsingErrorsFromExpression w.Body
        | ForIn forIn ->
            collectParsingErrorsFromPattern forIn.Pattern
            @ collectParsingErrorsFromExpression forIn.ListExpr
            @ collectParsingErrorsFromExpression forIn.Body
        | ForTo forTo | ForDownTo forTo ->
            collectParsingErrorsFromPattern forTo.Pattern
            @ collectParsingErrorsFromExpression forTo.InitialValue
            @ collectParsingErrorsFromExpression forTo.EndValue
            @ collectParsingErrorsFromExpression forTo.Body
        | ReAssign (_, expr) -> collectParsingErrorsFromExpression expr
        | Let (pat, expr) | Var (pat, expr) ->
            collectParsingErrorsFromPattern pat @ collectParsingErrorsFromExpression expr
        | Match m ->
            collectParsingErrorsFromExpression m.ToMatch
            @ List.collect (fun (pat, expr) -> collectParsingErrorsFromPattern pat @ collectParsingErrorsFromExpression expr) m.Cases
        | IfThenElse ifte ->
            collectParsingErrorsFromExpression ifte.Condition
            @ collectParsingErrorsFromExpression ifte.ThenBranch
            @ defaultArg (ifte.ElseBranch |> Option.map collectParsingErrorsFromExpression) []
        | Lambda lambda ->
            List.collect collectParsingErrorsFromPattern lambda.Patterns @ collectParsingErrorsFromExpression lambda.Body
        | HandleEffect handle ->
            collectParsingErrorsFromExpression handle.InitialState @ collectParsingErrorsFromExpression handle.Body
        | ResumeWith rw ->
            collectParsingErrorsFromExpression rw.Node.Value @ collectParsingErrorsFromExpression rw.Node.HandlerState
        | Substitution(env, inExpr) ->
            List.collect (snd >> collectParsingErrorsFromExpression) env @ collectParsingErrorsFromExpression inExpr
        | UsingContext { ContentExpr = expr } ->
            collectParsingErrorsFromExpression expr

    and private collectParsingErrorsFromPattern (pat: PatternWithPos) =
        match pat.Node with
        | VariablePattern _ | SymbolPattern _ | LiteralPattern _ | AlternativePattern _ | Wildcard -> []
        | ApplyPattern (head, args) ->
            collectParsingErrorsFromPattern head @ List.collect collectParsingErrorsFromPattern args
        | TuplePattern pats | ListPattern pats -> List.collect collectParsingErrorsFromPattern pats
        | RecordPattern fields -> List.collect (snd >> collectParsingErrorsFromPattern) fields
        | MixfixOperatorPattern (_, pats) -> List.collect collectParsingErrorsFromPattern pats
        | AsPattern (pat1, pat2) ->
            collectParsingErrorsFromPattern pat1 @ collectParsingErrorsFromPattern pat2
        | WhenPattern (pat, expr) ->
            collectParsingErrorsFromPattern pat @ collectParsingErrorsFromExpression expr
        | TypedPattern (pat, _) -> collectParsingErrorsFromPattern pat

    let public collectParsingErrors (program: TopLevelWithPos list) =
        List.collect collectParsingErrorsFromTopLevel program

module private Recoverable =
    open FParsec
    
    let private skipIndentedBlock (stream: CharStream<_>) =
        let rec loop () =
            let c = stream.Peek()
            if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
                skipRestOfLine true stream |> ignore
                if not stream.IsEndOfStream then loop ()
            else
                ()
        loop ()

    /// Handle parsing error using the given error handler, so that parsing can continue accumulating errors.
    let public recover
        (parser: Parser<'a, 'u>)
        (errorHandler: Position -> Position -> ErrorMessageList -> 'a)
        : Parser<'a, 'u>
        =
        fun stream ->
            let state = stream.State
            let startPos = stream.Position
            
            let reply = parser stream

            match reply.Status with
            | Ok -> reply
            | _ ->
                let failurePos = stream.Position
                let errorMessages = reply.Error

                let (reportStart, reportEnd) =
                    if failurePos.Index > startPos.Index then
                        stream.Seek(failurePos.Index)
                        skipRestOfLine true stream |> ignore
                        (failurePos, stream.Position)
                    else
                        stream.BacktrackTo(state)
                        skipRestOfLine true stream |> ignore
                        (startPos, stream.Position)

                // We return to the beginning to apply our "skip strategy"
                // so that the parser can continue properly after this block.
                stream.BacktrackTo(state)

                skipRestOfLine true stream |> ignore
                skipIndentedBlock stream

                Reply (errorHandler reportStart reportEnd errorMessages)

module Parser =
    open FParsec
    open Liyh.Utils.ErrorReporter
    open Indentation
    open SyntaxTree
    open MixFixExpression
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

    // Default notation state with basic operators
    let private defaultNotationState =
        { SourceCode = null
          MixfixOperators = []
          MixfixExpressionEngine = new MixfixExpressionParser()
          MixfixPatternEngine = new MixfixPatternParser() }

    // Utilities to work with notation state
    let private getMixfixOperators: Parser<MixfixOperator list, NotationState IndentState> =
        fun stream -> Reply stream.UserState.UserState.MixfixOperators

    let private addMixfixOperator (op: MixfixOperator): Parser<unit, NotationState IndentState> =
        fun stream ->
            let oldState = stream.UserState.UserState
            let newOperators = op :: oldState.MixfixOperators

            stream.UserState <-
                { stream.UserState with
                    UserState =
                        { oldState with
                            MixfixOperators = newOperators } }

            Reply Unchecked.defaultof<unit>

    // Forward reference to resolve recursion
    let private parseExpressionRefHolder = createParserForwardedToRef<ExpressionWithPos, NotationState IndentState>()
    let private parseExpressionRef = fst parseExpressionRefHolder
    let private parseExpressionImpl = snd parseExpressionRefHolder

    /// Reserved names and symbols for the language.
    let private reserved =
        [ "for"; "in"; "let"; "var"; "while"; "do"; "match"; "as"; "_"; "->"; "["; "|>";
          "if"; "then"; "else"; "("; "{"; "}"; ")"; "]"; "<-"; "with"; "handle"; "export"; "effect"; "=";
          "notation"; "using"; "use"; "innermost"; "outermost"; "invalid"; "--"; "to"; "downto"; "type";
          "type-alias"; "."; "extern"; "context" ]

    let private reservedSet = System.Collections.Generic.HashSet<string>(reserved)

    /// Retrieves operator parts defined by user custom notations.
    let private reservedByUser (id: string) (operators: MixfixOperator list) =
        operators
        |> List.map (fun { Pattern = pattern; Name = name } ->
            pattern
            |> List.filter _.IsFixed
            |> List.map (function Fixed s -> s), name)
        |> List.tryPick (fun (parts, opName) -> if List.contains id parts then Some opName else None)

    let private inlineComment =
        skipString "--" >>. skipRestOfLine true

    let private multilineComment =

        let rec commentContent (depth: int) =
            choice [
                skipString "{-" >>= fun _ -> commentContent (depth + 1)
                skipString "-}" >>= fun _ -> if depth = 1 then preturn () else commentContent (depth - 1)
                skipAnyChar     >>= fun _ -> commentContent depth ]

        skipString "{-" >>. commentContent 1

    let private comments =
        choice [ inlineComment; multilineComment ] <?> ""

    let private spacesOrComment =
        spaces >>. optional comments >>. spaces

    module private NameParser =
        open System.Globalization

        let private isExtendedDigit (c: char) =
            if System.Char.IsDigit c then true
            else
                let numericValue = CharUnicodeInfo.GetNumericValue c
                numericValue >= 0.0 && numericValue <= 9.0 && numericValue = System.Math.Floor(numericValue)

        /// Parses a valid name according to the Liyh specification and returns it as a character string.
        /// This parser may fail in a definition context if the name is already defined in a custom notation.
        /// The `export` parameter disables this failure if set to `true`.
        let public parseName (export: bool) =
            let parseUsualName =
                parse {
                    let! first = satisfy (fun c -> c = '_' || System.Char.IsLetter c)
                    let! rest = manySatisfy (fun c -> c = '_' || System.Char.IsLetter c || isExtendedDigit c)
                    return string first + rest
                } <?> "valid name (unicode string that does not begin with a number)"

            let parsePlainName =
                between
                    (pchar '`' <?> "")
                    (pchar '`' <?> "closing '`'")
                    (manySatisfy (fun c -> c <> '`' && c <> '\n' && c <> '\r'))

            choice [ parseUsualName; parsePlainName ]
            >>= fun name ->
                if not export && reservedSet.Contains(name) then
                    fail (sprintf "'%s' is a reserved symbol by the language" name)
                else
                    parse {
                        let! operators = getMixfixOperators
                        match reservedByUser name operators with
                        | None -> return name
                        | Some userReservedIn ->
                            if export then 
                                return name
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
                let parseQualifier = pchar '.' >>. parseWithPos parseIdentifierName
                
                many parseQualifier |>> fun qualifierParts ->
                    match qualifierParts with
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
            let parseSingleLine =
                let escapedChar =
                    pchar '\\' <?> "" >>.
                        choice [
                            pchar '{' >>% "{"
                            pchar '}' >>% "}"
                            pchar '"' >>% "\""
                            pchar '\\' >>% "\\"
                            pchar 'n' >>% "\n"
                            pchar 't' >>% "\t" ]

                let normalChar =
                    satisfy (fun c -> c <> '{' && c <> '"' && c <> '\\' && c <> '\n' && c <> '\r')
                    |>> string

                let interpolationFragment =
                    between
                        (pchar '{' <?> "")
                        (pchar '}' <?> "")
                        (parseExpr |>> InterpolatedPart.Interpolation)

                let textFragment =
                    many1 (attempt escapedChar <|> normalChar)
                    |>> fun strs -> InterpolatedPart.Str (String.concat "" strs)

                let fragment =
                    choice [ attempt interpolationFragment; textFragment ]

                parse {
                    let! content = between (pchar '"') (pchar '"') (many fragment)
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

            let parseMultiLine =
                parse {
                    let! startPos = getPosition
                    let! _ = pstring "\"\"\""
                    let indentCol = int startPos.Column - 1

                    do! many (satisfy (fun c -> c = ' ' || c = '\t')) >>% ()
                    do! optional (pstring "//" >>. restOfLine false)
                    do! skipNewline <?> "newline after \"\"\""

                    let rec readBlock acc =
                        parse {
                            do! many (satisfy (fun c -> c = ' ' || c = '\t')) >>% ()
                            let! afterIndentPos = getPosition
                            let currentIndent = int afterIndentPos.Column - 1

                            if currentIndent >= indentCol then
                                if currentIndent = indentCol then
                                    let! isCloser = choice [ attempt (pstring "\"\"\"") >>% true; preturn false ]
                                    if isCloser then return List.rev acc
                                    else return! readLineContent acc
                                else
                                    let extraSpaces = String.replicate (currentIndent - indentCol) " "
                                    return! readLineContent (InterpolatedPart.Str extraSpaces :: acc)
                            else
                                let! isLineEmpty = (skipNewline >>% true) <|> (eof >>% true) <|> preturn false
                                if isLineEmpty then return! readBlock (InterpolatedPart.Str "\n" :: acc)
                                else return! fail "Invalid indentation for multiline string."
                        }

                    and readLineContent acc =
                        choice [
                            skipNewline >>. readBlock (InterpolatedPart.Str "\n" :: acc)

                            (pchar '{' >>. parseExpr .>> pchar '}') >>= fun expr ->
                                readLineContent (InterpolatedPart.Interpolation expr :: acc)

                            many1Satisfy (fun c -> c <> '\n' && c <> '\r' && c <> '{') >>= fun text ->
                                readLineContent (InterpolatedPart.Str text :: acc)
                        ]

                    let! content = readBlock []
                    match content |> List.tryFind _.IsInterpolation with
                    | Some _ -> return Literal.InterpolatedString content
                    | None ->
                        let strContent =
                            content |> List.fold (fun acc frag ->
                                match frag with
                                | InterpolatedPart.Str s -> acc + s
                                | _ -> acc) ""
                            |> _.TrimEnd()
                        return Literal.String strContent
                }

            choice [
                attempt parseMultiLine
                parseSingleLine
            ]

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
                spacesOrComment >>. (parseType <?> "other elements in the parametrized's type") .>> spacesOrComment

            parseWithPos (
                parseWithPos NameParser.parseIdentifier
                .>>. opt (
                    skipChar '[' >>. spacesOrComment >>.
                    sepBy1 parseElementAfterComma (skipChar ',' <?> "other types") .>>
                    spacesOrComment .>> (skipChar ']' <?> "closing ']' to end the parametrized type")
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
                spacesOrComment >>. (parseType <?> "other elements in the tuple's type") .>> spacesOrComment

            parseWithPos (
                between
                    (skipChar '(' >>. spacesOrComment)
                    (spacesOrComment >>. skipChar ')' <?> "closing ')' to end tuple")
                    (sepBy1 parseElementAfterComma comma)

                |>> fun types ->
                    match types with
                    | [{ Node = single }] -> single
                    | lst -> Type.TupleType(lst)
            )

        // { a: Int, b: String }
        let private parseRowRecordType =
            let fieldName = NameParser.parseIdentifierName
            let colon = spacesOrComment >>. (skipChar ':' >>. spacesOrComment <?> "':' after field name")
            let comma = skipChar ',' <?> "comma ',' between fields or closing '}'"
            let closingBrace = skipChar '}' <?> "closing '}' to end record type"

            let field =
                fieldName .>> colon .>>. parseType <?> "other elements in the record"

            let parseFields =
                sepBy1 field (spacesOrComment >>. comma >>. spacesOrComment)

            parseWithPos (
                skipChar '{' >>. spacesOrComment >>.
                parseFields .>>
                spacesOrComment .>> closingBrace
                |>> Type.RowRecordType
            )

        // [Int, Int] -> Int
        let private parseRuleType =
            let openBracket = skipChar '['
            let closeBracket = skipChar ']' <?> "closing ']' after function arguments"
            let arrow = skipString "->" <?> "arrow '->' after function arguments"
            let comma = skipChar ',' <?> "comma ',' between arguments"

            let parseElementAfterComma =
                spacesOrComment >>. (parseType <?> "other elements in the function type parameters") .>> spacesOrComment

            let args =
                openBracket >>. spacesOrComment >>.
                sepBy parseElementAfterComma comma .>>
                spacesOrComment .>> closeBracket

            parseWithPos (
                pipe2
                    (args .>> spacesOrComment .>> arrow .>> spacesOrComment)
                    (parseType <?> "return type (the function must return something after '->')")
                    (fun args ret ->
                        let argsList = match args with | [] -> [] | xs -> xs
                        Type.RuleType(argsList, ret)
                    )
            )

        // t1 % { eff₁, eff₂, ..., effₙ }
        let private parseModuloEffectType =
            pipe2
                (spacesOrComment >>? skipChar '%' <?> "")
                (spacesOrComment >>.
                    between
                        (spacesOrComment >>. (skipChar '{' <?> "some effects"))
                        (spacesOrComment >>. (skipChar '}' <?> "closing '}'"))
                        (sepBy
                            (spacesOrComment >>? (parseWithPos NameParser.parseIdentifier <?> "effect name"))
                            (spacesOrComment >>? skipChar ',')))
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
            spacesOrComment >>. parseTypeWithContext .>> spacesOrComment

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
                (skipChar '(' >>. spacesOrComment)
                (spacesOrComment >>. skipChar ')' <?> "closing tuple pattern")
                (sepBy1 (spacesOrComment >>. parsePatternRef) (spacesOrComment >>. skipChar ',' <?> "other elements in the tuple pattern"))

            >>= function
                | [] -> fail "Tuple cannot be empty"
                | [ { Node = x } ] -> preturn x
                | xs -> preturn (Pattern.TuplePattern xs)

        // { 1, 2, 3 }
        let private parseListPattern =
            between
                (skipChar '{' >>. spacesOrComment)
                (spacesOrComment >>. skipChar '}' <?> "closing list pattern")
                (sepBy parsePatternRef (spacesOrComment >>. skipChar ',' <?> "other elements in the list pattern"))
            |>> Pattern.ListPattern

        // { a₁ = ..., a₂ = ..., ..., aₙ = ... }
        let private parseRecordPattern =
            let parseRecordField =
                pipe3
                    (spacesOrComment >>. NameParser.parseIdentifierName)
                    (spacesOrComment >>. skipChar '=')
                    (spacesOrComment >>. parsePatternRef)
                    (fun name _ pattern -> (name, pattern))

            spacesOrComment >>.
                between
                    (spacesOrComment >>. skipChar '{')
                    (spacesOrComment >>. skipChar '}')
                    (spacesOrComment >>. sepBy1 parseRecordField (spacesOrComment >>. skipChar ','))
            |>> Pattern.RecordPattern

        let private parseAtomicPattern =
            choice [
                attempt (parseWithPos parseVariablePattern)
                attempt (parseWithPos parseSymbolPattern)
                attempt (parseWithPos parseWildcard)
                attempt (parseWithPos parseLiteralPattern)
                attempt (parseWithPos parseTuplePattern)
                attempt (parseWithPos parseListPattern)
                attempt (parseWithPos parseRecordPattern)
                attempt (between (skipChar '(') (spacesOrComment >>. skipChar ')') parsePatternRef)
            ] <?> "atomic pattern" .>> spacesOrComment

        let private parsePatternWithMixfixInternal () =
            fun (stream: CharStream<NotationState IndentState>) ->
                let state = stream.UserState.UserState
                let engine = state.MixfixPatternEngine
                let operators = state.MixfixOperators

                engine.CreateParser operators parseAtomicPattern stream

        let private parsePatternWithPostfixInternal () =
            parsePatternWithMixfixInternal ()
            .>>. many (
                between (skipChar '[' >>. spacesOrComment) (spacesOrComment >>. skipChar ']')
                    (sepBy parsePatternRef (spacesOrComment >>. skipChar ',' >>. spacesOrComment))
            )
            |>> fun (basePattern, postfixesList) ->
                List.fold (fun pattern args ->
                    { Node = Pattern.ApplyPattern(pattern, args)
                      Pos = pattern.Pos
                      Pos' = pattern.Pos' }) basePattern postfixesList

        // as, when, `x : Type`
        let private parsePatternWithModifiersInternal () =
            let parseAs (basePattern: WithPos<_>) =
                spacesOrComment >>. skipString "as" >>. spacesOrComment >>. parsePatternRef
                |>> fun asPattern ->
                    { Node = Pattern.AsPattern(basePattern, asPattern)
                      Pos = basePattern.Pos
                      Pos' = basePattern.Pos' }

            let parseWhen (basePattern: WithPos<_>) =
                spacesOrComment >>. skipString "when" >>. spacesOrComment >>. parseExpressionRef
                |>> fun condition ->
                    { Node = Pattern.WhenPattern(basePattern, condition)
                      Pos = basePattern.Pos
                      Pos' = basePattern.Pos' }

            let parseTyped (basePattern: WithPos<_>) =
                spacesOrComment >>. skipChar ':' >>. spacesOrComment >>. TypeParser.parseType
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
                sepBy1 (LiteralParser.parseLiteral (Some parseExpressionRef)) (spacesOrComment >>. skipChar '|' >>. spacesOrComment)
                |>> fun literals ->
                    match literals with
                    | [single] -> Pattern.LiteralPattern single
                    | multiple -> Pattern.AlternativePattern multiple
            )
            <|>
            (parsePatternWithModifiersInternal () |>> fun pattern -> pattern.Node)

        let public createPatternParser () =
            parsePatternImpl.Value <-
                spacesOrComment >>. parseWithPos (parseAlternativePatternInternal ()) .>> spacesOrComment

            parsePatternRef

        let public parsePattern = parsePatternRef


    //                                   //
    // ------- Expression parser ------- //
    //                                   //


    // 'x, 'myVar
    let private parseBindingVariable =
        pipe2
            (skipChar '\'')
            (NameParser.parseName false)
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
        between (pchar '(' >>. spacesOrComment) (spacesOrComment >>. pchar ')') parseExpressionRef

    // Unicode identifier starting with a letter or '_'
    let private parseIdentifier =
        parseWithPos NameParser.parseIdentifier
        |>> Expression.Identifier

    // x <- y
    let private parseReAssign =
        pipe2
            //(spacesOrComment >>. NameParser.parseIdentifierName)
            //(spacesOrComment >>. skipChar ''' >>. NameParser.parseIdentifierName)
            (spacesOrComment >>. choice [ NameParser.parseIdentifierName; skipChar ''' >>. NameParser.parseIdentifierName ])
            (spacesOrComment >>. skipString "<-" >>. spacesOrComment >>. parseExpressionRef)
            (fun var value -> Expression.ReAssign(var, value))

    // (a, b, c)
    let private parseTuple =
        between
            (skipChar '(')
            (skipChar ')' <?> "closing tuple")
            (sepBy (spacesOrComment >>. parseExpressionRef) (spacesOrComment >>. skipChar ',' <?> "other elements in the tuple"))
        |> parseWithPos
        |>> function
            | { Node = []; Pos = pos; Pos' = pos' } -> { Node = Expression.Literal { Node = Literal.Unit; Pos = pos; Pos' = pos' }; Pos = pos; Pos' = pos' }
            | { Node = [ x ] } -> x
            | { Node = content; Pos = pos; Pos' = pos' } -> { Node = Expression.Tuple content; Pos = pos; Pos' = pos' }

    // { a = 3, b = "hello" }, { 0 .. 10 }, { 0 .. 0.1 .. 10 }, { 1, 2, 3, 4, 5 }
    // { k for k in { 0 .. 10_000 } if k % 2 = 0 }, { myRecord with a = 0 }
    let private parseBracedExpression =
        let sep = spacesOrComment >>. skipChar ',' <?> "other items before '}'" >>. spacesOrComment

        let parseRecordField =
            pipe3
                NameParser.parseIdentifierName
                (spacesOrComment >>. skipChar '=' >>. spacesOrComment)
                parseExpressionRef
                (fun name _ expr -> (name, expr))

        let parseRecord =
            sepBy1 parseRecordField sep
            |>> Expression.Record

        let parseRecordUsing =
            pipe3
                //NameParser.parseIdentifierName
                (spacesOrComment >>? parseExpressionRef)
                (spacesOrComment >>. skipString "using" >>. spacesOrComment)  // It clashes with "ResumeWith" using `with`
                (sepBy1 parseRecordField sep)
                (fun recordName _ fields -> Expression.RecordUsing(recordName, fields))

        let parseRangeWithStep =
            pipe3
                parseExpressionRef
                (spacesOrComment >>. skipString ".." >>. spacesOrComment >>. parseExpressionRef)
                (spacesOrComment >>. skipString ".." >>. spacesOrComment >>. parseExpressionRef)
                (fun start step endExpr -> Expression.Range { RangeStart = start; RangeStep = Some step; RangeStop = endExpr })

        let parseRangeSimple =
            pipe2
                parseExpressionRef
                (spacesOrComment >>. skipString ".." >>. spacesOrComment >>. parseExpressionRef)
                (fun start endExpr -> Expression.Range { RangeStart = start; RangeStep = None; RangeStop = endExpr })

        let parseRange = attempt parseRangeWithStep <|> parseRangeSimple

        let parseListComprehension =
            pipe4
                parseExpressionRef
                (spacesOrComment >>. skipString "for" >>. spacesOrComment >>. PatternParser.parsePattern)
                (spacesOrComment >>. skipString "in" >>. spacesOrComment >>. parseExpressionRef)
                (opt (spacesOrComment >>. skipString "if" >>. spacesOrComment >>. parseExpressionRef))
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
            (skipChar '{' >>. spacesOrComment)
            (spacesOrComment >>. skipChar '}' <?> "closing '{'")
            parseContent

    // while <PRED> do <EXPR>
    let private parseWhileDo =
        pipe2
            (skipString "while" >>. spacesOrComment >>. parseExpressionRef)
            (spacesOrComment >>. skipString "do" >>. parseExpressionRef)
            (fun cond content -> Expression.While { Predicate = cond; Body = content })

    // let x = y, var x = y
    let private parseLetVar =
        pipe4
            (spacesOrComment >>. choice [ pstring "let"; pstring "var" ])
            (spacesOrComment >>. PatternParser.parsePattern)
            (spacesOrComment >>. skipChar '=' >>. parseExpressionRef)
            (opt (spacesOrComment >>? skipString "in" >>. spacesOrComment >>. parseExpressionRef))
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
                (spacesOrComment >>. skipChar '[')
                (spacesOrComment >>. skipChar ']')
                (sepBy (spacesOrComment >>. PatternParser.parsePattern) (spacesOrComment >>. skipChar ','))

        let parseRHS =
            spacesOrComment >>. skipString "->" >>. spacesOrComment >>. parseExpressionRef

        pipe2
            parseLHS
            parseRHS
            (fun a b -> Expression.Lambda { Patterns = a; Body = b })

    let private parseUsingContext =
        pipe4
            (spacesOrComment >>. skipString "using" >>. spacesOrComment >>. skipString "context")
            (spacesOrComment >>. parseWithPos NameParser.parseIdentifier)
            (spacesOrComment >>. skipString "do")
            (spacesOrComment >>. parseExpressionRef)
            (fun _ contextName _ contextExpr ->
                UsingContext
                    { ContextName = contextName
                      ContentExpr = contextExpr })

    // using <HANDLER>(<STATE>) handle <TO HANDLE>
    let private parseHandleEffect =
        pipe3
            (spacesOrComment >>. skipString "using" >>. spacesOrComment >>. parseWithPos NameParser.parseIdentifier)
            (spacesOrComment >>. parseExpressionRef)
            (spacesOrComment >>. skipString "handle" >>. parseExpressionRef)
            (fun handler initState expr ->
                Expression.HandleEffect { Handler = handler; InitialState = initState; Body = expr })

    let private parseMatchingCases =
        blockOf
            (tuple2
                (spacesOrComment >>. optional (skipChar '|') >>. spacesOrComment >>. PatternParser.parsePattern)
                (spacesOrComment >>. skipString "->" >>. spacesOrComment >>. parseExpressionRef))

    // match cases
    let private parseMatch =
        pipe2
            (spacesOrComment >>. skipString "match" >>. spacesOrComment >>. parseExpressionRef .>> (spacesOrComment .>> skipString "with" <?> "'with' keyword"))
            (spacesOrComment >>. parseMatchingCases)
            (fun expr cases -> Expression.Match { ToMatch = expr; Cases = cases })

    let private parseIfThenElse =
        pipe3
            (skipString "if" >>. spacesOrComment >>. parseExpressionRef)
            (skipString "then" >>. spacesOrComment >>. parseExpressionRef)
            (opt (skipString "else" >>. spacesOrComment >>. parseExpressionRef))
            (fun condition thenBranch elseBranch ->
                IfThenElse { Condition = condition; ThenBranch = thenBranch; ElseBranch = elseBranch })

    // for <ITEM> in <COLLECTION> do <BODY>
    let private parseForIn =
        pipe3
            (spacesOrComment >>. skipString "for" >>. spacesOrComment >>. PatternParser.parsePattern)
            (spacesOrComment >>. skipString "in" >>. spacesOrComment >>. parseExpressionRef)
            (spacesOrComment >>. skipString "do" >>. spacesOrComment >>. parseExpressionRef)
            (fun pattern collection expression ->
                Expression.ForIn { Pattern = pattern; ListExpr = collection; Body = expression })

    // for <VAR> to <VAL> do <BODY>
    let private parseForTo =
        pipe4
            (spacesOrComment >>. skipString "for" >>. spacesOrComment >>. PatternParser.parsePattern)
            (spacesOrComment >>. skipChar '=' >>. spacesOrComment >>. parseExpressionRef)
            (spacesOrComment >>. (choice [ pstring "to" <|> pstring "downto" ] .>> spacesOrComment) .>>. parseExpressionRef)
            (spacesOrComment >>. skipString "do" >>. spacesOrComment >>. parseExpressionRef)
            (fun patt value (reachingMethod, toReach) expression ->
                if reachingMethod = "to"
                then Expression.ForTo { Pattern = patt; InitialValue = value; EndValue = toReach; Body = expression }
                else Expression.ForDownTo { Pattern = patt; InitialValue = value; EndValue = toReach; Body = expression })

    let private parseSubstitution =
        let sub =
            pipe3
                (spacesOrComment >>. NameParser.parseName false)
                (spacesOrComment >>. skipString "->")
                (spacesOrComment >>. parseExpressionRef)
                (fun symbol _ replace -> (symbol, replace))

        let subEnv =
            between
                (skipChar '[')
                (skipChar ']')
                (sepBy1 sub (spacesOrComment >>. skipChar ','))

        pipe3
            (spacesOrComment >>. subEnv)
            (spacesOrComment >>. skipString "in")
            (spacesOrComment >>. parseExpressionRef)
            (fun env _ inExpr -> Substitution(env, inExpr))

    let private parseBasicExpression =

        let parsers =
            [ attempt (parseWithPos parseReAssign)
              attempt (parseWithPos parseSubstitution)
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
              parseWithPos parseUsingContext
              parseWithPos parseHandleEffect ]

        choice parsers <?> "valid expression" .>> spacesOrComment

    do PatternParser.createPatternParser () |> ignore

    let private parseApplyArguments =
        sepBy parseExpressionRef (spacesOrComment >>. pchar ',' >>. spacesOrComment)

    let private parseTermRefHolder = createParserForwardedToRef<ExpressionWithPos, NotationState IndentState>()
    let private parseTerm = fst parseTermRefHolder
    let private parseTermRef = snd parseTermRefHolder

    let private parsePostfixNotations =
        let functionCall =
            parseWithPos (between (skipChar '[' <?> "" .>> spacesOrComment) (skipChar ']' <?> "closing '['") parseApplyArguments)
            |>> fun args expr ->
                { Pos = expr.Pos
                  Node = Expression.Apply { LHS = expr; Arguments = args.Node } //(expr, args)
                  Pos' = args.Pos' }

        let collectionAccess =
            spacesOrComment >>? skipChar '.' >>? notFollowedBy (skipChar '.') <?> "" >>. spacesOrComment >>. between
                (skipChar '[' <?> "collection access '.[ ... ]'" .>> spacesOrComment)
                (skipChar ']' <?> "closing '['")
                (spacesOrComment >>. sepBy1 parseExpressionRef (spacesOrComment >>. skipChar ',') .>> spacesOrComment)
            |> parseWithPos
            |>> fun indices expr ->
                { Pos = expr.Pos
                  Node = Expression.CollectionAccess { LHS = expr; Indices = indices.Node }
                  Pos' = indices.Pos' }

        let resume =
            spacesOrComment >>? skipString "with" <?> "" >>? notFollowedBy parseMatchingCases >>. parseExpressionRef
            |>> fun state resume ->
                let node = { Value = resume; HandlerState = state }
                { Pos = resume.Pos
                  Node = Expression.ResumeWith { Pos = resume.Pos; Node = node; Pos' = resume.Pos' }
                  Pos' = resume.Pos' }

        choice [
            // function call
            functionCall
            // collection access
            collectionAccess
            // resume with (semantically valid only in handlers)
            attempt resume
        ]

    let private parseMainExpression =
        parseTermRef.Value <-
            parseBasicExpression .>>. many parsePostfixNotations
            |>> fun (baseExpr, postfixes) ->
                List.fold (fun expr transf -> transf expr) baseExpr postfixes

        fun (stream: CharStream<_>) ->
            let state = stream.UserState.UserState
            let engine = state.MixfixExpressionEngine
            let operators = state.MixfixOperators

            let mixfixParser = engine.CreateParser operators parseTerm

            let pipeOp = 
                spacesOrComment >>? skipString "|>" >>. spacesOrComment 
                >>% (fun lhs rhs ->
                        { Node = Expression.UFCS { LHS = lhs; RHS = rhs }
                          Pos = lhs.Pos
                          Pos' = rhs.Pos' })

            let expressionWithPipes = chainl1 mixfixParser pipeOp

            let currentParser = parse {
                let blockParser = parse {
                    do! spacesOrComment
                    let! pos = getPosition

                    let! head = expressionWithPipes .>>? spacesOrComment

                    let exprErrorHandler (p: Position) (endP: Position) (msgs: ErrorMessageList) =
                         let sourceCode = stream.UserState.UserState.SourceCode
                         let report = ParsingErorr.buildErrorReport sourceCode p endP msgs
                         { Node = Expression.ParseError report; Pos = p; Pos' = endP }

                    let safeExprParser = 
                        Recoverable.recover 
                            (expressionWithPipes .>>? spacesOrComment) 
                            exprErrorHandler

                    let rec loop acc = parse {
                        match! (eof >>% true) <|>% false with
                        | true -> return List.rev acc
                        | false ->
                            let! isAligned = attempt (exact pos (preturn ())) >>% true <|>% false
                            if isAligned then
                                let! item = safeExprParser
                                let! endPos = getPosition
                                if pos = endPos then return List.rev (item :: acc)
                                else return! loop (item :: acc)
                            else return List.rev acc
                    }
                    let! tail = loop []

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

    do parseExpressionImpl.Value <- spacesOrComment >>. parseMainExpression



    //                                  //
    // ------- Top-level parser ------- //
    //                                  //


    let private parseStrategy =
        choice [
            (skipString "innermost" <|> skipString "strict") >>% Strict
            (skipString "lazy") >>% Lazy
            (skipString "outermost") >>% Outermost
            (skipString "memoize") >>% Memoize
            (skipString "invalid") >>% Invalid ] <?> "rewriting strategy (innermost, outermost or invalid)"

    let private parseUse =
        pipe3
            (spaces >>. skipString "use")
            (spacesOrComment >>. parseWithPos NameParser.parseIdentifier)
            (opt (attempt (spacesOrComment >>. skipString "as" >>. notFollowedBy letter >>. spacesOrComment >>. NameParser.parseName false)))
            (fun _ lib as' -> { Lib = lib; Qualifier = as' })
        |> parseWithPos
        |>> TopLevel.Use

    let private parseRule' =
        pipe6
            (spaces >>. parseWithPos (NameParser.parseName false))
            (spacesOrComment >>.
                choice [
                    between
                        (spacesOrComment >>. skipChar '[' <?> "parameters/patterns")
                        (spacesOrComment >>. skipChar ']' <?> "closing '['")
                        (sepBy (spacesOrComment >>. PatternParser.parsePattern) (spacesOrComment >>. skipChar ','));
                    preturn []
                ])
            (spacesOrComment >>. opt (skipString "when" <?> "when-clause" >>? spacesOrComment >>. parseExpressionRef))
            (spacesOrComment >>. opt (skipChar ':' <?> "rule's type" >>? spacesOrComment >>. TypeParser.parseType))
            (spacesOrComment >>. opt parseStrategy)
            (spacesOrComment >>. skipString "->" <?> "rewriting expression" >>. parseExpressionRef)
            (fun name pattern whenClause type' strategy rewriting ->
                TopLevel.Rule
                    { Name = name
                      Patterns = pattern
                      WhenClause = whenClause
                      Type = type'
                      Strategy = strategy
                      Body = rewriting })

    let private parseMixfixRule =
        fun (stream: CharStream<IndentState<NotationState>>) ->
            let state = stream.UserState.UserState
            let operators = state.MixfixOperators
            let engine = state.MixfixPatternEngine

            let atomicPattern = PatternParser.parsePattern
            let mixfixPatternParser = engine.CreateParser operators atomicPattern

            let currentParser = parse {
                return! pipe5
                    (spacesOrComment >>. between (skipChar '(') (skipChar ')') mixfixPatternParser)
                    (spacesOrComment >>. opt (skipString "when" <?> "when-clause" >>? spacesOrComment >>. parseExpressionRef))
                    (spacesOrComment >>. opt (skipChar ':' <?> "rule's type" >>? spacesOrComment >>. TypeParser.parseType))
                    (spacesOrComment >>. opt parseStrategy)
                    (spacesOrComment >>. skipString "->" <?> "rewriting expression" >>. parseExpressionRef)
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
            (spacesOrComment >>. sepBy1 (spacesOrComment >>. NameParser.parseName true) (spacesOrComment >>? skipChar ',' <?> "other symbols to export (separated by a comma)"))
            (fun _ lst -> TopLevel.ModuleExport lst)

    let private parseSignature (mustIndicateRetType: bool) =
        let parseRetType = (skipChar ':' <|> skipString "->") >>. spaces >>. TypeParser.parseType

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

    let private parseExtern =
        pipe5
            (spaces >>. skipString "extern")
            (spaces >>. opt (choice [ skipStringCI "C" >>% C ]) <?> "language target")
            (spaces >>. parseWithPos (between (pchar '"') (pchar '"') (many1Chars (noneOf "\""))))
            (spaces >>. skipString "as" >>. spaces >>. parseWithPos NameParser.parseIdentifier)
            (spaces >>. blockOf (parseSignature true))
            (fun _ lang lib asName content ->
                Extern
                    { Language = Option.defaultValue C lang
                      Library = lib
                      AsName = asName
                      Content = content })

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
                attempt (spaces >>. skipString "->")

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
            do! spaces >>. (skipString "->") <?> "rewriting the notation (`is/->`)"
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

    let rec private parseContext () =
        let using =
            pipe2
                (spacesOrComment >>. skipString "using")
                (spacesOrComment >>.
                    sepBy1
                        (spacesOrComment >>. parseWithPos NameParser.parseIdentifier <?> "other inherited contexts")
                        (spacesOrComment >>? skipChar ','))
                (fun _ lst -> lst)

        pipe4
            (spaces >>. skipString "context")
            (spacesOrComment >>. parseWithPos (NameParser.parseName true))
            (spacesOrComment >>. attempt (opt using))
            (spacesOrComment >>. parseTopLevelBlock)
            (fun _ name using content ->
                Context
                    { Name = name
                      Using = Option.defaultValue [] using
                      Content = content })

    and private parseTopLevel =
        let topLevelParsers =
            [ parseWithPos parseUse
              parseWithPos parseExport
              parseWithPos parseEffect
              parseWithPos parseTypeAlias
              parseWithPos parseType
              parseWithPos parseNotation
              parseWithPos (parseContext ())
              attempt (parseWithPos parseHandler)
              parseWithPos parseExtern
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

    and private blockOfTopLevel parser errorHandler =
        let itemParser = Recoverable.recover parser errorHandler

        parse {
            do! spaces
            let! pos = getPosition
            let! head = exact pos itemParser

            let rec loop acc = parse {
                match! (eof >>% true) <|>% false with
                | true -> return List.rev acc
                | false ->
                    let! isAligned = attempt (exact pos (preturn ())) >>% true <|>% false

                    if isAligned then
                        let! startPos = getPosition
                        let! item = itemParser
                        let! endPos = getPosition

                        if startPos = endPos 
                        then return List.rev (item :: acc)
                        else return! loop (item :: acc)
                    else
                        let! currentPos = getPosition

                        if currentPos.Column < pos.Column then
                            return List.rev acc
                        else
                            // We still try to parse to get a more relevant error messages.
                            let! startPos = getPosition
                            let! item = itemParser 
                            let! endPos = getPosition

                            // Infinite loop protection (if the parser does not consume anything).
                            if startPos = endPos then
                                do! skipRestOfLine true
                                return! loop acc
                            else
                                return! loop (item :: acc)
            }

            let! tail = loop []
            return head :: tail
        }

    and private parseTopLevelBlock =
        fun (stream: CharStream<NotationState IndentState>) ->
            let sourceCode = stream.UserState.UserState.SourceCode

            let topLevelErrorHandler (pos: Position) (endPos: Position) (msgs: ErrorMessageList) =
                let report = ParsingErorr.buildErrorReport sourceCode pos endPos msgs
                Some
                    { Node = TopLevel.ParseError report
                      Pos = pos
                      Pos' = endPos }

            let parser =
                spaces >>. blockOfTopLevel parseTopLevel topLevelErrorHandler
                |>> List.choose id
            
            parser stream

    and private parseModule =
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

    let private handleParseFailure (str: string) (err: ParserError) (position: Position) =
        let relevantPosition = ParsingErorr.findRelevantPosition err.Messages position
        let formattedErrors = ParsingErorr.groupAndFormatErrors err.Messages
        let errorMessage = ParsingErorr.formatErrorMessage formattedErrors

        ParsingErorr.createErrorReport str (Some position) (Some relevantPosition) errorMessage

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

        match runParser (finalParser streamName parseUsesOnly) defaultNotationState text with
        | Success(r, _, _) -> r
        | Failure(debugMsg, err, _) ->
            //printfn "FParsec debug message:\n%A" debugMsg
            let report = handleParseFailure text err err.Position
            errorQueue.AddError report
            None

    type public LiyhParsingResult =
        { Module: Module
          MixfixOperators: MixfixOperator list }

    let private createNotationShadowingReport (shortOp: MixfixOperator, longOp: MixfixOperator) (lines: string seq) =
        let posShort = fst shortOp.Position 
        let posLong = fst longOp.Position

        let msg = 
            $"The user-defined notation '{shortOp.Name}' (defined at line {posShort.Line}) is a prefix of the notation '{longOp.Name}' (defined at line {posLong.Line})."
        
        let infoMsg = 
            $"Since the pattern of '{shortOp.Name}' is included in '{longOp.Name}', an ambiguity exists.\n" +
            $"To resolve this, Liyh applies the 'Longest Match' rule: it will attempt to parse '{longOp.Name}' first.\n" +
            $"If parsing '{longOp.Name}' fails mid-way, it will backtrack to '{shortOp.Name}'."

        { ErrorType = Warning Syntax
          ErrorCode = null
          EnclosingPosition = (Some posShort, None)
          Description = msg
          AllLines = lines |> Seq.toList
          Informations = [ infoMsg ]
          Hint = "This is allowed, but ensure that any syntax error in the longer notation doesn't accidentally trigger the shorter one." }

    let private handleNotationShadowingWarning (notations: MixfixOperator list) (text: string) (errorQueue: ErrorQueue) =
        let ambiguities = findAmbiguities notations
        let lines = NodeInfo.getLines text

        ambiguities
        |> List.iter (fun ambiguity ->
            let report = createNotationShadowingReport ambiguity lines
            errorQueue.AddError report)

    let private getNotationWarnings (notations: MixfixOperator list) (text: string) =
        let ambiguities = findAmbiguities notations
        let lines = NodeInfo.getLines text
        
        ambiguities
        |> List.map (fun ambiguity -> createNotationShadowingReport ambiguity lines)

    /// Syntactically analyses the given text (which is supposed to be Liyh code) from the given stream name
    /// and reports parsing errors (which are always fatal) in `errorQueue`, returns the AST otherwise.
    let public parse (text: string) (streamName: string) (notations: MixfixOperator list) (errorQueue: ErrorQueue) =

        let notationState =
            { defaultNotationState with
                SourceCode = text
                MixfixOperators = defaultNotationState.MixfixOperators @ notations }

        match runParser (finalParser streamName parseModule) notationState text with
        | Success(Some result, userState, _) ->
            handleNotationShadowingWarning userState.UserState.MixfixOperators text errorQueue

            match ParsingErorr.collectParsingErrors result.ModuleContent with
            | [] ->
                Some { Module = result
                       MixfixOperators = userState.UserState.MixfixOperators }

            | reports ->
                errorQueue.AddErrors reports
                None // we should return the AST for further analysis (typechecking etc.)
                     // so that we are not locked only to parsing errors

        // This should not happens! But we handle in case.
        | Failure(debugMsg, err, userState) ->
            handleNotationShadowingWarning userState.UserState.MixfixOperators text errorQueue
            //printfn "FParsec debug message:\n%A" debugMsg
            let report = handleParseFailure text err err.Position
            errorQueue.AddError report
            None

    /// Checks if the AST contains parsing errors.
    let public containsParsingErrors (lpr: LiyhParsingResult) =
        ParsingErorr.collectParsingErrors lpr.Module.ModuleContent
        |> List.isEmpty
        |> not

    let public parseForTooling (text: string) (notations: MixfixOperator list) =
        let notationState =
            { defaultNotationState with
                SourceCode = text
                MixfixOperators = defaultNotationState.MixfixOperators @ notations }

        let result = runParser (finalParser null parseTopLevelBlock) notationState text

        let finalOperators = 
            match result with
            | Success(_, state, _) -> state.UserState.MixfixOperators
            | Failure(_, _, state) -> state.UserState.MixfixOperators

        let warnings = getNotationWarnings finalOperators text

        match result with
        | Success(ast, _, _) -> Some (ast, warnings)
        | Failure(_, err, _) -> None // This should not happens!

    let public testParse (text: string) =
        let tempErrorQueue = new ErrorQueue()

        match parse text null defaultNotationState.MixfixOperators tempErrorQueue with
        | Some result -> printfn "%A" result
        | None -> tempErrorQueue.ReportAll System.Console.Error true

    let public testTopLevelParse (text: string) =
        let notationState = { defaultNotationState with SourceCode = text }

        match runParser (finalParser null parseModule) notationState text with
        | Success(result, _, _) -> printfn "%A" result
        | Failure(debugMsg, _, _) -> printfn "%s" debugMsg

    let public test (text: string) =
        let notationState = { defaultNotationState with SourceCode = text }

        match runParser (finalParser null parseExpressionRef) notationState text with
        | Success(result, _, _) -> printfn "%A" result
        | Failure(debugMsg, _, _) -> printfn "%s" debugMsg

