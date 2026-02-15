#nowarn "25"
namespace rec Liyh.Syntax

//
// An experimental mixfix parser internal library based on a Pratt parsing approach.
//

[<AutoOpen>]
module Amb =
    open Liyh.Syntax.SyntaxTree

    let rec private isPrefix p1 p2 =
        match p1, p2 with
        | [], _ -> true
        | _, [] -> false
        | h1 :: t1, h2 :: t2 ->
            match h1, h2 with
            | Fixed f1, Fixed f2 when f1 = f2 -> isPrefix t1 t2
            | Hole, Hole -> isPrefix t1 t2
            | _ -> false

    /// Finds potential ambiguities between the given notations. Returns a list of tuples containing
    /// `(short operator, long operator)` where `long operator` contains `short operator` as a prefix.
    let public findAmbiguities (operators: MixfixOperator list) =

        let opsWithPatterns =
            operators
            |> List.map (fun op -> op, op.Pattern)

        opsWithPatterns 
        |> List.collect (fun (op1, pat1) ->
            opsWithPatterns 
            |> List.choose (fun (op2, pat2) ->
                if op1.Name = op2.Name || pat1.Length >= pat2.Length then None 
                else if isPrefix pat1 pat2 then Some (op1, op2) else None
            )
        )

module private MixfixEngine =
    open FParsec
    open Liyh.Syntax.Indentation
    open Liyh.Syntax.SyntaxTree

    let internal pstringAligned (refPos: Position) (s: string) (context: string) =
        parse {
            let! pos = getPosition
            return!
                (if pos.Line > refPos.Line
                 then exact refPos (skipString s)
                 else skipString s) <?> context
        }

    let rec private parseRestOfPattern
        (termParser: Set<string> -> Parser<'Node, _>) 
        (startPos: Position) 
        (parts: MixfixPattern) 
        (accArgs: 'Node list) 
        (opName: string)
        (currentStopTokens: Set<string>) 
        =
        match parts with
        | [] ->
            preturn (List.rev accArgs)

        | Fixed s :: rest ->
            let context = sprintf "'%s' part of operator '%s'" s opName
            pstringAligned startPos s context .>>? spaces
            >>. parseRestOfPattern termParser startPos rest accArgs opName currentStopTokens

        | Hole :: rest ->

            let nextDelimiter =
                match rest with
                | Fixed s :: _ -> Some s
                | _ -> None

            let childStopTokens =
                match nextDelimiter with
                | Some s -> Set.add s currentStopTokens
                | None -> currentStopTokens

            let context = sprintf "argument #%d of operator '%s'" (accArgs.Length + 1) opName

            termParser childStopTokens <?> context 
            >>= fun arg ->
                parseRestOfPattern termParser startPos rest (arg :: accArgs) opName currentStopTokens

    let inline private isHeadFixedPart (patt: MixfixPattern) =
        match patt with
        | Fixed _ :: _ -> true
        | _ -> false

    let inline private isHeadHolePart (patt: MixfixPattern) =
        match patt with
        | Hole :: _ -> true
        | _ -> false

    let public buildParser
        (operators: MixfixOperator list)
        (baseAtomParser: Parser<'Node, _>)
        (nodeFactory: string -> 'Node list -> Position -> Position -> 'Node)
        (getPos: 'Node -> Position)

        =

        let exprRef, exprImpl = createParserForwardedToRef()

        let sortedOperators =
            operators
            |> List.sortByDescending _.Pattern.Length

        let prefixOps =
            sortedOperators
            |> List.filter (_.Pattern >> isHeadFixedPart)

        let infixOps =
            sortedOperators
            |> List.filter (_.Pattern >> isHeadHolePart)

        // We prepare a sorted list of operator symbols for the longest match.

        let prefixMap =
            prefixOps
            |> List.groupBy (fun op -> match op.Pattern with Fixed s :: _ -> s | _ -> "")

        let infixMap =
            infixOps
            |> List.groupBy (fun op -> match op.Pattern with Hole :: Fixed s :: _ -> s | _ -> "")
            |> Map.ofList

        // List of prefix symbol parsers sorted by descending length (e.g., `>>` before `>`).
        // This avoids matching `>` when `>>` is present.
        let prefixSymbolParsers =
            prefixMap
            |> List.map (fun (k, ops) -> k, ops)
            |> List.sortByDescending (fun (k, _) -> k.Length)

        let rec parseExprWithMinPrec (minPrec: uint) (stopTokens: Set<string>) =

            // To solve certain problems, we need to cheat a little with Pratt parsing.
            // The problem is that some conflicts can arise, particularly when parsing signed numbers,
            // which conflicts with a negation operator. To do this, we explicitly check what to choose:
            // apply the operator or apply the basic parser? It's an inelegant heuristic, but it seems to work.

            let parsePrefixOrAtom =
                parse {
                    let! startPos = getPosition

                    // Looks ahead for an atom.
                    let! atomMatch = lookAhead (attempt (baseAtomParser .>>. getPosition) |> opt)

                    // Looks for which operator symbol matches the current input.
                    let! opMatch =

                        // Dynamically build a parser that tries operators.
                        let symbolMatcher =
                            prefixSymbolParsers
                            |> List.map (fun (s, ops) -> skipString s >>% (s, ops))
                            |> choice

                        lookAhead (attempt (symbolMatcher .>>. getPosition) |> opt)

                    let applyMixfixOperator (op: MixfixOperator) = parse {

                        // Determines wether the operator enclose its arguments within fixed
                        // parts (for example the mixfix operator `|arg|`).
                        let hasClosingFixedParts =
                            op.Pattern
                            |> List.skipWhile _.IsFixed
                            |> List.exists _.IsFixed

                        // Adapts the precedence if the operator has closing parts.
                        // This allows to isolate the parsing behaviour within the closed parts.
                        let minPrecForArgs =
                            if hasClosingFixedParts then 0u
                            else op.Precedence

                        let! args =
                            parseRestOfPattern
                                (parseExprWithMinPrec minPrecForArgs)
                                startPos
                                (List.tail op.Pattern)
                                []
                                op.Name
                                stopTokens

                        return nodeFactory op.Name args startPos startPos
                    }

                    // Attempts to apply the operators that "match best" considering that the longest match wins.
                    match atomMatch, opMatch with
                    | Some (_, atomEnd), Some ((opStr, operators), opEnd) ->

                        // if the atom is strictly longer, it wins (e.g., `-5` vs. `-`)
                        // otherwise, the operator wins (e.g., `>>=` vs `>>`)

                        if atomEnd.Index > opEnd.Index then
                            // The atom wins, we do not consider mixfix parsing.
                            return! baseAtomParser .>>? spaces
                        else
                            // The operator wins, the symbol is consumed and the parsing of arguments is started.
                            do! pstringAligned startPos opStr (sprintf "operator '%s'" opStr) .>>? spaces
                            return!
                                operators
                                |> List.map (attempt << applyMixfixOperator)
                                |> choice

                    | Some (_, _), None ->
                        // only the atom matches
                        return! baseAtomParser .>>? spaces

                    | None, Some ((opStr, operators), _) ->
                        // only the operator matches
                        do! pstringAligned startPos opStr (sprintf "operator '%s'" opStr) .>>? spaces |>> ignore
                        return!
                            operators 
                            |> List.map (attempt << applyMixfixOperator)
                            |> choice

                    | None, None ->
                        // no match
                        return! fail "Expected expression"
                }

            let parseInfix (lhs: 'Node) =
                let peekOp =
                    parse {
                        let cs = [| ' '; '\t'; '\n'; '\r'; '('; ')'; '['; ']'; '{'; '}'; ',' |] // stop when encounter this

                        let! nextToken = lookAhead (many1Satisfy (fun c -> 
                            not (Array.contains c cs) && not (System.Char.IsLetterOrDigit c)))

                        // Allows to handle ambiguities when operators contain parts of other operators.

                        if stopTokens.Contains nextToken then
                            return []
                        else
                            match infixMap.TryFind nextToken with
                            | None -> return []
                            | Some ops -> return ops
                    }

                let rec loop (currentLhs: 'Node) =
                    parse {
                        let! candidates = attempt peekOp <|> preturn []
                        let validOps = candidates |> List.filter (fun op -> op.Precedence >= minPrec)

                        if validOps.IsEmpty then return currentLhs
                        else
                            let parseOp (op: MixfixOperator) =
                                parse {
                                    let! startPos = getPosition 
                                    let nextPrec = 
                                        match op.Associativity with
                                        | Associativity.Left -> op.Precedence + 1u 
                                        | Associativity.Right -> op.Precedence     
                                        | _ -> op.Precedence + 1u                  

                                    let! args =
                                        parseRestOfPattern
                                            (parseExprWithMinPrec nextPrec)
                                            startPos
                                            (List.tail op.Pattern)
                                            [currentLhs]
                                            op.Name
                                            stopTokens

                                    return nodeFactory op.Name args (getPos currentLhs) startPos
                                }
                            let! newLhs = choice (validOps |> List.map (attempt << parseOp))
                            return! loop newLhs
                    }
                loop lhs

            parsePrefixOrAtom >>= parseInfix

        exprImpl.Value <- parseExprWithMinPrec 0u Set.empty
        exprRef

// Notation state type that manages mixfix operators.
type public NotationState =
    { SourceCode: string
      MixfixOperators: SyntaxTree.MixfixOperator list
      MixfixExpressionEngine: MixFixExpression.MixfixExpressionParser
      MixfixPatternEngine: MixFixPattern.MixfixPatternParser }

type private UserState = Indentation.IndentState<NotationState>

module public MixFixExpression =
    open FParsec
    open Liyh.Syntax.SyntaxTree

    let public pstringAligned = MixfixEngine.pstringAligned

    type public MixfixExpressionParser() =

        let mutable cachedOperators: MixfixOperator list = []
        let mutable cachedParser: Parser<ExpressionWithPos, UserState> option = None
        let mutable cachedAtomParser: Parser<ExpressionWithPos, UserState> option = None

        /// Create an expression parser using the given base atom parser for operands.
        member __.CreateParser (operators: MixfixOperator list) (baseAtomParser: Parser<ExpressionWithPos, _>) =

            let atomParserChanged =
                match cachedAtomParser with
                | Some cached -> not (obj.ReferenceEquals(cached, baseAtomParser))
                | None -> true

            match cachedParser with
            | Some p when obj.ReferenceEquals(cachedOperators, operators) && not atomParserChanged -> p
            | _ ->
                let newParser =
                    MixfixEngine.buildParser 
                        operators
                        baseAtomParser 
                        (fun name args startPos endPos -> 
                            { Node = MixfixOperator { Name = name; Arguments = args }
                              Pos = startPos
                              Pos' = endPos })
                        (fun e -> e.Pos)

                cachedOperators <- operators
                cachedAtomParser <- Some baseAtomParser
                cachedParser <- Some newParser

                newParser

module public MixFixPattern =
    open FParsec
    open Liyh.Syntax.SyntaxTree

    type public MixfixPatternParser() =

        let mutable cachedOperators: MixfixOperator list = []
        let mutable cachedParser: Parser<PatternWithPos, UserState> option = None
        let mutable cachedAtomParser: Parser<PatternWithPos, UserState> option = None  // Nouvelle ligne

        member __.CreateParser (operators: MixfixOperator list) (baseAtomParser: Parser<PatternWithPos, _>) =
            let atomParserChanged = 
                match cachedAtomParser with
                | Some cached -> not (obj.ReferenceEquals(cached, baseAtomParser))
                | None -> true

            match cachedParser with
            | Some p when obj.ReferenceEquals(cachedOperators, operators) && not atomParserChanged -> p
            | _ ->
                let newParser =
                    MixfixEngine.buildParser
                        operators
                        baseAtomParser
                        (fun name args startPos endPos -> 
                            { Node = MixfixOperatorPattern (name, args)
                              Pos = startPos
                              Pos' = endPos })
                        (fun p -> p.Pos)

                cachedOperators <- operators
                cachedAtomParser <- Some baseAtomParser
                cachedParser <- Some newParser

                newParser
