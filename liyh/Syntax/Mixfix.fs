#nowarn "25"
namespace Liyh.Syntax

/// A mixfix parser for the Liyh grammar.
/// We use a reference/implementation model similar to that found in FParsec with `createParserForwardedToRef`.
module MixFix =
    open FParsec
    open Indentation
    open SyntaxTree

    /// Parse fixed parts with aligned indentation.
    let public pstringAligned (refPos: Position) (s: string) (context: string) =
        parse {
            let! pos = getPosition
            return!
                (if pos.Line > refPos.Line
                 then exact refPos (skipString s)
                 else skipString s) <?> context
        }

    let private isValidPattern (pattern: MixfixPattern) (reservedParts: string list) =
        let hasHole = pattern |> List.exists _.IsHole
        let hasFixed = pattern |> List.exists _.IsFixed
        let fixedPartsValid =
            pattern
            |> List.choose (function Fixed s -> Some s | _ -> None)
            |> List.forall (fun s ->
                   not (System.String.IsNullOrWhiteSpace s) &&
                   not (s.Contains ' ') &&
                   not (s.Contains '\t') &&
                   not (List.contains s reservedParts))

        hasHole && hasFixed && fixedPartsValid

    exception public InvalidPatternException of MixfixOperator

    /// Classification of operators based on their actual structure.
    type private OperatorClass =
        | Prefix of MixfixOperator        // Starts with Fixed
        | Postfix of MixfixOperator       // Starts with Hole, ends with Fixed
        | Infix of MixfixOperator         // Starts and ends with Hole, with Fixed in the middle
        | Complex of MixfixOperator       // Complex multipart patterns

    let private classifyOperator (op: MixfixOperator) : OperatorClass =
        match op.Pattern with
        | [] -> failwith "Empty pattern not allowed"
        | Fixed _ :: _ -> 
            match List.rev op.Pattern with
            | Hole :: _ -> Prefix op
            | Fixed _ :: _ -> Complex op
            | [] -> failwith "Impossible"

        | Hole :: rest ->
            match List.rev rest with
            | [] -> failwith "Pattern avec seulement un Hole"
            | Fixed _ :: _ -> 
                if rest.Length = 1 then Postfix op
                else
                    match op.Pattern with
                    | [Hole; Fixed _; Hole] -> Infix op
                    | _ -> Complex op

            | Hole :: _ ->
                match op.Pattern with
                | [Hole; Fixed _; Hole] -> Infix op
                | _ -> Complex op

    /// Structure for infix operators by precedence.
    type private InfixLevel =
        { Level: uint
          LeftAssoc: MixfixOperator list
          RightAssoc: MixfixOperator list
          NonAssoc: MixfixOperator list }

    type public MixfixParserRef<'a, 'u> =
        { mutable Operators: MixfixOperator list
          mutable CurrentParser: Parser<'a, 'u> option }

        member this.GetFixedParts () =
            this.Operators
            |> List.map (fun { Pattern = pattern; Name = name } ->
                pattern
                |> List.filter _.IsFixed
                |> List.map (function Fixed s -> s), name)

    type public MixfixParser(parserRef: MixfixParserRef<_, _>) =
        let addOperator (op: MixfixOperator) =
            if not (isValidPattern op.Pattern []) then
                raise (InvalidPatternException op)

            parserRef.Operators <- op :: parserRef.Operators
            parserRef.CurrentParser <- None

        new() = MixfixParser { Operators = []; CurrentParser = None }

        member __.AddOperator = addOperator

        member __.CreateParser (holeParser: Parser<ExpressionWithPos, _>) =
            let exprRef, exprImpl = createParserForwardedToRef()
            let operators = parserRef.Operators

            /// Generic parser for any mixfix pattern.
            let rec parsePattern (startPos: Position) (pattern: MixfixPattern) (collectedArgs: ExpressionWithPos list) (opName: string) : Parser<ExpressionWithPos list, _> =
                match pattern with
                | [] -> preturn (List.rev collectedArgs)
                | Fixed s :: rest ->
                    let context = sprintf "'%s' part of operator '%s'" s opName
                    pstringAligned startPos s context .>> spaces >>. parsePattern startPos rest collectedArgs opName

                | Hole :: rest ->
                    let context = sprintf "argument %d of operator '%s'" (collectedArgs.Length + 1) opName
                    exprRef <?> context >>= fun arg -> parsePattern startPos rest (arg :: collectedArgs) opName

            /// Create a parser for a given operator.
            let createOperatorParser (op: MixfixOperator) =
                attempt (parse {
                    let! startPos = getPosition
                    let! args = parsePattern startPos op.Pattern [] op.Name

                    return
                        { Pos = startPos
                          Node = MixfixOperator { Name = op.Name; Arguments = args }
                          Pos' = startPos }
                })

            let classifiedOps   = operators     |> List.map (fun op -> (classifyOperator op, op))
            let prefixOps       = classifiedOps |> List.choose (function (Prefix _, op) -> Some op | _ -> None)
            let postfixOps      = classifiedOps |> List.choose (function (Postfix _, op) -> Some op | _ -> None)
            let infixOps        = classifiedOps |> List.choose (function (Infix _, op) -> Some op | _ -> None)
            let complexOps      = classifiedOps |> List.choose (function (Complex _, op) -> Some op | _ -> None)

            /// All non-infix operators (prefixes, postfixes, complex) are treated uniformly.
            let nonInfixOps = prefixOps @ complexOps

            // Organize infixes by precedence
            let infixLevels =
                infixOps
                |> List.groupBy _.Precedence
                |> List.map (fun (precedence, operators) ->
                    let byAssoc assoc =
                        operators
                        |> List.groupBy _.Associativity
                        |> List.tryFind (fst >> ( = ) assoc)
                        |> Option.map snd
                        |> Option.defaultValue []

                    { Level = precedence
                      LeftAssoc = byAssoc Associativity.Left
                      RightAssoc = byAssoc Associativity.Right
                      NonAssoc = byAssoc Associativity.None })

                |> List.sortBy _.Level

            let nonInfixParser =
                if nonInfixOps.IsEmpty then fail "no non-infix operators"
                else nonInfixOps |> List.map createOperatorParser |> choice

            let primaryParser =
                choice [ holeParser .>> spaces; nonInfixParser ] .>> spaces

            let parsePostfix (expr: ExpressionWithPos) =
                if postfixOps.IsEmpty then preturn expr
                else
                    let createPostfixParsers currentExpr =
                        postfixOps
                        |> List.map (fun op ->
                            attempt (parse {
                                let! pos = getPosition
                                // For postfixes, the first argument is the common expression
                                let! args = parsePattern pos (List.tail op.Pattern) [currentExpr] op.Name
                                return
                                    { Pos = currentExpr.Pos
                                      Node = MixfixOperator { Name = op.Name; Arguments = args }
                                      Pos' = pos }
                            }))

                    let rec applyPostfixes currentExpr =
                        parse {
                            let postfixParsers = createPostfixParsers currentExpr
                            let! newExpr = opt (choice postfixParsers)

                            match newExpr with
                            | Some e -> return! applyPostfixes e
                            | None -> return currentExpr
                        }
                    
                    applyPostfixes expr
                    <?> "" // There is no point in listing postfix operators as a probable cause of failure.

            // Main parser with precedence management for infixes
            let rec parseExprWithMinPrec (minPrec: uint) =
                parse {
                    let! left = primaryParser >>= parsePostfix
                    return! parseInfixRest left minPrec
                }

            and parseInfixRest (left: ExpressionWithPos) (minPrec: uint) =
                parse {
                    let applicableLevels = infixLevels |> List.filter (fun level -> level.Level >= minPrec)

                    if applicableLevels.IsEmpty then
                        return left
                    else
                        let! maybeResult = opt (parseAnyInfixAtLevels left applicableLevels minPrec)
                        match maybeResult with
                        | Some result -> return result
                        | None -> return left
                }

            and parseAnyInfixAtLevels (left: ExpressionWithPos) (levels: InfixLevel list) (minPrec: uint) =
                let parsersForLevel (level: InfixLevel) =
                    let byAssocParser (assoc: MixfixOperator list) (levelUpdate: uint) (isNoneAssoc: bool) =
                        assoc |> List.map (fun op ->
                            match op.Pattern with
                            | [Hole; Fixed sym; Hole] ->
                                attempt (parse {
                                    let! pos = getPosition
                                    do! pstringAligned left.Pos sym (sprintf "infix operator '%s'" sym) .>> spaces
                                    let! right = atLeast left.Pos (parseExprWithMinPrec (level.Level + levelUpdate))
                                    let result =
                                        { Pos = left.Pos
                                          Node = MixfixOperator { Name = op.Name; Arguments = [left; right] }
                                          Pos' = pos }

                                    if isNoneAssoc then return result
                                    else return! parseInfixRest result minPrec

                                })
                            | _ -> fail "Invalid infix pattern")

                    let leftAssocParsers  = byAssocParser level.LeftAssoc  1u false
                    let rightAssocParsers = byAssocParser level.RightAssoc 0u false
                    let nonAssocParsers   = byAssocParser level.NonAssoc   1u true

                    leftAssocParsers @ rightAssocParsers @ nonAssocParsers

                let allParsers = levels |> List.collect parsersForLevel
                choice allParsers
                <?> "" // At the moment this only list the operators... not very useful...

            let mainParser = parseExprWithMinPrec 0u <?> "an expression"

            exprImpl.Value <- mainParser
            exprRef

        member this.Parser (holeParser: Parser<ExpressionWithPos, _>) =
            parserRef.CurrentParser
            |> Option.defaultWith (fun _ ->
                   let p = this.CreateParser holeParser
                   parserRef.CurrentParser <- Some p
                   p)

        member __.GetOperators () = List.rev parserRef.Operators
        member __.Reference = parserRef
        member __.Operators
            with get() = parserRef.Operators
            and set(value) =
                parserRef.Operators <- value
                parserRef.CurrentParser <- None

    let public createMixfixParserForwardedToRef () =
        let parserRef = { Operators = []; CurrentParser = None }
        let parser = MixfixParser(parserRef)
        parser, parserRef

/// Custom notations can also be used in patterns, but this requires a few adjustments.
module MixFixPattern =
    open FParsec
    open SyntaxTree
    open MixFix

    type public MixfixPatternParserRef<'a, 'u> =
        { mutable Operators: MixfixOperator list
          mutable CurrentParser: Parser<'a, 'u> option }

    type public MixfixPatternParser(parserRef: MixfixPatternParserRef<_, _>) =
        
        member __.CreateParser (holeParser: Parser<PatternWithPos, _>) =
            let patternRef, patternImpl = createParserForwardedToRef()
            let operators = parserRef.Operators

            let argContextFor (argIndex: int) (opName: string) =
                match argIndex with
                | 0 -> sprintf "first pattern argument for '%s'" opName
                | 1 -> sprintf "second pattern argument for '%s'" opName
                | 2 -> sprintf "third pattern argument for '%s'" opName
                | n -> sprintf "pattern argument #%d for '%s'" (n + 1) opName

            let partContextFor (part: string) (opName: string) (isLast: bool) =
                if isLast then sprintf "closing '%s' for '%s'" part opName
                else sprintf "'%s' part of '%s'" part opName

            let rec parseParts (startPos: Position) (pattern: MixfixPattern) (args: PatternWithPos list) (opName: string) : Parser<PatternWithPos list, _> =
                match pattern with
                | [] -> preturn (List.rev args)
                | Fixed s :: rest ->
                    let context = partContextFor s opName rest.IsEmpty
                    pstringAligned startPos s context .>> spaces >>. parseParts startPos rest args opName

                | Hole :: rest ->
                    let context = argContextFor args.Length opName
                    patternRef <?> context >>= fun arg -> parseParts startPos rest (arg :: args) opName

            let createPrefixMixfixTermParser (ops: MixfixOperator list) =
                let prefixOps =
                    ops
                    |> List.filter (fun op ->
                        match op.Pattern with
                        | Fixed _ :: _ -> true
                        | _ -> false)

                if prefixOps.IsEmpty then fail "no prefix mixfix pattern operators are defined"
                else
                    let opsByFirstPart =
                        prefixOps
                        |> List.groupBy (fun op ->
                            match op.Pattern with
                            | Fixed s :: _ -> s
                            | _ -> failwith "Impossible: already filtered")

                    let prefixParsers =
                        opsByFirstPart
                        |> List.map (fun (keyword, opGroup) ->
                            getPosition >>= fun startPos ->
                            let pKeyword = pstringAligned startPos keyword (sprintf "pattern operator starting with '%s'" keyword) .>> spaces >>% startPos
                            let pRest (pos: Position) =
                                let restParsers =
                                    opGroup
                                    |> List.map (fun op ->
                                        parse {
                                            let! args = parseParts pos (List.tail op.Pattern) [] op.Name
                                            return
                                                { Pos = pos
                                                  Node = MixfixOperatorPattern(op.Name, args)
                                                  Pos' = pos }
                                        })
                                choice restParsers
                            attempt pKeyword >>= pRest
                        )
                    choice prefixParsers

            let categorizeOperator (op: MixfixOperator) =
                match op.Pattern with
                | [Hole; Fixed _; Hole] -> "Infix"
                | [Hole; Fixed _] -> "PostfixSimple"
                | _ -> "Complex"

            let operatorsByCategory =
                operators
                |> List.groupBy categorizeOperator
                |> Map.ofList

            let getCategory category =
                Map.tryFind category operatorsByCategory |> Option.defaultValue []

            let infixOps = getCategory "Infix"
            let postfixSimple = getCategory "PostfixSimple"
            let complexOps = getCategory "Complex"

            let mixfixTerm =
                if complexOps.IsEmpty then fail "no complex mixfix pattern operators"
                else createPrefixMixfixTermParser complexOps

            let baseTerm =
                if complexOps.IsEmpty then holeParser .>> spaces <?> "pattern"
                else choice [ holeParser; mixfixTerm ] .>> spaces <?> "pattern"

            let opp = OperatorPrecedenceParser<_, _, _>()
            opp.TermParser <- baseTerm

            let uniqueInfixOps = infixOps |> List.distinctBy _.Name
            let uniquePostfixOps = postfixSimple |> List.distinctBy _.Name

            for op in uniqueInfixOps do
                match op.Pattern with
                | [ Hole; Fixed s; Hole ] ->
                    try
                        // The case of the operator `_-_` causes problems for matching cases
                        // of the form `pattern -> expression`, so we add a little trick here
                        // to handle this case without ambiguity.

                        match s with
                        | "-" ->
                            opp.AddOperator(
                                InfixOperator("-", notFollowedBy (pchar '>') >>. spaces, 
                                            int op.Precedence, op.Associativity,
                                            fun x y -> { Pos = x.Pos
                                                         Node = MixfixOperatorPattern(op.Name, [ x; y ])
                                                         Pos' = x.Pos }))
                        | _ ->
                            opp.AddOperator(
                                InfixOperator(s, spaces, int op.Precedence, op.Associativity,
                                            fun x y -> { Pos = x.Pos
                                                         Node = MixfixOperatorPattern(op.Name, [ x; y ])
                                                         Pos' = x.Pos }))
                    with
                    | _ -> ()
                | _ -> ()

            for op in uniquePostfixOps do
                match op.Pattern with
                | [ Hole; Fixed s ] ->
                    try
                        opp.AddOperator(
                            PostfixOperator(s, spaces, int op.Precedence, true,
                                fun x -> { Pos = x.Pos
                                           Node = MixfixOperatorPattern(op.Name, [ x ])
                                           Pos' = x.Pos }))
                    with
                    | _ -> ()
                | _ -> ()

            let rec applyComplexPostfix (pattern: PatternWithPos) =
                let postfixParsers =
                    complexOps
                    |> List.choose (fun op ->
                        match op.Pattern with
                        | Hole :: restPattern ->
                            let p =
                                parse {
                                    let! pos = getPosition
                                    let! args = parseParts pos restPattern [pattern] op.Name
                                    return
                                        { Pos = pattern.Pos
                                          Node = MixfixOperatorPattern(op.Name, args)
                                          Pos' = pattern.Pos }
                                }
                            Some p
                        | _ -> None)

                if postfixParsers.IsEmpty then preturn pattern
                else
                    let rec applyUntilNoMatch currentPattern =
                        parse {
                            let! maybeNewPattern = attempt (choice postfixParsers) |> opt
                            match maybeNewPattern with
                            | Some newPattern -> return! applyUntilNoMatch newPattern
                            | None -> return currentPattern
                        }
                    applyUntilNoMatch pattern

            patternImpl.Value <-
                opp.ExpressionParser
                >>= applyComplexPostfix
                <?> "valid mixfix pattern"

            patternRef

        member this.Parser (holeParser: Parser<PatternWithPos, _>) =
            match parserRef.CurrentParser with
            | Some p -> p
            | None ->
                let p = this.CreateParser holeParser
                parserRef.CurrentParser <- Some p
                p

        member __.Operators = parserRef.Operators


//
// NOTE: The `MixFixPattern` module is based on an older version of mixfix parsing. In practice, we
// haven't noticed any problems, but the version of the `MixFix` module is more recent. So this is
// something to keep an eye on (too lazy to do it now).
//

