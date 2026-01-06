#nowarn "25"
namespace Liyh.Syntax

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
        (termParser: Parser<_, _>) 
        (startPos: Position) 
        (parts: MixfixPattern) 
        (accArgs: 'Node list) 
        (opName: string)
        =

        match parts with
        | [] -> preturn (List.rev accArgs)
        | Fixed s :: rest ->
            let context = sprintf "'%s' part of operator '%s'" s opName
            pstringAligned startPos s context .>> spaces 
            >>. parseRestOfPattern termParser startPos rest accArgs opName

        | Hole :: rest ->
            let context = sprintf "argument #%d of operator '%s'" (accArgs.Length + 1) opName
            termParser <?> context 
            >>= fun arg -> parseRestOfPattern termParser startPos rest (arg :: accArgs) opName

    /// Builder a mixfix pratt parser.
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
            |> List.filter (fun op -> match op.Pattern with Fixed _ :: _ -> true | _ -> false)

        let infixOps =
            sortedOperators
            |> List.filter (fun op -> match op.Pattern with Hole :: _ -> true | _ -> false)

        let prefixMap =
            prefixOps
            |> List.groupBy (fun op -> match op.Pattern with Fixed s :: _ -> s | _ -> "")
            |> Map.ofList

        let infixMap =
            infixOps
            |> List.groupBy (fun op -> match op.Pattern with Hole :: Fixed s :: _ -> s | _ -> "")
            |> Map.ofList

        let rec parseExprWithMinPrec (minPrec: uint) =

            let parsePrefix =
                let parseOp (s: string) (ops: MixfixOperator list) =
                    parse {
                        let! startPos = getPosition
                        do! pstringAligned startPos s (sprintf "operator '%s'" s) .>> spaces |>> ignore
                        return!
                            ops 
                            |> List.map (fun op ->
                                attempt (parse {
                                    let! args = parseRestOfPattern exprRef startPos (List.tail op.Pattern) [] op.Name
                                    return nodeFactory op.Name args startPos startPos
                                }))
                            |> choice
                    }

                let prefixParsers =
                    prefixMap
                    |> Map.toList
                    |> List.map (fun (k, ops) -> attempt (parseOp k ops))

                choice (prefixParsers @ [ baseAtomParser ]) .>> spaces

            let parseInfix (lhs: 'Node) =
                let peekOp =
                    parse {
                        let cs = [| ' '; '\t'; '\n'; '\r'; '('; ')' |] // not sure about this
                        let! nextToken = lookAhead (many1Satisfy (fun c -> not (Array.contains c cs)))

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

                                    return nodeFactory op.Name args (getPos currentLhs) startPos
                                }
                            let! newLhs = choice (validOps |> List.map (attempt << parseOp))
                            return! loop newLhs
                    }
                loop lhs

            parsePrefix >>= parseInfix

        exprImpl.Value <- parseExprWithMinPrec 0u
        exprRef

module public MixFix =
    open FParsec
    open Liyh.Syntax.SyntaxTree

    let public pstringAligned = MixfixEngine.pstringAligned

    type public MixfixParserRef<'a, 'u> =
        { mutable Operators: MixfixOperator list
          mutable CurrentParser: Parser<'a, 'u> option }

    type public MixfixParser(parserRef: MixfixParserRef<ExpressionWithPos, _>) =

        /// Create an expression parser using the given base atom parser for operands.
        member __.CreateParser (baseAtomParser: Parser<ExpressionWithPos, _>) =
            MixfixEngine.buildParser 
                parserRef.Operators 
                baseAtomParser 
                (fun name args startPos endPos -> 
                    { Node = MixfixOperator { Name = name; Arguments = args }
                      Pos = startPos
                      Pos' = endPos })
                (fun e -> e.Pos)

    /// Like `createParserForwardedToRef` of FParsec but for mixfix operators.
    let public createMixfixParserForwardedToRef () =
        let parserRef = { Operators = []; CurrentParser = None }
        let parser = MixfixParser(parserRef)

        (parser, parserRef)

module public MixFixPattern =
    open FParsec
    open Liyh.Syntax.SyntaxTree

    type public MixfixPatternParserRef<'a, 'u> =
        { mutable Operators: MixfixOperator list
          mutable CurrentParser: Parser<'a, 'u> option }

    type public MixfixPatternParser(parserRef: MixfixPatternParserRef<PatternWithPos, _>) =

        /// Create an expression parser using the given base atom parser for operands.
        member __.CreateParser (baseAtomParser: Parser<PatternWithPos, _>) =
            MixfixEngine.buildParser
                parserRef.Operators
                baseAtomParser
                (fun name args startPos endPos -> 
                    { Node = MixfixOperatorPattern (name, args)
                      Pos = startPos; Pos' = endPos })
                (fun p -> p.Pos)

