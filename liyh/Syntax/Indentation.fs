namespace Liyh.Syntax

module Indentation =
    open FParsec

    /// Different kind of indentation.
    type public Indent =
        | IndentAny
        | IndentExact of Position
        | IndentGreater of Position
        | IndentAtLeast of Position

    let private expected =
        function
        | IndentAny -> "any indentation"
        | IndentExact p -> sprintf "alignment at column %d" p.Column
        | IndentGreater p -> sprintf "indentation strictly greater than column %d" p.Column
        | IndentAtLeast p -> sprintf "indentation at least at column %d" p.Column

    type public IndentState<'t> = { Indent: Indent; UserState: 't }

    type public IndentParser<'t, 'u> = Parser<'t, 'u IndentState>

    let private getIndent: IndentParser<_, _> =
        fun stream -> Reply stream.UserState.Indent

    let private updateIndent (newIndent: Indent) : IndentParser<unit, _> =
        fun stream ->
            stream.UserState <-
                { stream.UserState with
                    Indent = newIndent }

            Reply Unchecked.defaultof<unit>

    let private correctIndent (indent: Indent) (pos: Position) =
        match indent with
        | IndentAny -> true
        | IndentExact p -> p.Column = pos.Column
        | IndentGreater p -> p.Column < pos.Column
        | IndentAtLeast p -> p.Column <= pos.Column

    let inline private parseWithIndent (p: Parser<_, IndentState<_>>) =
        parse {
            let! pos = getPosition
            let! indent = getIndent

            return!
                if correctIndent indent pos then p
                //else fail (sprintf "invalid indentation at line %d, expected %s" pos.Line (expected indent))
                else fail (sprintf "the parser could expect %s" (expected indent))
        }

    let inline private indented (indent: Indent) (p: Parser<_, IndentState<_>>) =
        parse {
            do! updateIndent indent
            do! spaces
            return! parseWithIndent p
        }

    let public any _ p = parse { return! p }
    let public exact pos = indented (IndentExact pos)
    let public greater pos = indented (IndentGreater pos)
    let public atLeast pos = indented (IndentAtLeast pos)

    let rec public blockOf (p: Parser<_, IndentState<_>>) =
        parse {
            do! spaces
            let! pos = getPosition

            let! head = exact pos p
            let! tail = attempt (blockOf p |> exact pos) <|>% []

            return head :: tail
        }

    let private withIndentState u = { Indent = IndentAny; UserState = u }

    let public runParser p u s =
        runParserOnString p (withIndentState u) "" s

    let public runParserOnFile p u path =
        runParserOnFile p (withIndentState u) path System.Text.Encoding.UTF8

