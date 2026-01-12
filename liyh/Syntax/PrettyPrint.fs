#nowarn "40"
namespace Liyh.Syntax

module PrettyPrint =
    open System.Text
    open Liyh.Syntax.SyntaxTree

    let rec public prettyPrintExpression =
        removePos
        >> function
            | Expression.ParseError error -> sprintf "Error: %A" error
            | UFCS ufcs -> sprintf "%s |> %s" (prettyPrintExpression ufcs.LHS) (prettyPrintExpression ufcs.RHS)
            | Identifier id -> (removePos id).ToString()
            | BindingVariable name -> sprintf "'%s" name
            | CollectionAccess ca ->
                sprintf
                    "%s.[%s]"
                    (prettyPrintExpression ca.LHS)
                    (ca.Indices |> List.map (fun i -> prettyPrintExpression i) |> String.concat ", ")
            | Literal lit -> prettyPrintLiteral lit
            | ExpressionSequence exprs -> exprs |> List.map (fun e -> prettyPrintExpression e) |> String.concat "; "
            | Apply app ->
                sprintf
                    "%s[%s]"
                    (prettyPrintExpression app.LHS)
                    (app.Arguments
                     |> List.map (fun a -> prettyPrintExpression a)
                     |> String.concat ", ")
            | MixfixOperator op ->
                sprintf
                    "`%s`[%s]"
                    op.Name
                    (op.Arguments
                     |> List.map (fun a -> prettyPrintExpression a)
                     |> String.concat ", ")
            | Tuple exprs ->
                exprs
                |> List.map (fun e -> prettyPrintExpression e)
                |> String.concat ", "
                |> sprintf "(%s)"
            | List exprs ->
                exprs
                |> List.map (fun e -> prettyPrintExpression e)
                |> String.concat ", "
                |> sprintf "{ %s }"
            | Record fields ->
                fields
                |> List.map (fun (n, v) -> sprintf "%s = %s" n (prettyPrintExpression v))
                |> String.concat ", "
                |> sprintf "{ %s }"
            | RecordUsing(baseExpr, fields) ->
                let baseStr = prettyPrintExpression baseExpr

                let fieldsStr =
                    fields
                    |> List.map (fun (n, v) -> sprintf "%s = %s" n (prettyPrintExpression v))
                    |> String.concat ", "

                sprintf "{ %s using %s }" baseStr fieldsStr
            | ListComprehension lc ->
                let ifStr =
                    match lc.IfPred with
                    | Some pred -> sprintf " if %s" (prettyPrintExpression pred)
                    | None -> ""

                sprintf
                    "{ %s for %s in %s%s }"
                    (prettyPrintExpression lc.ItemValue)
                    (prettyPrintPattern lc.Pattern)
                    (prettyPrintExpression lc.ListExpr)
                    ifStr
            | Range r ->
                let stepStr =
                    match r.RangeStep with
                    | Some s -> sprintf ", %s" (prettyPrintExpression s)
                    | None -> ""

                sprintf "%s%s .. %s" (prettyPrintExpression r.RangeStart) stepStr (prettyPrintExpression r.RangeStop)
            | While w -> sprintf "while %s do %s" (prettyPrintExpression w.Predicate) (prettyPrintExpression w.Body)
            | ForIn fi ->
                sprintf
                    "for %s in %s do %s"
                    (prettyPrintPattern fi.Pattern)
                    (prettyPrintExpression fi.ListExpr)
                    (prettyPrintExpression fi.Body)
            | ForTo ft ->
                sprintf
                    "for %s = %s to %s do %s"
                    (prettyPrintPattern ft.Pattern)
                    (prettyPrintExpression ft.InitialValue)
                    (prettyPrintExpression ft.EndValue)
                    (prettyPrintExpression ft.Body)
            | ForDownTo ft ->
                sprintf
                    "for %s = %s downto %s do %s"
                    (prettyPrintPattern ft.Pattern)
                    (prettyPrintExpression ft.InitialValue)
                    (prettyPrintExpression ft.EndValue)
                    (prettyPrintExpression ft.Body)
            | ReAssign(name, value) -> sprintf "%s := %s" name (prettyPrintExpression value)
            | Let(pat, value) -> sprintf "let %s = %s" (prettyPrintPattern pat) (prettyPrintExpression value)
            | Var(pat, value) -> sprintf "var %s = %s" (prettyPrintPattern pat) (prettyPrintExpression value)
            | Match m ->
                let cases =
                    m.Cases
                    |> List.map (fun (pat, expr) ->
                        sprintf "| %s -> %s" (prettyPrintPattern pat) (prettyPrintExpression expr))
                    |> String.concat "\n"

                sprintf "match %s with\n%s" (prettyPrintExpression m.ToMatch) cases
            | IfThenElse ifte ->
                sprintf
                    "if %s then %s%s"
                    (prettyPrintExpression ifte.Condition)
                    (prettyPrintExpression ifte.ThenBranch)
                    (Option.defaultValue "" (Option.map (sprintf " else %s" << prettyPrintExpression) ifte.ElseBranch))
            | Lambda l ->
                sprintf
                    "[%s] -> %s"
                    (l.Patterns |> List.map (fun p -> prettyPrintPattern p) |> String.concat ", ")
                    (prettyPrintExpression l.Body)
            | HandleEffect h ->
                sprintf
                    "using %s %s handle %s"
                    (h.Handler.ToString())
                    (prettyPrintExpression h.InitialState)
                    (prettyPrintExpression h.Body)
            | ResumeWith rw ->
                sprintf "%s with %s" (prettyPrintExpression rw.Node.Value) (prettyPrintExpression rw.Node.Value)

    and public prettyPrintLiteral =
        removePos
        >> function
            | Literal.Unit -> "()"
            | Integer i -> string i
            | Float f -> string f
            | String s -> sprintf "\"%s\"" s
            | InterpolatedString parts ->
                parts
                |> List.map (function
                    | Str s -> s
                    | Interpolation e -> sprintf "{%s}" (prettyPrintExpression e))
                |> String.concat ""
                |> sprintf "\"%s\""
            | Char c -> sprintf "'%c'" c

    and public prettyPrintPattern =
        removePos
        >> function
            | VariablePattern s -> sprintf "'%s" s
            | SymbolPattern id -> string id
            | ApplyPattern(p, ps) ->
                sprintf
                    "%s[%s]"
                    (prettyPrintPattern p)
                    (ps |> List.map (fun p -> prettyPrintPattern p) |> String.concat ", ")
            | LiteralPattern l -> prettyPrintLiteral l
            | TuplePattern ps ->
                ps
                |> List.map (fun p -> prettyPrintPattern p)
                |> String.concat ", "
                |> sprintf "(%s)"
            | ListPattern ps ->
                ps
                |> List.map (fun p -> prettyPrintPattern p)
                |> String.concat ", "
                |> sprintf "{%s}"
            | RecordPattern fields ->
                fields
                |> List.map (fun (n, v) -> sprintf "%s = %s" n (prettyPrintPattern v))
                |> String.concat "; "
                |> sprintf "{%s}"
            | MixfixOperatorPattern(name, args) ->
                sprintf "%s(%s)" name (args |> List.map (fun p -> prettyPrintPattern p) |> String.concat ", ")
            | AsPattern(p1, p2) -> sprintf "%s as %s" (prettyPrintPattern p1) (prettyPrintPattern p2)
            | WhenPattern(p, e) -> sprintf "%s when %s" (prettyPrintPattern p) (prettyPrintExpression e)
            | TypedPattern(p, t) -> sprintf "%s : %s" (prettyPrintPattern p) (t.ToString())
            | AlternativePattern lits -> lits |> List.map (fun l -> prettyPrintLiteral l) |> String.concat " | "
            | Wildcard -> "_"

