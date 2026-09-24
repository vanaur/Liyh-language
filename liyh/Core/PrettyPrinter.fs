#nowarn "26"
namespace Liyh.Core

module PrettyPrinter =
    open Liyh.Core
    open System

    let private indentSize = 4

    let rec private prettyPrintExprInternal (expr: CoreTerm) (depth: int) =
        let indentNext = depth + 1

        match expr with
        | Symbol { Symbol = s
                   Children = [] } -> s

        | Builtin.Ptr p ->
            sprintf "ptr[0x%016x]" (int64 p)

        | Symbol { Symbol = s
                   Children = xs } ->
            if List.isEmpty xs then
                s
            else
                sprintf "%s[%s]" s (String.concat ", " (List.map (fun e -> prettyPrintExprInternal e depth) xs))

        | VariableApply(v, args) ->
            sprintf "'%s[%s]" v (String.concat ", " (List.map (fun e -> prettyPrintExprInternal e depth) args))

        | Variable v -> sprintf "'%s" v
        | Wildcard -> "_"
        | Literal(Integer x) -> sprintf "%A" x
        | Literal(Float x) ->

            let formatDouble (x: double) =
                if System.Double.IsNaN(x) || System.Double.IsInfinity(x) then
                    x.ToString("G15", Globalization.CultureInfo.InvariantCulture)
                else
                    let s = x.ToString("G15", Globalization.CultureInfo.InvariantCulture)
                    if s.Contains(".") then
                        let trimmed = s.TrimEnd('0')
                        if trimmed.EndsWith(".") then trimmed + "0" else trimmed
                    else
                        s + ".0"

            formatDouble x

        | Literal(String x) -> sprintf "\"%s\"" x
        | Literal(Char x) -> sprintf "'%c'" x

        | CoreLet { Pattern = patt; Value = value } ->
            sprintf "let %s = %s" (prettyPrintExprInternal patt depth) (prettyPrintExprInternal value depth)

        | AsClause(a, b) -> sprintf "(%s) as (%s)" (prettyPrintExprInternal a depth) (prettyPrintExprInternal b depth)

        | WhenClause(a, b) ->
            sprintf "(%s) when (%s)" (prettyPrintExprInternal a depth) (prettyPrintExprInternal b depth)

        | RecordExtend { BaseRecord = baseRecord
                         Extension = xs } ->
            let brs =
                baseRecord
                |> Option.map (fun e -> sprintf "%s with " (prettyPrintExprInternal e depth))
                |> Option.defaultValue ""

            if List.isEmpty xs then
                "{ }"
            else
                let fields =
                    xs
                    |> List.map (fun (k, v) -> sprintf "%s = %s" k (prettyPrintExprInternal v depth))

                sprintf "{ %s%s }" brs (String.concat ", " fields)

        | TermSequence xs ->
            match xs with
            | [] -> "()"
            | [ single ] -> prettyPrintExprInternal single depth
            | _ ->
                let lines =
                    xs
                    |> List.map (fun e ->
                        sprintf "%s%s" (String(' ', indentNext * indentSize)) (prettyPrintExprInternal e indentNext))

                sprintf "\n%s" (String.concat "\n" lines)

        | Closure { Env = env
                    Parameters = parameters
                    Value = body } ->
            let envStr =
                if Map.isEmpty env then
                    ""
                else
                    let envItems =
                        env
                        |> Map.toList
                        |> List.map (fun (k, v) -> sprintf "'%s = %s" k (prettyPrintExprInternal v depth))

                    sprintf "{ %s }" (String.concat "; " envItems)

            let paramsStr = String.concat ", " parameters
            let bodyStr = prettyPrintExprInternal body depth

            if String.IsNullOrEmpty envStr then
                sprintf "closure[%s] -> %s" paramsStr bodyStr
            else
                sprintf "closure%s[%s] -> %s" envStr paramsStr bodyStr

        | FunctionalApplication { Base = func; Arguments = args } ->
            let funcStr = prettyPrintExprInternal func depth

            let argsStr =
                String.concat ", " (List.map (fun a -> prettyPrintExprInternal a depth) args)

            sprintf "%s(%s)" funcStr argsStr

        | UpdateVariable(v, e) -> sprintf "'%s <- %s" v (prettyPrintExprInternal e depth)
        | WhileLoop { Predicate = pred; Body = body } ->
            sprintf "while %s do %s" (prettyPrintExprInternal pred depth) (prettyPrintExprInternal body depth)

        | Match { ToMatch = toMatch; Cases = cases } ->
            let cases =
                cases
                |> List.map (fun (a, b) ->
                    sprintf
                        "\n%s| %s -> %s"
                        (String(' ', indentNext * indentSize))
                        (prettyPrintExprInternal a depth)
                        (prettyPrintExprInternal b depth))
                |> String.concat ""

            sprintf "match %s with %s" (prettyPrintExprInternal toMatch depth) cases

        | Handle { Handler = handler
                   State = state
                   ToHandle = toHandle } ->
            sprintf
                "using %s(%s) handle %s"
                handler
                (prettyPrintExprInternal state depth)
                (prettyPrintExprInternal toHandle depth)

        | Resume { Rewrite = rewrite; State = state } ->
            sprintf "resume %s with %s" (prettyPrintExprInternal rewrite depth) (prettyPrintExprInternal state depth)

        | Substitution { Env = env; InExpr = inExpr } ->
            let envStr = List.map (fun ({ Symbol = a }, b) -> sprintf "%s -> %s" a (prettyPrintExprInternal b depth)) env
            let inExprStr = prettyPrintExprInternal inExpr depth
            sprintf "[%s] in %s" (System.String.Join(", ", envStr)) inExprStr

        | UsingContext { Context = ctx; Expr = expr } ->
            sprintf "using context %s do %s" ctx (prettyPrintExprInternal expr depth)

    and private prettyPrintDefinitionInternal (def: CoreDefinition) : string =
        match def with
        | Rule { LHS = lhs
                 RHS = rhs
                 WhenClause = wc
                 Strategy = strat } ->
            let lhsStr = prettyPrintExprInternal lhs 0

            let wcStr =
                match wc with
                | Some cond -> sprintf " when %s" (prettyPrintExprInternal cond 0)
                | None -> ""

            let rhsStr = prettyPrintExprInternal rhs 0

            match strat with
            | Liyh.Syntax.SyntaxTree.RewritingStrategy.Strict -> sprintf "%s%s -> %s" lhsStr wcStr rhsStr
            | _ -> sprintf "%s%s %s -> %s" lhsStr wcStr ((string strat).ToLower()) rhsStr

        | other -> sprintf "TODO: %A" other

    let public prettyPrintExpr expr = prettyPrintExprInternal expr 0
    let public prettyPrintDefinition def = prettyPrintDefinitionInternal def
