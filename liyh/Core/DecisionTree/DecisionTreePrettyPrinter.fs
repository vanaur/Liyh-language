namespace Liyh.Core.DecisionTree

module DecisionTreePrinter =
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open System.Text

    // --- Pretty print for debug purpose --- //

    let private indent (level: int) =
        String.replicate (level * 2) " "

    let private pathToString (path: Path) =
        path.ToString()

    let private ppCoreTerm (term: CoreTerm) =
        PrettyPrinter.prettyPrintExpr term

    let rec private prettyPrintTree (tree: DecisionTree) (level: int) (sb: StringBuilder) =
        let appendLine (s: string) = sb.AppendLine(s) |> ignore
        let indented = indent level

        match tree with
        | Fail ->
            appendLine $"{indented}└─ FAIL"

        | Leaf(ruleIndex, bindings) ->
            let bindingsStr =
                if Map.isEmpty bindings then ""
                else
                    bindings
                    |> Map.toSeq
                    |> Seq.map (fun (v, p) -> $"{v} ← {pathToString p}")
                    |> String.concat ", "
                    |> fun s -> $" {{ {s} }}"

            appendLine $"{indented}└─ MATCH rule #{ruleIndex}{bindingsStr}"

        | Bind(varName, path, continuation) ->
            appendLine $"{indented}├─ BIND {varName} ← {pathToString path}"
            prettyPrintTree continuation (level + 1) sb

        | WhenGuard(guard, bindings, success, failure) ->
            let bindingsStr =
                if Map.isEmpty bindings then ""
                else
                    " | " + (bindings |> Map.toSeq |> Seq.map (fun (v, p) -> $"{v}@ {pathToString p}") |> String.concat ", ")

            appendLine $"{indented}├─ WHEN {ppCoreTerm guard}{bindingsStr} ?"
            appendLine $"{indented}│   └─ yes →"
            prettyPrintTree success (level + 2) sb

            match failure with
            | None -> ()
            | Some f ->
                appendLine $"{indented}│   └─ no →"
                prettyPrintTree f (level + 2) sb

        | Switch(path, cases, defaultCase) ->
            appendLine $"{indented}├─ SWITCH on {pathToString path} (constructor)"

            let caseList = Map.toList cases
            let lastIndex = caseList.Length - 1

            caseList |> List.iteri (fun i ((symbol, arity), subtree) ->
                let branch = if i = lastIndex then "└─" else "├─"
                let name = if symbol = "" then "<anonymous>" else symbol
                appendLine $"{indented}│ {branch} {name}/{arity} →"
                prettyPrintTree subtree (level + 2) sb
            )

            match defaultCase with
            | None -> ()
            | Some def ->
                appendLine $"{indented}│ └─ _ → (default)"
                prettyPrintTree def (level + 2) sb

        | SwitchLiteral(path, cases, defaultCase) ->
            appendLine $"{indented}├─ SWITCH on {pathToString path} (constructor)"

            let caseList = Map.toList cases
            let lastIndex = caseList.Length - 1

            caseList |> List.iteri (fun i (literal, subtree) ->
                let branch = if i = lastIndex then "└─" else "├─"
                appendLine $"{indented}│ {branch} {literal} →"
                prettyPrintTree subtree (level + 2) sb
            )

            match defaultCase with
            | None -> ()
            | Some def ->
                appendLine $"{indented}│ └─ _ → (default)"
                prettyPrintTree def (level + 2) sb

        | ArityCheck(path, arity, success, failure) ->
            appendLine $"{indented}├─ ARITY CHECK on {pathToString path} == {arity}?"
            appendLine $"{indented}│   └─ yes →"
            prettyPrintTree success (level + 2) sb
            match failure with
            | None -> ()
            | Some f ->
                appendLine $"{indented}│   └─ no →"
                prettyPrintTree f (level + 2) sb

        | TypeCheck(path, cases, defaultCase) ->
            appendLine $"{indented}├─ TYPE CHECK on {pathToString path}"

            let typeToString tt =
                match tt with
                | TSymbol -> "symbol"
                | TVariable -> "variable"
                | TLiteral TInteger -> "integer"
                | TLiteral TFloat -> "float"
                | TLiteral TString -> "string"
                | TLiteral TChar -> "char"
                | TClosure -> "closure"
                | TRecord -> "record"
                | TWildcard -> "_"

            let caseList = cases |> Map.toList
            caseList |> List.iteri (fun i (tt, subtree) ->
                let branch = if i = caseList.Length - 1 && Option.isNone defaultCase then "└─" else "├─"
                appendLine $"{indented}│ {branch} {typeToString tt} →"
                prettyPrintTree subtree (level + 2) sb
            )

            match defaultCase with
            | None -> ()
            | Some def ->
                appendLine $"{indented}│ └─ _ →"
                prettyPrintTree def (level + 2) sb

    let public prettyPrint (tree: DecisionTree) =
        let sb = StringBuilder()
        sb.AppendLine("DECISION TREE") |> ignore
        prettyPrintTree tree 0 sb
        sb.ToString()

