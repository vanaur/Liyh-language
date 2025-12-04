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

module DecisionTreeDotPrinter =
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open System.Text

    let private nodeId = 
        let mutable counter = 0
        fun () ->
            counter <- counter + 1
            $"node{counter}"

    let private escape (s: string) =
        s.Replace("\"", "\\\"")
         .Replace("\n", "\\n")
         .Replace("\r", "")

    let private pathToString (path: Path) =
        path.ToString()

    let private ppCoreTerm (term: CoreTerm) =
        PrettyPrinter.prettyPrintExpr term

    let rec private buildGraph
        (tree: DecisionTree)
        (parentId: string option)
        (sb: StringBuilder)
        (edgeLabel: string option)
        =
        let currentId = nodeId()
        let appendLine (s: string) = sb.AppendLine(s) |> ignore

        match parentId, edgeLabel with
        | Some pid, Some label -> appendLine $"  {pid} -> {currentId} [label=\"{escape label}\"];"
        | Some pid, None -> appendLine $"  {pid} -> {currentId};"
        | None, _ -> ()

        match tree with
        | Fail -> appendLine $"  {currentId} [label=\"FAIL\", shape=box, style=filled, fillcolor=lightcoral];"
        | Leaf(ruleIndex, bindings) ->
            let bindingsStr =
                if Map.isEmpty bindings then ""
                else
                    bindings
                    |> Map.toSeq
                    |> Seq.map (fun (v, p) -> $"{v} ← {pathToString p}")
                    |> String.concat "\\n"
                    |> fun s -> $"\\n{s}"

            let label = escape $"MATCH #{ruleIndex}{bindingsStr}"
            appendLine $"  {currentId} [label=\"{label}\", shape=box, style=filled, fillcolor=lightgreen];"

        | Bind(varName, path, continuation) ->
            let label = escape $"BIND\\n{varName} ← {pathToString path}"
            appendLine $"  {currentId} [label=\"{label}\", shape=ellipse];"
            buildGraph continuation (Some currentId) sb None

        | WhenGuard(guard, bindings, success, failure) ->
            let bindingsStr =
                if Map.isEmpty bindings then ""
                else " | " + (bindings |> Map.toSeq |> Seq.map (fun (v, p) -> $"{v}@{pathToString p}")
                             |> String.concat ", ")

            let label = escape $"WHEN\\n{ppCoreTerm guard}{bindingsStr}"
            appendLine $"  {currentId} [label=\"{label}\", shape=diamond];"
            
            buildGraph success (Some currentId) sb (Some "yes")
            match failure with
            | Some f -> buildGraph f (Some currentId) sb (Some "no")
            | None -> ()

        | Switch(path, cases, defaultCase) ->
            let label = escape $"SWITCH\\n{pathToString path}"
            appendLine $"  {currentId} [label=\"{label}\", shape=diamond];"

            cases |> Map.iter (fun (symbol, arity) subtree ->
                let name = if symbol = "" then "<anon>" else symbol
                buildGraph subtree (Some currentId) sb (Some $"{name}/{arity}")
            )

            match defaultCase with
            | Some def -> buildGraph def (Some currentId) sb (Some "_")
            | None -> ()

        | SwitchLiteral(path, cases, defaultCase) ->
            let label = escape $"SWITCH LIT\\n{pathToString path}"
            appendLine $"  {currentId} [label=\"{label}\", shape=diamond];"

            cases |> Map.iter (fun literal subtree ->
                buildGraph subtree (Some currentId) sb (Some (literal.ToString()))
            )

            match defaultCase with
            | Some def -> buildGraph def (Some currentId) sb (Some "_")
            | None -> ()

        | ArityCheck(path, arity, success, failure) ->
            let label = escape $"ARITY\\n{pathToString path} = {arity}?"
            appendLine $"  {currentId} [label=\"{label}\", shape=diamond];"
            
            buildGraph success (Some currentId) sb (Some "yes")
            match failure with
            | Some f -> buildGraph f (Some currentId) sb (Some "no")
            | None -> ()

        | TypeCheck(path, cases, defaultCase) ->
            let label = escape $"TYPE\\n{pathToString path}"
            appendLine $"  {currentId} [label=\"{label}\", shape=diamond];"

            let typeToString tt =
                match tt with
                | TSymbol -> "symbol"
                | TVariable -> "variable"
                | TLiteral TInteger -> "int"
                | TLiteral TFloat -> "float"
                | TLiteral TString -> "string"
                | TLiteral TChar -> "char"
                | TClosure -> "closure"
                | TRecord -> "record"
                | TWildcard -> "_"

            cases |> Map.iter (fun tt subtree ->
                buildGraph subtree (Some currentId) sb (Some (typeToString tt))
            )

            match defaultCase with
            | Some def -> buildGraph def (Some currentId) sb (Some "_")
            | None -> ()

    let public toDot (tree: DecisionTree) =
        let sb = StringBuilder()
        sb.AppendLine("digraph DecisionTree {") |> ignore
        sb.AppendLine("  rankdir=TB;") |> ignore
        sb.AppendLine("  node [fontname=\"Helvetica\"];") |> ignore
        sb.AppendLine("  edge [fontname=\"Helvetica\"];") |> ignore
        sb.AppendLine() |> ignore
        
        buildGraph tree None sb None |> ignore
        
        sb.AppendLine("}") |> ignore
        sb.ToString()

module RenderDecisionTree =
    open System.IO
    open System.Diagnostics

    let public renderAndOpen (tree: Liyh.Core.DecisionTree.DecisionTree) =
        let dotFile = Path.GetTempFileName() + ".dot"
        let pngFile = Path.ChangeExtension(dotFile, ".png")

        try
            let dotContent = DecisionTreeDotPrinter.toDot tree
            File.WriteAllText(dotFile, dotContent)

            let dotProcess = 
                ProcessStartInfo(
                    FileName = "dot",
                    Arguments = $"-Tpng \"{dotFile}\" -o \"{pngFile}\"",
                    UseShellExecute = false,
                    CreateNoWindow = true
                )
            
            use proc = Process.Start(dotProcess)
            proc.WaitForExit()
            
            if proc.ExitCode <> 0 then
                failwith "Cannot convert DOT -> PNG"

            let openProcess =
                ProcessStartInfo(
                    FileName = pngFile,
                    UseShellExecute = true
                )
            
            Process.Start(openProcess) |> ignore
            //System.Threading.Thread.Sleep(1000)
            
        finally
            try
                ()
                //if File.Exists(dotFile) then File.Delete(dotFile)
                //if File.Exists(pngFile) then File.Delete(pngFile)
            with
            | _ -> ()

