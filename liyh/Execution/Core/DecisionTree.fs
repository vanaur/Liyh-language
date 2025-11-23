namespace Liyh.Execution.Core

module DecisionTree =
    open Liyh.Execution

    type public Path =
        | Root
        | Child of Path * int

        member this.Extend(index: int) = Child(this, index)

        override this.ToString() =
            let rec build path acc =
                match path with
                | Root -> if List.isEmpty acc then "." else String.concat "" acc
                | Child(parent, idx) -> build parent (sprintf "[%d]" idx :: acc)
            build this []

    type public DecisionTree =
        | Switch of
            _path: Path *
            _cases: Map<string * int, DecisionTree> *
            _default: DecisionTree option

        | SwitchLiteral of
            _path: Path *
            _cases: Map<CoreLiteral, DecisionTree> *
            _default: DecisionTree option

        | ArityCheck of
            _path: Path *
            _arity: int *
            _success: DecisionTree *
            _failure: DecisionTree option

        | TypeCheck of
            _path: Path *
            _cases: Map<TermType, DecisionTree> *
            _default: DecisionTree option

        | Bind of
            _varName: string *
            _path: Path *
            _continuation: DecisionTree
        
        | WhenGuard of
            _guard: CoreTerm *
            _bindings: Map<string, Path> *
            _success: DecisionTree *
            _failure: DecisionTree option

        | Leaf of
            _ruleIndex: int *
            _bindings: Map<string, Path>
        
        | Fail

    and public TermType =
        | TSymbol
        | TVariable
        | TLiteral of LiteralType
        | TClosure
        | TRecord
        | TWildcard

    and public LiteralType =
        | TInteger
        | TFloat
        | TString
        | TChar

    module public PathAccess =

        let rec public access (path: Path) (term: CoreTerm) =
            match path with
            | Root -> term
            | Child(parent, idx) ->
                let parentTerm = access parent term
                match parentTerm with
                | Symbol { Children = children } when idx >= 0 && idx < children.Length ->
                    children.[idx]
                | Symbol { Children = children } ->
                    failwithf "Path %O out of bounds: index %d, but term %s has only %d children"
                        path idx (PrettyPrinter.prettyPrintExpr parentTerm) children.Length
                | _ ->
                    failwithf "Path %O cannot descend into non-symbol term: %s"
                        path (PrettyPrinter.prettyPrintExpr parentTerm)

module DecisionTreeCompiler =
    open DecisionTree
    open Liyh.Execution

    type public PatternInfo =
        { Variables: Set<string>
          HasWhenClause: bool }

        static member simple (variables: Set<string>) =
            { Variables = variables
              HasWhenClause = false }

    type public PatternOccurrence =
        { RuleIndex: int
          Pattern: CoreTerm
          Path: Path
          Bindings: Map<string, Path>
          WhenClause: CoreTerm option }

    type public PatternMatrix =
        { Occurrences: PatternOccurrence list
          RemainingPaths: Path list }

    let private selectBestPath (matrix: PatternMatrix) =
        matrix.RemainingPaths |> List.tryHead

    let rec private safeAccess (path: Path) (term: CoreTerm) =
        match path with
        | Root -> term
        | Child(parent, idx) ->
            match safeAccess parent term with
            | Symbol { Children = children } when idx >= 0 && idx < children.Length -> children.[idx]
            | Variable _ | Wildcard -> Wildcard
            | _ -> Wildcard

    let private mkEqualityGuard (var1: string) (var2: string) =
        Symbol { Symbol = "eq"; Children = [Variable var1; Variable var2]; IsVariable = false; __hashCache = 0 }

    let private mergeGuards (existing: CoreTerm option) (newGuard: CoreTerm) =
        match existing with
        | None -> newGuard
        | Some g -> Symbol { Symbol = "and"; Children = [g; newGuard]; IsVariable = false; __hashCache = 0 }

    let private partitionByConstructor (path: Path) (occurrences: PatternOccurrence list) =
        let mutable byConstructor = Map.empty<(string * int), PatternOccurrence list>
        let mutable byLiteral = Map.empty<CoreLiteral, PatternOccurrence list>
        let mutable defaults = List.empty 
        let mutable others = List.empty

        for occ in occurrences do
            match safeAccess path occ.Pattern with
            | Symbol { Symbol = sym; IsVariable = false; Children = children } ->
                let arity = children.Length
                let key = (sym, arity)
                let existing = Map.tryFind key byConstructor |> Option.defaultValue []
                byConstructor <- Map.add key (occ :: existing) byConstructor
            
            | Literal lit ->
                let existing = Map.tryFind lit byLiteral |> Option.defaultValue []
                byLiteral <- Map.add lit (occ :: existing) byLiteral

            | Wildcard -> defaults <- occ :: defaults
            | Variable _ -> defaults <- occ :: defaults
            
            | WhenClause(_, _) -> others <- occ :: others
            | _ -> others <- occ :: others

        let byConstructor = byConstructor |> Map.map (fun _ l -> List.rev l)
        let byLiteral = byLiteral |> Map.map (fun _ l -> List.rev l)
        let defaults = List.rev defaults
        let others = List.rev others

        (byConstructor, byLiteral, defaults, others)

    let private specializeOccurrence (path: Path) (symbolName: string) (occ: PatternOccurrence) =
        match safeAccess path occ.Pattern with
        | Symbol { Symbol = sym } when sym = symbolName -> Some [occ]
        | Wildcard -> Some [occ]
        | Variable v ->
            match Map.tryFind v occ.Bindings with
            | None -> Some [{ occ with Bindings = Map.add v path occ.Bindings }]
            | Some _ ->
                let tempVarName = sprintf "$nonlinear_%s_%d" v (path.GetHashCode() |> abs)
                let equalityCheck = mkEqualityGuard v tempVarName
                let newGuard = mergeGuards occ.WhenClause equalityCheck

                Some [{ occ with Bindings = Map.add tempVarName path occ.Bindings; WhenClause = Some newGuard }]

        | _ -> None

    let private specializeLiteral (path: Path) (lit: CoreLiteral) (occ: PatternOccurrence) =
        match safeAccess path occ.Pattern with
        | Literal l when l = lit -> Some [occ]
        | Wildcard -> Some [occ]
        | Variable v -> 
            match Map.tryFind v occ.Bindings with
            | None -> Some [{ occ with Bindings = Map.add v path occ.Bindings }]
            | Some _ -> 
                let tempVarName = sprintf "$nonlinear_%s_%d" v (path.GetHashCode() |> abs)
                let equalityCheck = mkEqualityGuard v tempVarName
                let newGuard = mergeGuards occ.WhenClause equalityCheck
                Some [{ occ with Bindings = Map.add tempVarName path occ.Bindings; WhenClause = Some newGuard }]
        | _ -> None

    let rec private compileBindings 
        (path: Path)
        (occurrences: PatternOccurrence list)
        (remainingPaths: Path list) =

        let nextOccurrences =
            occurrences
            |> List.map (fun occ ->
                match safeAccess path occ.Pattern with
                | Variable v ->
                    match Map.tryFind v occ.Bindings with
                    | None -> { occ with Bindings = Map.add v path occ.Bindings }
                    | Some _ ->
                        let tempVar = sprintf "$nonlinear_%s_%d" v (path.GetHashCode() |> abs)
                        let newGuard = mergeGuards occ.WhenClause (mkEqualityGuard v tempVar)
                        { occ with Bindings = Map.add tempVar path occ.Bindings; WhenClause = Some newGuard }
                | _ -> occ
            )

        let nextMatrix = {
            Occurrences = nextOccurrences
            RemainingPaths = List.filter ((<>) path) remainingPaths
        }
        
        compile nextMatrix

    and private compile (matrix: PatternMatrix) =
        let uniqueOccurrences = matrix.Occurrences |> List.distinctBy _.RuleIndex

        match uniqueOccurrences with
        | [] -> DecisionTree.Fail
        | [ occ ] when List.isEmpty matrix.RemainingPaths ->
            match occ.WhenClause with
            | None -> DecisionTree.Leaf(occ.RuleIndex, occ.Bindings)
            | Some guard ->
                DecisionTree.WhenGuard(
                    guard,
                    occ.Bindings,
                    DecisionTree.Leaf(occ.RuleIndex, occ.Bindings),
                    Some DecisionTree.Fail)
        | _ ->
            match selectBestPath { matrix with Occurrences = uniqueOccurrences } with
            | None -> compileWhenClauses uniqueOccurrences
            | Some path ->
                let (bySymbol, byLiteral, defaults, others) =
                    partitionByConstructor path uniqueOccurrences

                if not (Map.isEmpty bySymbol)
                then compileSwitch path bySymbol defaults matrix.RemainingPaths
                else
                    if not (Map.isEmpty byLiteral)
                    then compileSwitchLiteral path byLiteral defaults matrix.RemainingPaths
                    else compileBindings path (defaults @ others) matrix.RemainingPaths

    and private compileSwitch 
            (path: Path) 
            (byConstructor: Map<(string * int), PatternOccurrence list>)
            (defaults: PatternOccurrence list)
            (remainingPaths: Path list) =

        let cases =
            byConstructor
            |> Map.map (fun (symbolName, arity) occs ->
                let specialized = 
                    occs 
                    |> List.choose (specializeOccurrence path symbolName)
                    |> List.collect id

                let childPaths = [0 .. arity - 1] |> List.map (fun i -> path.Extend i)
                let newPaths = childPaths @ (List.filter (( <> ) path) remainingPaths)
                
                compile { Occurrences = specialized; RemainingPaths = newPaths }
            )

        let defaultCase =
            if List.isEmpty defaults then None
            else Some (compileBindings path defaults remainingPaths)
        
        DecisionTree.Switch(path, cases, defaultCase)

    and private compileSwitchLiteral
            (path: Path)
            (byLiteral: Map<CoreLiteral, PatternOccurrence list>)
            (defaults: PatternOccurrence list)
            (remainingPaths: Path list) =

        let cases =
            byLiteral
            |> Map.map (fun lit occs ->
                let specialized =
                    occs
                    |> List.choose (specializeLiteral path lit)
                    |> List.collect id
                
                let newPaths = List.filter (( <> ) path) remainingPaths
                compile { Occurrences = specialized; RemainingPaths = newPaths }
            )

        let defaultCase =
            if List.isEmpty defaults then None
            else Some (compileBindings path defaults remainingPaths)

        DecisionTree.SwitchLiteral(path, cases, defaultCase)

    and private compileWhenClauses (occurrences: PatternOccurrence list) =
        match occurrences with
        | [] -> DecisionTree.Fail
        | occ :: rest ->
            match occ.WhenClause with
            | None -> DecisionTree.Leaf(occ.RuleIndex, occ.Bindings)
            | Some guard ->
                DecisionTree.WhenGuard(
                    guard,
                    occ.Bindings,
                    DecisionTree.Leaf(occ.RuleIndex, occ.Bindings),
                    Some (compileWhenClauses rest))

    let public compileRules (rules: CoreRule array) =
        let occurrences =
            rules
            |> Array.mapi (fun i rule ->
                { RuleIndex = i
                  Pattern = rule.LHS
                  Path = Root
                  Bindings = Map.empty
                  WhenClause = rule.WhenClause })
            |> Array.toList

        compile { Occurrences = occurrences; RemainingPaths = [ Root ] }

module DecisionTreePrinter =
    open Liyh.Execution
    open DecisionTree
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

