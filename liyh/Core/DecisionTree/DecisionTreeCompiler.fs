namespace Liyh.Core.DecisionTree

module DecisionTreeCompiler =
    open Liyh.Core.DecisionTree
    open Liyh.Core
    open Liyh.Core.Helper

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
        symbol "eq" [Variable var1; Variable var2]

    let private mergeGuards (existing: CoreTerm option) (newGuard: CoreTerm) =
        match existing with
        | None -> newGuard
        | Some g -> symbol "and" [g; newGuard]

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
