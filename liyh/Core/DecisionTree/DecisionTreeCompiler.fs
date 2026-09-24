namespace Liyh.Core.DecisionTree

module DecisionTreeCompiler =
    open Liyh.Core.DecisionTree
    open Liyh.Core

    type public PatternOccurrence =
        { RuleIndex: int
          Pattern: CoreTerm
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
            | VariableApply(_, args) when idx >= 0 && idx < args.Length -> args.[idx]
            | Variable _ | Wildcard -> Wildcard
            | _ -> Wildcard

        | Field(parent, name) ->
            match safeAccess parent term with
            | RecordExtend { Extension = fields } ->
                match List.tryFind (fun (k, _) -> k = name) fields with
                | Some (_, v) -> v
                | None -> Wildcard
            | Variable _ | Wildcard -> Wildcard
            | _ -> Wildcard

        | Tag parent ->
            match safeAccess parent term with
            | Symbol { Symbol = name } -> symbol name []
            | VariableApply(v, _) -> Variable v
            | Variable _ | Wildcard -> Wildcard
            | _ -> Wildcard

    let private mkEqualityGuard (var1: string) (var2: string) =
        symbol "__internal_eq" [Variable var1; Variable var2]

    let private mergeGuards (existing: CoreTerm option) (newGuard: CoreTerm) =
        match existing with
        | None -> newGuard
        | Some g -> symbol "and" [g; newGuard]

    // --- Normalization helpers ---

    /// Recursively extracts `WhenClauses` from a term. Returns the term without `WhenClauses`
    /// and the combined guard (if any).
    let rec private extractGuards (term: CoreTerm) : CoreTerm * CoreTerm option =
        match term with
        | WhenClause(p, g) ->
            let (innerP, innerG) = extractGuards p
            let combinedG = 
                match innerG with
                | None -> g
                | Some ig -> symbol "and" [ig; g]
            (innerP, Some combinedG)
        
        // Handle `AsClause` recursion: (A when G) as B -> (A as B) with G extracted
        | AsClause(p, v) ->
             let (innerP, innerG) = extractGuards p
             (AsClause(innerP, v), innerG)

        | VariableApply(v, args) ->
            let results = args |> List.map extractGuards
            let newArgs = results |> List.map fst
            let guards = results |> List.choose snd

            let combinedGuard =
                match guards with
                | [] -> None
                | [ g ] -> Some g
                | g :: rest -> Some (List.fold (fun acc g -> symbol "and" [ acc; g ]) g rest)

            (VariableApply(v, newArgs), combinedGuard)

        | Symbol s ->
            let results = s.Children |> List.map extractGuards
            let newChildren = results |> List.map fst
            let guards = results |> List.choose snd

            let newSymbol = Symbol { s with Children = newChildren }

            let combinedGuard =
                match guards with
                | [] -> None
                | [g] -> Some g
                | g::rest -> Some (List.fold (fun acc g -> symbol "and" [acc; g]) g rest)

            (newSymbol, combinedGuard)

        | _ -> (term, None)

    /// Recursively extracts AsClause bindings from a term relative to a given Path.
    /// Returns the term stripped of AsClauses and a list of new bindings (Variable -> Path).
    let rec private extractAsBindings (path: Path) (term: CoreTerm) : CoreTerm * (string * Path) list =
        match term with
        | AsClause(inner, Variable v) ->
            let (cleanInner, innerBindings) = extractAsBindings path inner
            (cleanInner, (v, path) :: innerBindings)

        | VariableApply(v, args) ->
            let results = args |> List.mapi (fun i child -> extractAsBindings (path.Extend i) child)
            let newArgs = results |> List.map fst
            let childBindings = results |> List.collect snd

            (VariableApply(v, newArgs), childBindings)

        | Symbol s ->
            let results = 
                s.Children 
                |> List.mapi (fun i child -> extractAsBindings (path.Extend i) child)
            
            let newChildren = results |> List.map fst
            let childBindings = results |> List.collect snd

            let newSymbol = Symbol { s with Children = newChildren }
            (newSymbol, childBindings)

        // If we encounter a WhenClause here (should be handled by extractGuards first, but for safety).
        | WhenClause(p, g) ->
            let (cleanP, bindings) = extractAsBindings path p
            (WhenClause(cleanP, g), bindings)

        | _ -> (term, [])

    let private normalizeOccurrence (occ: PatternOccurrence) =
        let (cleanPatternGuard, extractedGuard) = extractGuards occ.Pattern
        let (cleanPatternStructure, extractedBindings) = extractAsBindings Root cleanPatternGuard

        let finalGuard = 
            match extractedGuard with
            | None -> occ.WhenClause
            | Some g -> Some (mergeGuards occ.WhenClause g)

        let finalBindings =
            extractedBindings
            |> List.fold (fun acc (var, path) -> Map.add var path acc) occ.Bindings

        { occ with 
            Pattern = cleanPatternStructure
            Bindings = finalBindings
            WhenClause = finalGuard }

    let private partitionByConstructor (path: Path) (occurrences: PatternOccurrence list) =
        let mutable byConstructor = Map.empty<(string * int), PatternOccurrence list>
        let mutable byLiteral = Map.empty<CoreLiteral, PatternOccurrence list>
        let mutable byRecord = List.empty
        let mutable defaults = List.empty 
        let mutable others = List.empty

        for occ in occurrences do
            match safeAccess path occ.Pattern with
            | Symbol { Symbol = sym; Children = children } ->
                let arity = children.Length
                let key = (sym, arity)
                let existing = Map.tryFind key byConstructor |> Option.defaultValue []
                byConstructor <- Map.add key (occ :: existing) byConstructor

            | Literal lit ->
                let existing = Map.tryFind lit byLiteral |> Option.defaultValue []
                byLiteral <- Map.add lit (occ :: existing) byLiteral

            | RecordExtend _ -> byRecord <- occ :: byRecord
            | (Wildcard | Variable _ | VariableApply _) -> defaults <- occ :: defaults
            | _ -> others <- occ :: others

        let byConstructor = byConstructor |> Map.map (fun _ l -> List.rev l)
        let byLiteral = byLiteral |> Map.map (fun _ l -> List.rev l)
        let byRecord = List.rev byRecord
        let defaults = List.rev defaults
        let others = List.rev others

        (byConstructor, byLiteral, byRecord, defaults, others)

    let private bindVar (path: Path) (v: string) (occ: PatternOccurrence) : PatternOccurrence =
        match Map.tryFind v occ.Bindings with
        | None -> { occ with Bindings = Map.add v path occ.Bindings }
        | Some _ ->
            let tempVarName = sprintf "$nonlinear_%s_%d" v (path.GetHashCode() |> abs)
            let equalityCheck = mkEqualityGuard v tempVarName
            let newGuard = mergeGuards occ.WhenClause equalityCheck

            { occ with Bindings = Map.add tempVarName path occ.Bindings; WhenClause = Some newGuard }

    let private specializeOccurrence (path: Path) (symbolName: string) (occ: PatternOccurrence) =
        match safeAccess path occ.Pattern with
        | Symbol { Symbol = sym } when sym = symbolName -> Some [occ]
        | Wildcard -> Some [occ]
        | VariableApply(v, _) ->
            // Bind `v` to the symbol's tag and propagate the occurrence to check its arguments
            match Map.tryFind v occ.Bindings with
            | None -> Some [ { occ with Bindings = Map.add v (Tag path) occ.Bindings } ]
            | Some _ ->
                let tempVarName = sprintf "$nonlinear_%s_%d" v (path.GetHashCode() |> abs)
                let equalityCheck = mkEqualityGuard v tempVarName
                let newGuard = mergeGuards occ.WhenClause equalityCheck
                
                Some [{ occ with Bindings = Map.add tempVarName (Tag path) occ.Bindings; WhenClause = Some newGuard }]

        | Variable v -> Some [ bindVar path v occ ]
        | _ -> None

    let private specializeLiteral (path: Path) (lit: CoreLiteral) (occ: PatternOccurrence) =
        match safeAccess path occ.Pattern with
        | Literal l when l = lit -> Some [occ]
        | Wildcard -> Some [occ]
        | Variable v -> Some [ bindVar path v occ ]
        | _ -> None

    let rec private compileBindings 
        (path: Path)
        (occurrences: PatternOccurrence list)
        (remainingPaths: Path list) =

        let mutable additionalPaths: Path list = List.empty

        let nextOccurrences =
            occurrences
            |> List.map (fun occ ->
                match safeAccess path occ.Pattern with
                | VariableApply (v, children) ->
                    let childPaths = List.init children.Length (fun i -> path.Extend i)
                    additionalPaths <- additionalPaths @ childPaths
                    bindVar (Tag path) v occ

                | Variable v ->
                    bindVar path v occ

                | _ -> occ
            )

        let nextMatrix = {
            Occurrences = nextOccurrences
            RemainingPaths = additionalPaths @ List.filter ((<>) path) remainingPaths
        }
        
        compileRec nextMatrix

    and private compileRec (matrix: PatternMatrix) =
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
                let (bySymbol, byLiteral, byRecord, defaults, others) =
                    partitionByConstructor path uniqueOccurrences

                // Identify the highest priority default rule (wildcard or variable).
                let bestDefault = List.tryHead defaults

                // Determine the highest priority (lowest index) among all specific rules.
                // We need this to ensure the default rule strictly precedes any specific rule.
                let minSpecificIndex =
                    let s = bySymbol |> Map.toSeq |> Seq.collect snd |> Seq.map _.RuleIndex
                    let l = byLiteral |> Map.toSeq |> Seq.collect snd |> Seq.map _.RuleIndex
                    let r = byRecord |> Seq.map _.RuleIndex

                    Seq.append s (Seq.append l r)
                    |> Seq.fold min System.Int32.MaxValue

                //
                // Generating a Switch forces evaluation of the pattern matched argument, which breaks
                // lazy evaluation semantics. For example, in `(true || bomb[])` where `bomb[] -> bomb[]`,
                // the second argument must never be evaluated if `(_ || _)` is lazy.
                //
                // Safety conditions for skipping the Switch:
                // 1. The default rule has higher priority (lower RuleIndex) than all specific rules
                // 2. The default rule has no when-clause
                // 3. The default rule matches unconditionally on all paths:
                //    - Only Wildcards (always match)
                //    - Only fresh Variables (bind without checking)
                //    - No repeated variables (would require equality checks)
                //    - No constructors or literals (would require type/value checks)
                //
                // If these conditions hold, the specific rules are unreachable, and we can safely
                // skip to compileBindings without generating a Switch.
                //

                let shadowAllSpecifics =
                    match bestDefault with
                    | Some def when def.RuleIndex < minSpecificIndex && def.WhenClause.IsNone ->

                        // We must check all remaining paths for this rule to ensure it's truly unconditional.
                        let pathsToCheck = path :: (matrix.RemainingPaths |> List.filter (( <> ) path))

                        let rec checkPaths paths seenVars =
                            match paths with
                            | [] -> true
                            | p :: rest ->
                                match safeAccess p def.Pattern with
                                | Wildcard -> checkPaths rest seenVars
                                | Variable v ->
                                    // Check for linear patterns
                                    let isBoundPreviously = def.Bindings.ContainsKey v
                                    let isBoundCurrently = Set.contains v seenVars

                                    if isBoundPreviously || isBoundCurrently then false
                                    else checkPaths rest (Set.add v seenVars)

                                // Specific patterns (Literals, etc.) in other paths mean this rule is conditional.
                                | _ -> false

                        checkPaths pathsToCheck Set.empty

                    | _ -> false

                // If shadowing is active, we discard the specific cases.
                let (bySymbol, byLiteral, byRecord) =
                    if shadowAllSpecifics then
                        (Map.empty, Map.empty, [])
                    else
                        (bySymbol, byLiteral, byRecord)

                let allDefaults = defaults @ others

                if not (Map.isEmpty bySymbol)
                then compileSwitch path bySymbol allDefaults matrix.RemainingPaths
                else
                    if not (Map.isEmpty byLiteral)
                    then compileSwitchLiteral path byLiteral allDefaults matrix.RemainingPaths
                    else
                        if not (List.isEmpty byRecord)
                        then compileRecordAccess path (byRecord @ defaults) matrix.RemainingPaths
                        else compileBindings path allDefaults matrix.RemainingPaths

    /// Merges specific occurrences and compatible defects by correctly managing Shadowing
    /// (priority by index) and Fallback (guards).
    and private resolveDefaultsAndMerge
        (path: Path)
        (remainingPaths: Path list)
        (specificOccs: PatternOccurrence list)
        (defaults: PatternOccurrence list)
        (hasChildren: bool) =

        //
        // A default case must be kept in a specific branch if:
        //
        //  - Shadowing (order): The default is defined before the specific rule (its `RuleIndex` is
        //    smaller). It must take priority.
        // 
        //  - Fallback (guards): The specific rule has a guard (`when`). The default (defined after)
        //    serves as a fallback if the guard fails.
        // 
        //  - Progression: We are not yet at the end of the tree (newPaths is not empty), so we keep
        //    everything to continue structural exploration.
        //

        // We have to check whether we have reached the end of the analysis for this path.
        let filteredPaths = List.filter ((<>) path) remainingPaths
        let isPathExhausted = List.isEmpty filteredPaths && not hasChildren

        // We check for guards (that we have to include).
        let hasGuards = specificOccs |> List.exists _.WhenClause.IsSome

        // Index of the specific rule with the highest priority (the smallest).
        let minSpecificIndex = 
            if List.isEmpty specificOccs then System.Int32.MaxValue  // should not happens
            else
                specificOccs
                |> List.map _.RuleIndex
                |> List.min

        let compatibleDefaults =
            defaults |> List.filter (fun occ ->
                match safeAccess path occ.Pattern with
                | Variable _ | VariableApply _ | Wildcard ->
                    if not isPathExhausted then
                        // Continue to explore the structure.
                        // This keeps the defaults to propagate the constraints.
                        true
                    else
                        // Keep the default if shadowing or a when-clause.
                        (occ.RuleIndex < minSpecificIndex) || hasGuards
                | _ -> false
            )

        let allOccs =
            (specificOccs @ compatibleDefaults)
            |> List.sortBy _.RuleIndex

        (filteredPaths, allOccs)

    and private compileSwitch
            (path: Path) 
            (byConstructor: Map<(string * int), PatternOccurrence list>)
            (defaults: PatternOccurrence list)
            (remainingPaths: Path list) =

        let cases =
            byConstructor
            |> Map.map (fun (symbolName, arity) occs ->
                let (filteredPaths, allOccs) = 
                    resolveDefaultsAndMerge path remainingPaths occs defaults (arity > 0)

                let specialized =
                    allOccs 
                    |> List.choose (specializeOccurrence path symbolName)
                    |> List.collect id

                let childPaths = [0 .. arity - 1] |> List.map (fun i -> path.Extend i)
                let newPaths = childPaths @ filteredPaths

                compileRec { Occurrences = specialized; RemainingPaths = newPaths }
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
                let (filteredPaths, allOccs) = 
                    resolveDefaultsAndMerge path remainingPaths occs defaults false

                let specialized =
                    allOccs
                    |> List.choose (specializeLiteral path lit)
                    |> List.collect id

                compileRec { Occurrences = specialized; RemainingPaths = filteredPaths }
            )

        let defaultCase =
            if List.isEmpty defaults then None
            else Some (compileBindings path defaults remainingPaths)

        DecisionTree.SwitchLiteral(path, cases, defaultCase)

    and private compileRecordAccess (path: Path) (occurrences: PatternOccurrence list) (remainingPaths: Path list) =

        let allFields =
            occurrences
            |> List.collect (fun occ ->
                match safeAccess path occ.Pattern with
                | RecordExtend { Extension = fields } -> List.map fst fields
                | _ -> [])
            |> Set.ofList
            |> Set.toList

        let specializedOccurrences =
            occurrences
            |> List.map (fun occ ->
                match safeAccess path occ.Pattern with
                | Variable v -> bindVar path v occ
                | _ -> occ
            )

        let fieldPaths = allFields |> List.map (fun f -> path.Access f)
        let newRemainingPaths = fieldPaths @ (List.filter ((<>) path) remainingPaths)

        let successTree =
            compileRec
                { Occurrences = specializedOccurrences
                  RemainingPaths = newRemainingPaths }

        DecisionTree.RecordCheck(path, successTree, Some DecisionTree.Fail)

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

    /// Compiles a pattern matrix into a decision tree.
    let public compile (matrix: PatternMatrix) =
        let normalizedOccurrences = matrix.Occurrences |> List.map normalizeOccurrence
        compileRec { matrix with Occurrences = normalizedOccurrences }

    /// Compiles an array of rules into a decision tree.
    let public compileRules (rules: CoreRule array) =
        let occurrences =
            rules
            |> Array.mapi (fun i rule ->
                { RuleIndex = i
                  Pattern = rule.LHS
                  Bindings = Map.empty
                  WhenClause = rule.WhenClause })
            |> Array.toList

        compile { Occurrences = occurrences; RemainingPaths = [ Root ] }
