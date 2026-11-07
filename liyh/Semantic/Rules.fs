#nowarn "3370"
namespace Liyh.Semantic

module private Rules =
    open Liyh.FFI.GeneralFFI
    open Liyh.Syntax.SyntaxTree
    open Liyh.Semantic.TypedSyntaxTree


    //                      //
    // --- Some Helpers --- //
    //                      //


    /// Generates a mangled name for a given signature based on parameter types.
    let private mangledRuleName (baseName: string) (paramTypes: LiyhType list) : string =
        if baseName = "main" then "main"
        else
            let cleanType (t: LiyhType) = t.Prune().ToString()
            let paramsStr = paramTypes |> List.map cleanType |> String.concat ", "
            //sprintf "%s[%s]" baseName paramsStr
            sprintf "%s@[%s]" baseName paramsStr

    /// Defines a provisional monomorphic signature for a given rule's name and arity.
    let private freshSignature (tsCtx: TypecheckContext) (name: string) (arity: int) =
        let paramsTypes =
            if name = "main" && arity = 1 then
                [ TApp("List", [ TString ]) ]
            else
                List.init arity (fun i -> tsCtx.FreshVar (sprintf "%s_p%d" name i))

        (paramsTypes, tsCtx.FreshVar (sprintf "%s_ret" name))

    /// Converts the AST type annotation of a rule's return type into the Liyh types and effects.
    let private resolveRetAnnotation (tsCtx: TypecheckContext) (scope: TypeScope) (env: Env) (rule: Rule) =
        match rule.Type with
        | Some { Node = ModuloEffectType(declRet, declEffs) } ->
            (Some (resolveType tsCtx scope env declRet), Some (resolveEffects tsCtx env declEffs))

        | Some declRet ->
            (Some (resolveType tsCtx scope env declRet), Some Set.empty)

        | None ->
            (None, None)

    /// Returns an error if the set of declared effects given differs from the set of inferred effects given.
    let private checkUndeclaredEffects
        (tsCtx: TypecheckContext)
        (name: string)
        (rule: Rule)
        (bodyEffects: Set<string>)
        (allowedEffectsOpt: Set<string> option)
        =
        match allowedEffectsOpt with
        | Some allowedEffects when not (Set.isSubset bodyEffects allowedEffects) ->
            let unhandledStr = String.concat ", " (bodyEffects - allowedEffects)
            let desc = sprintf "Rule '%s' produces undeclared effect(s): { %s }." name unhandledStr
            let hint = sprintf "Add '%% { %s }' to the return type annotation." unhandledStr
            tsCtx.ReportError ErrorCode.UnhandledEffectError desc [] hint rule.Type.Value

        | _ -> ()

    /// Checks that a rule pattern that destructures a reducible rule is declared as `outermost`.
    let rec private checkOutermostRulePatterns
        (tsCtx: TypecheckContext)
        (env: Env)
        (isOutermost: bool)
        (patt: PatternWithPos)
        =
        if not env.InSymbolicScope && not isOutermost then
            match removePos patt with
            | ApplyPattern(phead, pargs) ->
                let headNameOpt =
                    match removePos phead with
                    | IdentPattern id -> Some (string id)
                    | _ -> None

                match headNameOpt with
                // A reducible known rule.
                | Some name when Map.containsKey name env.Signatures && not (Map.containsKey name env.Constructors) ->
                    let desc = sprintf "Rule pattern matches reducible rule '%s', but evaluation strategy is not 'outermost'." name
                    let hint = "By default, Liyh applies 'innermost' (strict) rewriting. Subterms are reduced before this clause can match. You should use the 'outermost' rewriting strategy. Outermost rules are always tested before 'innermost' ones."
                    tsCtx.ReportWarning WarningCode.NonOutermostPatternWarning desc [] hint patt

                // A functional higher-order varaible
                | Some name when not (Map.containsKey name env.Constructors) ->
                    let desc = sprintf "Higher-order variable pattern `%s[...]` captures an unreduced function or rule call, but evaluation strategy is not 'outermost'." name
                    let hint = "By default, Liyh applies 'innermost' (strict) rewriting. Subterms are reduced before this clause can match. You should use the 'outermost' rewriting strategy. Outermost rules are always tested before 'innermost' ones."
                    tsCtx.ReportWarning WarningCode.NonOutermostPatternWarning desc [] hint patt

                | _ -> ()

                List.iter (checkOutermostRulePatterns tsCtx env isOutermost) pargs

            | MixfixOperatorPattern(nameWithPos, args) ->
                let notationName = removePos nameWithPos
                match Map.tryFind notationName env.Notations with
                | Some notation ->
                    let holes = Mixfix.getNotationHoles notation

                    if List.length args = List.length holes then
                        let subst = Map.ofList (List.zip holes args)
                        let expandedPattern = Mixfix.exprToPatternWithSubst tsCtx patt subst notation.NotationIs
                        checkOutermostRulePatterns tsCtx env isOutermost expandedPattern
                    else
                        List.iter (checkOutermostRulePatterns tsCtx env isOutermost) args

                | None ->
                    List.iter (checkOutermostRulePatterns tsCtx env isOutermost) args

            | TuplePattern patts | ListPattern patts ->
                List.iter (checkOutermostRulePatterns tsCtx env isOutermost) patts

            | AsPattern(p1, p2) ->
                checkOutermostRulePatterns tsCtx env isOutermost p1
                checkOutermostRulePatterns tsCtx env isOutermost p2

            | WhenPattern(p, _) | TypedPattern(p, _) ->
                checkOutermostRulePatterns tsCtx env isOutermost p

            | RecordPattern fields ->
                List.iter (snd >> checkOutermostRulePatterns tsCtx env isOutermost) fields

            | _ -> ()

    /// Infers the patterns of a rule, unifies them with the signature's expected types, and returns
    /// the scope, the environment of bound variables, and the elaborated TPattern list.
    let private prepareClause
        (tsCtx: TypecheckContext)
        (monoEnv: Env)
        (expectedParamsTypes: LiyhType list)
        (rule: Rule)
        : TypeScope * Env * TPattern list
        =
        let scope = TypeScope.create()

        let isOutermost =
            rule.Strategy
            |> Option.map removePos
            |> Option.exists (function Outermost -> true | _ -> false)

        List.iter (checkOutermostRulePatterns tsCtx monoEnv isOutermost) rule.Patterns

        let patternResults =
            rule.Patterns
            |> List.mapi (fun i p ->
                let expectedTypeOpt =
                    if i < List.length expectedParamsTypes
                    then Some (expectedParamsTypes.[i].Prune())
                    else None

                InferenceChecking.inferPattern InferenceChecking.RulePattern tsCtx scope monoEnv expectedTypeOpt p
            )

        let tpats, bindingsList = List.unzip patternResults
        let raw = mergeBindings tsCtx rule.Name bindingsList

        List.iteri2 (fun i (tp: TPattern) t2 ->
            Unification.unifyOrReport tsCtx tp.Type t2 rule.Patterns.[i]
        ) tpats expectedParamsTypes

        // Enforce commutativity on binary operators: operands must have identical types.
        match Mixfix.tryFindCommutativeNotation monoEnv (removePos rule.Name) with
        | Some notation when List.length tpats = 2 && not monoEnv.InSymbolicScope ->
            let desc = sprintf "Commutative operator `%s` requires both operands to have the same type." (Mixfix.describeNotationPattern notation)
            Unification.unifyOrReportWithDesc tsCtx tpats.[0].Type tpats.[1].Type desc rule.Patterns.[1]
        | _ -> ()

        (scope, envWithBindings monoEnv raw, tpats)

    /// Typechecks a rule's annotation, guard and body against the expected return type,
    /// and returns the elaborated TRule and its effects.
    let private checkClause
        (tsCtx: TypecheckContext)
        (monoEnv: Env)
        (name: string)
        (expectedRetType: LiyhType)
        (rule: Rule)
        (scope: TypeScope, fullEnv: Env, tpats: TPattern list)
        : TRule * Set<string>
        =
        let declRetTypeOpt, allowedEffectsOpt = resolveRetAnnotation tsCtx scope monoEnv rule
        Option.iter (fun d -> Unification.unifyOrReport tsCtx expectedRetType d rule.Type.Value) declRetTypeOpt

        let whenTExprOpt =
            rule.WhenClause
            |> Option.map (fun c -> fst (InferenceChecking.check tsCtx scope fullEnv c TBool))

        let targetRetType = Option.defaultValue expectedRetType declRetTypeOpt

        // Invalid rules have bottom semantic.

        let bodyTExpr, bodyEffects =
            match Option.map removePos rule.Strategy with
            | Some Invalid ->
                let bTExpr, effs = InferenceChecking.inferExpression tsCtx scope fullEnv rule.Body
                checkUndeclaredEffects tsCtx name rule effs allowedEffectsOpt
                bTExpr, effs

            | _ ->
                let bodyAttempt =
                    tsCtx.Attempt(fun _ ->
                        let bTExpr, effs = InferenceChecking.check tsCtx scope fullEnv rule.Body targetRetType
                        checkUndeclaredEffects tsCtx name rule effs allowedEffectsOpt
                        bTExpr, effs)

                match bodyAttempt with
                | Some (bTExpr, effs) -> bTExpr, effs
                | None ->
                    let actualTExpr, effs = InferenceChecking.inferExpression tsCtx scope fullEnv rule.Body

                    // Only raise a return value conflict error if the types are actually incompatible.
                    let isIncompatible = not (tsCtx.Probe(fun _ -> Unification.unify tsCtx actualTExpr.Type targetRetType))

                    if isIncompatible then
                        let desc =
                            sprintf "Return type mismatch in clause of rule '%s': body evaluates to `%s`, but expected `%s`."
                                name (string (actualTExpr.Type.Prune())) (string (targetRetType.Prune()))

                        let infoSource =
                            match declRetTypeOpt with
                            | Some _ -> sprintf "The return type was explicitly declared as `%s` on rule '%s'." (string targetRetType) name
                            | None -> sprintf "The return type `%s` was inferred from previous clauses of rule '%s'." (string targetRetType) name

                        let hint = sprintf "All clauses of rule '%s' must evaluate to the same return type, or use a distinct rule name." name
                        tsCtx.ReportError ErrorCode.ConflictingRuleReturnTypesError desc [ infoSource ] hint rule.Body

                    actualTExpr, effs

        let ruleSpan = spanOf rule.Name
        let ruleIdent = tsCtx.CreateIdent { Qualifier = []; Name = rule.Name } (SymbolKind.RuleReference name) (Some ruleSpan)

        let trule =
            { RuleSymbol = ruleIdent
              RulePatterns = tpats
              RuleWhen = whenTExprOpt
              RuleType = targetRetType
              RuleStrategy = rule.Strategy
              RuleBody = bodyTExpr }

        (trule, bodyEffects)

    /// Checks that outermost rules do indeed have at least one innermost or invalid fallback clause.
    let private checkOutermostCompleteness
        (tsCtx: TypecheckContext)
        (env: Env)
        (rules: (Rule * bool) list)
        =
        if not env.InSymbolicScope then
            let byArity = List.groupBy (fun (r, _) -> List.length r.Patterns) rules

            for arity, arityRules in byArity do
                let hasOutermost =
                    arityRules
                    |> List.exists (fun (r, _) ->
                        match Option.map removePos r.Strategy with
                        | Some Outermost -> true
                        | _ -> false)

                if hasOutermost then
                    let hasFallback =
                        arityRules
                        |> List.exists (fun (r, _) ->
                            match Option.map removePos r.Strategy with
                            | Some Outermost -> false
                            | _ -> true)

                    if not hasFallback then
                        let rep, _ = List.head arityRules
                        let ruleName = removePos rep.Name

                        let desc = sprintf "Rule '%s' (arity %d) defines 'outermost' clause(s), but lacks a non-'outermost' fallback clause." ruleName arity
                        let hint = "To prevent unreduced terms from existing in a non-symbolic environment, add a non-'outermost' base clause."
                        tsCtx.ReportWarning WarningCode.MissingFallbackClauseWarning desc [] hint rep.Name

    /// If the main function does exist, then check its consistency.
    let private checkMain (tsCtx: TypecheckContext) (env: Env) (rules: (Rule * bool) list) =
        let repRule = fst (List.head rules)

        if Map.containsKey "main" env.Signatures then
            let desc = "The program entry point 'main' is already defined."
            let hint = "A program can contain at most one 'main' function."
            tsCtx.ReportError ErrorCode.DuplicateDeclarationError desc [] hint repRule.Name

        if List.length rules > 1 then
            for (rule, _) in List.tail rules do
                let desc = "Duplicate definition of entry point 'main'."
                let hint = "The entry point 'main' must be defined exactly once with a single clause (e.g. 'main[]' or 'main[args]')."
                tsCtx.ReportError ErrorCode.DuplicateDeclarationError desc [] hint rule.Name

        for (rule, _) in rules do
            let arity = List.length rule.Patterns
            if arity <> 0 && arity <> 1 then
                let desc = sprintf "Entry point 'main' accepts %d argument(s), but only 0 (`main[]`) or 1 (`main[List[String]]`) are allowed." arity
                let hint = "Change the signature to `main[]` or `main[args: List[String]]`."
                tsCtx.ReportError ErrorCode.ArityMismatchError desc [] hint rule.Name

    /// Registers FFI external functions in the environment, checking their parameter
    /// and return types for C compatibility, and elaborates them into TTopLevel nodes.
    let public registerExternDefinitions
        (tsCtx: TypecheckContext)
        (env: Env)
        (externs: Extern list)
        : Env * TTopLevel list
        =
        let mutable currentEnv = env
        let mutable elaboratedExterns = []

        for extrn in externs do
            let rawLibFile = removePos extrn.Library
            let mutable elaboratedSigs = []

            for sigWp in extrn.Content do
                let signature = sigWp.Node
                let scope = TypeScope.create()
                let fnName = removePos signature.Name

                let args = List.map (resolveType tsCtx scope currentEnv) signature.ArgumentsType
                let ret = Option.map (resolveType tsCtx scope currentEnv) signature.ReturnType
                let retType = Option.defaultValue (TCType CType.Void) ret

                List.iter2 (fun argPos argTy ->
                    match ForeignTypes.check tsCtx argPos 0 argTy with
                    | Some _ -> ()
                    | None ->
                        let desc = sprintf "FFI argument type `%s` is not a valid C type." (string argTy)
                        let hint = "FFI parameters must be native C types"
                        tsCtx.ReportError ErrorCode.InvalidFfiTypeError desc [] hint argPos
                ) signature.ArgumentsType args

                match signature.ReturnType with
                | Some retPos ->
                    match retType with
                    | TUnit | TCType CType.Void -> ()
                    | other ->
                        match ForeignTypes.check tsCtx retPos 0 other with
                        | Some _ -> ()
                        | None ->
                            let desc = sprintf "FFI return type `%s` is not a valid C type." (string other)
                            let hint = "FFI return types must be native C types."
                            tsCtx.ReportError ErrorCode.InvalidFfiTypeError desc [] hint retPos
                | None -> ()

                let fnType = TArrow(args, retType, Set.empty)
                let scheme = Scheme.generalize currentEnv fnType

                let def =
                    { Library = rawLibFile
                      FunctionName = fnName
                      Scheme = scheme }

                let moduleName = string (removePos extrn.AsName)
                let key = (moduleName, fnName)
                let existing = Map.tryFind key currentEnv.Externs |> Option.defaultValue []
                currentEnv <- { currentEnv with Externs = Map.add key (existing @ [ def ]) currentEnv.Externs }

                let fnIdent = tsCtx.CreateIdent { Qualifier = [ extrn.AsName.Node.Name ]; Name = signature.Name } (SymbolKind.ExternFunction rawLibFile) (Some (spanOf signature.Name))
                let tsig : TSignature =
                    { SigSymbol = fnIdent
                      SigArguments = args
                      SigReturn = ret }
                elaboratedSigs <- { Node = tsig; StartPos = sigWp.StartPos; EndPos = sigWp.EndPos } :: elaboratedSigs

            let libIdent = tsCtx.CreateIdent extrn.AsName.Node (SymbolKind.ExternFunction rawLibFile) (Some (spanOf extrn.AsName))
            let textern =
                { ExternLanguage = extrn.Language
                  ExternLibrary = extrn.Library
                  ExternSymbol = libIdent
                  ExternSignatures = List.rev elaboratedSigs }

            let tTop = { Node = TTopLevelNode.TExternDef textern; StartPos = extrn.Library.StartPos; EndPos = extrn.AsName.EndPos }
            elaboratedExterns <- tTop :: elaboratedExterns

        (currentEnv, List.rev elaboratedExterns)


    //                                              //
    // --- Type Checking Rule & Handlers Groups --- //
    //                                              //


    /// Performs type inference and type checking on a set of rules grouped by a preliminary dependency
    /// analysis pass using strongly connected components (SCC) and elaborates them into TTopLevel nodes.
    ///
    /// This works as follow:
    ///     1. Assign a provisional monomorphic signature to each function of the SCC.
    ///     2. First pass: patterns for all clauses are unified with the expected parameters.
    ///     3. Second pass: body inference, with the parameters now constrained.
    ///     4. Mutually generalize the rules.
    ///
    /// The two passes allows to ensure that, at each step, enough informations are shared through
    /// the type checking environment to catch the errors in the patterns as well as in the bodies.
    let public typecheckMutuallyRecursiveGroup
        (tsCtx: TypecheckContext)
        (env: Env)
        (rulesByName: Map<string, (Rule * bool) list>)
        (names: string list)
        : Env * TTopLevel list
        =
        for name in names do
            checkOutermostCompleteness tsCtx env rulesByName.[name]

        // Assign a provisional monomorphic signature to each function of the SCC.
        let groups =
            names
            |> List.map (fun name ->
                let taggedRules = rulesByName.[name]
                let arity = List.length (fst (List.head taggedRules)).Patterns

                let validRules =
                    taggedRules
                    |> List.filter (fun (rule, _) ->
                        let ok = List.length rule.Patterns = arity
                        if not ok then
                            let desc = sprintf "Inconsistent arity: expected %d argument(s), got %d." arity (List.length rule.Patterns)
                            tsCtx.ReportError ErrorCode.ArityMismatchError desc [] null rule.Name
                        ok)

                let expectedParamsTypes, expectedRetType = freshSignature tsCtx name arity
                (name, validRules, expectedParamsTypes, expectedRetType))

        // All provisional signatures are imported into the shared environment.
        let monoEnv =
            List.fold (fun acc (name, _, ps, ret) ->
                addOverload name (Scheme.empty (TArrow(ps, ret, Set.empty))) acc) env groups

        // First pass: patterns for all clauses are unified with the expected parameters.
        let prepared =
            List.map (fun (name, taggedRules, ps, ret) ->
                let clauses =
                    List.map (fun (rule, isLet) ->
                        let prep = prepareClause tsCtx monoEnv ps rule
                        (rule, isLet, prep)
                    ) taggedRules
                (name, ps, ret, clauses)
            ) groups

        // Second pass: body inference, with the parameters now constrained.
        let typed =
            List.map (fun (name, ps, ret, clauses) ->
                let trulesWithEffs =
                    List.map (fun (rule, isLet, prep) ->
                        let trule, effs = checkClause tsCtx monoEnv name ret rule prep
                        (trule, isLet, effs)
                    ) clauses

                let totalEffects = trulesWithEffs |> List.map (fun (_, _, e) -> e) |> Set.unionMany
                let trules = trulesWithEffs |> List.map (fun (r, isLet, _) -> (r, isLet))
                (name, ps, ret, totalEffects, trules)
            ) prepared

        let finalEnv =
            // Joint generalization of the rules.
            List.fold (fun acc (name, ps, ret, effects, _) ->
                addOverload name (Scheme.generalize env (TArrow(ps, ret, effects))) acc
            ) env typed

        let elaboratedTopLevels =
            typed
            |> List.collect (fun (_, _, _, _, trules) ->
                trules
                |> List.map (fun (trule, isLet) ->
                    let topNode = if isLet then TTopLevelNode.TLetRuleDef trule else TTopLevelNode.TRuleDef trule
                    { Node = topNode; StartPos = trule.RuleSymbol.Written.Name.StartPos; EndPos = trule.RuleBody.Span.End }
                ))

        (finalEnv, elaboratedTopLevels)

    type private RuleCluster =
        { ClusterName: string
          CandidateParamTypes: LiyhType list
          CandidateRetType: LiyhType
          Rules: (Rule * bool) list }

    /// Partition the clauses of a rule into different clusters of overloads.
    let private partitionRules (tsCtx: TypecheckContext) (env: Env) (rules: (Rule * bool) list) : (Rule * bool) list list =
        let globalCp = tsCtx.Checkpoint()

        try
            let mutable clusters: RuleCluster list = []

            for (rule, isLet) in rules do
                let ruleName = removePos rule.Name
                let arity = List.length rule.Patterns
                let mutable matchedClusterIdx = None

                (*

                // checks if any cluster unifies with the actual signature
                let compatibleClusterIndices =
                    clusters
                    |> List.indexed
                    |> List.choose (fun (i, cluster) ->
                        if cluster.ClusterName = ruleName && List.length cluster.CandidateParamTypes = arity then
                            let matchSuccess =
                                tsCtx.Attempt (fun _ ->
                                    let scope = TypeScope.create()
                                    let pTypes =
                                        rule.Patterns
                                        |> List.mapi (fun idx p ->
                                            let expectedTypeOpt = Some (cluster.CandidateParamTypes.[idx].Prune())
                                            let (tp, _) = InferenceChecking.inferPattern InferenceChecking.RulePattern tsCtx scope env expectedTypeOpt p
                                            tp.Type)

                                    List.iter2 (Unification.unify tsCtx) cluster.CandidateParamTypes pTypes

                                    match fst (resolveRetAnnotation tsCtx scope env rule) with
                                    | Some declType ->
                                        match Option.map removePos rule.Strategy with
                                        | Some Invalid -> ()
                                        | _ -> Unification.unify tsCtx cluster.CandidateRetType declType
                                    | None -> ())
                            if Option.isSome matchSuccess then Some i else None
                        else None)

                *)




                let hasTypedPattern =
                    rule.Patterns
                    |> List.exists (removePos >> _.IsTypedPattern)

                let isInvalidStrategy =
                    match Option.map removePos rule.Strategy with
                    | Some Invalid -> true
                    | _ -> false

                let inferPatt (expectedOpt: LiyhType option) (scope: TypeScope) (patt: PatternWithPos) =
                    InferenceChecking.inferPattern InferenceChecking.RulePattern tsCtx scope env expectedOpt patt
                    |> fst
                    |> _.Type

                let isClusterCompatible (cluster: RuleCluster) =
                    cluster.ClusterName = ruleName
                    && cluster.CandidateParamTypes.Length = arity
                    && tsCtx.Probe (fun _ ->
                        let rawScope = TypeScope.create()

                        let checkGenericMismatch (cType: LiyhType) (patt: PatternWithPos) =
                            let rType = inferPatt None rawScope patt

                            match cType.Prune(), rType.Prune() with
                            | TVar _, TVar _ -> ()
                            | (TVar _, _ | _, TVar _) when hasTypedPattern ->
                                raise (UnifyException { Message = "Generic mismatch"; Informations = []; Hint = null })
                            | _ -> ()

                        List.iter2 checkGenericMismatch cluster.CandidateParamTypes rule.Patterns

                        let scope = TypeScope.create()
                        let unifyParam (cType: LiyhType) (patt: PatternWithPos) =
                            let pType = inferPatt (Some (cType.Prune())) scope patt
                            Unification.unify tsCtx cType pType

                        List.iter2 unifyParam cluster.CandidateParamTypes rule.Patterns

                        match fst (resolveRetAnnotation tsCtx scope env rule) with
                        | Some declType when not isInvalidStrategy ->
                            Unification.unify tsCtx cluster.CandidateRetType declType
                        | _ -> ()
                    )

                let compatibleClusterIndices =
                    clusters
                    |> List.indexed
                    |> List.choose (fun (i, cluster) -> if isClusterCompatible cluster then Some i else None)


                match compatibleClusterIndices with
                | [ idx ] ->
                    let cluster = clusters.[idx]
                    let updated = { cluster with Rules = cluster.Rules @ [ (rule, isLet) ] }
                    clusters <- List.mapi (fun i item -> if i = idx then updated else item) clusters

                | [] ->
                    if ruleName = "main" && not (List.isEmpty clusters) then
                        let desc = "The 'main' function cannot be overloaded."
                        tsCtx.ReportError ErrorCode.AmbiguousOverloadError desc [] null rule.Name

                    // No compatible cluster: creating a new cluster.
                    let scope = TypeScope.create()
                    let pTypes =
                        rule.Patterns
                        |> List.map (fun p ->
                            let (tp, _) = InferenceChecking.inferPattern InferenceChecking.RulePattern tsCtx scope env None p
                            tp.Type)

                    if ruleName = "main" && List.length pTypes = 1 then
                        let expectedMainArg = TApp("List", [ TString ])
                        Unification.unifyOrReport tsCtx pTypes.[0] expectedMainArg rule.Patterns.[0]

                    // Enforce commutativity symmetry on candidate cluster types
                    match Mixfix.tryFindCommutativeNotation env ruleName with
                    | Some _ when List.length pTypes = 2 && not env.InSymbolicScope ->
                        Unification.unify tsCtx pTypes.[0] pTypes.[1]
                    | _ -> ()

                    let provisionalRet = tsCtx.FreshVar (sprintf "%s_ret" ruleName)
                    let rType =
                        match fst (resolveRetAnnotation tsCtx scope env rule) with
                        | None -> provisionalRet
                        | Some declType ->
                            Unification.unifyOrReport tsCtx provisionalRet declType rule.Type.Value
                            declType

                    let newCluster =
                        { ClusterName = ruleName
                          CandidateParamTypes = pTypes
                          CandidateRetType = rType
                          Rules = [ (rule, isLet) ] }

                    clusters <- clusters @ [ newCluster ]

                | many ->
                    let candidatesDesc =
                        many
                        |> List.map (fun idx ->
                            let c = clusters.[idx]
                            let typesStr = c.CandidateParamTypes |> List.map (fun t -> (t.Prune()).ToString()) |> String.concat ", "
                            sprintf "Overload cluster `%s[%s]`" ruleName typesStr)

                    let desc = sprintf "Clause of rule '%s' matches multiple distinct overload clusters." ruleName
                    let hint = "Add explicit type annotations to the pattern parameters to specify which overload this clause belongs to."
                    tsCtx.ReportError ErrorCode.AmbiguousOverloadError desc candidatesDesc hint rule.Name

            clusters
            |> List.map _.Rules

        finally
            tsCtx.BacktrackBindingsTo globalCp

    /// Performs type inference and type checking on a set of rules of the same cluster,
    /// and elaborates them into TTopLevel nodes.
    let public typecheckPartitionedRules (tsCtx: TypecheckContext) (env: Env) (rules: (Rule * bool) list) : Env * TTopLevel list =
        match rules with
        | [] -> (env, [])
        | (firstRule, _) :: _ ->
            let ruleName = removePos firstRule.Name
            if ruleName = "main" then
                checkMain tsCtx env rules

            checkOutermostCompleteness tsCtx env rules
            let clusters = partitionRules tsCtx env rules

            (*

            // This approach is sequential, and if clusters of different arities are used together, the type
            // checker may not recognise them, depending on the order in which they are defined.

            rules
            |> partitionRules tsCtx env
            |> List.fold (typecheckRuleGroup tsCtx) env

            *)

            match clusters with
            | [] -> (env, [])
            | [ cluster ] ->
                let name = removePos (fst (List.head cluster)).Name
                typecheckMutuallyRecursiveGroup tsCtx env (Map.ofList [ (name, cluster) ]) [ name ]

            | _ ->
                let ruleName = removePos (fst (List.head rules)).Name

                // Provisional signatures by cluster.
                let clusterData =
                    clusters
                    |> List.mapi (fun i cluster ->
                        let scope = TypeScope.create()
                        let ps =
                            (fst (List.head cluster)).Patterns
                            |> List.map (fun p ->
                                (InferenceChecking.inferPattern InferenceChecking.RulePattern tsCtx scope env None p |> fst).Type)

                        // Unify the parameters for every clauses of the cluster.
                        for (rule, _) in List.tail cluster do
                            let otherPs =
                                rule.Patterns
                                |> List.map (fun p ->
                                    InferenceChecking.inferPattern InferenceChecking.RulePattern tsCtx scope env None p
                                    |> fst
                                    |> _.Type)

                            List.iter2 (Unification.unify tsCtx) ps otherPs

                        // Enforce commutativity symmetry.
                        match Mixfix.tryFindCommutativeNotation env ruleName with
                        | Some _ when List.length ps = 2 && not env.InSymbolicScope ->
                            Unification.unify tsCtx ps.[0] ps.[1]
                        | _ -> ()

                        let ret = tsCtx.FreshVar (sprintf "%s_c%d_ret" ruleName i)
                        (cluster, ps, ret))

                // Provisional monoEnv for discovery (raw names, no partial mangling).
                let discoveryMonoEnv =
                    List.fold (fun acc (_, ps, ret) ->
                        addOverload ruleName (Scheme.empty (TArrow(ps, ret, Set.empty))) acc
                    ) env clusterData

                // Discovery pass: unifies PS and RET across all branches.
                for (cluster, ps, ret) in clusterData do
                    for (rule, isLet) in cluster do
                        let prep = prepareClause tsCtx discoveryMonoEnv ps rule
                        checkClause tsCtx discoveryMonoEnv ruleName ret rule prep |> ignore

                // At this step, PS is resolved for the whole cluster.
                let finalizedClusters =
                    clusterData
                    |> List.map (fun (cluster, ps, ret) ->
                        let finalMangledName = mangledRuleName ruleName ps
                        (cluster, ps, ret, finalMangledName))

                // Final environment containing the final mangled names.
                let definitiveMonoEnv =
                    List.fold (fun acc (_, ps, ret, finalMangledName) ->
                        addOverload ruleName (Scheme.emptyWithMangled finalMangledName (TArrow(ps, ret, Set.empty))) acc
                    ) env finalizedClusters

                // Definitions and recursive calls share the same name
                let typed =
                    finalizedClusters
                    |> List.map (fun (cluster, ps, ret, finalMangledName) ->
                        let trulesWithEffs =
                            cluster
                            |> List.map (fun (rule, isLet) ->
                                let prep = prepareClause tsCtx definitiveMonoEnv ps rule
                                let trule, effs = checkClause tsCtx definitiveMonoEnv finalMangledName ret rule prep
                                (trule, isLet, effs)
                            )

                        let effects = trulesWithEffs |> List.map (fun (_, _, e) -> e) |> Set.unionMany
                        let trules = trulesWithEffs |> List.map (fun (r, isLet, _) -> (r, isLet))
                        (finalMangledName, ps, ret, effects, trules)
                    )

                // Joint generalisation of all clusters in the final environment.
                let finalEnv =
                    List.fold (fun acc (finalMangledName, ps, ret, effects, _) ->
                        let scheme = Scheme.generalizeWithMangled finalMangledName env (TArrow(ps, ret, effects))
                        addOverload ruleName scheme acc
                    ) env typed

                let elaboratedTopLevels =
                    typed
                    |> List.collect (fun (_, _, _, _, trules) ->
                        trules
                        |> List.map (fun (trule, isLet) ->
                            let topNode = if isLet then TTopLevelNode.TLetRuleDef trule else TTopLevelNode.TRuleDef trule
                            { Node = topNode; StartPos = trule.RuleSymbol.Written.Name.StartPos; EndPos = trule.RuleBody.Span.End }
                        ))

                (finalEnv, elaboratedTopLevels)
