namespace Liyh.Semantic

// Liyh has overloads in constructors, identifiers, handlers, and so on.
// The general mechanism is always the same given a list of candidates:
//
//  - If there is 0 candidate, then the overload resolution is `NotFound`.
//  - If there is 1 candidate, then we commit it or an error is thrown.
//  - If there is multiple candidates, then
//      - If the context is unconstrained, we cannot make a choice, the overload resolution is `Ambiguous`.
//      - Else, we probe then commit to select the unique candidate, the overload resolution is `Unique`.
//
// These modules are helpers for general overloads.

open Liyh.Syntax.SyntaxTree

/// The resulting of an overload resolution.
type private Resolution<'Result, 'Candidate> =
    | Unique of 'Result
    | Ambiguous of 'Candidate list
    | NotFound

module private OverloadResolver =

    /// Select from among the candidates following the rule:
    ///
    ///  - If there is 0 candidate, then the overload resolution is `NotFound`.
    ///  - If there is 1 candidate, then we commit it or an error is thrown.
    ///  - If there is multiple candidates, then
    ///      - If the context is unconstrained, we cannot make a choice, the overload resolution is `Ambiguous`.
    ///      - Else, we probe then commit to select the unique candidate, the overload resolution is `Unique`.
    let public select
        (probe: 'Candidate -> bool)         // checks if a candidate is compatible with the context
        (commit: 'Candidate -> 'Result)     // validates the successful candidate and commit the result
        (hasUnconstrainedArgs: bool)        // check if the arguments have unresolved constrainsts (TVar _)
        (candidates: 'Candidate list)       // the list of candidates to test
        : Resolution<'Result, 'Candidate>
        =
        match candidates with
        | [] -> NotFound

        | [ single ] ->
            if probe single then Unique (commit single)
            else NotFound

        | multiple ->
            // Filter by the probe to return the list of matching candidates.
            match List.filter probe multiple with
            | [ unique ] -> Unique (commit unique)
            | [] -> NotFound
            //| ambiguous -> Ambiguous ambiguous
            | first :: _ when not hasUnconstrainedArgs -> Unique (commit first)
            | ambiguous -> Ambiguous ambiguous

    let private findAmbiguityCauses (actualArgs: LiyhType list) : string list =
        actualArgs
        |> List.mapi (fun i argTy ->
            match argTy.Prune() with
            | TVar _ -> Some (sprintf "Argument %d has an unconstrained type (%s), which is compatible with multiple overloads." (i + 1) (string argTy))
            | _ -> None)
        |> List.choose id

    /// Filters the candidates by arity, then selects the unique one matching the context.
    /// On arity mismatch, ambiguity or no match, reports an error and returns `fallback`.
    let public resolve
        (tsCtx: TypecheckContext)
        (name: string)
        (node: WithPos<_>)
        (arity: int)
        (candidates: 'Candidate list)
        (getArity: 'Candidate -> int)
        (describe: 'Candidate -> string)
        (actualArgsOpt: LiyhType list option)
        (probe: 'Candidate -> bool)
        (commit: 'Candidate -> 'Result)
        (fallback: 'Result)
        : 'Result
        =
        // We first only keep the candidates that match the expected arity.
        let matchingArityCandidates = List.filter (fun c -> getArity c = arity) candidates
        let getCandidateStringList = List.map (fun c -> sprintf "Candidate: %s." (describe c))

        if List.isEmpty matchingArityCandidates then
            let arities =
                candidates
                |> List.map (getArity >> string)
                |> List.distinct
                |> String.concat ", "

            let desc = sprintf "No overload of '%s' accepts %d argument(s) (available arities: %s)." name arity arities
            tsCtx.ReportError ErrorCode.ArityMismatchError desc (getCandidateStringList candidates) null node
            fallback
        else
            let hasUnconstrainedArgs =
                match actualArgsOpt with
                | Some args -> args |> List.exists (fun t -> match t.Prune() with TVar _ -> true | _ -> false)
                | None -> false

            match select probe commit hasUnconstrainedArgs matchingArityCandidates with
            | Unique result ->
                result

            | Ambiguous inConflict ->
                let desc = sprintf "Ambiguous reference or call to overloaded '%s'." name

                let specificInfos =
                    match actualArgsOpt with
                    | Some args -> findAmbiguityCauses args
                    | None -> []

                let infos = specificInfos @ getCandidateStringList inConflict
                let hint =
                    if List.isEmpty specificInfos then
                        "Provide an explicit type annotation or qualify the identifier to resolve the ambiguity."
                    else
                        "Add a type annotation to the ambiguous argument(s) to select the intended overload."

                tsCtx.ReportError ErrorCode.AmbiguousOverloadError desc infos hint node
                fallback

            | NotFound ->
                let typesDesc =
                    match actualArgsOpt with
                    | Some args when not (List.isEmpty args) ->
                        let cleanArgs = args |> List.map (fun t -> string (t.Prune())) |> String.concat ", "
                        sprintf ": [%s]" cleanArgs
                    | _ -> " or expected type"

                let desc = sprintf "No overload of '%s' matches the provided argument types%s." name typesDesc
                let hint = "Check that the argument types match one of the available candidate signatures."
                tsCtx.ReportError ErrorCode.NoMatchingOverloadError desc (getCandidateStringList matchingArityCandidates) hint node
                fallback

module private ConstructorLookup =

    let public reportAmbiguity
        (tsCtx: TypecheckContext)
        (name: string)
        (candidates: ConstructorDef list)
        (node: WithPos<_>)
        =
        let desc = sprintf "Ambiguous reference to overloaded constructor '%s'." name
        let candidatesList = List.map (fun c -> sprintf "Candidate: %s.%s." c.TypeName c.Name) candidates
        let hint = "Provide an explicit type annotation or qualify the constructor (e.g. `TypeName.Constructor`)."
        tsCtx.ReportError ErrorCode.AmbiguousOverloadError desc candidatesList hint node

    /// Selects a type constructor given an optional type to test against (for bidirectional type inference).
    let public selectCandidateByExpectedType
        (tsCtx: TypecheckContext)
        (expectedOpt: LiyhType option)
        (candidates: ConstructorDef list)
        : Resolution<LiyhType, ConstructorDef>
        =
        let probe (cdef: ConstructorDef) =
            match expectedOpt with
            | None -> true
            | Some exp ->
                match exp.Prune() with
                | TVar { contents = UnboundVar _ } -> true
                | concrete ->
                    tsCtx.Probe (fun _ ->
                        let actual = cdef.ToType(tsCtx)
                        Unification.unify tsCtx actual concrete)

        let commit (cdef: ConstructorDef) =
            cdef.ToType(tsCtx)

        let hasUnconstrainedType =
            match expectedOpt with
            | None -> true
            | Some exp ->
                match exp.Prune() with
                | TVar _ -> true
                | _ -> false

        OverloadResolver.select probe commit hasUnconstrainedType candidates

module private RuleLookup =

    let public reportAmbiguity
        (tsCtx: TypecheckContext)
        (name: string)
        (candidates: Scheme list)
        (node: WithPos<_>)
        =
        let desc = sprintf "Ambiguous reference to overloaded rule '%s'." name
        let candidatesList = List.map (fun (Scheme(_, _, b, _)) -> sprintf "Candidate: %s%s." name (string b)) candidates
        let hint = "Provide an explicit type annotation to resolve the ambiguity."
        tsCtx.ReportError ErrorCode.AmbiguousOverloadError desc candidatesList hint node

    let public reportNoMatching (tsCtx: TypecheckContext) (name: string) (expected: LiyhType) (node: WithPos<_>) =
        let desc = sprintf "No overload of rule or identifier '%s' matches the expected type: `%s`." name (string expected)
        tsCtx.ReportError ErrorCode.NoMatchingOverloadError desc [] null node

    /// Selects a type scheme given an optional type to test against (for bidirectional type inference).
    let public selectCandidateByExpectedType
        (tsCtx: TypecheckContext)
        (name: string)
        (expectedOpt: LiyhType option)
        (schemes: Scheme list)
        : Resolution<LiyhType * Set<string> * string, Scheme>   // return: (type, effects, target name)
        =
        let probe s =
            match expectedOpt with
            | None -> true
            | Some exp ->
                match exp.Prune() with
                | TVar { contents = UnboundVar _ } -> true
                | concrete ->
                    tsCtx.Probe (fun _ ->
                        let actual = Scheme.instantiate tsCtx s
                        Unification.unify tsCtx actual concrete)

        let commit (scheme: Scheme) =
            let actual = Scheme.instantiate tsCtx scheme
            let latentEffects =
                match actual.Prune() with
                | TArrow(_, _, effs) -> effs
                | _ -> Set.empty

            let mangled = Scheme.getMangledName scheme
            let targetName = if System.String.IsNullOrEmpty mangled then name else mangled

            (actual, latentEffects, targetName)

        let hasUnconstrainedType =
            match expectedOpt with
            | None -> true
            | Some exp ->
                match exp.Prune() with
                | TVar _ -> true
                | _ -> false

        OverloadResolver.select probe commit hasUnconstrainedType schemes

    (*

    /// Selects a type scheme given a signature to test against (for bidirectional type inference).
    let public selectCandidateBySignature
        (tsCtx: TypecheckContext)
        (name: string)
        (schemes: Scheme list)
        (argTypes: LiyhType list)
        (retType: LiyhType)
        (node: WithPos<_>)
        : Set<string>
        =
        let arity = List.length argTypes

        let getArity (scheme: Scheme) =
            match scheme with
            | Scheme(_, _, body, _) ->
                match body.Prune() with
                | TArrow(args, _, _) -> List.length args
                | TVar _ -> arity
                | _ -> -1

        let probe (scheme: Scheme) =
            tsCtx.Probe (fun _ ->
                let instantiated = Scheme.instantiate tsCtx scheme

                match instantiated.Prune() with
                | TArrow(candArgs, candRet, _) ->
                    List.iter2 (Unification.unify tsCtx) argTypes candArgs
                    Unification.unify tsCtx retType candRet

                | TVar({ contents = UnboundVar _ } as r) ->
                    let candArgs = List.init arity (fun i -> tsCtx.FreshVar (sprintf "arg%d" i))
                    let candRet = tsCtx.FreshVar "ret"
                    tsCtx.BindTypeVar r (LinkVar (TArrow(candArgs, candRet, Set.empty)))
                    List.iter2 (Unification.unify tsCtx) argTypes candArgs
                    Unification.unify tsCtx retType candRet

                | _ ->
                    raise (UnifyException { Message = "Not a function"; Informations = []; Hint = null }))

        let commit (scheme: Scheme) =
            let instantiated = Scheme.instantiate tsCtx scheme

            match instantiated.Prune() with
            | TArrow(candArgs, candRet, effs) ->
                List.iter2 (Unification.unify tsCtx) argTypes candArgs
                Unification.unify tsCtx retType candRet
                effs

            | TVar({ contents = UnboundVar _ } as r) ->
                let candArgs = List.init arity (fun i -> tsCtx.FreshVar (sprintf "arg%d" i))
                let candRet = tsCtx.FreshVar "ret"
                tsCtx.BindTypeVar r (LinkVar (TArrow(candArgs, candRet, Set.empty)))
                List.iter2 (Unification.unify tsCtx) argTypes candArgs
                Unification.unify tsCtx retType candRet
                Set.empty

            | _ -> Set.empty

        OverloadResolver.resolve
            tsCtx
            name
            node
            arity
            schemes
            getArity
            (fun (Scheme(_, _, b, _)) -> sprintf "%s%s" name (string b))
            (Some argTypes)
            probe
            commit
            Set.empty

    *)

    let private tryInstantiateArrow (tsCtx: TypecheckContext) (scheme: Scheme) =
        match (Scheme.instantiate tsCtx scheme).Prune() with
        | TArrow(args, ret, effs) -> Some(args, ret, effs)
        | _ -> None

    /// Selects a type scheme given a signature to test against (for bidirectional type inference).
    let public selectCandidateBySignature
        (tsCtx: TypecheckContext)
        (name: string)
        (schemes: Scheme list)
        (argTypes: LiyhType list)
        (retType: LiyhType)
        (node: WithPos<_>)
        : Set<string>
        =
        let arity = List.length argTypes

        let probeWith (checkReturn: bool) (scheme: Scheme) =
            tsCtx.Probe(fun _ ->
                match tryInstantiateArrow tsCtx scheme with
                | Some(candArgs, candRet, _) when List.length candArgs = arity ->
                    List.iter2 (Unification.unify tsCtx) argTypes candArgs
                    if checkReturn then Unification.unify tsCtx retType candRet
                | _ -> raise (UnifyException { Message = ""; Informations = []; Hint = null }))

        let commit (scheme: Scheme) =
            match tryInstantiateArrow tsCtx scheme with
            | Some(candArgs, candRet, effs) when List.length candArgs = arity ->
                List.iter2 (Unification.unify tsCtx) argTypes candArgs
                Unification.unify tsCtx retType candRet
                effs
            | _ -> Set.empty

        let getArity (Scheme(_, _, body, _)) =
            match body.Prune() with
            | TArrow(args, _, _) -> List.length args
            | TVar _ -> arity
            | _ -> -1

        match schemes |> List.filter (probeWith false) with
        | [ single ] ->
            match tryInstantiateArrow tsCtx single with
            | Some(_, candRet, effs) ->
                let desc =
                    sprintf
                        "Return type mismatch in pattern '%s': rule produces `%s`, but the enclosing pattern context expects `%s`"
                        name (string (candRet.Prune())) (string (retType.Prune()))
                Unification.unifyOrReportWithDesc tsCtx candRet retType desc node
                effs
            | None -> Set.empty

        | _ ->
            OverloadResolver.resolve
                tsCtx name node arity schemes getArity
                (fun (Scheme(_, _, b, _)) -> sprintf "%s%s" name (string b))
                (Some argTypes)
                (probeWith true)
                commit
                Set.empty

