#nowarn "3370"
namespace Liyh.Semantic

module private InferenceChecking =
    open Liyh.Syntax.SyntaxTree
    open Liyh.FFI.GeneralFFI
    open Liyh.Semantic.TypedSyntaxTree


    //                                                      //
    // --- Helpers for type inference and type checking --- //
    //                                                      //


    /// A call candidate is defined by its parameter types, return type, latent effects,
    /// diagnostic description and resolved identity.
    type private CallCandidate =
        { ParamTypes: LiyhType list
          RetType: LiyhType
          LatentEffects: Set<string>
          Description: string
          Ident: ResolvedIdent }

    /// Liyh allows higher order pattern matching in rule definition's patterns only, so we
    /// have to enforce this when we are not type checking a rule's pattern using a context.
    type public PatternContext =
        | RulePattern   // allows higher order pattern matching, for rules only
        | ValuePattern  // first order pattern matching

    /// Checks if the given expression depends on any context. This is the case of overloadable
    /// expressions, such as lambda and identifiers (for rules and type constructors).
    let private isContextDependent (env: Env) (exprWithPos: ExpressionWithPos) : bool =
        match removePos exprWithPos with
        | Lambda _ -> true
        | Identifier id ->
            let name = string id
            match env.TryFindSignature name with
            | Some (_ :: _ :: _) -> true // a rule with multiple overloads
            | _ ->
                match env.TryFindConstructor name with
                | Some (_ :: _ :: _) -> true // a constructor with multiple overloads
                | _ -> false
        | _ -> false

    /// Check if a commutative mixfix operator is well typed.
    let private checkCommutative
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (notation: Notation)
        (args: _ list)
        (infer: TypecheckContext -> TypeScope -> Env -> WithPos<'a> -> LiyhType * 'b)
        : unit
        =
        if removePos notation.NotationCommutative = true && List.length args = 2 && not env.InSymbolicScope then
            let (t1: LiyhType, _) = infer tsCtx scope env args.[0]
            let (t2: LiyhType, _) = infer tsCtx scope env args.[1]

            if t1.Prune() <> TSymbolic && t2.Prune() <> TSymbolic then
                let desc = sprintf "Commutative operator `%s` requires both operands to have the same type" (Mixfix.describeNotationPattern notation)
                Unification.unifyOrReportWithDesc tsCtx t1 t2 desc args.[1]

    /// Helper for type inference of mixfix operators, used both in expressions and patterns.
    let private expandAndInferMixfix
        (tsCtx: TypecheckContext)
        (env: Env)
        (parent: WithPos<_>)
        (nameWithPos: WithPos<string>)
        (args: 'Arg list)
        (fallback: 'Result)
        (inferExpanded: Notation -> Map<string, 'Arg> -> 'Result)
        : 'Result
        =
        let notationName = removePos nameWithPos
        match env.TryFindNotation notationName with
        // This case should not happen since the parser won't allow it.
        | None ->
            let desc = sprintf "Unknown notation or mixfix operator: '%s'." notationName
            let infos = [ suggestAlternativesIdentifiers env notationName ]

            tsCtx.ReportError ErrorCode.UnboundIdentifierError desc infos null parent
            fallback

        // Check the notation for expression or pattern.
        | Some notation ->
            let holes = Mixfix.getNotationHoles notation
            let arity = List.length holes

            if List.length args <> arity then
                let desc = sprintf "Operator '%s' expects %d argument(s), but received %d." notationName arity (List.length args)
                tsCtx.ReportError ErrorCode.ArityMismatchError desc [] null parent
                fallback
            else
                let subst = Map.ofList (List.zip holes args)
                let cp = tsCtx.Checkpoint()
                let res = inferExpanded notation subst

                if tsCtx.HasDiagnosticsSince cp then
                    let showComm = if removePos notation.NotationCommutative then "commutative " else ""
                    let patternStr = Mixfix.describeNotationPattern notation
                    let info = sprintf "In expansion of operator `%s` (%snotation '%s', defined %s)." patternStr showComm notationName (showInlinePosition notation.NotationName)
                    tsCtx.AddInfoToDiagnosticsSince cp info

                res

    /// Extracts structural and annotated expected type information from a pattern.
    let rec private tryExtractExpectedType
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (patt: PatternWithPos)
        : LiyhType option
        =
        match removePos patt with
        | TypedPattern(_, declType) ->
            Some (resolveType tsCtx scope env declType)

        | LiteralPattern lit ->
            match lit with
            | Literal.Integer _ -> Some TInt
            | Literal.Float _   -> Some TFloat
            | Literal.Char _    -> Some TChar
            | Literal.String _  -> Some TString
            | Literal.Unit      -> Some TUnit
            | Literal.InterpolatedString _ -> None

        | IdentPattern (UnqualifiedIdentifier "true")
        | IdentPattern (UnqualifiedIdentifier "false") ->
            Some TBool

        | IdentPattern ident
            when not (List.isEmpty ident.Qualifier)
                || not (env.ContainsSignature (removePos ident.Name)) ->

            let lookupKey = string ident
            match env.TryFindConstructor lookupKey with
            | Some [ cdef ] when List.isEmpty cdef.ArgTypes -> Some (cdef.ToType(tsCtx))
            | _ -> None

        | AsPattern(p1, p2) ->
            match tryExtractExpectedType tsCtx scope env p1, tryExtractExpectedType tsCtx scope env p2 with
            | (Some t, None | None, Some t) -> Some t
            | None, None -> None
            | Some t1, Some t2 ->
                Unification.unifyOrReport tsCtx t1 t2 patt
                Some t1

        | WhenPattern(inner, _) ->
            tryExtractExpectedType tsCtx scope env inner

        | TuplePattern patts ->
            let subTypes = List.map (tryExtractExpectedType tsCtx scope env) patts
            let types =
                List.map (function
                    | Some t -> t
                    | None -> tsCtx.FreshVar "t") subTypes

            Some (TTuple types)

        | ApplyPattern(phead, pargs) ->
            match removePos phead with
            | IdentPattern id ->
                let name = string id
                match env.TryFindConstructor name with
                | Some cdefs ->
                    let matching = cdefs |> List.filter (fun c -> List.length c.ArgTypes = List.length pargs)
                    match matching with
                    | [ uniqueCdef ] ->
                        let argTypes, resType = uniqueCdef.Instantiate(tsCtx)
                        List.iter2 (fun p expectedArg ->
                            match tryExtractExpectedType tsCtx scope env p with
                            | Some t -> Unification.unifyOrReport tsCtx t expectedArg p
                            | None -> ()
                        ) pargs argTypes
                        Some resType
                    | _ -> None
                | None -> None
            | _ -> None

        | ListPattern items ->
            let itemType = tsCtx.FreshVar "elem"

            for item in items do
                match tryExtractExpectedType tsCtx scope env item with
                | Some t -> Unification.unifyOrReport tsCtx t itemType item
                | None -> ()

            Some (TApp("List", [ itemType ]))

        | RecordPattern fields ->
            let fieldMap =
                fields
                |> List.map (fun (nameWp, p) ->
                    let t =
                        tryExtractExpectedType tsCtx scope env p
                        |> Option.defaultWith (fun () -> tsCtx.FreshVar "f")
                    removePos nameWp, t)
                |> Map.ofList

            Some (TRecord(fieldMap, tsCtx.FreshVar "ρ"))

        | AlternativePattern (first :: _) ->
            match removePos first with
            | Literal.Integer _ -> Some TInt
            | Literal.Float _   -> Some TFloat
            | Literal.Char _    -> Some TChar
            | Literal.String _  -> Some TString
            | _ -> None

        | _ -> None

    let private externCandidates
        (tsCtx: TypecheckContext)
        (lib: string)
        (name: string)
        (defs: ExternDef list)
        (siteIdent: Identifier)
        : CallCandidate list
        =
        List.choose (fun def ->
            let instantiated = Scheme.instantiate tsCtx def.Scheme
            match instantiated.Prune() with
            | TArrow(ps, ret, effs) as arrow ->
                let resIdent = tsCtx.CreateIdent siteIdent (SymbolKind.ExternFunction lib) None
                Some { ParamTypes = ps
                       RetType = ret
                       LatentEffects = effs
                       Description = sprintf "extern %s.%s%s" lib name (string arrow)
                       Ident = resIdent }
            | _ -> None) defs

    let private warningPointlessLetVar (tsCtx: TypecheckContext) (expr: WithPos<_>) =
        let desc = sprintf "Pointless `let`-binding in expression tail: the scope ends here."
        let hint = "You can ignore the result using a wildcard pattern; this will evaluate to the `Unit` type."
        tsCtx.ReportWarning WarningCode.PointlessBindingWarning desc [] hint expr

    /// Do some checks and verifications for a end of lexical scope.
    let private checkScopeExit (tsCtx: TypecheckContext) (entryEnv: Env) (finalEnv: Env) =

        // Check if all variables declared as 'mutable' has been mutated.
        for KeyValue(name, mut) in finalEnv.Mutables do
            let isNewInThisBlock =
                match Map.tryFind name entryEnv.Mutables with
                | Some parentMut -> not (LanguagePrimitives.PhysicalEquality parentMut.Mutated mut.Mutated)
                | None -> true

            if isNewInThisBlock && not !mut.Mutated then
                let desc = sprintf "The variable `%s` was declared as mutable, but has never been reassigned." name
                let hint = "Consider marking it as a constant via a `let`-declaration rather than a `var`-declaration."
                tsCtx.ReportWarning WarningCode.MutableBindingUnmodified desc [] hint mut.PattDecl


    //                                   //
    // --- Type Inference & Checking --- //
    //                                   //


    /// Type inference on patterns. Returns the elaborated TPattern as well as
    /// the resulting binding variables (mapped to their `ResolvedIdent` and type).
    let rec public inferPattern
        (patternContext: PatternContext)
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (expectedTypeOpt: LiyhType option)
        (pattWithPos: PatternWithPos)
        : TPattern * Map<string, ResolvedIdent * LiyhType>
        =
        let inferPattern = inferPattern patternContext
        let span = spanOf pattWithPos

        match removePos pattWithPos with
        | Wildcard ->
            let tv = tsCtx.FreshVar "w"
            let tpat = mkTyped tv span TPatternNode.TPatWildcard
            (tpat, Map.empty)

        | LiteralPattern lit ->
            let t, litNode =
                match lit with
                | Literal.Integer i -> TInt, TLiteralNode.TLitInteger i
                | Literal.Float f   -> TFloat, TLiteralNode.TLitFloat f
                | Literal.Char c    -> TChar, TLiteralNode.TLitChar c
                | Literal.String s  -> TString, TLiteralNode.TLitString s
                | Literal.Unit      -> TUnit, TLiteralNode.TLitUnit
                | Literal.InterpolatedString _ -> failwith "unreachable"

            Option.iter (fun exp -> Unification.unifyOrReport tsCtx t exp pattWithPos) expectedTypeOpt
            let tpat = mkTyped t span (TPatternNode.TPatLiteral litNode)
            (tpat, Map.empty)

        | IdentPattern (UnqualifiedIdentifier ("true" | "false" as boolStr)) ->
            Option.iter (fun exp -> Unification.unifyOrReport tsCtx TBool exp pattWithPos) expectedTypeOpt
            let id = removePos pattWithPos |> function IdentPattern i -> i | _ -> failwith "unreachable"
            let resIdent = tsCtx.CreateIdent id (SymbolKind.Constructor "Bool") (Some span)
            let tpat = mkTyped TBool span (TPatternNode.TPatConstructor resIdent)
            (tpat, Map.empty)

        | IdentPattern ident ->
            let isQualified = not (List.isEmpty ident.Qualifier)
            let lookupKey = string ident

            match resolveConstructorPattern tsCtx lookupKey 0 expectedTypeOpt ident.Name env with
            | Some (_, resType) ->
                let resIdent = tsCtx.CreateIdent ident (SymbolKind.Constructor lookupKey) (Some span)
                let tpat = mkTyped resType span (TPatternNode.TPatConstructor resIdent)
                (tpat, Map.empty)

            | None ->
                if isQualified then
                    let desc = sprintf "Unknown constructor or module reference in pattern: `%s`." lookupKey
                    let infos = [ suggestAlternativesIdentifiers env lookupKey ]
                    tsCtx.ReportError ErrorCode.UnboundIdentifierError desc infos null ident.Name

                    let errTy = tsCtx.FreshError()
                    let resIdent = tsCtx.CreateIdent ident SymbolKind.LocalVariable (Some span)
                    let tpat = mkTyped errTy span (TPatternNode.TPatVariable resIdent)
                    (tpat, Map.empty)

                elif Set.contains lookupKey env.DeclaredSymbols || env.InSymbolicScope then
                    let resIdent = tsCtx.CreateIdent ident SymbolKind.PureSymbol (Some span)
                    let tpat = mkTyped TSymbolic span (TPatternNode.TPatVariable resIdent)
                    (tpat, Map.empty)

                else
                    let tv = tsCtx.FreshVar lookupKey
                    Option.iter (fun exp -> Unification.unifyOrReport tsCtx tv exp pattWithPos) expectedTypeOpt
                    let resIdent = tsCtx.CreateIdent ident SymbolKind.LocalVariable (Some span)
                    let tpat = mkTyped tv span (TPatternNode.TPatVariable resIdent)
                    (tpat, Map.ofList [ (lookupKey, (resIdent, tv)) ])

        | TuplePattern patts ->
            let subResults =
                match expectedTypeOpt with
                | Some (TTuple expTs) when List.length expTs = List.length patts ->
                    List.map2 (fun exp p -> inferPattern tsCtx scope env (Some exp) p) expTs patts
                | _ ->
                    List.map (inferPattern tsCtx scope env None) patts

            let subTpats, subBindings = List.unzip subResults
            let tupleType = TTuple (List.map (fun (p: TPattern) -> p.Type) subTpats)
            let merged = mergeBindings tsCtx pattWithPos subBindings
            let tpat = mkTyped tupleType span (TPatternNode.TPatTuple subTpats)
            (tpat, merged)

        | ApplyPattern(phead, pargs) ->
            let headNameOpt =
                match removePos phead with
                | IdentPattern id when List.isEmpty id.Qualifier -> Some (removePos id.Name)
                | IdentPattern id -> Some (string id)
                | _ -> None

            let ctorResolvedOpt =
                match headNameOpt with
                | Some name -> resolveConstructorPattern tsCtx name (List.length pargs) expectedTypeOpt phead env
                | None -> None

            match ctorResolvedOpt with
            | Some (argTypes, resType) ->
                let subResults =
                    pargs
                    |> List.mapi (fun i p ->
                        let expArg = if i < List.length argTypes then Some argTypes.[i] else None
                        inferPattern tsCtx scope env expArg p)

                let subTpats, subBindings = List.unzip subResults
                for (tpat, expected) in Seq.zip subTpats argTypes do
                    Unification.unifyOrReport tsCtx tpat.Type expected phead

                let headIdent =
                    match removePos phead with
                    | IdentPattern id -> tsCtx.CreateIdent id (SymbolKind.Constructor headNameOpt.Value) (Some (spanOf phead))
                    | _ -> failwith "unreachable"

                let headTpat = mkTyped resType (spanOf phead) (TPatternNode.TPatConstructor headIdent)
                let merged = mergeBindings tsCtx pattWithPos subBindings
                let applyNode = { PatApplyHead = headTpat; PatApplyArguments = subTpats }
                let tpat = mkTyped resType span (TPatternNode.TPatApply applyNode)
                (tpat, merged)

            | None ->
                match headNameOpt with
                | Some name when env.ContainsSignature name && patternContext = RulePattern ->
                    let schemes = env.TryFindSignature(name).Value
                    let subResults = pargs |> List.map (inferPattern tsCtx scope env None)
                    let subTpats, subBindings = List.unzip subResults
                    let subTypes = List.map (fun (p: TPattern) -> p.Type) subTpats
                    let retType = Option.defaultValue (tsCtx.FreshVar (sprintf "%s_ret" name)) expectedTypeOpt

                    let _ = RuleLookup.selectCandidateBySignature tsCtx name schemes subTypes retType phead
                    let headIdent =
                        match removePos phead with
                        | IdentPattern id -> tsCtx.CreateIdent id (SymbolKind.RuleReference name) (Some (spanOf phead))
                        | _ -> failwith "unreachable"

                    let headTpat = mkTyped retType (spanOf phead) (TPatternNode.TPatConstructor headIdent)
                    let merged = mergeBindings tsCtx pattWithPos subBindings
                    let applyNode = { PatApplyHead = headTpat; PatApplyArguments = subTpats }
                    let tpat = mkTyped retType span (TPatternNode.TPatApply applyNode)
                    (tpat, merged)

                | _ when patternContext = ValuePattern || env.InSymbolicScope ->
                    let desc =
                        match headNameOpt with
                        | None -> "Invalid pattern in expression binding."
                        | Some name -> sprintf "Invalid pattern: '%s' is not a known constructor." name
                    let hint = "Only data constructors can be destructured in a non-rule pattern binding."

                    tsCtx.ReportError ErrorCode.InvalidPatternError desc [] hint pattWithPos
                    let errTy = tsCtx.FreshError()
                    let tpat = mkTyped errTy span TPatternNode.TPatWildcard
                    (tpat, Map.empty)

                // Higher order pattern (e.g. h[x] where h and x are variables).
                | _ ->
                    let headTpat, headBindings = inferPattern tsCtx scope env None phead
                    let subResults = pargs |> List.map (inferPattern tsCtx scope env None)
                    let subTpats, argBindings = List.unzip subResults
                    let argTypes = List.map (fun (p: TPattern) -> p.Type) subTpats
                    let retType = tsCtx.FreshVar "ret"

                    Unification.unifyOrReport tsCtx headTpat.Type (TArrow(argTypes, retType, Set.empty)) phead
                    let merged = mergeBindings tsCtx pattWithPos (headBindings :: argBindings)
                    let applyNode = { PatApplyHead = headTpat; PatApplyArguments = subTpats }
                    let tpat = mkTyped retType span (TPatternNode.TPatApply applyNode)
                    (tpat, merged)

        | RecordPattern fieldPatts ->
            let fieldResults =
                fieldPatts
                |> List.map (fun (nameWithPos, p) ->
                    let (tpat, b) = inferPattern tsCtx scope env None p
                    let binding = { BindingName = nameWithPos; BindingValue = tpat }
                    ((removePos nameWithPos, tpat.Type), binding, b))

            let fieldTypes = List.map (fun (ft, _, _) -> ft) fieldResults |> Map.ofList
            let tBindings = List.map (fun (_, tb, _) -> tb) fieldResults
            let allBindings = List.map (fun (_, _, b) -> b) fieldResults

            let restRow = tsCtx.FreshVar "rho"
            let recType = TRecord(fieldTypes, restRow)
            Option.iter (fun exp -> Unification.unifyOrReport tsCtx recType exp pattWithPos) expectedTypeOpt

            let merged = mergeBindings tsCtx pattWithPos allBindings
            let tpat = mkTyped recType span (TPatternNode.TPatRecord tBindings)
            (tpat, merged)

        | AsPattern(p1, p2) ->
            let tpat1, b1 = inferPattern tsCtx scope env None p1
            let tpat2, b2 = inferPattern tsCtx scope env None p2

            let desc = "Type mismatch in 'as' pattern"
            Unification.unifyOrReportWithDesc tsCtx tpat1.Type tpat2.Type desc pattWithPos

            let merged = mergeBindings tsCtx pattWithPos [ b1; b2 ]
            let asNode = { PatAsBase = tpat1; PatAsAlias = tpat2 }
            let tpat = mkTyped tpat1.Type span (TPatternNode.TPatAs asNode)
            (tpat, merged)

        | WhenPattern(innerPattern, condition) ->
            let tpatInner, bindings = inferPattern tsCtx scope env expectedTypeOpt innerPattern
            let extendedEnv = envWithBindings env bindings
            let condTExpr, _ = check tsCtx scope extendedEnv condition TBool

            let whenNode = { PatWhenBase = tpatInner; PatWhenGuard = condTExpr }
            let tpat = mkTyped tpatInner.Type span (TPatternNode.TPatWhen whenNode)
            (tpat, bindings)

        | TypedPattern(innerPatt, declType) ->
            let expectedType = resolveType tsCtx scope env declType
            let tpatInner, bindings = inferPattern tsCtx scope env (Some expectedType) innerPatt

            let desc = "Type annotation mismatch"
            Unification.unifyOrReportWithDesc tsCtx tpatInner.Type expectedType desc pattWithPos

            let typedNode =
                { PatTypedInner = tpatInner
                  PatTypedAnnotation = expectedType
                  PatTypedAnnotationSpan = spanOf declType }

            let tpat = mkTyped expectedType span (TPatternNode.TPatTyped typedNode)
            (tpat, bindings)

        | AlternativePattern alts ->
            match alts with
            | [] ->
                let tv = tsCtx.FreshVar "a"
                (mkTyped tv span TPatternNode.TPatWildcard, Map.empty) // this should not happen

            | first :: rest ->
                let tFirstLit, _ = inferLiteral tsCtx scope env first false
                let tFirst = tFirstLit.Type

                for alt in rest do
                    let tAltLit, _ = inferLiteral tsCtx scope env alt false
                    let desc = "Incompatible type in alternative pattern"
                    Unification.unifyOrReportWithDesc tsCtx tFirst tAltLit.Type desc alt

                let tLiterals = alts |> List.map (fun a -> fst (inferLiteral tsCtx scope env a false))
                let tpat = mkTyped tFirst span (TPatternNode.TPatAlternative tLiterals)
                (tpat, Map.empty)

        | ListPattern items ->
            let itemType = tsCtx.FreshVar "elem"
            let itemResults =
                items
                |> List.map (fun p ->
                    let (tpat, b) = inferPattern tsCtx scope env None p
                    let desc = "List element type mismatch"
                    Unification.unifyOrReportWithDesc tsCtx tpat.Type itemType desc p
                    tpat, b)

            let itemTpats, itemBindings = List.unzip itemResults
            let listType = TApp("List", [ itemType ])
            Option.iter (fun exp -> Unification.unifyOrReport tsCtx listType exp pattWithPos) expectedTypeOpt

            let merged = mergeBindings tsCtx pattWithPos itemBindings
            let tpat = mkTyped listType span (TPatternNode.TPatList itemTpats)
            (tpat, merged)

        | MixfixOperatorPattern(nameWithPos, args) ->
            expandAndInferMixfix
                tsCtx env pattWithPos nameWithPos args
                (mkTyped (tsCtx.FreshError()) span TPatternNode.TPatWildcard, Map.empty)
                (fun notation subst ->
                    let expandedPattern = Mixfix.exprToPatternWithSubst tsCtx pattWithPos subst notation.NotationIs
                    let (resTpat, bindings) = inferPattern tsCtx scope env expectedTypeOpt expandedPattern

                    // Enforce commutativity directly on the instantiated operand types of the pattern
                    if removePos notation.NotationCommutative = true && not env.InSymbolicScope then
                        match resTpat.Kind with
                        | TPatternNode.TPatApply { PatApplyArguments = [ arg0; arg1 ] } ->
                            if arg0.Type.Prune() <> TSymbolic && arg1.Type.Prune() <> TSymbolic then
                                let desc = sprintf "Commutative operator `%s` requires both operands to have the same type" (Mixfix.describeNotationPattern notation)
                                Unification.unifyOrReportWithDesc tsCtx arg0.Type arg1.Type desc args.[1]
                        | _ -> ()

                    let opIdent = tsCtx.CreateIdent { Qualifier = []; Name = nameWithPos } (SymbolKind.RuleReference (removePos nameWithPos)) (Some (spanOf nameWithPos))
                    let targs = args |> List.map (fun p -> fst (inferPattern tsCtx scope env None p))
                    let mixNode = { PatMixfixSymbol = opIdent; PatMixfixOperands = targs; PatMixfixExpanded = resTpat }
                    let tpat = mkTyped resTpat.Type span (TPatternNode.TPatMixfix mixNode)
                    (tpat, bindings))

    /// Type inference for literals. Returns an elaborated TLiteral and its effects.
    and private inferLiteral
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (litWithPos: LiteralWithPos)
        (allowStringInterpolation: bool)
        : TLiteral * Set<string>
        =
        let span = spanOf litWithPos
        match removePos litWithPos with
        | Literal.Integer i -> (mkTyped TInt span (TLiteralNode.TLitInteger i), Set.empty)
        | Literal.Float f   -> (mkTyped TFloat span (TLiteralNode.TLitFloat f), Set.empty)
        | Literal.Char c    -> (mkTyped TChar span (TLiteralNode.TLitChar c), Set.empty)
        | Literal.String s  -> (mkTyped TString span (TLiteralNode.TLitString s), Set.empty)
        | Literal.Unit      -> (mkTyped TUnit span TLiteralNode.TLitUnit, Set.empty)

        | Literal.InterpolatedString _ when not allowStringInterpolation ->
            let desc = "Interpolated strings cannot be used in pattern matching."
            let hint = "Use a literal string or match against variables."
            tsCtx.ReportError ErrorCode.InvalidPatternError desc [] hint litWithPos
            (mkTyped (tsCtx.FreshError()) span (TLiteralNode.TLitString ""), Set.empty)

        // this case should not happens as the parser won't allows it
        | Literal.InterpolatedString _ ->
            failwith "Interpolated strings are expressions and handled directly in inferExpression"

    /// Type inference for an elementary instruction / expression.
    and private inferStep
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (expression: ExpressionWithPos)
        : TExpression * Set<string> * Env
        =
        let inline inferLetVar (pattern: PatternWithPos) (boundExpr: ExpressionWithPos) (isMutable: bool) =
            let expectedOpt = tryExtractExpectedType tsCtx scope env pattern

            // If the pattern is type annoted, we check the expression against this type
            // else we infer the expression's type.

            let boundTExpr, effects =
                match expectedOpt with
                | None -> inferExpression tsCtx scope env boundExpr
                | Some expected -> check tsCtx scope env boundExpr expected

            let tpat, bindings = inferPattern ValuePattern tsCtx scope env (Some boundTExpr.Type) pattern

            let desc = sprintf "Pattern binding type mismatch"
            Unification.unifyOrReportWithDesc tsCtx boundTExpr.Type tpat.Type desc expression

            let mutable extendedEnv = envWithBindings env bindings

            if isMutable then
                extendedEnv <-
                    { extendedEnv with
                        Mutables = Map.fold (fun acc key _ ->
                            let value = { LexicalDepth = env.LambdaDepth; Mutated = ref false; PattDecl = pattern }
                            Map.add key value acc) env.Mutables bindings }

            let letNode =
                { LetPattern = tpat
                  LetValue = boundTExpr
                  LetMutability = if isMutable then Mutability.Mutable else Mutability.Immutable }

            let tExpr = mkTyped TUnit (spanOf expression) (TExpressionNode.TLet letNode)
            (tExpr, effects, extendedEnv)

        match removePos expression with
        | Let(pattern, boundExpr) -> inferLetVar pattern boundExpr false
        | Var(pattern, boundExpr) -> inferLetVar pattern boundExpr true
        | _ ->
            let tExpr, effects = inferExpression tsCtx scope env expression
            (tExpr, effects, env)

    /// Type inference for a block of elementary instructions / expressions.
    and private inferSequence
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (expressions: ExpressionWithPos list)
        : TExpression * Set<string>
        =

        let rec loop (currentEnv: Env) (exprs: ExpressionWithPos list) =
            match exprs with
            | [] ->
                let tEmpty = mkTyped TUnit Span.Empty (TExpressionNode.TLit TLiteralNode.TLitUnit)
                ([ tEmpty ], TUnit, Set.empty, currentEnv)

            | [ expr ] ->
                let tExpr, effects, finalEnv = inferStep tsCtx scope currentEnv expr

                match removePos expr with
                | (Var(patt, _) | Let(patt, _)) when not (removePos patt).IsWildcard ->
                    warningPointlessLetVar tsCtx expr
                | _ -> ()

                ([ tExpr ], tExpr.Type, effects, finalEnv)

            | expr :: rest ->
                let tExpr, effects1, nextEnv = inferStep tsCtx scope currentEnv expr

                match tExpr.Type with
                | LiyhType.TUnit | LiyhType.TCType CType.Void -> ()
                | _ ->
                    let desc = sprintf "The result of this expression is of type `%s`, but it is not used." (string tExpr.Type)
                    let hint = "You can use `ignore` to ignore the result or bind it to a `let` expression."
                    tsCtx.ReportWarning WarningCode.UnusedResultWarning desc [] hint expr

                let tRest, finalTy, effectsRest, finalEnv = loop nextEnv rest
                (tExpr :: tRest, finalTy, effects1 + effectsRest, finalEnv)

        let tExprs, finalTy, effects, finalEnv = loop env expressions
        checkScopeExit tsCtx env finalEnv

        let seqSpan =
            match tExprs with
            | [] -> Span.Empty
            | [ single ] -> single.Span
            | _ -> spanBetween (List.head tExprs).Span (List.last tExprs).Span

        let tseq = mkTyped finalTy seqSpan (TExpressionNode.TSequence tExprs)
        (tseq, effects)

    /// Type inference for expressions of the expression AST.
    and public inferExpression
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (expression: ExpressionWithPos)
        : TExpression * Set<string>
        =
        let span = spanOf expression

        match removePos expression with
        | Literal (Literal.InterpolatedString parts) ->
            let mutable totalEffs = Set.empty
            let mutable tparts = []

            for part in parts do
                match part with
                | Str s ->
                    tparts <- TInterpolatedPart.TStringPart s :: tparts

                | Interpolation e ->
                    let te, effs = inferExpression tsCtx scope env e
                    totalEffs <- totalEffs + effs
                    tparts <- TInterpolatedPart.TInterpolation te :: tparts

            let tnode = TExpressionNode.TInterpolatedString (List.rev tparts)
            (mkTyped TString span tnode, totalEffs)

        | Literal lit ->
            let tLit, effs = inferLiteral tsCtx scope env (withPosOf expression lit) true
            (mkTyped tLit.Type span (TExpressionNode.TLit tLit.Kind), effs)

        | Identifier (UnqualifiedIdentifier ("true" | "false" as boolStr)) ->
            let id = removePos expression |> function Identifier i -> i | _ -> failwith "unreachable"
            let resIdent = tsCtx.CreateIdent id (SymbolKind.Constructor "Bool") (Some span)
            (mkTyped TBool span (TExpressionNode.TIdentifier resIdent), Set.empty)

        | Identifier (QualifiedIdentifier([ lib ], fn)) when env.ContainsExtern (lib, fn) ->
            let id = removePos expression |> function Identifier i -> i | _ -> failwith "unreachable"
            let resIdent = tsCtx.CreateIdent id (SymbolKind.ExternFunction lib) (Some span)

            match env.TryFindExtern(lib, fn).Value with
            | [ edef ] ->
                let ty = Scheme.instantiate tsCtx edef.Scheme
                (mkTyped ty span (TExpressionNode.TIdentifier resIdent), Set.empty)

            | edefs ->
                let schemes = edefs |> List.map (fun d -> d.Scheme)
                RuleLookup.reportAmbiguity tsCtx (sprintf "%s.%s" lib fn) schemes expression
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

        | Identifier ident ->
            let lookupKey = string ident

            match Map.tryFind lookupKey env.Locals with
            | Some local ->
                local.Used := true
                (mkTyped local.Type span (TExpressionNode.TIdentifier local.Ident), Set.empty)

            | None ->
                match env.TryFindSignature lookupKey with
                | Some schemes ->
                    match RuleLookup.selectCandidateByExpectedType tsCtx lookupKey None schemes with
                    | Unique (ty, _, targetName) ->
                        let resIdent = tsCtx.CreateIdent ident (SymbolKind.RuleReference targetName) (Some span)
                        (mkTyped ty span (TExpressionNode.TIdentifier resIdent), Set.empty)

                    | Ambiguous candidates ->
                        let resIdent = tsCtx.CreateIdent ident (SymbolKind.RuleReference lookupKey) (Some span)
                        RuleLookup.reportAmbiguity tsCtx lookupKey candidates expression
                        (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

                    | NotFound ->
                        let resIdent = tsCtx.CreateIdent ident (SymbolKind.RuleReference lookupKey) (Some span)
                        (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

                | None ->
                    match env.TryFindConstructor lookupKey with
                    | Some cdefs ->
                        let typeName = (List.head cdefs).TypeName
                        let resIdent = tsCtx.CreateIdent ident (SymbolKind.Constructor typeName) (Some span)

                        match ConstructorLookup.selectCandidateByExpectedType tsCtx None cdefs with
                        | Unique ctorType ->
                            (mkTyped ctorType span (TExpressionNode.TIdentifier resIdent), Set.empty)

                        | Ambiguous candidates ->
                            ConstructorLookup.reportAmbiguity tsCtx lookupKey candidates expression
                            (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

                        | NotFound ->
                            (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

                    | None ->
                        if Set.contains lookupKey env.DeclaredSymbols || env.InSymbolicScope then
                            let resIdent = tsCtx.CreateIdent ident SymbolKind.PureSymbol (Some span)
                            (mkTyped TSymbolic span (TExpressionNode.TIdentifier resIdent), Set.empty)
                        else
                            let desc = sprintf "No identifier named '%s' was found in the current environment." lookupKey
                            let infos = [ suggestAlternativesIdentifiers env lookupKey ]
                            tsCtx.ReportError ErrorCode.UnboundIdentifierError desc infos null expression

                            let resIdent = tsCtx.CreateIdent ident SymbolKind.LocalVariable (Some span)
                            (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

        | Tuple elements ->
            let results = List.map (inferExpression tsCtx scope env) elements
            let texprs, effects = List.unzip results
            let ts = List.map (fun (e: TExpression) -> e.Type) texprs
            (mkTyped (TTuple ts) span (TExpressionNode.TTuple texprs), Set.unionMany effects)

        | List elements ->
            let elemType = tsCtx.FreshVar "elem"
            let mutable listEffs = Set.empty
            let mutable texprs = []

            for elem in elements do
                let texpr, effs = inferExpression tsCtx scope env elem
                listEffs <- listEffs + effs

                let desc = sprintf "List element type mismatch"
                Unification.unifyOrReportWithDesc tsCtx texpr.Type elemType desc elem
                texprs <- texpr :: texprs

            let texprs = List.rev texprs
            (mkTyped (TApp("List", [ elemType ])) span (TExpressionNode.TList texprs), listEffs)

        | Match m ->
            let toMatchTExpr, toMatchEffs = inferExpression tsCtx scope env m.ToMatch
            let resType = tsCtx.FreshVar "match_res"
            let mutable totalCasesEffs = Set.empty
            let mutable tcases = []

            for (patt, caseBody) in m.Cases do
                let tpat, bindings = inferPattern ValuePattern tsCtx scope env (Some toMatchTExpr.Type) patt

                let desc = sprintf "Pattern does not match expression type"
                Unification.unifyOrReportWithDesc tsCtx toMatchTExpr.Type tpat.Type desc patt

                let caseEnv = envWithBindings env bindings
                let bodyTExpr, bodyEffs = check tsCtx scope caseEnv caseBody resType

                totalCasesEffs <- totalCasesEffs + bodyEffs
                tcases <- { CasePattern = tpat; CaseBody = bodyTExpr } :: tcases

            let matchNode = { MatchScrutinee = toMatchTExpr; MatchCases = List.rev tcases }
            (mkTyped resType span (TExpressionNode.TMatch matchNode), toMatchEffs + totalCasesEffs)

        | Apply apply ->
            inferApply tsCtx scope env apply

        | IfThenElse ifte ->
            let condTExpr, effsCond = check tsCtx scope env ifte.Condition TBool

            let (thenTExpr, effsThen), thenType =
                // if there is not `else`-branch, this means that the `then`-branch must be a unit
                if Option.isSome ifte.ElseBranch then
                    let t, eff = inferExpression tsCtx scope env ifte.ThenBranch
                    (t, eff), t.Type
                else
                    let t, eff = check tsCtx scope env ifte.ThenBranch TUnit
                    (t, eff), TUnit

            let mutable effsElifs = Set.empty
            let mutable elifNodes = []

            for (cond, thenBr) in ifte.ElifBranches do
                let cTExpr, cEffs = check tsCtx scope env cond TBool
                let tTExpr, tEffs = check tsCtx scope env thenBr thenType
                effsElifs <- effsElifs + cEffs + tEffs
                elifNodes <- { ElifCondition = cTExpr; ElifBody = tTExpr } :: elifNodes

            let elseTExprOpt, effsElse =
                match ifte.ElseBranch with
                | Some elseBr ->
                    let t, effs = check tsCtx scope env elseBr thenType
                    Some t, effs
                | None -> None, Set.empty

            let ifNode =
                { IfCondition = condTExpr
                  IfThen = thenTExpr
                  IfElifs = List.rev elifNodes
                  IfElse = elseTExprOpt }

            let totalEffs = effsCond + effsThen + effsElifs + effsElse
            (mkTyped thenType span (TExpressionNode.TIfThenElse ifNode), totalEffs)

        | ExpressionSequence exprs ->
            inferSequence tsCtx scope env exprs

        | (Let _) | (Var _) ->
            let tExpr, effects, _ = inferStep tsCtx scope env expression

            // If the flow reaches this point, it is because a `let` expression is being used as the final value.
            warningPointlessLetVar tsCtx expression

            (tExpr, effects)

        | ReAssign(varName, valueExpr) ->
            let varSpan = spanOf varName
            match env.TryFindSignature (removePos varName) with
            | Some schemes ->
                match Map.tryFind (removePos varName) env.Mutables with
                | None ->
                    let desc = sprintf "Cannot reassign a non mutable variable: '%s'." (removePos varName)
                    let hint = sprintf "Declare '%s' as mutable using `var` instead of `let`." (removePos varName)
                    tsCtx.ReportError ErrorCode.ImmutableVariableMutationError desc [] hint varName

                    let valTExpr, _ = inferExpression tsCtx scope env valueExpr
                    let dummyIdent = tsCtx.CreateIdent { Qualifier = []; Name = varName } SymbolKind.LocalVariable (Some varSpan)
                    (mkTyped TUnit span (TExpressionNode.TReAssign { ReAssignTarget = dummyIdent; ReAssignValue = valTExpr }), Set.empty)

                | Some { LexicalDepth = declDepth } when declDepth < env.LambdaDepth ->
                    let desc = sprintf "Cannot reassign variable '%s' defined outside of the lambda." (removePos varName)
                    let hint = sprintf "Variables (declared with `var`) in Liyh are not references and therefore cannot extend beyond their lexical scope. Use an additional argument or an algebraic effect."
                    tsCtx.ReportError ErrorCode.CapturedVariableMutationError desc [] hint expression

                    let valTExpr, _ = inferExpression tsCtx scope env valueExpr
                    let dummyIdent = tsCtx.CreateIdent { Qualifier = []; Name = varName } SymbolKind.LocalVariable (Some varSpan)
                    (mkTyped TUnit span (TExpressionNode.TReAssign { ReAssignTarget = dummyIdent; ReAssignValue = valTExpr }), Set.empty)

                | Some { Mutated = mutated } ->
                    assert (List.length schemes = 1)

                    let scheme = List.head schemes
                    let expectedType = Scheme.instantiate tsCtx scheme
                    let valTExpr, effects = check tsCtx scope env valueExpr expectedType
                    mutated := true

                    let targetIdent =
                        match Map.tryFind (removePos varName) env.Locals with
                        | Some l -> l.Ident
                        | None -> tsCtx.CreateIdent { Qualifier = []; Name = varName } SymbolKind.LocalVariable (Some varSpan)

                    let reassignNode = { ReAssignTarget = targetIdent; ReAssignValue = valTExpr }
                    (mkTyped TUnit span (TExpressionNode.TReAssign reassignNode), effects)

            | None ->
                let desc = sprintf "No variable named '%s' was found in the current environment." (removePos varName)
                let infos = [ suggestAlternativesIdentifiers env (removePos varName) ]
                tsCtx.ReportError ErrorCode.UnboundIdentifierError desc infos null varName

                let valTExpr, _ = inferExpression tsCtx scope env valueExpr
                let dummyIdent = tsCtx.CreateIdent { Qualifier = []; Name = varName } SymbolKind.LocalVariable (Some varSpan)
                (mkTyped TUnit span (TExpressionNode.TReAssign { ReAssignTarget = dummyIdent; ReAssignValue = valTExpr }), Set.empty)

        | Lambda lambda ->
            let lambdaEnv = { env with LambdaDepth = env.LambdaDepth + 1 }
            let paramResults =
                lambda.Patterns
                |> List.map (inferPattern ValuePattern tsCtx scope lambdaEnv None)

            let tpats, bindingsList = List.unzip paramResults
            let mergedBindings = mergeBindings tsCtx expression bindingsList
            let bodyEnv = envWithBindings lambdaEnv mergedBindings

            let bodyTExpr, bodyEffs = inferExpression tsCtx scope bodyEnv lambda.Body
            let paramTypes = List.map (fun (p: TPattern) -> p.Type) tpats
            let arrowType = TArrow(paramTypes, bodyTExpr.Type, bodyEffs)

            let lambdaNode = { LambdaParameters = tpats; LambdaBody = bodyTExpr }
            (mkTyped arrowType span (TExpressionNode.TLambda lambdaNode), Set.empty)

        | While whileLoop ->
            let condTExpr, effsCond = check tsCtx scope env whileLoop.Predicate TBool
            let bodyTExpr, effsBody = check tsCtx scope env whileLoop.Body TUnit
            let whileNode = { WhileCondition = condTExpr; WhileBody = bodyTExpr }
            (mkTyped TUnit span (TExpressionNode.TWhile whileNode), effsCond + effsBody)

        | (ForTo forTo) | (ForDownTo forTo) ->
            let isDownTo = match removePos expression with ForDownTo _ -> true | _ -> false
            let startTExpr, startEffs = inferExpression tsCtx scope env forTo.InitialValue
            let endTExpr, endEffs = check tsCtx scope env forTo.EndValue startTExpr.Type

            let tpat, bindings = inferPattern ValuePattern tsCtx scope env (Some startTExpr.Type) forTo.Pattern

            let desc = sprintf "Loop pattern counter was expected to be of the type '%s'" (string startTExpr.Type)
            Unification.unifyOrReportWithDesc tsCtx tpat.Type startTExpr.Type desc forTo.Pattern

            let bodyEnv = envWithBindings env bindings
            let bodyTExpr, bodyEffs = check tsCtx scope bodyEnv forTo.Body TUnit

            let forToNode =
                { ForToPattern = tpat
                  ForToInitial = startTExpr
                  ForToLimit = endTExpr
                  ForToDirection = if isDownTo then ForDirection.Downwards else ForDirection.Upwards
                  ForToBody = bodyTExpr }

            (mkTyped TUnit span (TExpressionNode.TForTo forToNode), startEffs + endEffs + bodyEffs)

        | ForIn forIn ->
            let listTExpr, listEffs = inferExpression tsCtx scope env forIn.ListExpr
            let elemType = tsCtx.FreshVar "elem"

            let desc1 = sprintf "Expression in 'for..in' loop must be a list"
            Unification.unifyOrReportWithDesc tsCtx listTExpr.Type (TApp("List", [ elemType ])) desc1 forIn.ListExpr

            let tpat, bindings = inferPattern ValuePattern tsCtx scope env (Some elemType) forIn.Pattern
            let desc2 = sprintf "Loop pattern does not match list element type"
            Unification.unifyOrReportWithDesc tsCtx tpat.Type elemType desc2 forIn.Pattern

            let bodyEnv = envWithBindings env bindings
            let bodyTExpr, bodyEffs = check tsCtx scope bodyEnv forIn.Body TUnit

            let forInNode =
                { ForInPattern = tpat
                  ForInSource = listTExpr
                  ForInBody = bodyTExpr }

            (mkTyped TUnit span (TExpressionNode.TForIn forInNode), listEffs + bodyEffs)

        | CollectionAccess ca ->
            let lhsTExpr, lhsEffs = inferExpression tsCtx scope env ca.LHS

            let rec resolveAccess (currentType: LiyhType) (indices: ExpressionWithPos list) (accTIndices: TExpression list) (effects: Set<string>) =
                match indices with
                | [] -> (currentType, List.rev accTIndices, effects)
                | idxExpr :: rest ->
                    let idxTExpr, idxEffs = check tsCtx scope env idxExpr TInt
                    let newEffects = effects + idxEffs

                    match currentType.Prune() with
                    | TApp("List", [ elemT ]) ->
                        resolveAccess elemT rest (idxTExpr :: accTIndices) newEffects

                    | TString ->
                        resolveAccess TChar rest (idxTExpr :: accTIndices) newEffects

                    | TVar _ ->
                        let desc = "Cannot determine the collection type for indexing on an unconstrained type variable."
                        let hint = "Specify whether the collection is a `List` or a `String` with an explicit type annotation."
                        tsCtx.ReportError ErrorCode.NonIndexableTypeError desc [] hint ca.LHS
                        (tsCtx.FreshError (), List.rev (idxTExpr :: accTIndices), newEffects)

                    | other ->
                        let desc = sprintf "Cannot index into value of type `%s`." (string other)
                        let hint = "Indexing is only supported on lists and strings."
                        tsCtx.ReportError ErrorCode.NonIndexableTypeError desc [] hint ca.LHS
                        (tsCtx.FreshError (), List.rev (idxTExpr :: accTIndices), newEffects)

            let resTy, tindices, totalEffs = resolveAccess lhsTExpr.Type ca.Indices [] lhsEffs
            let caNode = { AccessTarget = lhsTExpr; AccessIndices = tindices }
            (mkTyped resTy span (TExpressionNode.TCollectionAccess caNode), totalEffs)

        | Range range ->
            let startTExpr, startEffs = inferExpression tsCtx scope env range.RangeStart
            let stopTExpr, stopEffs = check tsCtx scope env range.RangeStop startTExpr.Type
            let stepTExprOpt, stepEffs =
                match range.RangeStep with
                | Some step ->
                    let s, eff = check tsCtx scope env step startTExpr.Type
                    Some s, eff
                | None -> None, Set.empty

            let rangeNode = { RangeFrom = startTExpr; RangeBy = stepTExprOpt; RangeTo = stopTExpr }
            let totalEffs = startEffs + stopEffs + stepEffs
            (mkTyped (TApp("List", [ startTExpr.Type ])) span (TExpressionNode.TRange rangeNode), totalEffs)

        | ListComprehension lc ->
            let sourceTExpr, sourceEffs = inferExpression tsCtx scope env lc.ListExpr
            let elemType = tsCtx.FreshVar "elem"

            let desc1 = sprintf "Expression in list comprehension generator must be a list"
            Unification.unifyOrReportWithDesc tsCtx sourceTExpr.Type (TApp("List", [ elemType ])) desc1 lc.ListExpr

            let tpat, bindings = inferPattern ValuePattern tsCtx scope env (Some elemType) lc.Pattern
            let desc2 = sprintf "Comprehension pattern does not match list element type"
            Unification.unifyOrReportWithDesc tsCtx tpat.Type elemType desc2 lc.Pattern

            let comprehensionEnv = envWithBindings env bindings
            let guardTExprOpt, guardEffs =
                match lc.IfPred with
                | Some cond ->
                    let g, eff = check tsCtx scope comprehensionEnv cond TBool
                    Some g, eff
                | None -> None, Set.empty

            let yieldTExpr, yieldEffs = inferExpression tsCtx scope comprehensionEnv lc.ItemValue
            let lcNode =
                { CompItem = yieldTExpr
                  CompPattern = tpat
                  CompSource = sourceTExpr
                  CompFilter = guardTExprOpt }

            let totalEffs = sourceEffs + guardEffs + yieldEffs
            (mkTyped (TApp("List", [ yieldTExpr.Type ])) span (TExpressionNode.TListComprehension lcNode), totalEffs)

        | Record fields ->
            let tBindings, effects = inferFields tsCtx scope env fields
            let fieldMap = tBindings |> List.map (fun b -> removePos b.BindingName, b.BindingValue.Type) |> Map.ofList
            (mkTyped (TRecord(fieldMap, TEmptyRow)) span (TExpressionNode.TRecord tBindings), effects)

        | RecordUsing(baseExpr, updates) ->
            let baseTExpr, baseEffs = inferExpression tsCtx scope env baseExpr
            let updateBindings, updatedEffects = inferFields tsCtx scope env updates
            let updatedMap = updateBindings |> List.map (fun b -> removePos b.BindingName, b.BindingValue.Type) |> Map.ofList
            let knownFields, restRow = Unification.flattenRecord tsCtx [] Map.empty baseTExpr.Type

            match restRow.Prune() with
            | TEmptyRow ->
                let finalFields = Map.fold (fun acc k v -> Map.add k v acc) knownFields updatedMap
                let recType = TRecord(finalFields, TEmptyRow)
                let ruNode = { RecordBase = baseTExpr; RecordUpdates = updateBindings }
                (mkTyped recType span (TExpressionNode.TRecordUsing ruNode), baseEffs + updatedEffects)

            | TVar ({ contents = UnboundVar _ } as r) ->
                let freshRow = tsCtx.FreshVar "ρ"
                tsCtx.BindTypeVar r (LinkVar (TRecord(Map.empty, freshRow)))

                let finalFields = Map.fold (fun acc k v -> Map.add k v acc) knownFields updatedMap
                let recType = TRecord(finalFields, freshRow)
                let ruNode = { RecordBase = baseTExpr; RecordUpdates = updateBindings }
                (mkTyped recType span (TExpressionNode.TRecordUsing ruNode), baseEffs + updatedEffects)

            | other ->
                let desc = sprintf "Cannot update or extend non-record type `%s`." (string other)
                let infos = [ "The 'using' expression requires a record as its base target." ]
                tsCtx.ReportError ErrorCode.NonRecordTypeError desc infos null baseExpr

                let ruNode = { RecordBase = baseTExpr; RecordUpdates = updateBindings }
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TRecordUsing ruNode), baseEffs + updatedEffects)

        | MixfixOperator mixfix ->
            expandAndInferMixfix
                tsCtx env expression mixfix.Name mixfix.Arguments
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TLit TLiteralNode.TLitUnit), Set.empty)
                (fun notation subst ->
                    let expandedExpression = Mixfix.substExpression expression subst notation.NotationIs
                    let resTExpr, effs = inferExpression tsCtx scope env expandedExpression
                    let infer tsCtx scope env e =
                        let (te, eff) = inferExpression tsCtx scope env e
                        (te.Type, eff)

                    checkCommutative tsCtx scope env notation mixfix.Arguments infer

                    let opIdent = tsCtx.CreateIdent { Qualifier = []; Name = mixfix.Name } (SymbolKind.RuleReference (removePos mixfix.Name)) (Some (spanOf mixfix.Name))
                    let targs = mixfix.Arguments |> List.map (fun e -> fst (inferExpression tsCtx scope env e))
                    let mixNode = { MixfixSymbol = opIdent; MixfixOperands = targs; MixfixExpanded = resTExpr }
                    (mkTyped resTExpr.Type span (TExpressionNode.TMixfixOperator mixNode), effs))

        | UFCS ufcs ->

            // Unified Function Call Syntax (UFCS) uses the pipe operator: `x₀ |> f[x₁, ..., xₙ]` is
            // desugared as `f[x₀, x₁, ..., xₙ]` for the nodes `Apply`, `Lambda` and `Identifier`.

            let desugaredNode =
                match removePos ufcs.RHS with
                | Apply apply -> Some (Apply { apply with Arguments = ufcs.LHS :: apply.Arguments })
                | Lambda _ | Identifier _ -> Some (Apply { LHS = ufcs.RHS; Arguments = [ ufcs.LHS ] })
                | _ -> None

            match desugaredNode with
            | Some dNode ->
                let receiverTExpr, effsRecv = inferExpression tsCtx scope env ufcs.LHS
                let fullCallTExpr, effsCall = inferExpression tsCtx scope env (withPosOf expression dNode)
                match fullCallTExpr.Kind with
                | TExpressionNode.TApply tapply ->
                    let ufcsNode = { UfcsReceiver = receiverTExpr; UfcsCall = tapply }
                    (mkTyped fullCallTExpr.Type span (TExpressionNode.TUFCS ufcsNode), effsRecv + effsCall)
                | _ ->
                    (fullCallTExpr, effsRecv + effsCall)

            | None ->
                let desc = "RHS of UFCS (method call) must imply an application."
                tsCtx.ReportError ErrorCode.InvalidMethodCallError desc [] null ufcs.RHS
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TLit TLiteralNode.TLitUnit), Set.empty)

        | Substitution (substs, targetExpr) ->
            let replResults =
                substs
                |> List.map (fun (nameWp, expr) ->
                    let texpr, effs = inferExpression tsCtx scope env expr
                    let b = { BindingName = nameWp; BindingValue = texpr }
                    (removePos nameWp, b, effs))

            let totalReplEffs = replResults |> List.map (fun (_, _, effs) -> effs) |> Set.unionMany
            let extendedEnv =
                List.fold (fun (accEnv: Env) (name, b, _) ->
                    if accEnv.ContainsConstructor name then
                        accEnv
                    elif accEnv.ContainsSignature name then
                        let currentSigs = accEnv.LocalScope.Signatures
                        accEnv.WithLocalSignatures (Map.add name [ Scheme.empty b.BindingValue.Type ] currentSigs)
                    else
                        { accEnv with DeclaredSymbols = Set.add name accEnv.DeclaredSymbols }
                ) env replResults

            let targetTExpr, targetEffs = inferExpression tsCtx scope extendedEnv targetExpr
            let totalEffs = targetEffs + totalReplEffs

            if env.InSymbolicScope then
                let tBindings = replResults |> List.map (fun (_, b, _) -> b)
                let substNode = { SubstReplacements = tBindings; SubstTarget = targetTExpr }
                (mkTyped TSymbolic span (TExpressionNode.TSubstitution substNode), totalEffs)
            else
                let mutable i = -1
                for (name, b, _) in replResults do
                    i <- i + 1
                    let nameWp, _ = substs.[i]
                    let originTypeOpt =
                        match env.TryFindSignature name with
                        | Some [ scheme ] -> Some (Scheme.instantiate tsCtx scheme)
                        | _ ->
                            match env.TryFindConstructor name with
                            | Some [ cdef ] -> Some (cdef.ToType(tsCtx))
                            | _ -> None

                    match originTypeOpt with
                    | Some originType ->
                        let desc = sprintf "Target '%s' has type `%s`, but replacement has type `%s`" name (string (originType.Prune())) (string (b.BindingValue.Type.Prune()))
                        let hint = "Outside symbolic environments, substitution assumes that the type of the substituent is the same as that of the substituted term."
                        try
                            Unification.unify tsCtx originType b.BindingValue.Type
                        with
                        | UnifyException d ->
                            tsCtx.ReportError ErrorCode.TypeMismatchError (sprintf "%s: %s." desc d.Message) d.Informations hint nameWp

                    | None ->
                        let desc = sprintf "Cannot substitute unknown identifier or ambiguous constructor '%s'." name
                        tsCtx.ReportError ErrorCode.UnboundIdentifierError desc [] null nameWp

                let tBindings = replResults |> List.map (fun (_, b, _) -> b)
                let substNode = { SubstReplacements = tBindings; SubstTarget = targetTExpr }
                (mkTyped targetTExpr.Type span (TExpressionNode.TSubstitution substNode), totalEffs)

        | Expression.ParseError err ->
            (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TError err), Set.empty)

        | other ->
            // we still has to handle some non-trivial constructs.
            failwithf "unsupported AST node: %A" other

    /// Type inference for record fields.
    and public inferFields
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (fields: (WithPos<string> * ExpressionWithPos) list)
        : TBinding<TExpression> list * Set<string>
        =

        // We check for duplicate fields.
        let duplicatedGroups =
            fields
            |> List.map fst
            |> List.groupBy removePos
            |> List.filter (fun (_, instances) -> instances.Length > 1)

        for (name, instances) in duplicatedGroups do
            let desc = sprintf "Duplicate field '%s' in record definition." name
            let hint = sprintf "The field '%s' is already defined earlier in this record. Remove or rename this duplicate." name

            for duplicate in List.tail instances do
                tsCtx.ReportError ErrorCode.DuplicateRecordFields desc [] hint duplicate

        // We infer each field individualy: `list<(name * type) * effects>`
        let results =
            List.map (fun (nameWp, expr) ->
                let texpr, eff = inferExpression tsCtx scope env expr
                let b = { BindingName = nameWp; BindingValue = texpr }
                (b, eff)) fields

        // We get the map of `field : type`.
        let tBindings = List.map fst results

        // We collect each effects.
        let effects =
            results
            |> List.map snd
            |> Set.unionMany

        (tBindings, effects)

    /// Type inference for application.
    and private inferApply (tsCtx: TypecheckContext) (scope: TypeScope) (env: Env) (apply: Apply) : TExpression * Set<string> =
        let arity = List.length apply.Arguments
        let lhs = removePos apply.LHS

        let applySpan =
            match apply.Arguments with
            | [] -> spanOf apply.LHS
            | _ -> spanBetween (spanOf apply.LHS) (spanOf (List.last apply.Arguments))

        let inline reportCallError code desc candidates effects =
            tsCtx.ReportError code desc candidates null apply.LHS
            let dummyIdent = tsCtx.CreateIdent { Qualifier = []; Name = withPosOf apply.LHS "err" } SymbolKind.LocalVariable None
            let calleeTExpr = mkTyped (tsCtx.FreshError()) (spanOf apply.LHS) (TExpressionNode.TIdentifier dummyIdent)
            let tapply = { ApplyCallee = calleeTExpr; ApplyArguments = [] }
            (mkTyped (tsCtx.FreshError()) applySpan (TExpressionNode.TApply tapply), effects)


        // --- We begin by analysing the arguments --- //


        // Distinction between independent arguments (which can be inferred directly)
        // and dependent arguments (lambdas, unannotated overloaded identifiers).
        let independent, dependentArgs =
            List.indexed apply.Arguments
            |> List.partition (snd >> isContextDependent env >> not)

        let independentTyped =
            independent
            |> List.map (fun (i, arg) ->
                let t, effs = inferExpression tsCtx scope env arg
                (i, arg, t), effs)

        let independentArgs = List.map fst independentTyped
        let independentEffects = independentTyped |> List.map snd |> Set.unionMany

        // Type-diriged verification of dependent arguments based on parameter types.
        let checkDependentArgs (paramTypes: LiyhType list) =
            dependentArgs
            |> List.map (fun (i, arg) ->
                let t, effs = check tsCtx scope env arg (paramTypes.[i].Prune())
                (i, t), effs)


        // --- Evaluate and testing call candidates --- //


        // Final application of a candidate: unifies the independent arguments,
        // types the dependent arguments and aggregates all effects.
        let applyCandidate (c: CallCandidate) (baseEffects: Set<string>) : TExpression * Set<string> =

            let independentArgs =
                independentArgs
                |> List.map (fun (i, argExpr, actualTExpr) ->
                    let expected = c.ParamTypes.[i]

                    match actualTExpr.Kind, expected.Prune() with
                    | TExpressionNode.TLit (TLiteralNode.TLitInteger n), TFloat ->
                        let convertedNode = TExpressionNode.TLit (TLiteralNode.TLitFloat (float n))
                        let convertedTExpr = mkTyped TFloat actualTExpr.Span convertedNode
                        (i, convertedTExpr)

                    | _ ->
                        Unification.unifyOrReport tsCtx actualTExpr.Type expected argExpr
                        (i, actualTExpr)
                )

            let dependentResults = checkDependentArgs c.ParamTypes
            let dependentTExprs = List.map fst dependentResults
            let dependentEffects = dependentResults |> List.map snd |> Set.unionMany

            let allArgsIndexed =
                independentArgs @ dependentTExprs
                |> List.sortBy fst
                |> List.map snd

            let calleeTExpr = mkTyped (TArrow(c.ParamTypes, c.RetType, c.LatentEffects)) (spanOf apply.LHS) (TExpressionNode.TIdentifier c.Ident)
            let tapply = { ApplyCallee = calleeTExpr; ApplyArguments = allArgsIndexed }
            let totalEffs = baseEffects + independentEffects + dependentEffects + c.LatentEffects

            (mkTyped c.RetType applySpan (TExpressionNode.TApply tapply), totalEffs)

        /// Non-destructive testing (Probe) of a candidate to remove overloads without harming the environment.
        /// When `allowIntFloatLitCoercion = true`, this allows integer literals to match TFloat.
        let probeCandidate (allowIntFloatLitCoercion: bool) (c: CallCandidate) : bool =
            tsCtx.Probe (fun _ ->
                for (i, _, actualTExpr) in independentArgs do
                    match actualTExpr.Kind, c.ParamTypes.[i].Prune() with
                    | TExpressionNode.TLit (TLiteralNode.TLitInteger _), TFloat when allowIntFloatLitCoercion -> ()
                    | _ -> Unification.unify tsCtx actualTExpr.Type c.ParamTypes.[i]
                checkDependentArgs c.ParamTypes |> ignore)


        // --- Generating the candidates --- //


        let ruleCandidates (name: string) (schemes: Scheme list) : CallCandidate list =
            let id = removePos apply.LHS |> function Identifier i -> i | _ -> { Qualifier = []; Name = withPosOf apply.LHS name }
            schemes
            |> List.choose (fun scheme ->
                let instantiated = Scheme.instantiate tsCtx scheme
                let mangled = Scheme.getMangledName scheme
                let targetName = if System.String.IsNullOrEmpty mangled then name else mangled

                match instantiated.Prune() with
                | TArrow(ps, ret, effs) as arrow ->
                    let resIdent = tsCtx.CreateIdent id (SymbolKind.RuleReference targetName) (Some (spanOf apply.LHS))

                    Some { ParamTypes = ps
                           RetType = ret
                           LatentEffects = effs
                           Description = sprintf "%s%s" name (string arrow)
                           Ident = resIdent }

                | TVar({ contents = UnboundVar _ } as r) ->
                    let candArgs = List.init arity (fun i -> tsCtx.FreshVar (sprintf "%s_arg%d" name i))
                    let candRet = tsCtx.FreshVar (sprintf "%s_ret" name)

                    tsCtx.BindTypeVar r (LinkVar (TArrow(candArgs, candRet, Set.empty)))
                    let resIdent = tsCtx.CreateIdent id (SymbolKind.RuleReference targetName) (Some (spanOf apply.LHS))
                    Some { ParamTypes = candArgs
                           RetType = candRet
                           LatentEffects = Set.empty
                           Description = sprintf "%s%s." name (string (TArrow(candArgs, candRet, Set.empty)))
                           Ident = resIdent }

                | _ -> None)


        // --- Unified resolution of call overloads --- //


        let constructorCandidates (cdefs: ConstructorDef list) : CallCandidate list =
            let id = removePos apply.LHS |> function Identifier i -> i | _ -> failwith "unreachable"
            cdefs
            |> List.map (fun cdef ->
                let argTypes, resType = cdef.Instantiate(tsCtx)
                let typeStr =
                    if List.isEmpty argTypes then string resType
                    else sprintf "[%s] -> %s" (argTypes |> List.map string |> String.concat ", ") (string resType)

                let resIdent = tsCtx.CreateIdent id (SymbolKind.Constructor cdef.TypeName) (Some (spanOf apply.LHS))

                { ParamTypes = argTypes
                  RetType = resType
                  LatentEffects = Set.empty
                  Description = sprintf "%s.%s: %s" cdef.TypeName cdef.Name typeStr
                  Ident = resIdent })

        let resolveCandidates (calleeName: string) (candidates: CallCandidate list) : TExpression * Set<string> =

            let matchingArityCandidates =
                candidates
                |> List.filter (fun c -> List.length c.ParamTypes = arity)

            let knownArgTypes =
                List.init arity (fun idx ->
                    independentArgs
                    |> List.tryFind (fun (i, _, _) -> i = idx)
                    |> Option.map (fun (_, _, t) -> t.Type)
                    |> Option.defaultWith (fun _ -> tsCtx.FreshVar "arg"))

            // Type checking error result to continue the static analysis.
            let fallback =
                let dummyIdent = tsCtx.CreateIdent { Qualifier = []; Name = withPosOf apply.LHS calleeName } SymbolKind.LocalVariable None
                let calleeTExpr = mkTyped (tsCtx.FreshError()) (spanOf apply.LHS) (TExpressionNode.TIdentifier dummyIdent)
                let tapply = { ApplyCallee = calleeTExpr; ApplyArguments = [] }
                mkTyped (tsCtx.FreshError()) applySpan (TExpressionNode.TApply tapply)

            let hasUnconstrainedArgs =
                knownArgTypes
                |> List.exists (fun t -> t.Prune().IsTVar)

            let selectedCandidates =
                OverloadResolver.select
                    (probeCandidate false)
                    (fun c -> applyCandidate c Set.empty)
                    hasUnconstrainedArgs
                    matchingArityCandidates

            /// Filters the candidates by arity, then selects the unique one matching the context.
            /// On arity mismatch, ambiguity or no match, reports an error and returns fallback.
            /// When `allowIntFloatLitCoercion = true`, this allows integer literals to match TFloat.
            let inline resolve (allowIntFloatLitCoercion: bool) =
                OverloadResolver.resolve
                    tsCtx calleeName apply.LHS arity candidates
                    (fun c -> List.length c.ParamTypes)
                    (fun c -> c.Description)
                    (Some knownArgTypes)
                    (probeCandidate allowIntFloatLitCoercion)
                    (fun c -> applyCandidate c Set.empty)
                    (fallback, independentEffects)

            match selectedCandidates with
            // A single candidate meets the requirements perfectly and is selectionned.
            | Unique result -> result

            // Ambiguities are presents even without the Int to Float conversion of literals.
            | Ambiguous _ -> resolve false

            // No exact matches, we try again converting the Int literals to Float.
            | NotFound -> resolve true


        // --- Special cases: Direct lambda & Regular call --- //


        let inferDirectLambdaCall (lambda: Lambda) : TExpression * Set<string> =
            let known = Map.ofList [ for (i, _, t) in independentArgs -> i, t.Type ]

            let paramTypes =
                List.init arity (fun i ->
                    Map.tryFind i known
                    |> Option.defaultWith (fun _ -> tsCtx.FreshVar (sprintf "arg%d" i)))

            let lambdaEnv = { env with LambdaDepth = env.LambdaDepth + 1 }
            let clauseScope = TypeScope.create ()

            let paramResults =
                List.map2 (fun patt expectedP ->
                    let tpat, bindings = inferPattern ValuePattern tsCtx clauseScope lambdaEnv (Some expectedP) patt
                    Unification.unifyOrReport tsCtx tpat.Type expectedP patt
                    tpat, bindings) lambda.Patterns paramTypes

            let tpats, paramBindings = List.unzip paramResults
            let bodyEnv = envWithBindings lambdaEnv (mergeBindings tsCtx apply.LHS paramBindings)
            let bodyTExpr, bodyEffs = inferExpression tsCtx clauseScope bodyEnv lambda.Body

            let lambdaNode = { LambdaParameters = tpats; LambdaBody = bodyTExpr }
            let lambdaType = TArrow(paramTypes, bodyTExpr.Type, bodyEffs)
            let lambdaTExpr = mkTyped lambdaType (spanOf apply.LHS) (TExpressionNode.TLambda lambdaNode)

            let dependentResults = checkDependentArgs paramTypes
            let dependentTExprs = List.map fst dependentResults
            let dependentEffects = dependentResults |> List.map snd |> Set.unionMany

            let allArgs =
                (List.map (fun (i, _, t) -> i, t) independentArgs) @ dependentTExprs
                |> List.sortBy fst
                |> List.map snd

            let tapply = { ApplyCallee = lambdaTExpr; ApplyArguments = allArgs }
            let totalEffs = independentEffects + dependentEffects + bodyEffs
            (mkTyped bodyTExpr.Type applySpan (TExpressionNode.TApply tapply), totalEffs)

        let inferRegularCall () : TExpression * Set<string> =
            let funcTExpr, funcEffects = inferExpression tsCtx scope env apply.LHS

            match funcTExpr.Type.Prune() with
            | TSymbolic ->
                let depResults = dependentArgs |> List.map (fun (_, arg) -> inferExpression tsCtx scope env arg)
                let depTExprs = List.map fst depResults
                let depEffects = List.map snd depResults |> Set.unionMany

                let allArgs =
                    (List.map (fun (i, _, t) -> i, t) independentArgs) @ (List.zip (List.map fst dependentArgs) depTExprs)
                    |> List.sortBy fst
                    |> List.map snd

                let tapply = { ApplyCallee = funcTExpr; ApplyArguments = allArgs }
                (mkTyped TSymbolic applySpan (TExpressionNode.TApply tapply), funcEffects + independentEffects + depEffects)

            | TArrow(paramTypes, retType, latentEffs) ->
                if List.length paramTypes <> arity then
                    let desc = sprintf "Function expects %d argument(s), but received %d." (List.length paramTypes) arity
                    reportCallError ErrorCode.ArityMismatchError desc [] (funcEffects + latentEffs)
                else
                    for (i, argExpr, actualTExpr) in independentArgs do
                        Unification.unifyOrReport tsCtx actualTExpr.Type paramTypes.[i] argExpr

                    let depResults = checkDependentArgs paramTypes
                    let depTExprs = List.map fst depResults
                    let depEffects = depResults |> List.map snd |> Set.unionMany

                    let allArgs =
                        (List.map (fun (i, _, t) -> i, t) independentArgs) @ depTExprs
                        |> List.sortBy fst
                        |> List.map snd

                    let tapply = { ApplyCallee = funcTExpr; ApplyArguments = allArgs }
                    let totalEffs = funcEffects + independentEffects + depEffects + latentEffs
                    (mkTyped retType applySpan (TExpressionNode.TApply tapply), totalEffs)

            | TVar _ as tv ->
                let paramTypes = List.init arity (fun i -> tsCtx.FreshVar (sprintf "arg%d" i))
                let retType = tsCtx.FreshVar "ret"
                Unification.unifyOrReport tsCtx tv (TArrow(paramTypes, retType, Set.empty)) apply.LHS

                for (i, argExpr, actualTExpr) in independentArgs do
                    Unification.unifyOrReport tsCtx actualTExpr.Type paramTypes.[i] argExpr

                let depResults = checkDependentArgs paramTypes
                let depTExprs = List.map fst depResults
                let depEffects = depResults |> List.map snd |> Set.unionMany

                let allArgs =
                    (List.map (fun (i, _, t) -> i, t) independentArgs) @ depTExprs
                    |> List.sortBy fst
                    |> List.map snd

                let tapply = { ApplyCallee = funcTExpr; ApplyArguments = allArgs }
                (mkTyped retType applySpan (TExpressionNode.TApply tapply), funcEffects + independentEffects + depEffects)

            | other ->
                let desc = sprintf "Expression of type `%s` cannot be invoked as a function." (string other)
                reportCallError ErrorCode.NonCallableExpressionError desc [] funcEffects


        // --- Final Dispatch --- //


        let calleeInfo =
            match lhs with
            | Identifier (QualifiedIdentifier([ lib ], fn)) -> Some (lib, fn, env.TryFindExtern(lib, fn))
            | _ -> None

        let calleeNameOpt =
            match lhs with
            | Identifier id -> Some(string id)
            | _ -> None

        let lookupSig =
            calleeNameOpt
            |> Option.bind (fun n -> env.TryFindSignature n |> Option.map (fun v -> n, v))

        let lookupCtor =
            calleeNameOpt
            |> Option.bind (fun n -> env.TryFindConstructor n |> Option.map (fun v -> n, v))

        let isLocal =
            match lhs with
            | Identifier id -> Map.containsKey (string id) env.Locals
            | _ -> false

        match isLocal, lookupSig, lookupCtor, calleeInfo, lhs with
        // Local variables take precedence over any global rule or constructor.
        | true, _, _, _, _ ->
            inferRegularCall ()

        // Rule reference (takes precedence over constructors with the same name).
        | false, Some(name, schemes), _, _, _ when not (List.isEmpty (ruleCandidates name schemes)) ->
            resolveCandidates name (ruleCandidates name schemes)

        // Sum type constructors calls.
        | false, _, Some(name, cdefs), _, _ ->
            resolveCandidates name (constructorCandidates cdefs)

        // Extern functions.
        | false, _, _, Some(lib, fn, Some edefs), Identifier id ->
            let fullName = sprintf "%s.%s" lib fn
            resolveCandidates fullName (externCandidates tsCtx lib fn edefs id)

        // Direct call of a lambda.
        | false, _, _, _, Lambda lambda when List.length lambda.Patterns = arity ->
            inferDirectLambdaCall lambda

        // Higher-order expression, first-order variable or non-callable.
        | _ ->
            inferRegularCall ()

    /// Checks if the given expression is of the given expected type.
    and public check
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (expression: ExpressionWithPos)
        (expectedType: LiyhType)
        : TExpression * Set<string>
        =
        let span = spanOf expression

        match removePos expression, expectedType.Prune() with
        | _, TSymbolic ->
            let tExpr, effets = inferExpression tsCtx scope env expression
            (tExpr, effets)

        | Lambda lambda, TArrow(expectedParams, expectedRet, _)
            when List.length lambda.Patterns = List.length expectedParams ->

            let lambdaEnv = { env with LambdaDepth = env.LambdaDepth + 1 }
            let clauseScope = TypeScope.create()

            let paramResults =
                List.map2 (fun patt expectedP ->
                    let tpat, bindings = inferPattern ValuePattern tsCtx clauseScope lambdaEnv (Some expectedP) patt
                    Unification.unifyOrReport tsCtx tpat.Type expectedP patt
                    tpat, bindings
                ) lambda.Patterns expectedParams

            let tpats, paramBindings = List.unzip paramResults
            let merged = mergeBindings tsCtx expression paramBindings
            let bodyEnv = envWithBindings lambdaEnv merged
            let bodyTExpr, bodyEffs = check tsCtx clauseScope bodyEnv lambda.Body expectedRet

            let lambdaNode = { LambdaParameters = tpats; LambdaBody = bodyTExpr }
            let arrowType = TArrow(expectedParams, expectedRet, bodyEffs)
            (mkTyped arrowType span (TExpressionNode.TLambda lambdaNode), bodyEffs)

        | Identifier (QualifiedIdentifier([ lib ], fn)), expected when env.ContainsExtern(lib, fn) ->
            let fullName = sprintf "%s.%s" lib fn
            let id = removePos expression |> function Identifier i -> i | _ -> failwith "unreachable"
            let resIdent = tsCtx.CreateIdent id (SymbolKind.ExternFunction lib) (Some span)

            match env.TryFindExtern(lib, fn).Value with
            | [ edef ] ->
                let actual = Scheme.instantiate tsCtx edef.Scheme
                Unification.unifyOrReport tsCtx actual expected expression
                (mkTyped actual span (TExpressionNode.TIdentifier resIdent), Set.empty)

            | edefs ->
                let schemes = edefs |> List.map (fun d -> d.Scheme)
                RuleLookup.reportAmbiguity tsCtx fullName schemes expression
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

        // Local variables take precedence over any global definitions.
        | Identifier ident, expected
            when Map.containsKey (string ident) env.Locals ->
            
            let lookupKey = string ident
            let local = env.Locals.[lookupKey]

            local.Used := true

            Unification.unifyOrReport tsCtx local.Type expected expression
            (mkTyped local.Type span (TExpressionNode.TIdentifier local.Ident), Set.empty)

        // Type-based resolution for overloaded constructors.
        | Identifier ident, expected
            when not (env.ContainsSignature (string ident))
            && env.ContainsConstructor (string ident) ->

            let lookupKey = string ident
            let cdefs = (env.TryFindConstructor lookupKey).Value
            let typeName = (List.head cdefs).TypeName
            let resIdent = tsCtx.CreateIdent ident (SymbolKind.Constructor typeName) (Some span)

            match ConstructorLookup.selectCandidateByExpectedType tsCtx (Some expected) cdefs with
            | Unique ctorType ->
                Unification.unifyOrReport tsCtx ctorType expected expression
                (mkTyped ctorType span (TExpressionNode.TIdentifier resIdent), Set.empty)

            | Ambiguous candidates ->
                ConstructorLookup.reportAmbiguity tsCtx lookupKey candidates expression
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

            | NotFound ->
                let desc = sprintf "No overload of constructor '%s' matches the expected type: `%s`." lookupKey (string expected)
                tsCtx.ReportError ErrorCode.NoMatchingOverloadError desc [] null expression
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

        // Type-based resolution for overloaded rules.
        | Identifier ident, expected
            when env.ContainsSignature (string ident) ->

            let name = string ident
            let schemes = env.TryFindSignature(name).Value

            match RuleLookup.selectCandidateByExpectedType tsCtx name (Some expected) schemes with
            | Unique(actual, effects, targetName) ->
                let resIdent = tsCtx.CreateIdent ident (SymbolKind.RuleReference targetName) (Some span)
                Unification.unifyOrReport tsCtx actual expected expression
                (mkTyped actual span (TExpressionNode.TIdentifier resIdent), effects)

            | Ambiguous candidates ->
                let resIdent = tsCtx.CreateIdent ident (SymbolKind.RuleReference name) (Some span)
                RuleLookup.reportAmbiguity tsCtx name candidates expression
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

            | NotFound ->
                let resIdent = tsCtx.CreateIdent ident (SymbolKind.RuleReference name) (Some span)
                RuleLookup.reportNoMatching tsCtx name expected expression
                (mkTyped (tsCtx.FreshError()) span (TExpressionNode.TIdentifier resIdent), Set.empty)

        | _ ->
            let actualTExpr, effects = inferExpression tsCtx scope env expression

            match actualTExpr.Kind, expectedType.Prune() with
            | TExpressionNode.TLit (TLiteralNode.TLitInteger n), TFloat ->
                let convertedNode = TExpressionNode.TLit (TLiteralNode.TLitFloat (float n))
                let convertedTExpr = mkTyped TFloat actualTExpr.Span convertedNode
                (convertedTExpr, effects)

            | _ ->
                Unification.unifyOrReport tsCtx actualTExpr.Type expectedType expression
                (actualTExpr, effects)

