namespace Liyh.LyVM

module public BytecodeCompiler =
    open System
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open Liyh.Core.DecisionTree.DecisionTreeCompiler

    type private GlobalContext =
        { SymbolLabels: DispatchTable }

    type private CompilationContext =
        { Global: GlobalContext
          Env: Map<string, Reg>
          mutable PathCache: Map<Path, Reg>
          Arguments: Reg[]
          Strategy: Strategy
          ActiveContexts: string list }

    let private runtimeError (msg: string) =
        let sb = new Text.StringBuilder()
        sb.Append(Liyh.Utils.ColorTerm.colorize (Liyh.Utils.ColorTerm.Color.Basic "red") "Runtime Error: ") |> ignore
        sb.Append(msg) |> ignore
        sb.ToString()

    let rec private getPatternVariables (patt: CoreTerm) =
        match patt with
        | Variable v -> Set.singleton v
        | Symbol { Children = children } -> children |> List.map getPatternVariables |> Set.unionMany
        | CoreLet { Pattern = p } -> getPatternVariables p
        | _ -> Set.empty

    let rec private getFreeVariables (bound: Set<string>) (term: CoreTerm) =
        match term with
        | Variable v ->
            if bound.Contains v then Set.empty
            else Set.singleton v

        | Symbol { Children = children } ->
            children |> List.map (getFreeVariables bound) |> Set.unionMany

        | FunctionalApplication { Base = f; Arguments = args } ->
            let fFree = getFreeVariables bound f
            let argsFree = args |> List.map (getFreeVariables bound) |> Set.unionMany
            Set.union fFree argsFree

        | Closure { Parameters = ps; Value = body } ->
            let newBound = Set.union bound (Set.ofList ps)
            getFreeVariables newBound body

        | TermSequence terms ->
            let (free, _) =
                terms |> List.fold (fun (freeVars, boundVars) t ->
                    match t with
                    | CoreLet { Pattern = Variable v; Value = expr } ->
                        let exprFree = getFreeVariables boundVars expr
                        (Set.union freeVars exprFree, Set.add v boundVars)
                    | _ ->
                        let termFree = getFreeVariables boundVars t
                        (Set.union freeVars termFree, boundVars)
                ) (Set.empty, bound)
            free

        | Match { ToMatch = tm; Cases = cases } ->
            let tmFree = getFreeVariables bound tm
            let casesFree =
                cases |> List.map (fun (p, b) ->
                    let pVars = getPatternVariables p
                    let newBound = Set.union bound pVars
                    getFreeVariables newBound b
                ) |> Set.unionMany
            Set.union tmFree casesFree

        | CoreLet { Pattern = p; Value = v } ->
            getFreeVariables bound v

        | _ ->
            Set.empty

    /// Compiles a LiyhCore program into a LyVM's bytecode equivalent program.
    /// The `optimize: bool` parameter applys very basic optimization onto the bytecode if set to `true`.
    /// The effects of optimizations are not noticeable in practice, but they mainly include the elimination
    /// of dead code and basic peephole optimization. It is mainly useful for AOT compilation to reduce the size.
    let public compile (program: CoreProgram) (optimize: bool) =
        let builder = new ByteCodeBuilder()
        let mutable nextLabelId = 1000 // For aesthetic reasons, labels are generated from the index ‘1000’ in
                                       // order to have a continuous 4-digit representation. This is purely aesthetic.

        let freshLabel() =
            let l = nextLabelId
            nextLabelId <- nextLabelId + 1
            l

        let contextParents =
            program
            |> List.choose (function Context c -> Some (c.ContextName, c.Using) | _ -> None)
            |> Map.ofList

        // Retrieve all parents in order.
        let getContextDependencies (contextName: string) =

            let rec loop (contextName: string) (visited: Set<string>) =
                if Set.contains contextName visited then []
                else
                    match Map.tryFind contextName contextParents with
                    | Some parents ->
                        let newVisited = Set.add contextName visited
                        parents @ (parents |> List.collect (fun p -> loop p newVisited))
                    | None -> []

            loop contextName Set.empty

        let inline createContextualName (symbolName: string) (contextName: string) =
            symbolName + "$$" + contextName

        let inline uncreateContextualName (symbolName: string) (contextName: string) =
            symbolName.Replace("$$" + contextName, "")

        let allRules =
            program
            |> List.collect (fun def ->
                match def with
                | Rule r -> [ (r.LHS, r, None) ]
                | Context ctx ->
                    ctx.Content
                    |> List.choose (function Rule r -> Some r | _ -> None)
                    |> List.map (fun r ->
                        let newLhsSymbol =
                            match r.LHS with
                            | Symbol { Symbol = s } -> createContextualName s ctx.ContextName
                            | _ -> failwithf "Invalid LHS" // should not happen

                        let newLhs =
                            match r.LHS with
                            | Symbol s -> symbol newLhsSymbol s.Children
                            | _ -> r.LHS

                        let newRule = { r with LHS = newLhs }
                        (newLhs, newRule, Some ctx.ContextName)
                    )
                | _ -> []
            )

        let groupedRules =
            allRules
            |> List.groupBy (fun (lhs, _, _) ->
                match lhs with
                | Symbol { Symbol = symb; Children = children } -> (symb, List.length children)
                | _ -> failwith "Invalid LHS")

            |> List.map (fun ((name, arity), items) ->
                let (_, _, contextNameOpt) = List.head items
                let rules = List.map (fun (_, r, _) -> r) items

                let strategyWeight = function
                    | Outermost -> 2
                    | (Lazy | Strict | Memoize) -> 1
                    | Invalid -> 0

                let unifiedStrategy =
                    rules
                    |> List.map (_.Strategy >> Strategy.FromAST)
                    |> List.maxBy strategyWeight

                let sortedRules =
                    rules
                    |> List.sortByDescending (fun rule -> strategyWeight (Strategy.FromAST rule.Strategy))

                let ruleInfo =
                    { Name = name
                      Arity = arity
                      Strategy = unifiedStrategy
                      ContextName = contextNameOpt }

                (ruleInfo, sortedRules))

            |> Map.ofList

        let globalLabels =
            groupedRules
            |> Map.map (fun _ _ -> freshLabel ())

        let globalContext =
            { SymbolLabels = globalLabels }

        /// Resolves a symbol in the given compilation context, given its arity.
        /// The search is first performed in active contexts (with implicit qualification),
        /// then at the global level. Returns the resolved name and a boolean indicating whether the symbol
        /// is used as a captured value (zero arity with existing rule).
        let resolveSymbolForContext (context: CompilationContext) (symbolName: string) (arity: int) =
            let dp = context.Global.SymbolLabels

            let tryResolve name =
                // Exact Match (function call)
                if DispatchTable.contains (name, arity) dp then
                    Some (name, false)

                // Capture (symbol used as value, arity 0, but existing rule)
                elif arity = 0 && DispatchTable.containsByName name dp then

                    Some (name, true)

                // Symbolic data
                else
                    None

            let tryResolveInContext contextName =
                let resolvedName = createContextualName symbolName contextName
                tryResolve resolvedName

            // search in active contexts
            context.ActiveContexts
            |> List.tryPick tryResolveInContext
            // if no context claimed the symbol, try global
            |> Option.orElseWith (fun () -> tryResolve symbolName)
            // raw global data
            |> Option.defaultValue (symbolName, false)

        let rec compilePath (context: CompilationContext) (path: Path) =
            match context.PathCache.TryGetValue path with
            | true, reg -> reg
            | false, _ ->
                let reg =
                    match path with
                    | Root ->
                        failwith "Unresolved root path" // this may not happens

                    | Child(Root, idx) when not (context.PathCache.ContainsKey Root) ->
                        if idx >= 0 && idx < context.Arguments.Length then
                            context.Arguments.[idx]
                        else
                            failwithf "Index out of bounds: %d (arity %d)" idx context.Arguments.Length

                    | Child(parent, idx) ->
                        let parentReg = compilePath context parent

                        let effectiveParent =
                            match context.Strategy with
                            | Strategy.Lazy -> builder.Force(parentReg)
                            | _ -> parentReg

                        let childReg = builder.Deconstruct(effectiveParent, idx)

                        // Always force after deconstruction (because we don't know where the value comes from)
                        // except for outermost (which wants to keep the symbolic structures)
                        match context.Strategy with
                        | Strategy.Outermost -> childReg
                        | _ -> builder.Force(childReg)

                    | Field(parent, name) ->
                        let parentReg = compilePath context parent

                        let effectiveParent =
                            match context.Strategy with
                            | Strategy.Lazy -> builder.Force(parentReg)
                            | _ -> parentReg

                        let failLabel = freshLabel()
                        let successLabel = freshLabel()

                        let res = builder.GetField(effectiveParent, name, failLabel)

                        builder.Jump(successLabel)

                        builder.Scope(fun _ ->
                            builder.SetLabel(failLabel)
                            let msg = runtimeError $"Field '{name}' not found."
                            builder.Print(builder.LoadString msg)
                            builder.Halt(1)
                        )

                        builder.SetLabel(successLabel)

                        // Always force after deconstruction (because we don't know where the value comes from)
                        // except for outermost (which wants to keep the symbolic structures)
                        match context.Strategy with
                        | Strategy.Outermost -> res
                        | _ -> builder.Force(res)

                context.PathCache <- Map.add path reg context.PathCache
                reg

        // Utility function to convert a Boolean result (0/1) to Atom (true/false).
        let convertBoolToAtom (boolReg: Reg) =
            let resReg = builder.Alloc()
            let lblFalse = freshLabel()
            let lblEnd = freshLabel()

            builder.JumpFalse(boolReg, lblFalse)
            builder.Mov(resReg, builder.LoadAtom(Builtin.True))
            builder.Jump(lblEnd)

            builder.SetLabel(lblFalse)
            builder.Mov(resReg, builder.LoadAtom(Builtin.False))

            builder.SetLabel(lblEnd)
            resReg

        // Utility function to convert an Atom (true/false) to a Boolean (0/1).
        let convertAtomToBool (atomReg: Reg) =
            let resReg = builder.Alloc()
            let trueAtom = builder.LoadAtom(Builtin.True)
            let cmpRes = builder.Eq(atomReg, trueAtom)

            builder.Mov(resReg, cmpRes)
            resReg

        let rec compileTerm (context: CompilationContext) (isTail: bool) (term: CoreTerm) =
            match term with
            | Variable name ->
                match Map.tryFind name context.Env with
                | Some r -> r
                | None -> failwithf "Variable '%s unfound." name

            | Literal lit ->
                match lit with
                | Integer i -> builder.LoadInt (int i)  // bingint -> int64 -> int62 : be careful
                | Float f -> builder.LoadFloat f
                | String s -> builder.LoadString s
                | Char c -> builder.LoadChar c

            | RecordExtend { BaseRecord = base'; Extension = extensions } ->
                let extensionRegs =
                    extensions
                    |> List.collect (fun (name, expr) ->
                        let rVal = compileTerm context false expr
                        let rKey = builder.LoadAtom name
                        [ rKey; rVal ])

                match base' with
                | None -> builder.MkRecord(extensionRegs)
                | Some baseTerm ->
                    let rBase = compileTerm context false baseTerm
                    builder.ExtendRecord(rBase, extensionRegs)

            // --- Internals --- //

            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray Internals.arithmeticInternals) ->

                let rLeft = compileTermStrict context left
                let rRight = compileTermStrict context right

                match op with
                | Internals.Add -> builder.Add(rLeft, rRight)
                | Internals.Sub -> builder.Sub(rLeft, rRight)
                | Internals.Mul -> builder.Mul(rLeft, rRight)
                | Internals.Div -> builder.Div(rLeft, rRight)
                | Internals.Mod -> builder.Mod(rLeft, rRight)
                | _ -> failwith "??" // This may not happens

            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray Internals.booleanInternals) ->

                let rLeft = compileTermStrict context left
                let rRight = compileTermStrict context right

                let cmpRes =
                    match op with
                    | Internals.Eq  -> builder.Eq(rLeft, rRight)
                    | Internals.Neq -> builder.NotEqual(rLeft, rRight)
                    | Internals.Le  -> builder.Le(rLeft, rRight)
                    | Internals.Leq -> builder.Leq(rLeft, rRight)
                    | Internals.Ge  -> builder.Ge(rLeft, rRight)
                    | Internals.Geq -> builder.Geq(rLeft, rRight)
                    | _ -> failwith "??" // This may not happens

                convertBoolToAtom cmpRes

            | Internals.Internal_print(x) ->
                let xReg = compileTermStrict context x
                builder.Print(xReg)
                builder.Unit()

            | Internals.Internal_strcat(left, right) ->
                let rLeft = compileTermStrict context left
                let rRight = compileTermStrict context right
                builder.StrCat(rLeft, rRight)

            | Internals.Internal_ppshow(term) ->
                let r = compileTermStrict context term
                builder.PPShow(r)

            // --- Lazy and force "keywords" (testing for now) --- //

            | Symbol { Symbol = "lazy"; Children = [ body ] } ->
                compileThunk context isTail body

            | Symbol { Symbol = "force"; Children = [ expr ] } ->
                let thunkReg = compileTerm context isTail expr
                builder.Force(thunkReg)

            // ----------------------------------------------

            | Symbol { Symbol = name; Children = children } ->

                // Arguments are prepared differently depending on the main strategy associated
                // with the different rules using the symbol as LHS.
                let inline argsRegs (strategy: Strategy) =
                    match strategy with
                    | (Strict | Memoize) ->
                        // Strict: everything is evaluated before the call (default behavior).
                        List.map (compileTermStrict context) children

                    | Lazy ->
                        // Lazy: each argument is transformed into a Thunk.
                        List.map (compileThunk context false) children

                    | (Outermost | Invalid) ->
                        // Outermost: each argument is reified in symbolic data.
                        List.map (compileAsData context) children

                let arity = List.length children
                let (resolvedName, isCaptureWithinContext) = resolveSymbolForContext context name arity

                if isCaptureWithinContext then
                    // Not a function call, but an "applicable" value
                    builder.LoadAtom(resolvedName)
                else
                    match DispatchTable.tryFindByNameArity (resolvedName, List.length children) context.Global.SymbolLabels with
                    | Some (label, strategy) ->
                        if isTail then
                            builder.Tailcall(label, argsRegs strategy)
                            Reg 0 // dummy
                        else
                            builder.Call(label, argsRegs strategy)

                    | None ->
                        let args =
                            match context.Strategy with
                            | Outermost ->
                                // In the RHS of an outermost rule, we want to evaluate children
                                // to allow function calls rather that a simple substitution.
                                List.map (compileTerm context false) children
                            | _ ->
                                argsRegs context.Strategy

                        builder.AllocData(name, args)

            | FunctionalApplication { Base = b; Arguments = args } ->
                let bReg = compileTerm context false b
                let bStrict = builder.Force(bReg)
                let argsRegs = List.map (compileTerm context false) args

                builder.Apply(bStrict, argsRegs)

            | Closure { Parameters = parameters; Value = body } ->
                let boundInClosure = Set.ofList parameters
                let freeVars = getFreeVariables boundInClosure body

                let captures =
                    freeVars
                    |> Set.toList
                    |> List.choose (fun name ->
                        match Map.tryFind name context.Env with
                        | Some reg -> Some (name, reg)
                        | None -> None
                    )

                let captureRegs = List.map snd captures
                let labelBody = freshLabel ()
                let labelSkip = freshLabel ()

                builder.Jump(labelSkip)
                builder.Scope(fun () ->
                    builder.SetLabel(labelBody)

                    let (argRegs, patchIndex, savedMaxStack) = builder.DefineFunction(parameters.Length)
                    let argEnv = List.zip parameters argRegs |> Map.ofList

                    let captureEnv =
                        captures
                        |> List.mapi (fun i (name, _) -> name, builder.GetUpvalue(i))
                        |> Map.ofList

                    let bodyEnv =
                        Map.fold (fun acc k v -> Map.add k v acc) captureEnv argEnv

                    let bodyContext =
                        { context with
                            Env = bodyEnv
                            Arguments = Array.ofList argRegs
                            PathCache = Map.empty }

                    let resReg = compileTerm bodyContext true body
                    builder.Ret(resReg)
                    builder.FinalizeFunction(patchIndex, savedMaxStack)
                )

                builder.SetLabel(labelSkip)
                builder.Closure(labelBody, captureRegs)

            | TermSequence terms ->
                let rec compileSeq currentEnv remaining =
                    let seqContext = { context with Env = currentEnv }

                    match remaining with
                    | [] -> builder.Unit() // dummy
                    | [ x ] -> compileTerm seqContext isTail x
                    | x :: xs ->
                        match x with
                        | CoreLet { Pattern = Variable name; Value = value; IsVariable = isVar } ->
                            let valReg = compileTerm seqContext false value

                            let finalReg =
                                if isVar then
                                    let newReg = builder.Alloc()
                                    builder.Mov(newReg, valReg)
                                    newReg
                                else
                                    valReg

                            compileSeq (Map.add name finalReg currentEnv) xs

                        | CoreLet { Pattern = pattern; Value = value; IsVariable = isVar } ->
                            let valReg = compileTerm seqContext false value

                            let rootReg =
                                if isVar then
                                    let r = builder.Alloc()
                                    builder.Mov(r, valReg)
                                    r
                                else
                                    valReg

                            let occurence = { RuleIndex = 0; Pattern = pattern; Path = Root; Bindings = Map.empty; WhenClause = None }
                            let matrix = { Occurrences = [occurence]; RemainingPaths = [Root] }
                            let tree = DecisionTreeCompiler.compile matrix

                            let onMatch _ (leaftContext: CompilationContext) =
                                compileSeq leaftContext.Env xs

                            let onMismatch () =
                                let gotReg = builder.PPShow valReg
                                let expected = PrettyPrinter.prettyPrintExpr pattern

                                let msg1 = builder.LoadString $"The case was incomplete. Expected pattern `{expected}`, but got `"
                                let msg2 = builder.LoadString "` instead."

                                let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                                builder.RuntimeError finalMsg

                            builder.Scope(fun () ->
                                let letContext = { seqContext with PathCache = Map.ofList [(Root, rootReg)] }
                                compileTree letContext tree onMatch onMismatch
                            )

                        | _ ->
                            compileTerm seqContext false x |> ignore
                            compileSeq currentEnv xs

                compileSeq context.Env terms

            | UpdateVariable(name, value) ->
                let valReg = compileTerm context false value

                match Map.tryFind name context.Env with
                | None -> failwithf "Cannot compile the variable update '%s'." name
                | Some targetReg ->
                    builder.Mov(targetReg, valReg)
                    builder.Unit()

            | WhileLoop { Predicate = pred; Body = body } ->
                let startLabel = freshLabel()
                let endLabel = freshLabel()

                builder.SetLabel(startLabel)

                // Attempts to compile the predicate as a native comparison.
                let predBool =
                    match tryCompileIntrinsicBool context pred with
                    | Some rawReg -> rawReg
                    | None ->
                        let predReg = compileTerm context false pred
                        convertAtomToBool predReg

                builder.JumpFalse(predBool, endLabel)

                builder.Scope(fun () -> compileTerm context false body |> ignore)
                builder.Jump(startLabel)
                builder.SetLabel(endLabel)
                builder.Unit()

            | CoreLet { Pattern = Variable _; Value = value } ->
                compileTerm context false value |> ignore
                builder.Unit() // dummy

            | CoreLet { Pattern = pattern; Value = value; IsVariable = isVar } ->
                let valReg = compileTerm context false value

                let rootReg =
                    if isVar then
                        let r = builder.Alloc()
                        builder.Mov(r, valReg)
                        r
                    else
                        valReg

                let occurrence = { RuleIndex = 0; Pattern = pattern; Path = Root; Bindings = Map.empty; WhenClause = None }
                let matrix = { Occurrences = [occurrence]; RemainingPaths = [Root] }
                let tree = DecisionTreeCompiler.compile matrix

                let onMatch _ _ =
                    builder.Unit()

                let onMismatch () =
                    let gotReg = builder.PPShow valReg
                    let expected = PrettyPrinter.prettyPrintExpr pattern

                    let msg1 = builder.LoadString $"The case was incomplete. Expected pattern `{expected}`, but got `"
                    let msg2 = builder.LoadString "` instead."

                    let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                    builder.RuntimeError finalMsg

                builder.Scope(fun () ->
                    let letContext = { context with PathCache = Map.ofList [(Root, rootReg)] }
                    compileTree letContext tree onMatch onMismatch
                )

            | Match { ToMatch = toMatch; Cases = cases } ->
                let toMatchReg = compileTerm context false toMatch
                let occurrences =
                    cases |> List.mapi (fun i (patt, _) ->
                        { RuleIndex = i; Pattern = patt; Path = Root; Bindings = Map.empty; WhenClause = None })

                let matrix =
                    { Occurrences = occurrences
                      RemainingPaths = [Root] }

                let tree = DecisionTreeCompiler.compile matrix
                let bodies = cases |> List.map snd |> Array.ofList

                let onMatch ruleIndex leafContext =
                    compileTerm leafContext isTail bodies.[ruleIndex]

                let onMismatch () =
                    let gotReg = builder.PPShow toMatchReg
                    let allPatterns = cases |> List.map (fst >> PrettyPrinter.prettyPrintExpr)

                    let displayedPatterns, remaining =
                        if allPatterns.Length > 5 then
                            List.take 5 allPatterns, Some(allPatterns.Length - 5)
                        else
                            allPatterns, None

                    let patternsList =
                        displayedPatterns
                        |> List.map (sprintf " - `%s`")
                        |> String.concat "\n"

                    let extraMsg =
                        match remaining with
                        | Some n -> $"\n ... and {n} other pattern(s)"
                        | None -> ""

                    let msg1 = builder.LoadString $"The case was incomplete. Expected one of the following patterns:\n{patternsList}{extraMsg}\n\nbut got `"
                    let msg2 = builder.LoadString "` instead."

                    let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                    builder.RuntimeError finalMsg

                builder.Scope(fun () ->
                    let matchContext = { context with PathCache = Map.ofList [(Root, toMatchReg)] }
                    compileTree matchContext tree onMatch onMismatch
                )

            | Substitution { Env = subEnv; InExpr = inExpr } ->
                let astReg = compileTermStrict context inExpr

                let finalReg =
                    subEnv
                    |> List.fold (fun currentTreeReg (sym, valExpr) ->
                        let valReg = compileTermStrict context valExpr
                        let atomReg = builder.LoadAtom(sym.Symbol)
                        let nextReg = builder.Alloc()

                        builder.Subst(nextReg, currentTreeReg, atomReg, valReg)
                        nextReg
                    ) astReg

                finalReg

            | UsingContext { Context = contextName; Expr = expr } ->
                let contextDependencies = getContextDependencies contextName
                let addedContextDependencies = contextName :: contextDependencies @ context.ActiveContexts

                let newCompilationContext = { context with ActiveContexts = addedContextDependencies }
                compileTerm newCompilationContext isTail expr

            | _ -> failwithf "TODO: %s" (PrettyPrinter.prettyPrintExpr term)

        // Compiles an expression as a thunk (for the Lazy strategy)
        and compileThunk (context: CompilationContext) (isTail: bool) (body: CoreTerm) =

            // Capture free variables (such as a zero-arity closure).
            let captures =
                getFreeVariables Set.empty body
                |> Set.toList
                |> List.choose (fun name ->
                    match Map.tryFind name context.Env with
                    | Some reg -> Some (name, reg)
                    | None -> None
                )

            let captureRegs = List.map snd captures
            let labelBody = freshLabel ()
            let labelSkip = freshLabel ()

            // Generation of the thunk body (like a zero-arity closure).
            builder.Jump(labelSkip)
            builder.Scope(fun () ->
                builder.SetLabel(labelBody)
                let (_, patchIndex, savedMaxStack) = builder.DefineFunction(0)

                let bodyEnv =
                    captures
                    |> List.mapi (fun i (name, _) -> name, builder.GetUpvalue(i))
                    |> Map.ofList

                let bodyContext =
                    { context with
                        Env = bodyEnv
                        Arguments = Array.empty
                        PathCache = Map.empty }

                let resReg = compileTerm bodyContext isTail body
                builder.Ret(resReg) // will trigger the update of the thunk (memoization)
                builder.FinalizeFunction(patchIndex, savedMaxStack)
            )

            builder.SetLabel(labelSkip)
            builder.Delay(labelBody, captureRegs)

        // Compiles an expression as Data / AST (for the Outermost strategy)
        and compileAsData (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = name; Children = children } ->
                let arity = List.length children
                let (resolvedName, isCaptureWithinContext) = resolveSymbolForContext context name arity

                if isCaptureWithinContext then
                    // Not a function call, but an "applicable" value
                    builder.LoadAtom(resolvedName)
                else
                    // A symbolic data structure
                    let childRegs = List.map (compileAsData context) children
                    builder.AllocData(resolvedName, childRegs)

            | RecordExtend { BaseRecord = base'; Extension = extensions } ->
                // We compile fields as data recursively and allocate a symbolic object for it.
                let extensionRegs =
                    extensions
                    |> List.collect (fun (name, expr) ->
                        let rVal = compileAsData context expr
                        let rKey = builder.LoadAtom name
                        [ rKey; rVal ])

                match base' with
                | None -> builder.MkRecord(extensionRegs)
                | Some baseTerm ->
                    let rBase = compileAsData context baseTerm
                    builder.ExtendRecord(rBase, extensionRegs)

            | other ->
                // The rest is not compilable as a symbolic data.
                compileTerm context false other

        and compileTermStrict (context: CompilationContext) (term: CoreTerm) =
            let reg = compileTerm context false term
            builder.Force(reg) // This allows strict code to consume the result of lazy code.

        and tryCompileIntrinsicBool (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray Internals.booleanInternals) ->

                let rLeft = compileTermStrict context left
                let rRight = compileTermStrict context right

                let rawResult =
                    match op with
                    | Internals.Eq  -> builder.Eq(rLeft, rRight)
                    | Internals.Neq -> builder.NotEqual(rLeft, rRight)
                    | Internals.Le  -> builder.Le(rLeft, rRight)
                    | Internals.Leq -> builder.Leq(rLeft, rRight)
                    | Internals.Ge  -> builder.Ge(rLeft, rRight)
                    | Internals.Geq -> builder.Geq(rLeft, rRight)
                    | _ -> failwith "??" // should not happen

                Some rawResult
            | _ -> None

        and compileTree
            (ctx: CompilationContext)
            (tree: DecisionTree)
            (onMatch: int -> CompilationContext -> Reg)
            (fallback: unit -> Reg)
            : Reg =

            let inline branchContext (ctx': CompilationContext) =
                { ctx' with PathCache = ctx'.PathCache }

            match tree with
            | Fail -> fallback()

            | Leaf(ruleIndex, bindings) ->
                let newEnv =
                    bindings
                    |> Map.fold (fun env varName path ->
                        let reg = compilePath ctx path
                        Map.add varName reg env
                    ) ctx.Env
                let leafCtx = { ctx with Env = newEnv }
                onMatch ruleIndex leafCtx

            | Switch(path, cases, defaultCase) ->
                let pathReg = compilePath ctx path
                let endLabel = freshLabel()

                let shouldForce =
                    match ctx.Strategy with
                    | Strategy.Lazy -> true
                    | Strategy.Outermost ->
                        let involvesFunctionMatching =
                            cases
                            |> Map.exists (fun (name, arity) _ ->
                                DispatchTable.contains (name, arity) ctx.Global.SymbolLabels
                            )

                        not involvesFunctionMatching

                    | _ -> false

                let testReg =
                    if shouldForce then builder.Force(pathReg)
                    else pathReg

                builder.Scope(fun () ->
                    let phiReg = builder.Alloc()

                    for KeyValue((tag, _), subTree) in cases do
                        let nextLbl = freshLabel()
                        builder.TestTag(testReg, tag, nextLbl)
                        let ctxBranch = branchContext ctx
                        let res = compileTree ctxBranch subTree onMatch fallback
                        builder.Mov(phiReg, res)
                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)

                    match defaultCase with
                    | Some def ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault def onMatch fallback
                        builder.Mov(phiReg, res)
                    | None ->
                        let res = fallback()
                        builder.Mov(phiReg, res)

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | SwitchLiteral(path, cases, defaultCase) ->
                let pathReg = compilePath ctx path
                let endLabel = freshLabel()

                let testReg =
                    match ctx.Strategy with
                    | (Strategy.Lazy) -> builder.Force(pathReg)
                    | _ -> pathReg

                builder.Scope(fun () ->
                    let phiReg = builder.Alloc()

                    for KeyValue(lit, subTree) in cases do
                        let nextLbl = freshLabel()
                        let litReg =
                            match lit with
                            | Integer i -> builder.LoadInt(int i)
                            | Float f -> builder.LoadFloat(f)
                            | String s -> builder.LoadString(s)
                            | Char c -> builder.LoadChar(c)

                        let eq = builder.Eq(testReg, litReg)
                        builder.JumpFalse(eq, nextLbl)

                        let ctxBranch = branchContext ctx
                        let res = compileTree ctxBranch subTree onMatch fallback
                        builder.Mov(phiReg, res)
                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)

                    match defaultCase with
                    | Some def ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault def onMatch fallback
                        builder.Mov(phiReg, res)

                    | None ->
                        let res = fallback()
                        builder.Mov(phiReg, res)

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | WhenGuard(guardExpr, bindings, successTree, failureTreeOpt) ->
                builder.Scope(fun () ->
                    let guardEnv =
                        bindings |> Map.fold (fun env varName path ->
                            Map.add varName (compilePath ctx path) env
                        ) ctx.Env
                    let guardCtx = { ctx with Env = guardEnv }

                    let guardReg = compileTerm guardCtx false guardExpr
                    let trueAtom = builder.LoadAtom(Builtin.True)
                    let isTrue = builder.Eq(guardReg, trueAtom)

                    let failLabel = freshLabel()
                    let endLabel = freshLabel()
                    let phiReg = builder.Alloc()

                    builder.JumpFalse(isTrue, failLabel)

                    let ctxBranch = branchContext ctx
                    let res = compileTree ctxBranch successTree onMatch fallback
                    builder.Mov(phiReg, res)
                    builder.Jump(endLabel)

                    builder.SetLabel(failLabel)
                    match failureTreeOpt with
                    | Some failTree ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault failTree onMatch fallback
                        builder.Mov(phiReg, res)

                    | None ->
                        let res = fallback()
                        builder.Mov(phiReg, res)

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | TypeCheck(path, cases, defaultCase) ->
                let pathReg = compilePath ctx path
                let endLabel = freshLabel()
                let phiReg = builder.Alloc()

                let testReg =
                    match ctx.Strategy with
                    | (Strategy.Outermost | Strategy.Lazy) -> builder.Force(pathReg)
                    | _ -> pathReg

                builder.Scope(fun () ->
                    for KeyValue(t, subTree) in cases do
                        let nextLbl = freshLabel()

                        match t with
                        | TRecord -> builder.TestRecord(testReg, nextLbl)
                        | _ -> builder.Jump(nextLbl)

                        let ctxBranch = branchContext ctx
                        let res = compileTree ctxBranch subTree onMatch fallback
                        builder.Mov(phiReg, res)
                        builder.Jump(endLabel)

                        builder.SetLabel(nextLbl)

                    match defaultCase with
                    | Some d ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault d onMatch fallback
                        builder.Mov(phiReg, res)

                    | None ->
                        let res = fallback()
                        builder.Mov(phiReg, res)

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | other -> failwithf "TODO: %A" other

        let entryPointLabel =
            match DispatchTable.tryFindByNameArity ("main", 0) globalLabels with
            | Some (label, _) -> label
            | None ->
                match DispatchTable.tryFindByNameArity ("main", 1) globalLabels with
                | Some (label, _) -> label
                | None -> failwith "No entry point (main) found."

        let compiledFunctions =
            DispatchTable.count globalLabels

        let comments = [
            ""
            " Bytecode generated by Liyh's Compiler (version 0.1.1)."
            $" Compiled on: {DateTime.Now}."
            " This textual representation is for information only and is not usable as such."
            ""
            ""
            " You can search for a function with CTRL+F with `name/arity`."
            ""
            $" The entry point is `main` at label L{entryPointLabel}."
            $" There are {compiledFunctions} compiled functions."
            ""
        ]

        let maxLength =
            comments
            |> List.map String.length
            |> List.max

        comments 
        |> List.iter (fun comment -> 
            let paddedComment = comment.PadRight(maxLength)
            builder.Comment($"{paddedComment}  ;"))

        for KeyValue({ Name = symbolName; Arity = arity; Strategy = strategy } as key, rules) in groupedRules do
            let label = globalLabels.[key]
            builder.CommentNewLine($"--- {symbolName}/{arity} ---\n")
            builder.SetLabel(label)

            let (argRegsList, patchIndex, savedMaxStack) = builder.DefineFunction(arity)
            let argRegs = Array.ofList argRegsList
            let rulesArray = Array.ofList rules
            let tree = DecisionTreeCompiler.compileRules rulesArray

            let activeContexts =
                match key.ContextName with
                | Some contextName -> contextName :: getContextDependencies contextName
                | None -> []

            let context =
                { Global = globalContext
                  Env = Map.empty
                  PathCache = Map.empty
                  Arguments = argRegs
                  Strategy = strategy
                  ActiveContexts = activeContexts }

            let fallback () =

                // The `tryFallbackToGlobal` mechanism prevents a local context from completely shadowing
                // global functions that share the same name but do not satisfy the current context's rules.
                // This ensures the implementation of the "overlay" resolution semantics: local definitions
                // take precedence, followed by global ones, and finally symbolic data constructions.

                let originalName =
                    match key.ContextName with
                    | Some contextName -> uncreateContextualName symbolName contextName
                    | None -> symbolName

                let tryFallbackToGlobal () =
                    if DispatchTable.contains (originalName, arity) globalLabels then
                        let globalLabel, _ = DispatchTable.get (originalName, arity) globalLabels
                        if globalLabel = label then
                            false // AllocData (don't loop forever)
                        else
                            builder.Tailcall(globalLabel, List.ofArray argRegs)
                            true
                    else
                        false // AllocData

                match strategy with
                | Outermost ->

                    // In case of fallback, we force the arguments because nothing else matched
                    // (that's why the control stream goes there).

                    let newArgs = Array.map builder.Force argRegs

                    let labelRetry = freshLabel()
                    let labelStable = freshLabel()

                    // Check if an argument changed after this FORCE.
                    // If `oldReg != newReg` it means that a reduction has taken place.
                    // If there is a difference, immediately jump to the RETRY label.

                    for (oldReg, newReg) in Array.zip argRegs newArgs do
                        let isDifferent = builder.NotEqual(oldReg, newReg)
                        builder.JumpTrue(isDifferent, labelRetry)

                    builder.Jump(labelStable)

                    // RETRY label: at least one argument has changed, so we restart the
                    // function (the root) with the new reduced arguments.
                    builder.SetLabel(labelRetry)
                    builder.Tailcall(label, List.ofArray newArgs)

                    // STABLE label: a normal form has been reached (or blocked at the root),
                    // so we reconstruct the symbolic term.
                    builder.SetLabel(labelStable)
                    if tryFallbackToGlobal() then
                        // already jumped in `tryFallbackToGlobal`
                        builder.Alloc() // dummy
                    else
                        builder.AllocData(originalName, List.ofArray newArgs)

                | _ ->
                    if tryFallbackToGlobal() then
                        // already jumped in `tryFallbackToGlobal`
                        builder.Alloc() // dummy
                    else
                        builder.AllocData(originalName, List.ofArray argRegs)

            let onMatch ruleIndex leafContext =
                let rule = rulesArray.[ruleIndex]
                let localStrategy = Strategy.FromAST rule.Strategy

                match localStrategy with
                | Strategy.Invalid ->
                    let errorValReg = compileTerm leafContext false rule.RHS
                    let errorStrReg = builder.PPShow(errorValReg)
                    let prefixReg = builder.LoadString "Invalid rule matched: "
                    let fullMsgReg = builder.StrCat(prefixReg, errorStrReg)

                    builder.Print(fullMsgReg)
                    builder.Halt(1)
                    builder.Alloc() // dummy

                | _ ->
                    compileTerm leafContext (symbolName <> "main") rule.RHS

            let optimizedTree =
                match tree with
                | Switch(Root, cases, _) ->
                    match Map.tryFind (symbolName, arity) cases with
                    | Some t -> t
                    | None -> tree
                | _ -> tree

            let result = compileTree context optimizedTree onMatch fallback

            if symbolName = "main" then
                // builder.Print(result)
                builder.Halt()
            else
                builder.Ret(result)

            builder.FinalizeFunction(patchIndex, savedMaxStack)

        let dispatchTable = globalLabels
        builder.Compile(entryPointLabel, dispatchTable)

