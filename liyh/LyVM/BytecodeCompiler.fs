namespace Liyh.LyVM

//
// The bytecode compiler takes Liyh's LiyhCore representation and compiles it into bytecode instructions
// for the Liyh VM (LyVM - RCL). The compiler produces bytecode that is not optimized, except where
// optimization opportunities are straightforward.
//

module public BytecodeCompiler =
    open System
    open System.Collections.Generic
    open Liyh.Utils
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open Liyh.Core.DecisionTree.DecisionTreeCompiler

    type private GlobalContext =
        { SymbolLabels: DispatchTable }         // dispatch table (RuleInfo : LabelIndex)

    type private CompilationContext =
        { Global: GlobalContext                 // the static global context of compilation
          Env: Map<string, Reg>                 // the current binding variable environment
          mutable PathCache: Map<Path, Reg>     // cache for decision tree's path
          Arguments: Reg[]                      // arguments for closures
          Strategy: Strategy                    // the current evaluation strategy
          ActiveContexts: string list           // the stack of active Liyh's contexts
          EvaluatedRegs: HashSet<int> }         // keep track of the "FORCED" registers


    // --- Helper modules --- //


    module private BindingVariables =

        /// Gets the binding variables from a pattern (a CoreTerm used as a pattern).
        let rec private getPatternBindingVariables (patt: CoreTerm) =
            match patt with
            | Variable v -> Set.singleton v
            | Symbol { Children = children } -> children |> List.map getPatternBindingVariables |> Set.unionMany
            | CoreLet { Pattern = p } -> getPatternBindingVariables p
            | _ -> Set.empty

        /// Gets the binding variables from the given term, with a set of already existing bindings.
        let rec public getBindingVariables (bound: Set<string>) (term: CoreTerm) =
            match term with
            | Variable v ->
                if bound.Contains v
                then Set.empty else Set.singleton v

            | Symbol { Children = children } ->
                children
                |> List.map (getBindingVariables bound)
                |> Set.unionMany

            | FunctionalApplication { Base = f; Arguments = args } ->
                let fFree = getBindingVariables bound f
                let argsFree =
                    args
                    |> List.map (getBindingVariables bound)
                    |> Set.unionMany

                Set.union fFree argsFree

            | Closure { Parameters = ps; Value = body } ->
                let newBound = Set.union bound (Set.ofList ps)
                getBindingVariables newBound body

            | TermSequence terms ->
                let (free, _) =
                    terms |> List.fold (fun (freeVars, boundVars) t ->
                        match t with
                        | CoreLet { Pattern = Variable v; Value = expr } ->
                            let exprFree = getBindingVariables boundVars expr
                            (Set.union freeVars exprFree, Set.add v boundVars)
                        | _ ->
                            let termFree = getBindingVariables boundVars t
                            (Set.union freeVars termFree, boundVars)
                    ) (Set.empty, bound)
                free

            | Match { ToMatch = tm; Cases = cases } ->
                let tmFree = getBindingVariables bound tm
                let casesFree =
                    cases |> List.map (fun (p, b) ->
                        let pVars = getPatternBindingVariables p
                        let newBound = Set.union bound pVars
                        getBindingVariables newBound b
                    ) |> Set.unionMany
                Set.union tmFree casesFree

            | CoreLet { Pattern = p; Value = v } ->
                getBindingVariables bound v

            | _ -> Set.empty

    module private ContextResolution =

        let private getContextParents (program: CoreProgram) =
            program
            |> List.choose (function Context c -> Some (c.ContextName, c.Using) | _ -> None)
            |> Map.ofList

        /// Retrieve all parents of the given context identifier, in order.
        let public getContextDependencies (program: CoreProgram) (contextName: string) =
            let contextParents = getContextParents program

            let rec loop (contextName: string) (visited: Set<string>) =
                if Set.contains contextName visited then []
                else
                    match Map.tryFind contextName contextParents with
                    | Some parents ->
                        let newVisited = Set.add contextName visited
                        parents @ (parents |> List.collect (fun p -> loop p newVisited))
                    | None -> []

            loop contextName Set.empty

        /// Creates a specialized name for a symbol given a context's name.
        let public createContextualName (symbolName: string) (contextName: string) =
            symbolName + "$$" + contextName

        /// Gets the specialized name of the symbol from the given context's name.
        let public uncreateContextualName (symbolName: string) (contextName: string) =
            symbolName.Replace("$$" + contextName, "")

        /// Resolves a symbol in the given compilation context, given its arity.
        /// Returns the resolved name and a boolean indicating capture usage.
        let public resolveSymbolForContext (context: CompilationContext) (symbolName: string) (arity: int) =
            let dp = context.Global.SymbolLabels

            let tryResolve name =
                // Exact Match (function call)
                if DispatchTable.contains (name, arity) dp then Some (name, false)
                // Capture (symbol used as value, arity 0, but existing rule)
                elif arity = 0 && DispatchTable.containsByName name dp then Some (name, true)
                // Symbolic data
                else None

            let tryResolveInContext contextName =
                let resolvedName = createContextualName symbolName contextName
                tryResolve resolvedName

            // search in active contexts
            context.ActiveContexts
            |> List.tryPick tryResolveInContext
            // if no context claimed the symbol, try global
            |> Option.orElseWith (fun _ -> tryResolve symbolName)
            // raw global data
            |> Option.defaultValue (symbolName, false)

    module private RuleProcessing =

        /// Builds a "fake" rule to be added to the global context. Used for internal rules.
        let private makeIntrinsicRule (arity: int) (name: string) =
            let args = List.init arity (fun i -> Variable $"arg{i}")
            let term = symbol name args

            // A placeholder rule definition

            { LHS = term
              RHS = term
              Strategy = Liyh.Syntax.SyntaxTree.RewritingStrategy.Strict
              WhenClause = None }

        /// Placeholder rules for the internals.
        let private internalIntrinsicRules =
            (Array.concat >> List.ofArray)
                [| Internals.primitiveTypeCheckingInternals
                   |> Array.map (makeIntrinsicRule 1)

                   Internals.arithmeticInternals
                   |> Array.map (makeIntrinsicRule 2)

                   Internals.booleanInternals
                   |> Array.map (makeIntrinsicRule 2)

                   [| Internals.Print; Internals.Ppshow |]
                   |> Array.map (makeIntrinsicRule 1)

                   [| Internals.Strcat |]
                   |> Array.map (makeIntrinsicRule 2) |]

        /// Returns all the rules defined in the given program.
        let private getAllRules (program: CoreProgram) =
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
                            | Symbol { Symbol = s } -> ContextResolution.createContextualName s ctx.ContextName
                            | _ -> failwithf "Invalid LHS" 

                        let newLhs =
                            match r.LHS with
                            | Symbol s -> symbol newLhsSymbol s.Children
                            | _ -> r.LHS

                        let newRule = { r with LHS = newLhs }
                        (newLhs, newRule, Some ctx.ContextName)
                    )
                | _ -> []
            )
            |> List.append (internalIntrinsicRules |> List.map (fun r -> (r.LHS, r, None)))

        /// Returns a map of rule info associated with the actual corresponding rules.
        let public groupRules (program: CoreProgram) =
            getAllRules program
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

    module private MiscHelpers =
        open Liyh.Utils

        /// Formats a message to be printted for runtime errors.
        let public runtimeError (msg: string) =
            let sb = new Text.StringBuilder()
            let header = ColorTerm.colorize (ColorTerm.Color.Basic "red") "Runtime Error: "

            sb.Append(header).Append(msg).ToString()

        /// Marks the given registerd as "evaluated" not to "FORCE" it after.
        let public markEvaluated (reg: Reg) (ctx: CompilationContext) =
            ctx.EvaluatedRegs.Add(reg.Index) |> ignore
            reg

    // --- The actual compiler class --- //


    /// Class containing all compilation logic, encapsulates mutable states and numerous functions using them.
    /// The only public member is `__.Compile` which returns the compiled bytecode of the given program.
    type private Compiler(program: CoreProgram) =
        let builder = new ByteCodeBuilder()
        let mutable nextLabelId = 1000


        // --- General helpers --- //


        let freshLabel() =
            let label = nextLabelId
            nextLabelId <- nextLabelId + 1
            label

        let globalLabels =
            RuleProcessing.groupRules program
            |> Map.map (fun _ _ -> freshLabel ())

        let globalContext =
            { SymbolLabels = globalLabels }

        let convertBoolToAtom (boolReg: Reg) =
            let resReg = builder.Alloc()
            let trueAtom = builder.LoadAtom(Builtin.True)
            let falseAtom = builder.LoadAtom(Builtin.False)
            let lblEnd = freshLabel()

            builder.Mov(resReg, trueAtom)
            builder.JumpTrue(boolReg, lblEnd)
            builder.Mov(resReg, falseAtom)
            builder.SetLabel(lblEnd)
            resReg

        let convertAtomToBool (atomReg: Reg) =
            let resReg = builder.Alloc()
            let trueAtom = builder.LoadAtom(Builtin.True)
            let cmpRes = builder.Eq(atomReg, trueAtom)

            builder.Mov(resReg, cmpRes)
            resReg

        /// The `builder.Mov` instruction but updating the compilation context for tracking.
        let emitMov (dest: Reg, src: Reg) (ctx: CompilationContext) =
            builder.Mov(dest, src)

            if ctx.EvaluatedRegs.Contains(src.Index)
            then ctx.EvaluatedRegs.Add(dest.Index) |> ignore
            else ctx.EvaluatedRegs.Remove(dest.Index) |> ignore

        // --- Path and decision tree compilation --- //


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
                            let msg = MiscHelpers.runtimeError $"Field '{name}' not found."
                            builder.Print(builder.LoadString msg)
                            builder.Halt(1))

                        builder.SetLabel(successLabel)

                        // Always force after deconstruction (because we don't know where the value comes from)
                        // except for outermost (which wants to keep the symbolic structures)
                        match context.Strategy with
                        | Strategy.Outermost -> res
                        | _ -> builder.Force(res)

                context.PathCache <- Map.add path reg context.PathCache
                reg

        /// Compiles a decision tree into bytecode.
        /// 
        /// Parameters:
        /// - `ctx`: Compilation context containing the environment and evaluation strategy
        /// - `tree`: Decision tree to be compiled
        /// - `onMatch`: Callback called when a rule matches (receives the rule index and context)
        /// - `fallback`: Callback called if pattern matching fails
        /// 
        /// Returns the register containing the evaluation result.
        and compileTree
            (ctx: CompilationContext)
            (tree: DecisionTree)
            (onMatch: int -> CompilationContext -> Reg)
            (fallback: unit -> Reg)
            : Reg =

            let inline branchContext (ctx': CompilationContext) =
                { ctx' with
                    PathCache = ctx'.PathCache
                    EvaluatedRegs = new HashSet<int>(ctx'.EvaluatedRegs) }

            match tree with
            | Fail -> fallback()

            | Leaf(ruleIndex, bindings) ->
                let newEnv =
                    bindings |> Map.fold (fun env varName path ->
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
                        // check if we are matching against functions
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

                builder.Scope(fun _ ->
                    let phiReg = builder.Alloc()

                    for KeyValue((tag, _), subTree) in cases do
                        let nextLbl = freshLabel()
                        builder.TestTag(testReg, tag, nextLbl)

                        let ctxBranch = branchContext ctx
                        let res = compileTree ctxBranch subTree onMatch fallback

                        emitMov (phiReg, res) ctxBranch
                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)

                    match defaultCase with
                    | Some def ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault def onMatch fallback
                        emitMov (phiReg, res) ctxDefault

                    | None ->
                        let res = fallback()
                        emitMov (phiReg, res) ctx

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | SwitchLiteral(path, cases, defaultCase) ->
                let pathReg = compilePath ctx path
                let endLabel = freshLabel()

                let testReg =
                    match ctx.Strategy with
                    | Strategy.Lazy -> builder.Force(pathReg)
                    | _ -> pathReg

                builder.Scope(fun _ ->
                    let phiReg = builder.Alloc()

                    for KeyValue(lit, subTree) in cases do
                        let nextLbl = freshLabel()
                        let litReg = compileLiteral lit ctx

                        let eq = builder.Eq(testReg, litReg)
                        builder.JumpFalse(eq, nextLbl)

                        let ctxBranch = branchContext ctx
                        let res = compileTree ctxBranch subTree onMatch fallback

                        emitMov (phiReg, res) ctxBranch
                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)
                    
                    match defaultCase with
                    | Some def ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault def onMatch fallback
                        emitMov (phiReg, res) ctxDefault

                    | None ->
                        let res = fallback()
                        emitMov (phiReg, res) ctx

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | WhenGuard(guardExpr, bindings, successTree, failureTreeOpt) ->
                builder.Scope(fun _ ->
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

                    emitMov (phiReg, res) ctxBranch
                    builder.Jump(endLabel)
                    builder.SetLabel(failLabel)

                    match failureTreeOpt with
                    | Some failTree ->
                        let ctxDefault = branchContext ctx
                        let res = compileTree ctxDefault failTree onMatch fallback
                        emitMov (phiReg, res) ctxDefault

                    | None ->
                        let res = fallback()
                        emitMov (phiReg, res) ctx

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

                builder.Scope(fun _ ->
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
                        emitMov (phiReg, res) ctxDefault

                    | None ->
                        let res = fallback()
                        emitMov (phiReg, res) ctx

                    builder.SetLabel(endLabel)
                    phiReg
                )
            
            | other -> failwithf "TODO: %A" other

        /// Compiles a term using a strict evaluation strategy.
        and compileTermStrict (context: CompilationContext) (term: CoreTerm) =
            let reg = compileTerm context false term

            if context.EvaluatedRegs.Contains(reg.Index) then
                reg
            else
                let forcedReg = builder.Force(reg)
                MiscHelpers.markEvaluated forcedReg context

        /// Helper to compile the call to the internals functions for boolean comparisons.
        /// Returns a raw result (0 or 1). This is used when the user does not need the boolean result.
        and tryCompileIntrinsicBoolRaw (context: CompilationContext) (term: CoreTerm) =
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
                    | _ -> failwith "??"

                Some rawResult
            | _ -> None

        /// Helper to compile the call to the internals functions for boolean comparisons.
        /// Returns a symbolic result (true or false). This is used when the user needs the boolean result.
        and tryCompileIntrinsicBoolSymbolic (context: CompilationContext) (term: CoreTerm) =
            match tryCompileIntrinsicBoolRaw context term with
            | Some rawReg ->
                let atomReg = convertBoolToAtom rawReg
                Some (MiscHelpers.markEvaluated atomReg context)
            | None -> None

        /// Helper to compile the call to the internals functions for arithmetic.
        and tryCompileIntrinsicArithmetic (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray Internals.arithmeticInternals) ->

                let rLeft = compileTermStrict context left
                let rRight = compileTermStrict context right

                let rawResult =
                    match op with
                    | Internals.Add -> builder.Add(rLeft, rRight)
                    | Internals.Sub -> builder.Sub(rLeft, rRight)
                    | Internals.Mul -> builder.Mul(rLeft, rRight)
                    | Internals.Div -> builder.Div(rLeft, rRight)
                    | Internals.Mod -> builder.Mod(rLeft, rRight)
                    | _ -> failwith "??" // this may not happen

                Some (MiscHelpers.markEvaluated rawResult context)
            | _ -> None

        /// Helper to compile the call to the internals functions for primitive type checking.
        and tryCompileIntrinsicTypeCheck (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = symb; Children = [ arg ] } when
                Array.contains symb Internals.primitiveTypeCheckingInternals ->

                let targetTag =
                    match symb with
                    | Internals.IsInt -> BindingRCL.SYM_INT_NATIVE
                    | Internals.IsFloat -> BindingRCL.SYM_FLOAT_NATIVE
                    | Internals.IsChar -> BindingRCL.SYM_CHAR_NATIVE
                    | Internals.IsString -> BindingRCL.SYM_STRING_NATIVE
                    | _ -> failwith "??" // this may not happen

                let rArg = compileTermStrict context arg
                let rRes = builder.Alloc()
                let lblFail = freshLabel()
                let lblEnd = freshLabel()

                builder.TestTag(rArg, targetTag, lblFail)
                emitMov (rRes, builder.LoadAtom(Builtin.True)) context
                builder.Jump(lblEnd)
                builder.SetLabel(lblFail)
                emitMov (rRes, builder.LoadAtom(Builtin.False)) context
                builder.SetLabel(lblEnd)

                Some (MiscHelpers.markEvaluated rRes context)

            | _ -> None

        /// Helper to compile the call to the internals functions for other primitives.
        and tryCompileIntrinsicMisc (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Internals.Internal_print(x) ->
                let xReg = compileTermStrict context x
                builder.Print(xReg)
                Some (builder.Unit())
            
            | Internals.Internal_strcat(left, right) ->
                let rLeft = compileTermStrict context left
                let rRight = compileTermStrict context right
                Some (builder.StrCat(rLeft, rRight))

            | Internals.Internal_ppshow(term) ->
                let r = compileTermStrict context term
                Some (builder.PPShow(r))
            
            | _ -> None

        /// Helper to compile internals if applyable.
        and tryCompileIntrinsic (context: CompilationContext) (term: CoreTerm) =
            [ tryCompileIntrinsicBoolSymbolic
              tryCompileIntrinsicArithmetic
              tryCompileIntrinsicTypeCheck
              tryCompileIntrinsicMisc ]

            |> List.tryPick (fun tryCompile -> tryCompile context term)

        /// Compiles a lazy closure or thunk by capturing free variables from the environment.
        /// 
        /// Parameters:
        /// - `context`: Current compilation context
        /// - `parameters`: List of function parameters (empty for a thunk)
        /// - `body`: Body of the function to compile
        /// - `isLazyThunk`: true to create a lazy thunk, false for a normal closure
        /// 
        /// Returns the register containing the created closure/thunk.
        and compileCaptureScope (context: CompilationContext) (parameters: string list) (body: CoreTerm) (isLazyThunk: bool) (isTail: bool) =
            let boundVars = if isLazyThunk then Set.empty else Set.ofList parameters
            let freeVars = BindingVariables.getBindingVariables boundVars body

            // Captures the corresponding registers of the current environment.

            let captures =
                freeVars
                |> Set.toList
                |> List.choose (fun name ->
                    match Map.tryFind name context.Env with
                    | Some reg -> Some (name, reg)
                    | None -> None
                )

            // Generates the function code in a separate scope.

            let captureRegs = List.map snd captures
            let labelBody = freshLabel ()
            let labelSkip = freshLabel ()

            builder.Jump(labelSkip)
            builder.Scope(fun _ ->
                builder.SetLabel(labelBody)
                let (argRegs, patchIndex, savedMaxStack) = builder.DefineFunction(parameters.Length)
                
                let argEnv = List.zip parameters argRegs |> Map.ofList
                let captureEnv =
                    captures
                    |> List.mapi (fun i (name, _) -> name, builder.GetUpvalue(i))
                    |> Map.ofList
                let bodyEnv = Map.fold (fun acc k v -> Map.add k v acc) captureEnv argEnv

                let bodyContext =
                    { context with
                        Env = bodyEnv
                        Arguments = Array.ofList argRegs
                        PathCache = Map.empty }

                let resReg = compileTerm bodyContext isTail body
                builder.Ret(resReg)
                builder.FinalizeFunction(patchIndex, savedMaxStack)
            )

            // Creates a Closure or Delay with the captured upvalues.

            builder.SetLabel(labelSkip)
            if isLazyThunk then builder.Delay(labelBody, captureRegs)
            else builder.Closure(labelBody, captureRegs)

        and compileThunk (context: CompilationContext) (isTail: bool) (body: CoreTerm) =
            compileCaptureScope context [] body true isTail

        and compileClosure (context: CompilationContext) (parameters: string list) (body: CoreTerm) (isTail: bool) =
            compileCaptureScope context parameters body false isTail

        /// Compiles an expression as Data / AST (for the Outermost strategy)
        and compileAsData (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = name; Children = children } ->
                let arity = List.length children
                let (resolvedName, isCaptureWithinContext) =
                    ContextResolution.resolveSymbolForContext context name arity

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
                        let rKey = builder.LoadAtom name
                        let rVal = compileAsData context expr
                        [ rKey; rVal ])

                match base' with
                | None -> builder.MkRecord(extensionRegs)
                | Some baseTerm ->
                    let rBase = compileAsData context baseTerm
                    builder.ExtendRecord(rBase, extensionRegs)

            | other ->
                // The rest is not compilable as a symbolic data.
                compileTerm context false other


        // --- Expression compiling --- //


        and (|Intrinsic|_|) =
            tryCompileIntrinsic

        and compileMatch (match': CoreTermMatch) (context: CompilationContext) (isTail: bool) =

            let toMatchReg = compileTerm context false match'.ToMatch
            let occurrences =
                match'.Cases
                |> List.mapi (fun i (patt, _) ->
                    { RuleIndex = i; Pattern = patt; Path = Root; Bindings = Map.empty; WhenClause = None })

            let matrix =
                { Occurrences = occurrences
                  RemainingPaths = [ Root ] }

            let tree = DecisionTreeCompiler.compile matrix
            let bodies = match'.Cases |> List.map snd |> Array.ofList

            let onMatch ruleIndex leafContext =
                compileTerm leafContext isTail bodies.[ruleIndex]

            let onMismatch () =
                let gotReg = builder.PPShow toMatchReg
                let allPatterns = match'.Cases |> List.map (fst >> PrettyPrinter.prettyPrintExpr)

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

            builder.Scope(fun _ ->
                let matchContext = { context with PathCache = Map.ofList [(Root, toMatchReg)] }
                compileTree matchContext tree onMatch onMismatch)

        and compileLet (let': CoreLet) (context: CompilationContext) =
            let valReg = compileTerm context false let'.Value

            let rootReg =
                if let'.IsVariable then
                    let r = builder.Alloc()
                    emitMov (r, valReg) context
                    r
                else
                    valReg

            let occurrence =
                { RuleIndex = 0; Pattern = let'.Pattern; Path = Root; Bindings = Map.empty; WhenClause = None }

            let matrix = { Occurrences = [occurrence]; RemainingPaths = [Root] }
            let tree = DecisionTreeCompiler.compile matrix

            let onMatch _ _ = builder.Unit() // if it matches, it is handled in `valReg`

            let onMismatch () =
                let gotReg = builder.PPShow valReg
                let expected = PrettyPrinter.prettyPrintExpr let'.Pattern

                let msg1 = builder.LoadString $"The case was incomplete. Expected pattern `{expected}`, but got `"
                let msg2 = builder.LoadString "` instead."

                let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                builder.RuntimeError finalMsg

            builder.Scope(fun _ ->
                let letContext = { context with PathCache = Map.ofList [(Root, rootReg)] }
                compileTree letContext tree onMatch onMismatch)

        and compileTermSequence (terms: CoreTerm list) (context: CompilationContext) (isTail: bool) =

            let rec compileSeq (currentEnv: Map<string, Reg>) (remaining: CoreTerm list) =
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
                                emitMov (newReg, valReg) context
                                newReg
                            else
                                valReg

                        compileSeq (Map.add name finalReg currentEnv) xs

                    | CoreLet { Pattern = pattern; Value = value; IsVariable = isVar } ->
                        let valReg = compileTerm seqContext false value

                        let rootReg =
                            if isVar then
                                let r = builder.Alloc()
                                emitMov (r, valReg) context
                                r
                            else valReg
                        
                        let occurence = { RuleIndex = 0; Pattern = pattern; Path = Root; Bindings = Map.empty; WhenClause = None }
                        let matrix = { Occurrences = [occurence]; RemainingPaths = [Root] }
                        let tree = DecisionTreeCompiler.compile matrix

                        let onMatch _ (leafContext: CompilationContext) =
                            compileSeq leafContext.Env xs

                        let onMismatch () =
                            let gotReg = builder.PPShow valReg
                            let expected = PrettyPrinter.prettyPrintExpr pattern

                            let msg1 = builder.LoadString $"The case was incomplete. Expected pattern `{expected}`, but got `"
                            let msg2 = builder.LoadString "` instead."

                            let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                            builder.RuntimeError finalMsg

                        builder.Scope(fun _ ->
                            let letContext = { seqContext with PathCache = Map.ofList [(Root, rootReg)] }
                            compileTree letContext tree onMatch onMismatch)

                    | _ ->
                        compileTerm seqContext false x |> ignore
                        compileSeq currentEnv xs

            compileSeq context.Env terms

        and compileWhileLoop (whileLoop: CoreWhile) (context: CompilationContext) =
            let loopLabel = freshLabel()
            let testLabel = freshLabel()
            let endLabel = freshLabel()

            // Loop Inversion: Jump to the test first.
            builder.Jump(testLabel)

            // The body of the loop.
            builder.SetLabel(loopLabel)
            builder.Scope(fun _ -> compileTerm context false whileLoop.Body |> ignore)

            // The predicate check.
            builder.SetLabel(testLabel)

            // Attempts to compile the predicate as a native comparison.
            let predBool =
                match tryCompileIntrinsicBoolRaw context whileLoop.Predicate with
                | Some rawReg -> rawReg
                | None ->
                    let predReg = compileTerm context false whileLoop.Predicate
                    convertAtomToBool predReg

            // If true, jump back to the body.
            builder.JumpTrue(predBool, loopLabel)

            builder.SetLabel(endLabel)
            builder.Unit()

        and compileRecordExtend (record: CoreRecordExtend) (context: CompilationContext) =
            let extensionRegs =
                record.Extension
                |> List.collect (fun (name, expr) ->
                    let rVal = compileTerm context false expr
                    let rKey = builder.LoadAtom name
                    [ rKey; rVal ])

            match record.BaseRecord with
            | None -> builder.MkRecord(extensionRegs)
            | Some baseTerm ->
                let rBase = compileTerm context false baseTerm
                builder.ExtendRecord(rBase, extensionRegs)

        and compileSymbol (symbol: CoreSymbol) (context: CompilationContext) (isTail: bool) =
            let name = symbol.Symbol
            let children = symbol.Children
            let arity = List.length children

            match symbol with
            | { Symbol = "lazy"; Children = [ body ] } ->
                compileThunk context isTail body

            | { Symbol = "force"; Children = [ expr ] } ->
                let thunkReg = compileTerm context isTail expr
                let res = builder.Force(thunkReg)
                MiscHelpers.markEvaluated res context

            | _ ->

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

                let (resolvedName, isCaptureWithinContext) =
                    ContextResolution.resolveSymbolForContext context name arity

                if isCaptureWithinContext then
                    // Not a function call, but an "applicable" value
                    builder.LoadAtom(resolvedName)
                else
                    let dp = context.Global.SymbolLabels
                    let resolvedInfo = DispatchTable.tryFindByNameArity (resolvedName, List.length children) dp

                    match resolvedInfo with
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

        and compileSubstitution (substitution: CoreSubstitution) (context: CompilationContext) =
            let astReg = compileTermStrict context substitution.InExpr

            let finalReg =
                substitution.Env
                |> List.fold (fun currentTreeReg (sym, valExpr) ->
                    let valReg = compileTermStrict context valExpr
                    let atomReg = builder.LoadAtom(sym.Symbol)
                    let nextReg = builder.Alloc()

                    builder.Subst(nextReg, currentTreeReg, atomReg, valReg)
                    nextReg
                ) astReg

            finalReg

        and compileUsingContext (usingContext: CoreUsingContext) (context: CompilationContext) (isTail: bool) =
            let usingContextName = usingContext.Context

            let contextDependencies = ContextResolution.getContextDependencies program usingContextName
            let addedContextDependencies = usingContextName :: contextDependencies @ context.ActiveContexts
            let newCompilationContext = { context with ActiveContexts = addedContextDependencies }

            compileTerm newCompilationContext isTail usingContext.Expr

        and compileFunctionalApplication (fa: FunctionalApplication) (context: CompilationContext) =
            let bReg = compileTerm context false fa.Base
            let bStrict = builder.Force(bReg)
            let argsRegs = List.map (compileTerm context false) fa.Arguments

            builder.Apply(bStrict, argsRegs)

        and compileUpdateVariable (name: string, value: CoreTerm) (context: CompilationContext) =
            let valReg = compileTerm context false value

            match Map.tryFind name context.Env with
            | None -> failwithf "Cannot compile the variable update '%s'." name
            | Some targetReg ->
                emitMov (targetReg, valReg) context
                builder.Unit()

        and compileLiteral (lit: CoreLiteral) (context: CompilationContext) =
            let reg =
                match lit with
                | Integer i -> builder.LoadInt (int i)
                | Float f -> builder.LoadFloat f
                | String s -> builder.LoadString s
                | Char c -> builder.LoadChar c

            MiscHelpers.markEvaluated reg context

        and compileVariable (name: string) (context: CompilationContext) =
            match Map.tryFind name context.Env with
            | Some r -> r
            | None -> failwithf "Variable '%s unfound." name

        and compileTerm (context: CompilationContext) (isTail: bool) (term: CoreTerm) =
            match term with
            | Intrinsic context reg -> reg
            | Variable name -> compileVariable name context
            | Literal lit -> compileLiteral lit context
            | RecordExtend record -> compileRecordExtend record context
            | CoreLet let' -> compileLet let' context
            | Match match' -> compileMatch match' context isTail
            | TermSequence terms -> compileTermSequence terms context isTail
            | WhileLoop whileLoop -> compileWhileLoop whileLoop context
            | Symbol symbol -> compileSymbol symbol context isTail
            | FunctionalApplication fa -> compileFunctionalApplication fa context
            | Closure closure -> compileClosure context closure.Parameters closure.Value isTail
            | UpdateVariable(name, value) -> compileUpdateVariable (name, value) context
            | Substitution sub -> compileSubstitution sub context
            | UsingContext usingContext -> compileUsingContext usingContext context isTail
            | _ -> failwithf "TODO: %s" (PrettyPrinter.prettyPrintExpr term)

        member public __.Compile() =

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

            let groupedRules = RuleProcessing.groupRules program

            comments 
            |> List.iter (fun comment -> 
                let paddedComment = comment.PadRight(maxLength)
                builder.Comment($"{paddedComment}  ;"))

            for KeyValue(ruleInfo, rules) in groupedRules do
                let { Name = symbolName; Arity = arity; Strategy = strategy } = ruleInfo
                let label = globalLabels.[ruleInfo]

                builder.CommentNewLine($"--- {symbolName}/{arity} ---\n")
                builder.SetLabel(label)

                let (argRegsList, patchIndex, savedMaxStack) = builder.DefineFunction(arity)
                let argRegs = Array.ofList argRegsList
                let rulesArray = Array.ofList rules
                let tree = DecisionTreeCompiler.compileRules rulesArray

                let activeContexts =
                    match ruleInfo.ContextName with
                    | Some contextName -> contextName :: ContextResolution.getContextDependencies program contextName
                    | None -> []

                let context =
                    { Global = globalContext
                      Env = Map.empty
                      PathCache = Map.empty
                      Arguments = argRegs
                      Strategy = strategy
                      ActiveContexts = activeContexts
                      EvaluatedRegs = new HashSet<int>() }

                let fallback () =

                    // The `tryFallbackToGlobal` mechanism prevents a local context from completely shadowing
                    // global functions that share the same name but do not satisfy the current context's rules.
                    // This ensures the implementation of the "overlay" resolution semantics: local definitions
                    // take precedence, followed by global ones, and finally symbolic data constructions.

                    let originalName =
                        match ruleInfo.ContextName with
                        | Some contextName -> ContextResolution.uncreateContextualName symbolName contextName
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
                        let header = ColorTerm.colorize (ColorTerm.Color.Basic "red") "Invalid rule matched: "
                        let prefixReg = builder.LoadString header
                        let eolReg = builder.LoadString "\n"

                        let fullMsgReg = builder.ConcatMany [ prefixReg; errorStrReg; eolReg ]

                        builder.Print(fullMsgReg)
                        builder.Halt(1) // error
                        builder.Alloc() // dummy

                    | _ ->
                        compileTerm leafContext (symbolName <> "main") rule.RHS

                let optimizedTree =
                    match tree with
                    | Switch(Root, cases, _) ->
                        let newTree = Map.tryFind (symbolName, arity) cases
                        Option.defaultValue tree newTree
                    | _ -> tree

                let result = compileTree context optimizedTree onMatch fallback

                if symbolName = "main" then builder.Halt() // stop the program
                else builder.Ret(result)

                builder.FinalizeFunction(patchIndex, savedMaxStack)

            let dispatchTable = globalLabels
            builder.Compile(entryPointLabel, dispatchTable)

    /// Compiles a LiyhCore program into a LyVM's bytecode equivalent program.
    /// The `optimize` flag has no effect, for now.
    let public compile (program: CoreProgram) =
        let compiler = new Compiler(program)
        compiler.Compile()

