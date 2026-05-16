namespace Liyh.LyVM

//
// The bytecode compiler takes Liyh's LiyhCore representation and compiles it into bytecode instructions
// for the Liyh VM (LyVM - RCL). The compiler produces bytecode that is not optimized, except where
// optimization opportunities are straightforward.
//

module public BytecodeCompiler =
    open System
    open System.Collections.Generic
    open Liyh.Module
    open Liyh.FFI.GeneralFFI
    open Liyh.Module.LiyhPackage
    open Liyh.Utils
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open Liyh.Core.DecisionTree.DecisionTreeCompiler

    /// A registry/dispatch table for the foreign function interfaces.
    type private FFIRegistry(globalFFIBindings: GlobalFFIBindings) =

        let mapCTypeToRclType (ctype: CType) =
            match ctype with
            | CType.UInt8 -> RclType.UINT8
            | CType.Int8 -> RclType.INT8
            | CType.UInt16 -> RclType.UINT16
            | CType.Int16 -> RclType.INT16
            | CType.UInt32 -> RclType.UINT32
            | CType.Int32 -> RclType.INT32
            | CType.UInt64 -> RclType.UINT64
            | CType.Int64 -> RclType.INT64
            | CType.Float32 -> RclType.FLOAT32
            | CType.Float64 -> RclType.FLOAT64
            | CType.LongDouble -> RclType.LONGDOUBLE
            | CType.Char -> RclType.CHAR
            | CType.String -> RclType.STRING
            | CType.Pointer _ -> RclType.PTR
            | CType.Void -> RclType.VOID

        let flatBindings =
            globalFFIBindings
            |> Map.values
            |> Seq.collect id
            |> Seq.map (fun info ->

                let argTypes = info.ArgumentsType |> Seq.map mapCTypeToRclType |> Array.ofSeq
                let retType = mapCTypeToRclType info.ReturnType

                // External functions are always qualified by their library FFI's name.
                let qualifiedName = sprintf "%s.%s" info.ExternalQualifier info.FunctionName

                let rclBinding =
                    { Library = info.LibraryPath
                      FunctionName = info.FunctionName
                      Arity = info.Arity
                      ArgTypes = argTypes
                      RetType = retType }

                (qualifiedName, rclBinding)
            ) |> Array.ofSeq

        let entries = Array.map snd flatBindings
        let indices =
            flatBindings
            |> Array.mapi (fun idx (qualName, _) -> (qualName, idx))
            |> Map.ofArray

        /// Returns the array of `RCLFFIBinding` associated to the global FFI bindings.
        member public _.Entries = entries

        /// Attempts to return the associated label index to an FFI function.
        member public _.TryGetIndex(qualName: string) = Map.tryFind qualName indices

    type private GlobalContext =
        { SymbolLabels: DispatchTable           // dispatch table (RuleInfo : LabelIndex)
          FFIRegistery: FFIRegistry }           // ffi registry (dispatch table-like for foreign functions)

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

            | Symbol { Children = children } -> 
                children
                |> List.map getPatternBindingVariables
                |> Set.unionMany

            | RecordExtend re ->
                let baseVars =
                    re.BaseRecord
                    |> Option.map getPatternBindingVariables
                    |> Option.defaultValue Set.empty

                let extVars =
                    re.Extension
                    |> List.map (snd >> getPatternBindingVariables)
                    |> Set.unionMany

                Set.union baseVars extVars

            | CoreLet { Pattern = p } -> 
                getPatternBindingVariables p

            | AsClause (p1, p2) -> 
                Set.union (getPatternBindingVariables p1) (getPatternBindingVariables p2)

            | WhenClause (p, _) -> 
                getPatternBindingVariables p

            | Substitution sub ->
                getPatternBindingVariables sub.InExpr

            | _ -> Set.empty

        /// Gets the binding variables from the given term, with a set of already existing bindings.
        let rec public getBindingVariables (bound: Set<string>) (term: CoreTerm) =
            match term with
            | Variable v ->
                if bound.Contains v then Set.empty else Set.singleton v

            | Literal _ | Wildcard -> 
                Set.empty

            | Symbol { Children = children } ->
                children
                |> List.map (getBindingVariables bound)
                |> Set.unionMany

            | RecordExtend re ->
                let baseFree =
                    re.BaseRecord
                    |> Option.map (getBindingVariables bound)
                    |> Option.defaultValue Set.empty

                let extFree =
                    re.Extension
                    |> List.map (snd >> getBindingVariables bound)
                    |> Set.unionMany

                Set.union baseFree extFree

            | Match m ->
                let tmFree = getBindingVariables bound m.ToMatch
                let casesFree =
                    m.Cases |> List.map (fun (p, b) ->
                        let pVars = getPatternBindingVariables p
                        let newBound = Set.union bound pVars

                        let rec getPatternFreeVars p bound =
                            match p with
                            | WhenClause(innerP, cond) -> 
                                let innerPVars = getPatternBindingVariables innerP
                                let condFree = getBindingVariables (Set.union bound innerPVars) cond
                                Set.union (getPatternFreeVars innerP bound) condFree

                            | AsClause(p1, p2) ->
                                Set.union (getPatternFreeVars p1 bound) (getPatternFreeVars p2 bound)

                            | Symbol s ->
                                s.Children
                                |> List.map (fun c -> getPatternFreeVars c bound)
                                |> Set.unionMany

                            | RecordExtend re -> 
                                let baseFree =
                                    re.BaseRecord
                                    |> Option.map (fun b -> getPatternFreeVars b bound)
                                    |> Option.defaultValue Set.empty

                                let extFree =
                                    re.Extension
                                    |> List.map (fun (_, v) -> getPatternFreeVars v bound)
                                    |> Set.unionMany

                                Set.union baseFree extFree

                            | _ -> Set.empty

                        let pattFree = getPatternFreeVars p bound
                        let bodyFree = getBindingVariables newBound b
                        Set.union pattFree bodyFree

                    ) |> Set.unionMany
                Set.union tmFree casesFree

            | Closure c ->
                let newBound = Set.union bound (Set.ofList c.Parameters)
                getBindingVariables newBound c.Value

            | FunctionalApplication fa ->
                let fFree = getBindingVariables bound fa.Base
                let argsFree =
                    fa.Arguments
                    |> List.map (getBindingVariables bound)
                    |> Set.unionMany

                Set.union fFree argsFree

            | Substitution sub ->
                let envFree =
                    sub.Env
                    |> List.map (snd >> getBindingVariables bound)
                    |> Set.unionMany

                let inExprFree = getBindingVariables bound sub.InExpr
                Set.union envFree inExprFree

            | UsingContext ctx ->
                getBindingVariables bound ctx.Expr

            | TermSequence terms ->
                terms |> List.fold (fun (freeVars, boundVars) t ->
                    match t with
                    | CoreLet { Pattern = p; Value = expr } ->
                        let exprFree = getBindingVariables boundVars expr
                        let pVars = getPatternBindingVariables p
                        (Set.union freeVars exprFree, Set.union boundVars pVars)

                    | _ ->
                        let termFree = getBindingVariables boundVars t
                        (Set.union freeVars termFree, boundVars)

                ) (Set.empty, bound)
                |> fst

            | CoreLet let' ->
                getBindingVariables bound let'.Value

            | WhileLoop w ->
                let pFree = getBindingVariables bound w.Predicate
                let bFree = getBindingVariables bound w.Body
                Set.union pFree bFree

            | UpdateVariable (v, expr) ->
                let exprFree = getBindingVariables bound expr
                if bound.Contains v then exprFree else Set.add v exprFree

            | Resume r ->
                let rwFree = getBindingVariables bound r.Rewrite
                let stFree = getBindingVariables bound r.State
                Set.union rwFree stFree
                
            | Handle h ->
                let stFree = getBindingVariables bound h.State
                let thFree = getBindingVariables bound h.ToHandle
                Set.union stFree thFree

            | WhenClause (patt, cond) ->
                let pVars = getPatternBindingVariables patt
                let condFree = getBindingVariables (Set.union bound pVars) cond
                condFree

            | AsClause (p1, p2) ->
                Set.union (getBindingVariables bound p1) (getBindingVariables bound p2)

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
                   |> Array.map (makeIntrinsicRule 2)
                   
                   Internals.primitiveTypeCastingInternals
                   |> Array.map (makeIntrinsicRule 1) |]

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
    type private Compiler(globalFFIBindings: GlobalFFIBindings, program: CoreProgram) =
        let builder = new ByteCodeBuilder()
        let mutable nextLabelId = 1000

        let ffiRegistery = FFIRegistry(globalFFIBindings)


        // --- General helpers --- //


        let freshLabel() =
            let label = nextLabelId
            nextLabelId <- nextLabelId + 1
            label

        let globalLabels =
            RuleProcessing.groupRules program
            |> Map.map (fun _ _ -> freshLabel ())

        let globalContext =
            { SymbolLabels = globalLabels
              FFIRegistery = ffiRegistery }

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

                    | Tag parent ->
                        // We have to add an instruction to the VM that only gets
                        // the head of a symbol, without its children. This is necessary
                        // if we want to extract a variable symbol with children.
                        //
                        // For now, we return the whole binding. This is therefore a
                        // semantic gap, but it is far from being the most important feature.
                        compilePath context parent

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
            (onMatch: int -> CompilationContext -> Reg option -> Reg)
            (fallback: Reg option -> Reg)
            (target: Reg option)
            : Reg =

            let inline branchContext (ctx': CompilationContext) =
                { ctx' with
                    PathCache = ctx'.PathCache
                    EvaluatedRegs = new HashSet<int>(ctx'.EvaluatedRegs) }

            match tree with
            | Fail -> fallback target

            | Leaf(ruleIndex, bindings) ->
                let newEnv =
                    bindings |> Map.fold (fun env varName path ->
                        let reg = compilePath ctx path
                        Map.add varName reg env
                    ) ctx.Env
                let leafCtx = { ctx with Env = newEnv }
                onMatch ruleIndex leafCtx target

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
                    let phiReg = defaultArg target (builder.Alloc())

                    for KeyValue((tagName, arity), subTree) in cases do
                        let nextLbl = freshLabel()

                        if tagName = "true" && arity = 0 then
                            builder.JumpFalse(testReg, nextLbl)

                        elif tagName = "false" && arity = 0 then
                            builder.JumpTrue(testReg, nextLbl)

                        else
                            builder.TestTag(testReg, tagName, nextLbl)

                        let ctxBranch = branchContext ctx
                        compileTree ctxBranch subTree onMatch fallback (Some phiReg) |> ignore

                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)

                    match defaultCase with
                    | Some def ->
                        let ctxDefault = branchContext ctx
                        compileTree ctxDefault def onMatch fallback (Some phiReg) |> ignore

                    | None ->
                        fallback (Some phiReg) |> ignore

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
                    let phiReg = defaultArg target (builder.Alloc())

                    for KeyValue(lit, subTree) in cases do
                        let nextLbl = freshLabel()
                        let litReg = compileLiteral lit ctx None

                        let eq = builder.Eq(testReg, litReg)
                        builder.JumpFalse(eq, nextLbl)

                        let ctxBranch = branchContext ctx
                        compileTree ctxBranch subTree onMatch fallback (Some phiReg) |> ignore

                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)
                    
                    match defaultCase with
                    | Some def ->
                        let ctxDefault = branchContext ctx
                        compileTree ctxDefault def onMatch fallback (Some phiReg) |> ignore

                    | None ->
                        fallback (Some phiReg) |> ignore

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

                    let guardReg = compileTerm guardCtx false None guardExpr
                    let failLabel = freshLabel()
                    let endLabel = freshLabel()
                    let phiReg = defaultArg target (builder.Alloc())

                    builder.JumpFalse(guardReg, failLabel)

                    let ctxBranch = branchContext ctx
                    compileTree ctxBranch successTree onMatch fallback (Some phiReg) |> ignore

                    builder.Jump(endLabel)
                    builder.SetLabel(failLabel)

                    match failureTreeOpt with
                    | Some failTree ->
                        let ctxDefault = branchContext ctx
                        compileTree ctxDefault failTree onMatch fallback (Some phiReg) |> ignore

                    | None ->
                        fallback (Some phiReg) |> ignore

                    builder.SetLabel(endLabel)
                    phiReg
                )

            | TypeCheck(path, cases, defaultCase) ->
                let pathReg = compilePath ctx path
                let endLabel = freshLabel()
                let phiReg = defaultArg target (builder.Alloc())

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
                        compileTree ctxBranch subTree onMatch fallback (Some phiReg) |> ignore

                        builder.Jump(endLabel)
                        builder.SetLabel(nextLbl)

                    match defaultCase with
                    | Some d ->
                        let ctxDefault = branchContext ctx
                        compileTree ctxDefault d onMatch fallback (Some phiReg) |> ignore

                    | None ->
                        fallback (Some phiReg) |> ignore

                    builder.SetLabel(endLabel)
                    phiReg
                )
            
            | other -> failwithf "TODO: %A" other

        and compileTermStrict (context: CompilationContext) (target: Reg option) (term: CoreTerm) =
            let rawReg = compileTerm context false target term

            if context.EvaluatedRegs.Contains(rawReg.Index) then
                rawReg
            else
                let forcedReg = builder.Force(rawReg, ?target = target)
                MiscHelpers.markEvaluated forcedReg context

        and compileOr (context: CompilationContext) (target: Reg option) (left: CoreTerm) (right: CoreTerm) =
            let rRes = defaultArg target (builder.Alloc())
            let labelEnd = freshLabel()

            compileTermStrict context (Some rRes) left |> ignore
            builder.JumpTrue(rRes, labelEnd)
            compileTermStrict context (Some rRes) right |> ignore

            builder.SetLabel(labelEnd)
            MiscHelpers.markEvaluated rRes context

        and compileAnd (context: CompilationContext) (target: Reg option) (left: CoreTerm) (right: CoreTerm) =
            let rRes = defaultArg target (builder.Alloc())
            let labelEnd = freshLabel()

            compileTermStrict context (Some rRes) left |> ignore
            builder.JumpFalse(rRes, labelEnd)
            compileTermStrict context (Some rRes) right |> ignore

            builder.SetLabel(labelEnd)
            MiscHelpers.markEvaluated rRes context

        /// Helper to compile the call to the internals functions for boolean comparisons.
        /// Returns a raw result (0 or 1). This is used when the user does not need the boolean result.
        and tryCompileIntrinsicBoolean (context: CompilationContext) (term: CoreTerm) (target: Reg option) =
            match term with
            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray Internals.booleanInternals) ->

                let rLeft = compileTermStrict context None left
                let rRight = compileTermStrict context None right

                let resReg =
                    match op with
                    | Internals.Eq  -> builder.Eq(rLeft, rRight, ?target = target)
                    | Internals.Neq -> builder.NotEqual(rLeft, rRight, ?target = target)
                    | Internals.Le  -> builder.Le(rLeft, rRight, ?target = target)
                    | Internals.Leq -> builder.Leq(rLeft, rRight, ?target = target)
                    | Internals.Ge  -> builder.Ge(rLeft, rRight, ?target = target)
                    | Internals.Geq -> builder.Geq(rLeft, rRight, ?target = target)
                    | Internals.Or -> compileOr context target left right
                    | Internals.And -> compileAnd context target left right
                    | other -> failwithf "Unknown: %s" other

                Some (MiscHelpers.markEvaluated resReg context)
            | _ -> None

        /// Helper to compile the call to the internals functions for arithmetic.
        and tryCompileIntrinsicArithmetic (context: CompilationContext) (term: CoreTerm) (target: Reg option) =
            match term with
            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray Internals.arithmeticInternals) ->

                let rLeft = compileTermStrict context None left
                let rRight = compileTermStrict context None right

                let rawResult =
                    match op with
                    | Internals.Add -> builder.Add(rLeft, rRight, ?target = target)
                    | Internals.Sub -> builder.Sub(rLeft, rRight, ?target = target)
                    | Internals.Mul -> builder.Mul(rLeft, rRight, ?target = target)
                    | Internals.Div -> builder.Div(rLeft, rRight, ?target = target)
                    | Internals.Mod -> builder.Mod(rLeft, rRight, ?target = target)
                    | _ -> failwith "??" // this may not happen

                Some (MiscHelpers.markEvaluated rawResult context)
            | _ -> None

        /// Helper to compile the call to the internals functions for primitive type checking.
        and tryCompileIntrinsicTypeCheck (context: CompilationContext) (term: CoreTerm) (target: Reg option) =
            match term with
            | Symbol { Symbol = symb; Children = [ arg ] } when
                Array.contains symb Internals.primitiveTypeCheckingInternals ->

                let targetTag =
                    match symb with
                    | Internals.IsInt -> BindingRCL.SYM_INT_NATIVE
                    | Internals.IsFloat -> BindingRCL.SYM_FLOAT_NATIVE
                    | Internals.IsChar -> BindingRCL.SYM_CHAR_NATIVE
                    | Internals.IsString -> BindingRCL.SYM_STRING_NATIVE
                    | Internals.IsBool -> BindingRCL.SYM_BOOL_NATIVE
                    | Internals.IsNumeric -> BindingRCL.SYM_NUM_NATIVE
                    | _ -> failwith "??" // this may not happen

                let rArg = compileTermStrict context None arg
                let rRes = defaultArg target (builder.Alloc())
                let lblFail = freshLabel()
                let lblEnd = freshLabel()

                builder.TestTag(rArg, targetTag, lblFail)

                // Success -> true
                builder.LoadBool(true, ?target = Some rRes) |> ignore
                builder.Jump(lblEnd)

                // Failure -> false
                builder.SetLabel(lblFail)
                builder.LoadBool(false, ?target = Some rRes) |> ignore

                // End label
                builder.SetLabel(lblEnd)

                Some (MiscHelpers.markEvaluated rRes context)

            | _ -> None

        /// Helper to compile the call to the internals functions for other primitives.
        and tryCompileIntrinsicMisc (context: CompilationContext) (term: CoreTerm) (target: Reg option) =
            match term with
            | Internals.Internal_print(x) ->
                let xReg = compileTermStrict context None x
                builder.Print(xReg)
                Some (builder.Unit(?target = target))

            | Internals.Internal_strcat(left, right) ->
                let rLeft = compileTermStrict context None left
                let rRight = compileTermStrict context None right
                Some (builder.StrCat(rLeft, rRight, ?target = target))

            | Internals.Internal_ppshow(term) ->
                let r = compileTermStrict context None term
                Some (builder.PPShow(r, ?target = target))

            | _ -> None

        and tryCompileIntrinsicTypeCast (context: CompilationContext) (term: CoreTerm) (target: Reg option) =

            let emitRawCast srcTerm targetType sourceType =
                let srcReg = compileTermStrict context None srcTerm
                let resReg = builder.Cast(srcReg, targetType, sourceType, ?target = target)
                Some resReg

            match term with
            | Internals.Internal_cast_itf(x) -> emitRawCast x BindingRCL.SYM_FLOAT_NATIVE BindingRCL.SYM_INT_NATIVE
            | Internals.Internal_cast_itc(x) -> emitRawCast x BindingRCL.SYM_CHAR_NATIVE BindingRCL.SYM_INT_NATIVE
            | Internals.Internal_cast_its(x) -> emitRawCast x BindingRCL.SYM_STRING_NATIVE BindingRCL.SYM_INT_NATIVE

            | Internals.Internal_cast_fti(x) -> emitRawCast x BindingRCL.SYM_INT_NATIVE BindingRCL.SYM_FLOAT_NATIVE
            | Internals.Internal_cast_ftc(x) -> emitRawCast x BindingRCL.SYM_CHAR_NATIVE BindingRCL.SYM_FLOAT_NATIVE
            | Internals.Internal_cast_fts(x) -> emitRawCast x BindingRCL.SYM_STRING_NATIVE BindingRCL.SYM_FLOAT_NATIVE

            | Internals.Internal_cast_cti(x) -> emitRawCast x BindingRCL.SYM_INT_NATIVE BindingRCL.SYM_CHAR_NATIVE
            | Internals.Internal_cast_ctf(x) -> emitRawCast x BindingRCL.SYM_FLOAT_NATIVE BindingRCL.SYM_CHAR_NATIVE
            | Internals.Internal_cast_cts(x) -> emitRawCast x BindingRCL.SYM_STRING_NATIVE BindingRCL.SYM_CHAR_NATIVE

            | Internals.Internal_cast_sti(x) -> emitRawCast x BindingRCL.SYM_INT_NATIVE BindingRCL.SYM_STRING_NATIVE
            | Internals.Internal_cast_stf(x) -> emitRawCast x BindingRCL.SYM_FLOAT_NATIVE BindingRCL.SYM_STRING_NATIVE
            | Internals.Internal_cast_stc(x) -> emitRawCast x BindingRCL.SYM_CHAR_NATIVE BindingRCL.SYM_STRING_NATIVE

            | _ -> None

        /// Helper to compile internals if applyable.
        and tryCompileIntrinsic (context: CompilationContext) (term: CoreTerm) (target: Reg option) =
            [ tryCompileIntrinsicBoolean
              tryCompileIntrinsicArithmetic
              tryCompileIntrinsicTypeCheck
              tryCompileIntrinsicMisc
              tryCompileIntrinsicTypeCast ]

            |> List.tryPick (fun tryCompile -> tryCompile context term target)

        /// Compiles a lazy closure or thunk by capturing free variables from the environment.
        /// 
        /// Parameters:
        /// - `context`: Current compilation context
        /// - `parameters`: List of function parameters (empty for a thunk)
        /// - `body`: Body of the function to compile
        /// - `isLazyThunk`: true to create a lazy thunk, false for a normal closure
        /// 
        /// Returns the register containing the created closure/thunk.
        and compileCaptureScope (context: CompilationContext) (parameters: string list) (body: CoreTerm) (isLazyThunk: bool) (isTail: bool) (target: Reg option) =
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

                let resReg = compileTerm bodyContext isTail None body
                builder.Ret(resReg)
                builder.FinalizeFunction(patchIndex, savedMaxStack)
            )

            // Creates a Closure or Delay with the captured upvalues.

            builder.SetLabel(labelSkip)
            if isLazyThunk then builder.Delay(labelBody, captureRegs, ?target = target)
            else builder.Closure(labelBody, captureRegs, ?target = target)

        and compileThunk (context: CompilationContext) (isTail: bool) (body: CoreTerm) =
            compileCaptureScope context [] body true isTail

        and compileClosure (context: CompilationContext) (parameters: string list) (body: CoreTerm) (isTail: bool) =
            compileCaptureScope context parameters body false isTail

        /// Compiles an expression as Data / AST (for the Outermost strategy)
        and compileAsData (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = "true"; Children = [] } ->
                MiscHelpers.markEvaluated (builder.LoadBool(true)) context

            | Symbol { Symbol = "false"; Children = [] } ->
                MiscHelpers.markEvaluated (builder.LoadBool(false)) context

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
                compileTerm context false None other


        // --- Expression compiling --- //


        and (|Intrinsic|_|) (context: CompilationContext) (target: Reg option) (term: CoreTerm) =
            tryCompileIntrinsic context term target

        and compileMatch (match': CoreTermMatch) (context: CompilationContext) (isTail: bool) (target: Reg option) =

            let toMatchReg = compileTerm context false None match'.ToMatch
            let occurrences =
                match'.Cases
                |> List.mapi (fun i (patt, _) ->
                    { RuleIndex = i; Pattern = patt; Path = Root; Bindings = Map.empty; WhenClause = None })

            let matrix =
                { Occurrences = occurrences
                  RemainingPaths = [ Root ] }

            let tree = DecisionTreeCompiler.compile matrix
            let bodies = match'.Cases |> List.map snd |> Array.ofList

            let onMatch ruleIndex leafContext matchTarget =
                compileTerm leafContext isTail matchTarget bodies.[ruleIndex]

            let onMismatch mismatchTarget =
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
                builder.RuntimeError finalMsg |> ignore
                builder.Unit(?target = mismatchTarget)

            builder.Scope(fun _ ->
                let matchContext = { context with PathCache = Map.ofList [(Root, toMatchReg)] }
                compileTree matchContext tree onMatch onMismatch target)

        and compileLet (let': CoreLet) (context: CompilationContext) (target: Reg option) =
            let evaluatedReg =
                if let'.IsVariable then
                    let varReg = builder.Alloc()
                    compileTerm context false (Some varReg) let'.Value |> ignore
                    varReg
                else
                    compileTerm context false None let'.Value

            let occurrence =
                { RuleIndex = 0; Pattern = let'.Pattern; Path = Root; Bindings = Map.empty; WhenClause = None }

            let matrix = { Occurrences = [occurrence]; RemainingPaths = [Root] }
            let tree = DecisionTreeCompiler.compile matrix

            let onMatch _ _ _ = builder.Unit(?target = target) // if it matches, it is handled in `valReg`

            let onMismatch mismatchTarget =
                let gotReg = builder.PPShow evaluatedReg
                let expected = PrettyPrinter.prettyPrintExpr let'.Pattern

                let msg1 = builder.LoadString $"The case was incomplete. Expected pattern `{expected}`, but got `"
                let msg2 = builder.LoadString "` instead."

                let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                builder.RuntimeError finalMsg |> ignore
                builder.Unit(?target = mismatchTarget)

            builder.Scope(fun _ ->
                let letContext = { context with PathCache = Map.ofList [(Root, evaluatedReg)] }
                compileTree letContext tree onMatch onMismatch target)

        and compileTermSequence (terms: CoreTerm list) (context: CompilationContext) (isTail: bool) (target: Reg option) =

            let rec compileSeq (currentEnv: Map<string, Reg>) (currentTarget: Reg option) (remaining: CoreTerm list) =
                let seqContext = { context with Env = currentEnv }

                match remaining with
                | [] -> builder.Unit(?target = currentTarget) // dummy
                | [ x ] -> compileTerm seqContext isTail currentTarget x
                | x :: xs ->
                    match x with
                    | CoreLet { Pattern = Variable name; Value = value; IsVariable = isVar } ->

                        let finalReg =
                            if isVar then
                                let newReg = builder.Alloc()
                                compileTerm seqContext false (Some newReg) value |> ignore
                                newReg
                            else
                                compileTerm seqContext false None value

                        compileSeq (Map.add name finalReg currentEnv) currentTarget xs

                    | CoreLet { Pattern = pattern; Value = value; IsVariable = isVar } ->

                        let evaluatedReg =
                            if isVar then
                                let r = builder.Alloc()
                                compileTerm seqContext false (Some r) value |> ignore
                                r
                            else 
                                compileTerm seqContext false None value

                        let occurence = { RuleIndex = 0; Pattern = pattern; Path = Root; Bindings = Map.empty; WhenClause = None }
                        let matrix = { Occurrences = [occurence]; RemainingPaths = [Root] }
                        let tree = DecisionTreeCompiler.compile matrix

                        let onMatch _ (leafContext: CompilationContext) matchTarget =
                            compileSeq leafContext.Env matchTarget xs

                        let onMismatch mismatchTarget =
                            let gotReg = builder.PPShow evaluatedReg 
                            let expected = PrettyPrinter.prettyPrintExpr pattern
                            let msg1 = builder.LoadString $"The case was incomplete. Expected pattern `{expected}`, but got `"
                            let msg2 = builder.LoadString "` instead."
                            let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])

                            builder.RuntimeError finalMsg |> ignore
                            builder.Unit(?target = mismatchTarget)

                        builder.Scope(fun _ ->
                            let letContext = { seqContext with PathCache = Map.ofList [(Root, evaluatedReg)] }
                            compileTree letContext tree onMatch onMismatch currentTarget)

                    | _ ->
                        compileTerm seqContext false None x |> ignore
                        compileSeq currentEnv currentTarget xs

            compileSeq context.Env target terms

        and compileWhileLoop (whileLoop: CoreWhile) (context: CompilationContext) (target: Reg option) =
            let loopLabel = freshLabel()
            let testLabel = freshLabel()
            let endLabel = freshLabel()

            // Loop Inversion: Jump to the test first.
            builder.Jump(testLabel)

            // The body of the loop.
            builder.SetLabel(loopLabel)
            builder.Scope(fun _ -> compileTerm context false None whileLoop.Body |> ignore)

            // The predicate check.
            builder.SetLabel(testLabel)

            // Attempts to compile the predicate as a native comparison.
            let predBool =
                match tryCompileIntrinsicBoolean context whileLoop.Predicate target with
                | Some rawReg -> rawReg
                | None -> compileTerm context false None whileLoop.Predicate

            // If true, jump back to the body.
            builder.JumpTrue(predBool, loopLabel)

            builder.SetLabel(endLabel)
            builder.Unit(?target = target)

        and compileRecordExtend (record: CoreRecordExtend) (context: CompilationContext) (target: Reg option) =
            let extensionRegs =
                record.Extension
                |> List.collect (fun (name, expr) ->
                    let rVal = compileTerm context false None expr
                    let rKey = builder.LoadAtom name
                    [ rKey; rVal ])

            match record.BaseRecord with
            | None -> builder.MkRecord(extensionRegs, ?target = target)
            | Some baseTerm ->
                let rBase = compileTerm context false None baseTerm
                builder.ExtendRecord(rBase, extensionRegs, ?target = target)

        and compileSymbol (symbol: CoreSymbol) (context: CompilationContext) (isTail: bool) (target: Reg option) =
            let name = symbol.Symbol
            let children = symbol.Children
            let arity = List.length children

            match symbol with
            | { Symbol = "true"; Children = [] } ->
                MiscHelpers.markEvaluated (builder.LoadBool(true, ?target = target)) context

            | { Symbol = "false"; Children = [] } ->
                MiscHelpers.markEvaluated (builder.LoadBool(false, ?target = target)) context

            | { Symbol = "lazy"; Children = [ body ] } ->
                compileThunk context isTail body target

            | { Symbol = "force"; Children = [ expr ] } ->
                let thunkReg = compileTerm context isTail None expr
                let res = builder.Force(thunkReg, ?target = target)
                MiscHelpers.markEvaluated res context

            | { Symbol = "__buffer_alloc"; Children = [ sizeExpr ] } ->
                let sizeReg = compileTermStrict context None sizeExpr
                let res = builder.BufferAlloc(sizeReg, ?target = target)
                MiscHelpers.markEvaluated res context

            | { Symbol = "__buffer_get"; Children = [ bufExpr; indexExpr ] } ->
                let bufReg = compileTermStrict context None bufExpr
                let indexReg = compileTermStrict context None indexExpr
                let res = builder.BufferGet(bufReg, indexReg, ?target = target)
                MiscHelpers.markEvaluated res context

            | { Symbol = "__buffer_set"; Children = [ bufExpr; indexExpr; valExpr ] } ->
                let bufReg = compileTermStrict context None bufExpr
                let indexReg = compileTermStrict context None indexExpr
                let valReg = compileTermStrict context None valExpr

                builder.BufferSet(bufReg, indexReg, valReg) // in-place modification but still return the pointer

                let finalReg =
                    match target with
                    | Some t when t.Index <> bufReg.Index ->
                        emitMov (t, bufReg) context
                        t
                    | _ -> bufReg

                MiscHelpers.markEvaluated finalReg context

            | { Symbol = "__buffer_realloc"; Children = [ bufExpr; newSizeExpr ] } ->
                let bufReg = compileTermStrict context None bufExpr
                let newSizeReg = compileTermStrict context None newSizeExpr

                builder.BufferRealloc(bufReg, newSizeReg) // in-place modification but still return the pointer

                let finalReg =
                    match target with
                    | Some t when t.Index <> bufReg.Index ->
                        emitMov (t, bufReg) context
                        t
                    | _ -> bufReg

                MiscHelpers.markEvaluated finalReg context

            | { Symbol = "__buffer_length"; Children = [ bufExpr ] } ->
                let bufReg = compileTermStrict context None bufExpr
                let res = builder.BufferLength(bufReg, ?target = target)

                MiscHelpers.markEvaluated res context

            | { Symbol = "__buffer_to_string"; Children = [ bufExpr ] } ->
                let bufReg = compileTermStrict context None bufExpr
                let res = builder.BufferToString(bufReg, ?target = target)

                MiscHelpers.markEvaluated res context

            | { Symbol = "__string_to_buffer"; Children = [ strExpr ] } ->
                let strReg = compileTermStrict context None strExpr
                let res = builder.StringToBuffer(strReg, ?target = target)

                MiscHelpers.markEvaluated res context

            | _ ->

                // Arguments are prepared differently depending on the main strategy associated
                // with the different rules using the symbol as LHS.
                let inline argsRegs (strategy: Strategy) =
                    match strategy with
                    | (Strict | Memoize) ->
                        // Strict: everything is evaluated before the call (default behavior).
                        List.map (compileTermStrict context None) children

                    | Lazy ->
                        // Lazy: each argument is transformed into a Thunk.
                        List.map (fun child -> compileThunk context false child target) children

                    | (Outermost | Invalid) ->
                        // Outermost: each argument is reified in symbolic data.
                        List.map (compileAsData context) children

                let (resolvedName, isCaptureWithinContext) =
                    ContextResolution.resolveSymbolForContext context name arity

                if isCaptureWithinContext then
                    // Not a function call, but an "applicable" value
                    builder.LoadAtom(resolvedName)
                else
                    // Check in the FFI first
                    match context.Global.FFIRegistery.TryGetIndex(resolvedName) with
                    | Some ffiIndex ->
                        let strictArgs = List.map (compileTermStrict context None) children
                        builder.CallFFI(ffiIndex, strictArgs, ?target = target)

                    | None ->

                        let dp = context.Global.SymbolLabels
                        let resolvedInfo = DispatchTable.tryFindByNameArity (resolvedName, List.length children) dp

                        match resolvedInfo with
                        | Some (label, strategy) ->
                            if isTail then
                                builder.Tailcall(label, argsRegs strategy)
                                defaultArg target (Reg 0)
                            else
                                builder.Call(label, argsRegs strategy, ?target = target)

                        | None ->
                            let args =
                                match context.Strategy with
                                | Outermost ->
                                    // In the RHS of an outermost rule, we want to evaluate children
                                    // to allow function calls rather that a simple substitution.
                                    List.map (compileTerm context false None) children
                                | _ ->
                                    argsRegs context.Strategy

                            builder.AllocData(name, args, ?target = target)

        and compileSubstitution (substitution: CoreSubstitution) (context: CompilationContext) (target: Reg option) =
            let astReg = compileTermStrict context None substitution.InExpr

            let finalReg =
                substitution.Env
                |> List.fold (fun currentTreeReg (sym, valExpr) ->
                    let valReg = compileTermStrict context None valExpr
                    let atomReg = builder.LoadAtom(sym.Symbol)
                    let nextReg = builder.Alloc()

                    builder.Subst(nextReg, currentTreeReg, atomReg, valReg)
                    nextReg
                ) astReg

            match target with
            | Some t when t.Index <> finalReg.Index ->
                emitMov (t, finalReg) context
                t
            | _ -> finalReg

        and compileUsingContext (usingContext: CoreUsingContext) (context: CompilationContext) (isTail: bool) (target: Reg option) =
            let usingContextName = usingContext.Context

            let contextDependencies = ContextResolution.getContextDependencies program usingContextName
            let addedContextDependencies = usingContextName :: contextDependencies @ context.ActiveContexts
            let newCompilationContext = { context with ActiveContexts = addedContextDependencies }

            compileTerm newCompilationContext isTail target usingContext.Expr

        and compileFunctionalApplication (fa: FunctionalApplication) (context: CompilationContext) (target: Reg option) =
            let bReg = compileTerm context false None fa.Base
            let bStrict = builder.Force(bReg)
            let argsRegs = List.map (compileTerm context false None) fa.Arguments

            builder.Apply(bStrict, argsRegs, ?target = target)

        and compileUpdateVariable (name: string, value: CoreTerm) (context: CompilationContext) (target: Reg option) =
            match Map.tryFind name context.Env with
            | None -> failwithf "Cannot compile the variable update '%s'." name
            | Some varReg ->
                compileTerm context false (Some varReg) value |> ignore
                builder.Unit(?target = target)

        and compileLiteral (lit: CoreLiteral) (context: CompilationContext) (target: Reg option) =
            let reg =
                match lit with
                | Integer i -> builder.LoadInt (int i, ?target = target)
                | Float f -> builder.LoadFloat (f, ?target = target)
                | String s -> builder.LoadString (s, ?target = target)
                | Char c -> builder.LoadChar (c, ?target = target)

            MiscHelpers.markEvaluated reg context

        and compileVariable (name: string) (context: CompilationContext) (target: Reg option) =
            match Map.tryFind name context.Env with
            | Some r ->
                match target with
                | Some t when t.Index <> r.Index ->
                    emitMov (t, r) context
                    t
                | _ -> r
            | None -> failwithf "Variable '%s unfound." name

        and compileTerm (context: CompilationContext) (isTail: bool) (target: Reg option) (term: CoreTerm) =
            match term with
            | Intrinsic context target reg -> reg
            | Variable name -> compileVariable name context target
            | Literal lit -> compileLiteral lit context target
            | RecordExtend record -> compileRecordExtend record context target
            | CoreLet let' -> compileLet let' context target
            | Match match' -> compileMatch match' context isTail target
            | TermSequence terms -> compileTermSequence terms context isTail target
            | WhileLoop whileLoop -> compileWhileLoop whileLoop context target
            | Symbol symbol -> compileSymbol symbol context isTail target
            | FunctionalApplication fa -> compileFunctionalApplication fa context target
            | Closure closure -> compileClosure context closure.Parameters closure.Value isTail target
            | UpdateVariable(name, value) -> compileUpdateVariable (name, value) context target
            | Substitution sub -> compileSubstitution sub context target
            | UsingContext usingContext -> compileUsingContext usingContext context isTail target
            | _ -> failwithf "TODO: %s" (PrettyPrinter.prettyPrintExpr term)

        member public __.Compile() =

            let entryPointLabel =
                match DispatchTable.tryFindByNameArity ("main", 1) globalLabels with
                | Some (label, _) -> label
                | None ->
                    match DispatchTable.tryFindByNameArity ("main", 0) globalLabels with
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

                // if symbolName = "transpose_list" then
                //     Liyh.Core.DecisionTree.RenderDecisionTree.renderAndOpen tree

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

                let fallback mismatchTarget =

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
                            builder.AllocData(originalName, List.ofArray newArgs, ?target = mismatchTarget)

                    | _ ->
                        if tryFallbackToGlobal() then
                            // already jumped in `tryFallbackToGlobal`
                            builder.Alloc() // dummy
                        else
                            builder.AllocData(originalName, List.ofArray argRegs, ?target = mismatchTarget)

                let onMatch ruleIndex leafContext matchTarget =
                    let rule = rulesArray.[ruleIndex]
                    let localStrategy = Strategy.FromAST rule.Strategy

                    match localStrategy with
                    | Strategy.Invalid ->
                        let errorValReg = compileTerm leafContext false None rule.RHS
                        let errorStrReg = builder.PPShow(errorValReg)
                        let header = ColorTerm.colorize (ColorTerm.Color.Basic "red") "Invalid rule matched: "
                        let prefixReg = builder.LoadString header
                        let eolReg = builder.LoadString "\n"

                        let fullMsgReg = builder.ConcatMany [ prefixReg; errorStrReg; eolReg ]

                        builder.Print(fullMsgReg)
                        builder.Halt(1) // error
                        builder.Unit(?target = matchTarget)

                    | _ ->
                        compileTerm leafContext (symbolName <> "main") matchTarget rule.RHS

                let optimizedTree =
                    match tree with
                    | Switch(Root, cases, _) ->
                        let newTree = Map.tryFind (symbolName, arity) cases
                        Option.defaultValue tree newTree
                    | _ -> tree

                let result = compileTree context optimizedTree onMatch fallback None

                if symbolName = "main" then builder.Halt() // stop the program
                else builder.Ret(result)

                builder.FinalizeFunction(patchIndex, savedMaxStack)

            let dispatchTable = globalLabels
            builder.Compile(entryPointLabel, dispatchTable, ffiRegistery.Entries)

    /// Compiles a LiyhCore program into a LyVM's bytecode equivalent program.
    /// The `optimize` flag has no effect, for now.
    let public compile (ffiBindings: LiyhPackage.GlobalFFIBindings) (program: CoreProgram) =
        let compiler = new Compiler(ffiBindings, program)
        compiler.Compile()

