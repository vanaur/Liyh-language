namespace Liyh.LyVM

module public BytecodeCompiler =
    open System
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open Liyh.Core.DecisionTree.DecisionTreeCompiler

    type private GlobalContext =
        { SymbolLabels: Map<string * int, int> }    // (symbol/arity, label)

    type private CompilationContext =
        { Global: GlobalContext
          Env: Map<string, Reg>
          mutable PathCache: Map<Path, Reg>
          Args: Reg[] }

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

        let coreRules =
            program
            |> List.choose (function Rule r -> Some r | _ -> None)

        let getHeadSymbolAndArity (rule: CoreRule) =
            match rule.LHS with
            | Symbol { Symbol = s; Children = children } -> (s, List.length children)
            | _ -> failwith "??" // this may not happen

        let groupedRules =
            coreRules
            |> List.groupBy getHeadSymbolAndArity
            |> Map.ofList

        let globalLabels =
            groupedRules
            |> Map.map (fun _ _ -> freshLabel ())

        let globalContext =
            { SymbolLabels = globalLabels }

        let rec compilePath (context: CompilationContext) (path: Path) =
            match context.PathCache.TryGetValue path with
            | true, reg -> reg
            | false, _ ->
                let reg = 
                    match path with
                    | Root ->
                        failwith "Unresolved root path" // Doit être pré-rempli par compileTerm

                    | Child(Root, idx) when not (context.PathCache.ContainsKey Root) ->
                        if idx >= 0 && idx < context.Args.Length then
                            context.Args.[idx]
                        else
                            failwithf "Index out of bounds: %d (arity %d)" idx context.Args.Length
                    
                    | Child(parent, idx) ->
                        let parentReg = compilePath context parent
                        builder.Deconstruct(parentReg, idx)

                    | Field(parent, name) ->
                        let parentReg = compilePath context parent

                        let failLabel = freshLabel()
                        let successLabel = freshLabel()

                        let res = builder.GetField(parentReg, name, failLabel)

                        builder.Jump(successLabel)

                        builder.Scope(fun _ ->
                            builder.SetLabel(failLabel)
                            let msg = runtimeError $"Field '{name}' not found."
                            builder.Print(builder.LoadString msg)
                            builder.Halt()
                        )
                        
                        builder.SetLabel(successLabel)
                        res

                context.PathCache <- Map.add path reg context.PathCache
                reg

        // Utility function to convert a Boolean result (0/1) to Atom (true/false).
        let convertBoolToAtom (boolReg: Reg) =
            let resReg = builder.Alloc()
            let lblFalse = freshLabel()
            let lblEnd = freshLabel()
            
            builder.JumpFalse(boolReg, lblFalse)
            builder.Mov(resReg, builder.LoadAtom("true"))
            builder.Jump(lblEnd)
            
            builder.SetLabel(lblFalse)
            builder.Mov(resReg, builder.LoadAtom("false"))
            
            builder.SetLabel(lblEnd)
            resReg

        // Utility function to convert an Atom (true/false) to a Boolean (0/1).
        let convertAtomToBool (atomReg: Reg) =
            let resReg = builder.Alloc()
            let trueAtom = builder.LoadAtom("true")
            let cmpRes = builder.Eq(atomReg, trueAtom)

            builder.Mov(resReg, cmpRes)
            resReg

        let arithmeticIntrinsics =
            [| "__internal_add"
               "__internal_sub"
               "__internal_mul"
               "__internal_div"
               "__internal_mod" |]

        let booleanIntrinsics =
            [| "__internal_eq"
               "__internal_neq"
               "__internal_le"
               "__internal_leq"
               "__internal_ge"
               "__internal_geq" |]

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

            // --- Intrinsics --- //

            | Symbol { Symbol = op; Children = [left; right] } 
                when Set.contains op (Set.ofArray arithmeticIntrinsics) ->

                let rLeft = compileTerm context false left
                let rRight = compileTerm context false right

                match op with
                | "__internal_add" -> builder.Add(rLeft, rRight)
                | "__internal_sub" -> builder.Sub(rLeft, rRight)
                | "__internal_mul" -> builder.Mul(rLeft, rRight)
                | "__internal_div" -> builder.Div(rLeft, rRight)
                | "__internal_mod" -> builder.Mod(rLeft, rRight)
                | _ -> failwith "??" // This may not happens

            | Symbol { Symbol = op; Children = [left; right] } 
                when Set.contains op (Set.ofArray booleanIntrinsics) ->

                let rLeft = compileTerm context false left
                let rRight = compileTerm context false right

                let cmpRes = 
                    match op with
                    | "__internal_eq"  -> builder.Eq(rLeft, rRight)
                    | "__internal_neq" -> builder.NotEqual(rLeft, rRight)
                    | "__internal_le"  -> builder.Le(rLeft, rRight)
                    | "__internal_leq" -> builder.Leq(rLeft, rRight)
                    | "__internal_ge"  -> builder.Ge(rLeft, rRight)
                    | "__internal_geq" -> builder.Geq(rLeft, rRight)
                    | _ -> failwith "??" // This may not happens

                convertBoolToAtom cmpRes

            | Symbol { Symbol = "__internal_print"; Children = [x] } ->
                let xReg = compileTerm context false x
                builder.Print(xReg)
                builder.LoadAtom("unit")

            | Symbol { Symbol = "__internal_strcat"; Children = [left; right] } ->
                let rLeft = compileTerm context false left
                let rRight = compileTerm context false right
                builder.StrCat(rLeft, rRight)

            | Symbol { Symbol = "__internal_ppshow"; Children = [term] } ->
                let r = compileTerm context false term
                builder.PPShow(r)

            // --- --- //

            | Symbol { Symbol = name; Children = children } ->
                let childRegs = List.map (compileTerm context false) children

                match Map.tryFind (name, List.length children) context.Global.SymbolLabels with
                | Some label ->
                    if isTail then
                        builder.Tailcall(label, childRegs)
                        Reg 0 // dummy
                    else
                        builder.Call(label, childRegs)
                | None ->
                    builder.AllocData(name, childRegs)

            | FunctionalApplication { Base = b; Arguments = args } ->
                let bReg = compileTerm context false b
                let argsRegs = List.map (compileTerm context false) args

                builder.Apply(bReg, argsRegs)

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
                            Args = Array.ofList argRegs
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
                    | [] -> builder.LoadAtom("unit") // dummy
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

                                let msg1 = builder.LoadString $"The `let` case was incomplete. Expected pattern `{expected}`, but got `"
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
                    builder.LoadAtom("unit")

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
                builder.LoadAtom("unit")

            | CoreLet { Pattern = Variable _; Value = value } ->
                compileTerm context false value |> ignore
                builder.LoadAtom("unit") // dummy

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
                    builder.LoadAtom("unit")

                let onMismatch () =
                    let gotReg = builder.PPShow valReg
                    let expected = PrettyPrinter.prettyPrintExpr pattern

                    let msg1 = builder.LoadString $"The `let` case was incomplete. Expected pattern `{expected}`, but got `"
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

                    let msg1 = builder.LoadString $"The `match` case was incomplete. Expected one of the following patterns:\n{patternsList}{extraMsg}\n\nbut got `"
                    let msg2 = builder.LoadString "` instead."

                    let finalMsg = builder.ConcatMany([msg1; gotReg; msg2])
                    builder.RuntimeError finalMsg

                builder.Scope(fun () ->
                    let matchContext = { context with PathCache = Map.ofList [(Root, toMatchReg)] }
                    compileTree matchContext tree onMatch onMismatch
                )

            | _ -> failwithf "TODO: %s" (PrettyPrinter.prettyPrintExpr term)

        and tryCompileIntrinsicBool (context: CompilationContext) (term: CoreTerm) =
            match term with
            | Symbol { Symbol = op; Children = [left; right] }
                when Set.contains op (Set.ofArray booleanIntrinsics) ->

                let rLeft = compileTerm context false left
                let rRight = compileTerm context false right

                let rawResult = 
                    match op with
                    | "__internal_eq"  -> builder.Eq(rLeft, rRight)
                    | "__internal_neq" -> builder.NotEqual(rLeft, rRight)
                    | "__internal_le"  -> builder.Le(rLeft, rRight)
                    | "__internal_leq" -> builder.Leq(rLeft, rRight)
                    | "__internal_ge"  -> builder.Ge(rLeft, rRight)
                    | "__internal_geq" -> builder.Geq(rLeft, rRight)
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

                builder.Scope(fun () ->
                    let phiReg = builder.Alloc() 

                    for KeyValue((tag, _), subTree) in cases do
                        let nextLbl = freshLabel()
                        builder.TestTag(pathReg, tag, nextLbl)
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
                        
                        let eq = builder.Eq(pathReg, litReg)
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
                    let trueAtom = builder.LoadAtom("true") 
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

                builder.Scope(fun () ->
                    for KeyValue(t, subTree) in cases do
                        let nextLbl = freshLabel()
                        
                        match t with
                        | TRecord -> builder.TestRecord(pathReg, nextLbl) 
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

        builder.Comment("                                                                                 ;")
        builder.Comment(" Bytecode generated by Liyh's Compiler (version 0.1.1). 🐿️                       ;")
        builder.Comment(" This textual representation is for information only and is not usable as such.  ;")
        builder.Comment("                                                                                 ;\n")

        for KeyValue((symbolName, arity) as key, rules) in groupedRules do
            let label = globalLabels.[key]
            builder.CommentNewLine($"--- {symbolName}/{arity} ---\n")
            builder.SetLabel(label)

            let (argRegsList, patchIndex, savedMaxStack) = builder.DefineFunction(arity)
            let argRegs = Array.ofList argRegsList
            let rulesArray = Array.ofList rules
            let tree = DecisionTreeCompiler.compileRules rulesArray
            let bodies = rulesArray |> Array.map _.RHS

            let context =
                { Global = globalContext
                  Env = Map.empty
                  PathCache = Map.empty
                  Args = argRegs }

            let fallback () =
                builder.AllocData(symbolName, List.ofArray argRegs)
            
            let onMatch ruleIndex leafContext =
                compileTerm leafContext (symbolName <> "main") bodies.[ruleIndex]

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

        let entryPointLabel =
            match Map.tryFind ("main", 0) globalLabels with
            | Some l -> l
            | None ->
                match Map.tryFind ("main", 1) globalLabels with
                | Some l -> l
                | None -> failwith "No entry point (main) found."

        let dispatchTable = globalLabels

        builder.Compile(entryPointLabel, dispatchTable)
        |> if optimize then Optimize.apply else id
