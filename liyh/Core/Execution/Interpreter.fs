namespace Liyh.Core.Execution.Core

//
// An interpreter for 'LiyhCore', i.e., a minimal (~ desugared) intermediate representation of Liyh. 🐿️
//
// The interpreter is naive and comparable to a tree walk, but adapted and designed primarily with the
// symbolic rewriting model in mind:
//
//      the symbols are first class, and the rules are applied by "trial and error" (each
//      applicable rule is tested on the term to be reduced, building a pattern matching
//      and substitution environment at each test), the rewrites are chained together until
//      nothing more can be reduced given the rewriting model defined for the language.
//
// The only two optimizations made are the indexing of rules (each rule with a common header is grouped
// together and terms that do not have this header are not tested for rewriting) and loops are implemented
// in a tail-recursive manner, so as to never overflow the program stack. The interpreter struggles with
// large programs and becomes slow when performing multiple recursive tasks or creating intermediate
// objects (memory management is left to the host language's garbage collector, F#).
//
// The interpreter is therefore quite slow and clearly not suitable for real use as is (except perhaps in
// REPL), but it provides a first approach to using and testing the language and its features.
//

//
// TODO (interpreter-side only):
//  - outermost evaluation & matching
//  - effects & handlers
//  - track deep recursion
//

module Interpreter =
    open System.Collections.Generic
    open System.Runtime.InteropServices
    open Liyh.FFI.CFFI
    open Liyh.Core.Execution.FFI
    open Liyh.Core
    open Liyh.Core.DecisionTree
    open Liyh.Core.Helper
    open Liyh.Core.Builtin
    open Liyh.Utils.ErrorReporter

    exception private InvalidRuleException of string
    exception private VariableToUpdateNotFoundException of string
    exception private WhenClauseException of got: string
    exception private NonApplicationSymbolException of string
    exception private CyclicBindingException of string
    exception private FreeVariableException of string
    exception private PatternMatchFailedException of got: string * expected: string * where: string
    exception private NotBaseRecordException of string
    exception private WhileLoopPredicateException of string
    exception private UncompletePatternMatchingException of string
    exception private ArityMismatchException of int * int * string
    exception private NonUnitFinalizerException of got: string
    exception private UnboundExternalFunctionException of lib: string * fn: string

    #if DEBUG
    let private maxRecursionDepth = 443
    #else
    let private maxRecursionDepth = 1399
    #endif

    /// For debugging purpose, count each call to a specific rule.
    let mutable private ruleCallCounts = Dictionary<string * int, int>()

    /// For rules marked as `memoized`.
    let mutable private memoizedRules = Dictionary<CoreTerm, CoreTerm>()

    /// For the fast-path symbol handling of passive symbols.
    let private passiveSymbolsCache = Dictionary<string, bool>()

    /// Optimised mapping utility: if no elements change physically, the original list is returned.
    /// This avoids creating thousands of new symbols that are unnecessary for the Garbage Collector.
    let private physicalMap (f: 'a -> 'a) (l: 'a list) =
        let rec scan l =
            match l with
            | [] -> ValueNone
            | x :: xs ->
                let x' = f x
                if LanguagePrimitives.PhysicalEquality x x' then scan xs
                else ValueSome (x', xs)

        match scan l with
        | ValueNone -> l
        | ValueSome (x', rest) ->
            let rec mapRest = function
                | [] -> []
                | y :: ys -> f y :: mapRest ys
            x' :: mapRest rest

    /// Display a table that shows how many time a given symbol was invoked.
    let private printRuleCallCounts (ruleCallCounts: IDictionary<(string * int), int>) =
        if ruleCallCounts.Count = 0 then () else
        let data = ruleCallCounts |> Seq.toList |> List.sortByDescending (function KeyValue (_, c) -> c)
        let maxLen = data |> Seq.map (fun (KeyValue((s, a), _)) -> sprintf "%s/%d" s a |> String.length) |> Seq.max
        let headerLabel = "Symbol/arity"
        let headerCount = "Count"
        printfn "\n%s" (String.replicate (maxLen + headerCount.Length + 3) "-")
        printfn "%-*s   %s" maxLen headerLabel headerCount
        printfn "%s" (String.replicate (maxLen + headerCount.Length + 3) "-")
        for KeyValue((s, a), c) in data do
            let label = sprintf "%s/%d" s a
            let formattedCount = c.ToString("N0", System.Globalization.CultureInfo.InvariantCulture).Replace(",", "'")
            printfn "%-*s   %s" maxLen label formattedCount
        printfn "%s\n" (String.replicate (maxLen + headerCount.Length + 3) "-")

    module private Map =

        /// Combine the two maps and overwrite the values of `m1` with those of `m2` if there is a conflict.
        let public crushingMerge (m1: Map<'a, 'b>) (m2: Map<'a, 'b>) =
            Map.fold (fun s k v -> Map.add k v s) m1 m2

    type private Substitution = Map<string, CoreTerm>

    type HandlerEnvironment =
        { HandlerName: string
          Handlers: CoreHandler array
          HandlerState: CoreTerm
          Resumed: bool }

    type RunningState =
        { VariableEnvironments: Substitution list
          RecursionDepth: int
          HandlerEnvironment: Map<string, HandlerEnvironment> }

        static member Empty =
            { VariableEnvironments = List.empty
              HandlerEnvironment = Map.empty
              RecursionDepth = 0 }

    exception private ZeroShot of {| Result: CoreTerm; FinalState: RunningState |}

    module private Environment =

        /// Retrieves the variable given in the running state if found.
        let inline public lookupVariable (name: string) (state: RunningState) =
            state.VariableEnvironments
            |> List.tryPick (Map.tryFind name)

        /// Returns a new running state after modifying the value of the given variable,
        /// or throws an exception if the variable is not found.
        let public updateVariable (name: string) (value: CoreTerm) (state: RunningState) =
            let rec loop prefix = function
                | [] -> raise (VariableToUpdateNotFoundException name)
                | env :: rest ->
                    if Map.containsKey name env then
                        let updatedEnv = Map.add name value env
                        List.rev prefix @ (updatedEnv :: rest)
                    else
                        loop (env :: prefix) rest

            let updatedEnvironments = loop [] state.VariableEnvironments
            { state with VariableEnvironments = updatedEnvironments }

        /// Returns a new running state after adding a scope to the environment.
        let inline public pushVariableScope (state: RunningState) =
            { state with VariableEnvironments = Map.empty :: state.VariableEnvironments }

        /// Returns a new running state after removing the last added scope, if it exists, otherwise throws an exception.
        let inline public popVariableScope (state: RunningState) =
            match state.VariableEnvironments with
            | [] -> failwith "Cannot pop from empty environment stack"
        //    | [_] -> failwith "Cannot pop the global environment"
            | _ :: rest -> { state with VariableEnvironments = rest }

        /// Returns a new running state after adding a binding. New bindings overwrite old ones.
        let inline public addBindings (bindings: Substitution) (state: RunningState) =
            match state.VariableEnvironments with
            | [] -> failwith "No environment to bind to"
            | currentEnv :: rest ->
                let newEnv = Map.crushingMerge currentEnv bindings
                { state with VariableEnvironments = newEnv :: rest }

        /// Evaluates `action` within a scoped environment where the given bindings have been added.
        /// After the evaluation, the variable environment is popped, and the result of `action` return.
        let inline public withinScope
            (state: RunningState)
            (subst: Substitution option)
            (action: RunningState -> CoreTerm -> RunningState * CoreTerm)
            (term: CoreTerm option)
            =
            let term = Option.defaultValue (simpleSymbol "unit") term
            let scopedState = pushVariableScope state
            let boundState = Option.map (fun a -> addBindings a scopedState) subst |> Option.defaultValue scopedState
            let newState, result = action boundState term
            let poppedState = popVariableScope newState
            poppedState, result

    type private GlobalEnvironment =
        { RulesMap: Map<string, CoreRule array>
          HandlersMap: Map<string, CoreHandler array * CoreHandler option>
          DecisionTree: Map<string, DecisionTree.DecisionTree>
          ExternLibraries: Map<string, DynLib * Map<string, FunctionSignature>> }

        member inline public this.GetExternLibrary (term: CoreTerm) =
            match term with
            | Symbol { Symbol = symbol } as symb ->
                this.ExternLibraries
                |> Map.tryPick (fun qualifier value ->
                    if symbol.StartsWith(qualifier + ".") then Some value
                    else None)
            | _ -> None

        member inline public this.GetDecisionTree (term: CoreTerm) =
            match term with
            | Symbol { Symbol = symbol } -> Map.tryFind symbol this.DecisionTree
            | _ -> None

        member inline public this.GetRelevantRules (term: CoreTerm) =
            match term with
            | Symbol { Symbol = symbol } when Map.containsKey symbol this.RulesMap -> this.RulesMap.[symbol]
            | _ -> Array.empty

        member inline public this.HasOutermostRules (term: CoreTerm) =
            term
            |> this.GetRelevantRules
            |> Array.exists _.Strategy.IsOutermost

        member inline public this.GetRelevantHandlers (handler: string) =
            Map.tryFind handler this.HandlersMap
            |> Option.defaultValue (Array.empty, None)

    /// Builds the global runtime environment based on the given definitions.
    let private buildGlobalEnvironment (defs: CoreDefinition seq) =

        let inline projectSymbol (lhs: CoreTerm) =
            match lhs with
            | Symbol { Symbol = s } -> s
            | _ -> failwith "expected symbol on LHS"

        let inline addRule (rm: Map<string, CoreRule list>) (r: CoreRule) =
            let sym = projectSymbol r.LHS
            let updated = r :: (Map.tryFind sym rm |> Option.defaultValue [])
            Map.add sym updated rm

        let inline addHandler (hm: Map<string, CoreHandler list>) (h: CoreHandler) =
            let updated = h :: (Map.tryFind h.HandlerName hm |> Option.defaultValue [])
            Map.add h.HandlerName updated hm

        let inline addExtern (ex: Map<string, DynLib * Map<string, FunctionSignature>>) (e: CoreExtern) =
            Map.add e.LibraryName (e.Library, e.Functions) ex

        let rmInit: Map<string, CoreRule list> = Map.empty
        let hmInit: Map<string, CoreHandler list> = Map.empty
        let exInit: Map<string, DynLib * Map<string, FunctionSignature>> = Map.empty

        let rulesLists, handlersLists, externLibraries =
            defs
            |> Seq.fold (fun (rm, hm, ex) ->
                function
                | Rule r -> addRule rm r, hm, ex
                | Handler h -> rm, addHandler hm h, ex
                | Extern e -> rm, hm, addExtern ex e

            ) (rmInit, hmInit, exInit)

        let inline finalizer (v: CoreHandler list) =
            match List.partition (fun h -> h.LHS.IsWildcard) v with
            | [], others -> Array.ofList others, None
            | f :: _, others -> Array.ofList others, Some f

        let rulesMap = rulesLists |> Map.map (fun _ v -> v |> List.rev |> List.toArray)
        //let handlersMap = handlersLists |> Map.map (fun _ v -> (v |> List.rev |> List.toArray), None)
        let handlersMap = handlersLists |> Map.map (fun _ -> finalizer)
        let decisionTree = rulesMap |> Map.map (fun _ -> DecisionTreeCompiler.compileRules)

        { RulesMap = rulesMap
          HandlersMap = handlersMap
          DecisionTree = decisionTree
          ExternLibraries = externLibraries }

    /// Experimental pattern matching via decision tree for rules.
    module private DecisionTreeEvaluation =

        type public MatchResult =
            | Success of ruleIndex: int * bindings: Map<string, CoreTerm>
            | Failure

        let rec public eval
            (state: RunningState)
            (normalize: RunningState -> CoreTerm -> RunningState * CoreTerm)
            (tree: DecisionTree.DecisionTree)
            (term: CoreTerm)
            (currentBindings: Substitution)
            =

            let evalRecursive = eval state normalize

            match tree with
            | Fail -> Failure
            
            | Leaf(ruleIndex, pathBindings) ->
                let finalBindings =
                    pathBindings
                    |> Map.fold (fun acc varName path ->
                        let value = PathAccess.access path term
                        Map.add varName value acc) currentBindings

                Success(ruleIndex, finalBindings)

            | Switch(path, cases, defaultCase) ->
                let accessedTerm = PathAccess.access path term
                match accessedTerm with
                | Symbol { Symbol = sym; IsVariable = false; Children = children } ->
                    let arity = children.Length
                    match Map.tryFind (sym, arity) cases with
                    | Some subtree -> evalRecursive subtree term currentBindings
                    | None -> 
                        defaultCase 
                        |> Option.map (fun subtree -> evalRecursive subtree term currentBindings)
                        |> Option.defaultValue Failure
                | _ ->
                    defaultCase 
                    |> Option.map (fun subtree -> evalRecursive subtree term currentBindings)
                    |> Option.defaultValue Failure

            | SwitchLiteral(path, cases, defaultCase) ->
                let accessedTerm = PathAccess.access path term
                match accessedTerm with
                | Literal lit ->
                    match Map.tryFind lit cases with
                    | Some subtree -> evalRecursive subtree term currentBindings
                    | None ->
                        defaultCase
                        |> Option.map (fun subtree -> evalRecursive subtree term currentBindings)
                        |> Option.defaultValue Failure
                | _ ->
                    defaultCase
                    |> Option.map (fun subtree -> evalRecursive subtree term currentBindings)
                    |> Option.defaultValue Failure

            | ArityCheck(path, expectedArity, success, failure) ->
                match PathAccess.access path term with
                | Symbol { Children = children } when children.Length = expectedArity ->
                    evalRecursive success term currentBindings
                | _ ->
                    match failure with
                    | Some subtree -> evalRecursive subtree term currentBindings
                    | None -> Failure

            | TypeCheck(path, cases, defaultCase) ->
                let termType =
                    match PathAccess.access path term with
                    | Symbol _ -> TSymbol
                    | Variable _ -> TVariable
                    | Literal (Integer _) -> TLiteral TInteger
                    | Literal (Float _) -> TLiteral TFloat
                    | Literal (String _) -> TLiteral TString
                    | Literal (Char _) -> TLiteral TChar
                    | Closure _ -> TClosure
                    | RecordExtend _ -> TRecord
                    | Wildcard -> TWildcard
                    | _ -> TWildcard

                match Map.tryFind termType cases with
                | Some subtree -> evalRecursive subtree term currentBindings
                | None ->
                    defaultCase
                    |> Option.map (fun subtree -> evalRecursive subtree term currentBindings)
                    |> Option.defaultValue Failure

            | Bind(varName, path, continuation) ->
                let value = PathAccess.access path term
                match Map.tryFind varName currentBindings with
                | Some existingValue when existingValue = value -> evalRecursive continuation term currentBindings
                | Some _ -> Failure
                | None ->
                    let newBindings = Map.add varName value currentBindings
                    evalRecursive continuation term newBindings

            | WhenGuard(guard, pathBindings, success, failure) ->
                let guardBindings =
                    pathBindings
                    |> Map.fold (fun acc varName path ->
                        let value = PathAccess.access path term
                        Map.add varName value acc) currentBindings

                match evalGuard state normalize guard guardBindings with
                | true -> evalRecursive success term currentBindings
                | false ->
                    match failure with
                    | Some subtree -> evalRecursive subtree term currentBindings
                    | None -> Failure

        and private evalGuard
            (state: RunningState)
            (normalize: RunningState -> CoreTerm -> RunningState * CoreTerm)
            (guard: CoreTerm)
            (bindings: Substitution) =

            let _, result = Environment.withinScope state (Some bindings) normalize (Some guard)

            match result with
            | SymbolTrue -> true
            | SymbolFalse -> false
            | other -> raise (WhenClauseException(PrettyPrinter.prettyPrintExpr other))

    /// Substitution for outermost rules.
    let rec private substitute (env: Substitution) (term: CoreTerm) : CoreTerm =
        match term with
        | (Literal _ | Wildcard) -> term
        | Variable v ->
            match Map.tryFind v env with
            | Some t -> t
            | None -> term

        | Symbol s -> copySymbolWithNewChildren s (List.map (substitute env) s.Children)

        | RecordExtend { BaseRecord = br; Extension = ext } ->
            RecordExtend {
                BaseRecord = br |> Option.map (substitute env)
                Extension = List.map (fun (k, v) -> k, substitute env v) ext }

        | Match matchTerm ->
            Match {
                ToMatch = substitute env matchTerm.ToMatch
                Cases = List.map (fun (pat, body) -> substitute env pat, substitute env body) matchTerm.Cases }

        | Closure c ->
            Closure {
                c with 
                    Value = substitute env c.Value
                    Env = Map.map (fun _ v -> substitute env v) c.Env }

        | FunctionalApplication { Base = f; Arguments = args } ->
            FunctionalApplication {
                Base = substitute env f
                Arguments = List.map (substitute env) args }

        | TermSequence terms ->
            TermSequence (List.map (substitute env) terms)

        | CoreLet letTerm ->
            CoreLet {
                letTerm with
                    Pattern = substitute env letTerm.Pattern
                    Value = substitute env letTerm.Value }

        | WhileLoop whileTerm ->
            WhileLoop {
                Predicate = substitute env whileTerm.Predicate
                Body = substitute env whileTerm.Body }

        | UpdateVariable(name, value) ->
            UpdateVariable(name, substitute env value)

        | Handle handleTerm ->
            Handle {
                Handler = handleTerm.Handler
                State = substitute env handleTerm.State
                ToHandle = substitute env handleTerm.ToHandle }

        | Resume resumeTerm ->
            Resume {
                FromHandler = resumeTerm.FromHandler
                State = substitute env resumeTerm.State
                Rewrite = substitute env resumeTerm.Rewrite }

        | AsClause(p, v) -> AsClause(substitute env p, v)
        | WhenClause(p, w) -> WhenClause(substitute env p, substitute env w)

    let mutable private whenClauseStack = Set.empty<CoreTerm>

    let rec private matchTerm
        (state: RunningState)
        (globalEnv: GlobalEnvironment)
        (pattern: CoreTerm)
        (subject: CoreTerm)
        (subst: Substitution)
        =
        let matchTerm pattern subject = matchTerm state globalEnv pattern subject

        match pattern, subject with
        | p, s when p = s -> Some subst
        | Wildcard, _ -> Some subst

        | Variable v, _ ->
            match subst.TryGetValue v with
            | true, term -> if term = subject then Some subst else None
            | _ -> Some (Map.add v subject subst)

        | AsClause(a, b), subject ->
            matchTerm a subject subst
            |> Option.bind (fun m1 ->
                   matchTerm b subject subst
                   |> Option.map (fun m2 -> Map.crushingMerge m1 m2))

        | WhenClause(a, b), c ->
            match matchTerm a c subst with
            | None -> None
            | Some subst' ->
                if whenClauseStack.Contains b then
                    None // Cycle detected in the when-clause, pattern failure
                else
                    whenClauseStack <- whenClauseStack.Add b
                    try
                        match checkWhenClause state globalEnv subst' (Some b) with
                        | true -> Some subst'
                        | false -> None
                    finally
                        // As it stands, the `try-finally` is unnecessary, but in case of doubt where the exception
                        // is caught and the interpreter is restarted, this is the step that must be taken.
                        whenClauseStack <- whenClauseStack.Remove b

        | Symbol s1, Symbol s2 when s1.Children.Length = s2.Children.Length ->
            let rec matchChildren i subst =
                if i >= s1.Children.Length then Some subst
                else
                    matchTerm s1.Children.[i] s2.Children.[i] subst
                    |> Option.bind (matchChildren (i + 1))

            let parent =
                if s1.IsVariable then
                    match subst.TryGetValue s1.Symbol with
                    | true, term -> if term = subject then Some subst else None
                    | _ -> Some (Map.add s1.Symbol (copySymbolWithNewChildren s1 []) subst)

                else
                    if s1.Symbol = s2.Symbol then Some subst
                    else None

            let children = matchChildren 0
            Option.bind children parent

        | RecordExtend { BaseRecord = None; Extension = fs }, RecordExtend { BaseRecord = None; Extension = fs' } ->
            let rec matchFields fs mapFs subst =
                match fs with
                | [] -> Some subst
                | (name, field) :: rest ->
                    match Map.tryFind name mapFs with
                    | Some field' -> matchTerm field field' subst |> Option.bind (matchFields rest mapFs)
                    | None -> None

            let mapFs = Map.ofList fs'
            matchFields fs mapFs subst

        | Closure clo1, Closure clo2 ->
            if clo1.Parameters <> clo2.Parameters || clo1.Env.Count <> clo2.Env.Count then None
            else
                match matchTerm clo1.Value clo2.Value subst with
                | None -> None
                | Some subst' ->
                    Map.toArray clo1.Env
                    |> Array.fold (fun acc (k, v1) ->
                        acc |> Option.bind (fun substAcc ->
                            match Map.tryFind k clo2.Env with
                            | Some v2 -> matchTerm v1 v2 substAcc
                            | None -> None)) (Some subst')

        | FunctionalApplication { Base = f1; Arguments = args1 }, FunctionalApplication { Base = f2; Arguments = args2 } ->
            match matchTerm f1 f2 subst with
            | None -> None
            | Some subst' ->
                if args1.Length <> args2.Length then None
                else List.fold2 (fun acc a1 a2 -> Option.bind (matchTerm a1 a2) acc) (Some subst') args1 args2

        | _ -> None

    and private checkWhenClause
        (state: RunningState)
        (globalEnv: GlobalEnvironment)
        (subst: Substitution)
        (wc: CoreTerm option)
        =
        match wc with
        | None -> true
        | Some wc ->
            match Environment.withinScope state (Some subst) (fun s _ -> s, normalize s globalEnv wc) None with
            | _, SymbolTrue -> true
            | _, SymbolFalse -> false
            | _, other -> raise (WhenClauseException(PrettyPrinter.prettyPrintExpr other))

    and private normalize (state: RunningState) (globalEnv: GlobalEnvironment) (term: CoreTerm) =

        //
        // Outermost vs Innermost evaluation strategy:
        //
        // The interpreter uses two distinct evaluation strategies that are selected based on rule annotations:
        //
        // 1. Outermost-first strategy (top-down):
        //    - When a symbol has at least one outermost rule, the entire subtree is evaluated using outermost-first strategy
        //    - Rules are applied to the unevaluated term first, without evaluating children
        //    - If no rule applies, children are recursively evaluated using the same outermost-first strategy
        //    - After child evaluation, outermost rules are tried again on the reconstructed term
        //    - Only if no outermost rule applies even after child evaluation, it falls back to innermost strategy
        //
        // 2. Innermost-first strategy (bottom-up):
        //    - Used when no outermost rules exist for a symbol
        //    - Children are evaluated first (recursively, using their appropriate strategies)
        //    - Rules are applied to the fully evaluated term
        //
        // The main evaluation loop dynamically selects the appropriate strategy based on the presence of outermost rules.
        // This should preserves lexical scoping while allowing both strategies to coexist in the same program.
        //

        let rec loop (state: RunningState) (term: CoreTerm) =
            if term.IsSymbol
            then (if globalEnv.HasOutermostRules term then loopOutermost else loopInnermost) state term
            else loopInnermost state term

        and loopInnermost (state: RunningState) (term: CoreTerm) =
            let inline processNormalize () =
                match term with

                // Early return from the loop for irreducible terms
                | Literal _ -> (state, term)
                | Closure { IsEvaluated = true } -> state, term

                | Closure closure ->
                    let evaluatedEnv = Map.map (fun _ v -> snd (loop state v)) closure.Env
                    let evaluatedClosure = Closure { closure with Env = evaluatedEnv; IsEvaluated = true }
                    (state, evaluatedClosure)

                | Variable v ->
                    match Environment.lookupVariable v state with
                    | Some value when value = term -> raise (CyclicBindingException v) //(state, term)
                    | Some value -> loop state value
                    | None -> raise (FreeVariableException v) //(state, term)

                | CoreLet l ->
                    let state', evaluatedValue = loop state l.Value

                    match matchTerm state globalEnv l.Pattern evaluatedValue Map.empty with
                    | None ->
                        let got = PrettyPrinter.prettyPrintExpr term
                        let expected = PrettyPrinter.prettyPrintExpr l.Pattern
                        raise (PatternMatchFailedException (got, expected, "let-expression"))

                    | Some bindings ->
                        let newState = Environment.addBindings bindings state'
                        (newState, simpleSymbol "unit")

                | TermSequence terms ->
                    Environment.withinScope state None (fun scopedState _ ->
                        let mutable currentState = scopedState
                        let mutable lastResult = simpleSymbol "unit"

                        for term in terms do
                            let newState, result = loop currentState term
                            currentState <- newState
                            lastResult <- result

                        currentState, lastResult
                    ) None

                | RecordExtend { BaseRecord = Some baseRecord; Extension = extensionFields } ->
                    let state', evaluatedBaseRecord = loop state baseRecord
                    match evaluatedBaseRecord with
                    | RecordExtend { BaseRecord = None; Extension = originalFields } ->
                        let map1 = Map.ofList extensionFields
                        let map2 = Map.ofList originalFields
                        let map3 = Map.crushingMerge map2 map1
                        let map3 = Map.map (fun _ -> loop state >> snd) map3
                        (state', RecordExtend { BaseRecord = None; Extension = Map.toList map3 })

                    | other -> raise (NotBaseRecordException (PrettyPrinter.prettyPrintExpr other))

                | RecordExtend { BaseRecord = None; Extension = fields } ->
                    let evaluatedFields = fields |> List.map (fun (a, b) -> a, snd (loop state b))
                    state, RecordExtend { BaseRecord = None; Extension = evaluatedFields }

                | FunctionalApplication { Base = func; Arguments = args } ->
                    let state1, normalizedFunc = loop state func
                    let finalState, normalizedArgs =
                        List.foldBack (fun arg (currentState, argAcc) ->
                            let newState, normalizedArg = loop currentState arg
                            (newState, normalizedArg :: argAcc)
                        ) args (state1, [])

                    match normalizedFunc with
                    | Closure closure ->
                        applyClosure closure normalizedArgs state

                    | Symbol s ->   // TODO: handle outermost also here?
                        let newSymbol = copySymbolWithNewChildren s (s.Children @ normalizedArgs)
                        let _, result = applyRules finalState newSymbol
                        (finalState, result)

                    | Variable v ->
                        let varSymbol = variableSymbol v normalizedArgs
                        let _, result = applyRules finalState varSymbol
                        (finalState, result)

                    | _ ->
                        raise (NonApplicationSymbolException (PrettyPrinter.prettyPrintExpr normalizedFunc))

                | UpdateVariable(variable, value) ->
                    let _, evaluatedValue = loop state value
                    (Environment.updateVariable variable evaluatedValue state, simpleSymbol "unit")

                | WhileLoop whileLoop ->

                    let rec loopExecution currentState =
                        let newState, predResult = loop currentState whileLoop.Predicate
                        match predResult with
                        | SymbolTrue ->
                            let bodyState, _ = loop newState whileLoop.Body
                            loopExecution bodyState

                        | SymbolFalse -> (newState, simpleSymbol "unit")
                        | other -> raise (WhileLoopPredicateException (PrettyPrinter.prettyPrintExpr other))

                    loopExecution state

                | Match match' ->
                    let toMatch = snd (loop state match'.ToMatch) // innermost/strict

                    let inline chooser (pattern, value) =
                        matchTerm state globalEnv pattern toMatch Map.empty
                        |> Option.map (fun subst -> subst, value)

                    match List.tryPick chooser match'.Cases with
                    | None -> raise (UncompletePatternMatchingException (PrettyPrinter.prettyPrintExpr toMatch))
                    | Some (bindings, rewrite) -> Environment.withinScope state (Some bindings) loop (Some rewrite)

                | Symbol s -> processSymbol state s

                | Handle handle -> processHandle state handle
                | Resume resume -> processResume state resume

                | _ ->
                    // Unevaluated value and unchanged state
                    (state, term)

            processNormalize()

        and loopOutermost (state: RunningState) (term: CoreTerm) =

            let rec applyAndContinue state term rules =
                let newState, newTerm = applyGivenRules state term rules
                if newTerm <> term then loopOutermost newState newTerm
                else newState, newTerm

            match term with
            | Symbol s ->
                let rules = globalEnv.GetRelevantRules term
                if globalEnv.HasOutermostRules term then
                    let state1, term1 = applyAndContinue state term rules
                    if term1 <> term then state1, term1
                    else
                        let children = List.map (loopOutermost state1 >> snd) s.Children
                        let newTerm = copySymbolWithNewChildren s children
                        applyAndContinue state1 newTerm rules
                else
                    loopInnermost state term

            | _ ->
                loopInnermost state term

        and processHandle (state: RunningState) (handle: CoreHandle) =
            match globalEnv.GetRelevantHandlers handle.Handler with
            | [||], _ -> failwithf "No handler found for `%s`." handle.Handler
            | handlers, finalizer ->
                let newHandlerEnv =
                    { HandlerName = handle.Handler
                      Handlers = handlers
                      HandlerState = snd (loop state handle.State)
                      Resumed = false }

                let stateWithHandlers =
                    { state with HandlerEnvironment = Map.add handle.Handler newHandlerEnv state.HandlerEnvironment }

                // The finaliser must be of type `unit` and is used to clean up external resources
                // (flush, free, dispose, close file, etc.) when using algebraic effects with an FFI.
                // Otherwise, they don't serve much other purpose, but that's normal; that's the point.
                // It's a `defer`-like or a `finally`-like feature.

                let resultState, resultTerm =
                    try Environment.withinScope stateWithHandlers None loop (Some handle.ToHandle)
                    with ZeroShot zeroShot -> zeroShot.FinalState, zeroShot.Result

                let finalize = processFinalizer resultState finalizer newHandlerEnv
                let resultState = Option.defaultValue resultState finalize

                resultState, resultTerm

        and processFinalizer (state: RunningState) (finalizer: CoreHandler option) (henv: HandlerEnvironment) =
            match finalizer with
            | None -> None
            | Some fh ->
                match getCurrentHandlerState state henv.HandlerName with
                | Some hstate ->
                    match matchTerm state globalEnv fh.State hstate Map.empty with
                    | Some subst ->
                        match Environment.withinScope state (Some subst) loop (Some fh.RHS) with
                        | fialState, Symbol { Symbol = "unit"; Children = [] } -> Some fialState
                        | _, other -> raise (NonUnitFinalizerException (PrettyPrinter.prettyPrintExpr other))

                    | None ->
                        let got = PrettyPrinter.prettyPrintExpr hstate
                        let expected = PrettyPrinter.prettyPrintExpr fh.State
                        raise (PatternMatchFailedException (got, expected, $"{henv.HandlerName}'s finalizer"))

                | None -> failwithf "State does not exist for the finaliser."

        and getCurrentHandlerState (state: RunningState) (hname: string) =
            state.HandlerEnvironment
            |> Map.tryFind hname
            |> Option.map _.HandlerState

        and processResume (state: RunningState) (resume: CoreResume) =
            let _, evaluatedHandlerState = loop state resume.State

            let state =
                { state with
                    HandlerEnvironment = 
                        Map.change resume.FromHandler 
                            (Option.map (fun henv -> 
                                { henv with
                                    HandlerState = evaluatedHandlerState
                                    Resumed = true }))
                            state.HandlerEnvironment }

            loop state resume.Rewrite

        and tryHandler (state: RunningState) (term: CoreTerm) (handlerName: string) (henv: HandlerEnvironment) (handler: CoreHandler) =
            let inline hasResumed (state: RunningState) (handlerName: string) =
                (Map.find handlerName state.HandlerEnvironment).Resumed

            match matchTerm state globalEnv handler.LHS term Map.empty with
            | None -> None
            | Some subst1 ->
                match matchTerm state globalEnv handler.State henv.HandlerState subst1 with
                | None -> None
                | Some subst2 ->
                    match checkWhenClause state globalEnv subst2 handler.WhenClause with
                    | false -> None
                    | true ->
                        let state, result = Environment.withinScope state (Some subst2) loop (Some handler.RHS)

                        if not (hasResumed state handlerName) then
                            // If the handler has not resumed, then it does not continue the calculation,
                            // so we must stop at this point, hence the `ZeroShot` exception for the exact
                            // same control-flow behaviour.
                            raise (ZeroShot {| Result = result; FinalState = state |})
                        else
                            // Otherwise, the calculation continues, resetting the `Resumed` field for the next time.
                            let newState =
                                { state with
                                    HandlerEnvironment =
                                        Map.change handlerName
                                            (Option.map (fun henv -> { henv with Resumed = false }))
                                            state.HandlerEnvironment }

                            Some (newState, result)

        and tryHandlers (state: RunningState) (term: CoreTerm) =

            // TODO: we have to handle innermost AND outermost handlers

            state.HandlerEnvironment
            |> Map.tryPick (fun handlerName handlerEnvironment ->
                handlerEnvironment.Handlers
                |> Array.tryPick (tryHandler state term handlerName handlerEnvironment))

        /// Function optimised for symbol processing that returns None if not applicable. The purpose of this
        /// function is to note that certain symbols do not have rewriting rules, thereby avoiding running the
        /// interpreter in vain. This function therefore typically speeds up the management of recursive data
        /// structures (lists, trees, etc.).
        and processSymbolFast (state: RunningState) (symbol: CoreSymbol) =

            // il y a aussi des erreurs avec la FFI

            let isPassiveSymbol (s: string) (term: CoreTerm) =
                match passiveSymbolsCache.TryGetValue s with
                | true, value -> value
                | false, _ ->
                    let computedValue =
                        not (Array.contains s builtinFunctions)
                        && Array.isEmpty (globalEnv.GetRelevantRules term)
                        && Array.isEmpty (fst (globalEnv.GetRelevantHandlers s)) // c'est pas bon, ça prend comme
                                                                                 // argument le nom du handler générale
                                                                                 // pas un symbole. Donc par exemple ça
                                                                                 // prend `Counter`. Il faut modifier ça
                    passiveSymbolsCache.[s] <- computedValue
                    computedValue

            /// A fast-path `loop` for common cases.
            let rec fastResolve (t: CoreTerm) =
                match t with
                | Literal _ -> t
                | Closure clo when clo.IsEvaluated -> t
                | Symbol s when isPassiveSymbol s.Symbol t ->
                    let newChildren = physicalMap fastResolve s.Children

                    if LanguagePrimitives.PhysicalEquality s.Children newChildren then t
                    else copySymbolWithNewChildren s newChildren

                | _ -> snd (loop state t)

            if not (isPassiveSymbol symbol.Symbol (Symbol symbol)) then
                None
            else
                let newChildren = physicalMap fastResolve symbol.Children

                if LanguagePrimitives.PhysicalEquality newChildren symbol.Children
                then Some (state, Symbol symbol)
                else Some (state, copySymbolWithNewChildren symbol newChildren)

        and processSymbol (state: RunningState) (symbol: CoreSymbol) =

            (*

            // Check the recursion depth and throw an error to avoid getting the .NET exception on stack overflow.
            if state.RecursionDepth >= maxRecursionDepth then
                let msg = sprintf "Maximum recursion depth exceeded (%d) while handling the symbol `%s`.\nThis is fixed and cannot be changed with this runtime." maxRecursionDepth symbol.Symbol
                immediateRuntimeError RuntimeInternal msg

            let state = { state with RecursionDepth = state.RecursionDepth + 1 }

            *)

            // --- debug purpose --- //

            //let key = symbol.Symbol, symbol.Children.Length
            //match ruleCallCounts.TryGetValue key with
            //| false, _ -> ruleCallCounts.Add(key, 1)
            //| true, count -> ruleCallCounts.[key] <- count + 1

            // -- -- //

          //  match processSymbolFast state symbol with
          //  | Some result -> result
          //  | None ->

                if symbol.IsVariable then
                    match Environment.lookupVariable symbol.Symbol state with
                    | None -> raise (FreeVariableException symbol.Symbol)
                    | Some _ -> raise (NonApplicationSymbolException symbol.Symbol)
                else

                    let term = Symbol symbol

                    match globalEnv.GetExternLibrary term with
                    | Some (lib, functions) ->
                        match symbol.Symbol.Split '.' with      // not a big fan of this...
                        | [| qual; functionName |] ->
                            match Map.tryFind functionName functions with
                            | Some f ->
                                let children = symbol.Children |> List.map (loop state >> snd)
                                state, callExternalFunction f lib children
                            | None ->
                                raise (UnboundExternalFunctionException(qual, functionName))
                        | _ ->
                            failwith $"Invalid symbol format: expected 'Namespace.FunctionName', got '{symbol.Symbol}'."

                    | None ->
                        match tryHandlers state term with
                        | None -> tryRules state symbol term
                        //| None -> tryRulesWithDecisionTree state symbol term
                        | Some result -> result

        and applyClosure (closure: Closure) (args: CoreTerm list) (state: RunningState) =
            let clen = closure.Parameters.Length
            if args.Length <> clen then
                raise (ArityMismatchException(clen, args.Length, PrettyPrinter.prettyPrintExpr (Closure closure)))

            let paramEnv = Map.ofList (List.zip closure.Parameters args)
            let combinedEnv = Map.crushingMerge closure.Env paramEnv

            let newEnvStack = combinedEnv :: state.VariableEnvironments
            let newState = { state with VariableEnvironments = newEnvStack }

            loop newState closure.Value

        and applyGivenRules (state: RunningState) (term: CoreTerm) (rules: CoreRule array) =
            let result =
                try
                    Array.tryPick
                        (fun r -> try tryRule state globalEnv r term with InvalidRuleException _ as ex -> raise ex)
                        rules
                    |> Option.defaultValue (state, term)
                with
                | InvalidRuleException msg ->
                    let msg = sprintf "Invalid rule reached: %s" msg
                    immediateRuntimeError Runtime msg
                | ex -> raise ex

            result

        and applyRules (state: RunningState) (term: CoreTerm) =
            let rules = globalEnv.GetRelevantRules term
            applyGivenRules state term rules

        and tryRules (state: RunningState) (symbol: CoreSymbol) (term: CoreTerm) =

            //
            // If outermost rules exist for this symbol, then the children are not evaluated and only those
            // rules (only the outermost rules) are applied. If the result has changed, then it means the
            // rule applied, the outermost result is returned. If it has not changed, then the innermost
            // rules are applied, this time reducing the children and testing only the innermost rules.
            //

            let rules = globalEnv.GetRelevantRules term
            let outRules, inRules = rules |> Array.partition _.Strategy.IsOutermost
            let outermostResult = applyGivenRules state term outRules

            if snd outermostResult <> term
            then outermostResult
            else
                let newChildren = List.map (loop state >> snd) symbol.Children
                let newTerm = copySymbolWithNewChildren symbol newChildren
                let innermostResult = applyGivenRules state newTerm inRules

                if snd innermostResult <> newTerm
                then innermostResult
                else
                    match newTerm with
                    | Builtin state result -> result // in practice, we woul add them in `inRules`.
                    | _ -> state, newTerm

        and tryRule state globalEnv rule term =
            match matchTerm state globalEnv rule.LHS term Map.empty with
            | None -> None
            | Some subst ->
                if not (checkWhenClause state globalEnv subst rule.WhenClause) then None
                else
                    let rhs () =
                        if rule.Strategy.IsOutermost then substitute subst rule.RHS
                        else rule.RHS

                    let rewriteFn () =
                        if rule.Strategy.IsOutermost then loopOutermost
                        else loop

                    // This should not be done foolishly. The behaviour of memoization may not be as expected
                    // if effects, I/O, etc. are used. A preliminary analysis is necessary to justify that
                    // the use of memoization is valid; here, no verification is performed.
                    match rule.Strategy.IsMemoize, memoizedRules.TryGetValue term with
                    | true, (true, value) -> Some (state, value)
                    | true, (false, _) ->
                        let (_, value) as res = Environment.withinScope state (Some subst) (rewriteFn()) (Some (rhs()))
                        memoizedRules.[term] <- value
                        Some res

                    | false, _ ->
                        Some (Environment.withinScope state (Some subst) (rewriteFn()) (Some (rhs())))

        and tryRulesWithDecisionTree (state: RunningState) (symbol: CoreSymbol) (term: CoreTerm) =

            let runTree (s: RunningState) (t: CoreTerm) =
                match globalEnv.GetDecisionTree t with
                | Some tree -> DecisionTreeEvaluation.eval s loop tree t Map.empty
                | None -> DecisionTreeEvaluation.Failure

            let processSuccess (s: RunningState) (t: CoreTerm) (ruleIndex: int) (bindings: Substitution) =
                let rule = globalEnv.GetRelevantRules(t).[ruleIndex]
                let rhs = if rule.Strategy.IsOutermost then substitute bindings rule.RHS else rule.RHS
                let strategy = if rule.Strategy.IsOutermost then loopOutermost else loopInnermost

                Environment.withinScope s (Some bindings) strategy (Some rhs)

            if globalEnv.HasOutermostRules term then
                match runTree state term with
                | DecisionTreeEvaluation.Success(idx, bindings) -> processSuccess state term idx bindings
                | DecisionTreeEvaluation.Failure ->
                    let newChildren = List.map (loop state >> snd) symbol.Children
                    let newTerm = copySymbolWithNewChildren symbol newChildren

                    match runTree state newTerm with
                    | DecisionTreeEvaluation.Success(idx, bindings) -> processSuccess state newTerm idx bindings
                    | DecisionTreeEvaluation.Failure ->
                        match newTerm with
                        | Builtin state result -> result
                        | _ -> state, newTerm

            else
                let newChildren = List.map (loop state >> snd) symbol.Children
                let newTerm = copySymbolWithNewChildren symbol newChildren

                match runTree state newTerm with
                | DecisionTreeEvaluation.Success(idx, bindings) -> processSuccess state newTerm idx bindings
                | DecisionTreeEvaluation.Failure ->
                    match newTerm with
                    | Builtin state result -> result
                    | _ -> state, newTerm

        and (|Builtin|_|) (state: RunningState) (term: CoreTerm) =

            let inline literalBinaryOperation a b actionInt64 actionFloat64 =
                let a = snd (loop state a)
                let b = snd (loop state b)

                try
                    match a, b with
                    | Literal (Integer a), Literal (Integer b) -> Some (Literal (Integer (actionInt64 a b)))
                    | Literal (Float a), Literal (Float b) -> Some (Literal (Float (actionFloat64 a b)))
                    | Literal (Integer a), Literal (Float b) -> Some (Literal (Float (actionFloat64 (double a) b)))
                    | Literal (Float a), Literal (Integer b) -> Some (Literal (Float (actionFloat64 a (double b))))
                    | _ -> None
                with
                | :? System.DivideByZeroException ->
                    term |> PrettyPrinter.prettyPrintExpr
                         |> sprintf "division by zero in `%s`"
                         |> InvalidRuleException
                         |> raise

            let exponentiationOperation a b =
                let a = snd (loop state a)
                let b = snd (loop state b)

                let raiseError message =
                    term |> PrettyPrinter.prettyPrintExpr
                         |> sprintf "%s in `%s`" message
                         |> InvalidRuleException
                         |> raise

                let validateFloat result =
                    if System.Double.IsNaN result then raiseError "invalid result (NaN) in exponentiation"
                    elif System.Double.IsInfinity result then raiseError "overflow in exponentiation"
                    else Some (Literal (Float result))

                try
                    match a, b with
                    | Literal (Integer a), Literal (Integer b) when b = 0I ->
                        if a = 0I then raiseError "undefined operation"
                        else Some (Literal (Integer 1I))

                    | Literal (Integer a), Literal (Integer b) when a = 0I && b < 0I ->
                        raiseError "division by zero"

                    | Literal (Integer a), Literal (Integer b) when b > 0I ->
                        if b <= 2147483647I then
                            try
                                Some (Literal (Integer (pown a (int32 b))))
                            with
                            | :? System.OverflowException ->
                                raiseError "overflow in exponentiation"
                        else
                            raiseError "overflow in exponentiation"

                    | Literal (Integer a), Literal (Integer b) when b < 0I ->
                        if a = 0I then raiseError "division by zero"
                        System.Math.Pow(double a, double b) |> validateFloat

                    | Literal (Float a), Literal (Float b) ->
                        System.Math.Pow(a, b) |> validateFloat

                    | Literal (Integer a), Literal (Float b) ->
                        System.Math.Pow(double a, b) |> validateFloat
                    
                    | Literal (Float a), Literal (Integer b) ->
                        System.Math.Pow(a, double b) |> validateFloat

                    | _ -> None
                with
                | :? InvalidRuleException as ex -> raise ex
                | :? System.DivideByZeroException -> raiseError "division by zero"
                | :? System.OverflowException -> raiseError "overflow in exponentiation"

            let inline literalBinaryComparison a b actionInt64 actionFloat64 =
                let a = snd (loop state a)
                let b = snd (loop state b)

                match a, b with
                | Literal (Integer a), Literal (Integer b) -> Some (simpleSymbol (if actionInt64 a b then "true" else "false"))
                | Literal (Float a), Literal (Float b) -> Some (simpleSymbol (if actionFloat64 a b then "true" else "false"))
                | Literal (Float a), Literal (Integer b) -> Some (simpleSymbol (if actionFloat64 a (double b) then "true" else "false"))
                | Literal (Integer a), Literal (Float b) -> Some (simpleSymbol (if actionFloat64 (double a) b then "true" else "false"))
                | _ -> None

            let inline booleanAlgebra a b action shortCircuit =

                let symbolToBool =
                    function
                    | SymbolTrue -> Some true
                    | SymbolFalse -> Some false
                    | _ -> None

                let boolToSymbol =
                    function
                    | true -> trueSymbol
                    | false -> falseSymbol

                let _, evalA = loop state a

                match symbolToBool evalA with
                | Some valueA ->
                    match shortCircuit valueA with
                    | Some result -> Some (boolToSymbol result)
                    | None ->
                        let _, evalB = loop state b
                        match symbolToBool evalB with
                        | Some valueB -> Some (boolToSymbol (action valueA valueB))
                        | _ -> None
                | None -> None

            let inline collectionAccess (lst: CoreTerm) (tpl: CoreTerm) =
                match tpl with
                | Symbol { Symbol = "tuple"; Children = [ index ] } ->
                    match snd (loop state index) with
                    | Literal (Integer i) ->
                        let rec findNth n term =
                            match term with
                            | Nil -> raise (InvalidRuleException $"index out of range, {i}.")
                            | Cons(x, _) when n = 0 -> Some x
                            | Cons(_, xs) -> findNth (n - 1) xs
                            | other -> raise (InvalidRuleException $"invalid list structure, {PrettyPrinter.prettyPrintExpr other}.")

                        let idx = int i
                        if idx < 0 then raise (InvalidRuleException $"index out of range, {i}.")
                        findNth idx lst
                    | _ -> None
                | _ -> None

            match term with
            | Symbol { Symbol = "collection_access"; Children = [ lst; tuple ] } -> collectionAccess lst tuple
            | Plus(a, b) -> literalBinaryOperation a b ( + ) ( + )
            | Minus(a, b) -> literalBinaryOperation a b ( - ) ( - )
            | Asterisk(a, b) -> literalBinaryOperation a b ( * ) ( * )
            | Slash(a, b) -> literalBinaryOperation a b ( / ) ( / )
            | Percent(a, b) -> literalBinaryOperation a b ( % ) ( % )
            | DoubleAsterisk(a, b) -> exponentiationOperation a b

            | Eq(a, b) -> literalBinaryComparison a b ( = ) ( = )
            | Neq(a, b) -> literalBinaryComparison a b ( <> ) ( <> )
            | Le(a, b) -> literalBinaryComparison a b ( < ) ( < )
            | Leq(a, b) -> literalBinaryComparison a b ( <= ) ( <= )
            | Ge(a, b) -> literalBinaryComparison a b ( > ) ( > )
            | Geq(a, b) -> literalBinaryComparison a b ( >= ) ( >= )

            | And(a, b) -> booleanAlgebra a b ( && ) (fun a -> if not a then Some false else None)
            | Or(a, b) -> booleanAlgebra a b ( || ) (fun a -> if a then Some true else None)
            | Not a ->
                match snd (loop state a) with
                | SymbolTrue -> Some falseSymbol
                | SymbolFalse -> Some trueSymbol
                | _ -> None

            (* // --- under consideration --- //

            | IsType(a, t) ->
                let _, a = loop state a
                let _, t = loop state t

                match a, t with
                | _, Symbol { Symbol = "Any" } -> Some (simpleSymbol "true")
                | Literal (Integer _), Symbol { Symbol = "Int" }    -> Some (simpleSymbol "true")
                | Literal (Float _),   Symbol { Symbol = "Float" }  -> Some (simpleSymbol "true")
                | Literal (String _),  Symbol { Symbol = "String" } -> Some (simpleSymbol "true")
                | Literal (Char _),    Symbol { Symbol = "Char" }   -> Some (simpleSymbol "true")
                | _ ->
                    None
                    //Some (simpleSymbol "false")

            *)

            | Cast(a, t) ->
                let _, a = loop state a
                let _, t = loop state t

                let convertLiteral lit targetType =
                    match lit, targetType with
                    | Integer i, "Int"   -> Integer i
                    | Integer i, "Float" -> Float (float i)
                    | Integer i, "Char"  -> Char (char i)

                    | Float f, "Int"     -> Integer (bigint f)
                    | Float f, "Float"   -> Float f
                    | Float f, "Char"    -> Char (char (bigint f))

                    | Char c, "Int"      -> Integer (bigint c)
                    | Char c, "Float"    -> Float (float (int c))
                    | Char c, "Char"     -> Char c

                    | _ ->
                        raise
                            (InvalidRuleException
                                (sprintf "The `cast` function cannot convert `%s` to `%s`"
                                    (PrettyPrinter.prettyPrintExpr a)
                                    (PrettyPrinter.prettyPrintExpr t)))

                match a, t with
                | Literal lit, Symbol { Symbol = s } when s = "Int" || s = "Float" || s = "Char" ->
                    Some (Literal (convertLiteral lit s))

                | Ptr ptr, Symbol { Symbol = "String" } ->
                    Some (Literal (String (Marshal.PtrToStringUTF8 ptr)))

                | _ -> None

            | Show value ->
                let _, value = loop state value
                let text = PrettyPrinter.prettyPrintExpr value
                Some (Literal (String text))

            | PrintingShow value ->
                let text =
                    match snd (loop state value) with
                    | Literal (String s) -> s
                    | other -> PrettyPrinter.prettyPrintExpr other

                Some (Literal (String text))

            | Concat(a, b) ->
                let _, a = loop state a
                let _, b = loop state b

                match a, b with
                | Literal (String s1), Literal (String s2) -> Some (Literal (String (s1 + s2)))
                | _ -> None

            | Range(start, step, stop) ->
                let start = snd (loop state start)
                let stop = snd (loop state stop)
                let step =
                    match step with
                    | None' -> simpleSymbol "none"
                    | Some' expr -> symbol "some" [ snd (loop state expr) ]
                    | _ -> raise (InvalidRuleException(sprintf "The `range` function does not consider `%s` to be a valid step." (PrettyPrinter.prettyPrintExpr step)))

                let inline generateRange (makeLiteral: 'a -> CoreLiteral) (rangeFn: 'a -> 'a -> 'a -> seq<'a>) (start: 'a) (step: 'a option) (stop: 'a) =
                    match step with
                    | None -> rangeFn start LanguagePrimitives.GenericOne stop
                    | Some s -> rangeFn start s stop
                    |> Seq.map (makeLiteral >> Literal)
                    |> Seq.toList
                    |> listSymbol
                    |> Some

                match start, step, stop with
                | Literal (Integer start), None', Literal (Integer stop) ->
                    generateRange Integer (fun a _ b -> seq { a .. b }) start None stop

                | Literal (Integer start), Some' (Literal (Integer step)), Literal (Integer stop) ->
                    generateRange Integer (fun a s b -> seq { a .. s .. b }) start (Some step) stop

                | Literal (Float start), None', Literal (Float stop) ->
                    generateRange Float (fun a _ b -> seq { a .. b }) start None stop

                | Literal (Float start), Some' (Literal (Float step)), Literal (Float stop) ->
                    generateRange Float (fun a s b -> seq { a .. s .. b }) start (Some step) stop

                | _ -> None

            | DebugPrint value ->
                let _, value = loop state value
                match value with
                | Literal (String s) -> printfn "%s" s
                | _ -> printfn "%s" (PrettyPrinter.prettyPrintExpr value)

                Some(simpleSymbol "unit")

            | DebugBench(a, b) ->
                let _, a = loop state a
                let _, b = loop state b

                match a, b with
                | Closure closure, Literal (Integer n) ->
                    let action () = applyClosure closure [] state

                    let oldCache1 = Dictionary(ruleCallCounts)
                    let oldCache2 = Dictionary(memoizedRules)

                    System.GC.Collect()
                    System.GC.WaitForPendingFinalizers()
                    System.GC.Collect()

                    // Warm-up
                    for _ in 1 .. (min 5 (int n)) do
                        ruleCallCounts <- Dictionary(oldCache1)
                        memoizedRules <- Dictionary(oldCache2)
                        action() |> ignore

                    // First real run (to get the result)
                    ruleCallCounts <- Dictionary(oldCache1)
                    memoizedRules <- Dictionary(oldCache2)
                    let _, result = action()

                    // Timings
                    let times =
                        [| for _ in 1 .. int n ->
                            ruleCallCounts <- Dictionary(oldCache1)
                            memoizedRules <- Dictionary(oldCache2)
                            let sw = System.Diagnostics.Stopwatch.StartNew()
                            action() |> ignore
                            sw.Stop()
                            sw.Elapsed.TotalMilliseconds |]

                    // Restore memo
                    ruleCallCounts <- oldCache1
                    memoizedRules <- oldCache2

                    Array.sortInPlace times
                    let median = times.[times.Length / 2]
                    let mean = Array.average times
                    let stdDev = sqrt (Array.averageBy (fun t -> (t - mean) ** 2.0) times)

                    Some (RecordExtend {
                        BaseRecord = None
                        Extension = [
                            ("mean", Literal (Float mean))
                            ("median", Literal (Float median))
                            ("stdDev", Literal (Float stdDev))
                            ("min", Literal (Float times.[0]))
                            ("max", Literal (Float times.[times.Length - 1]))
                            ("result", result)
                        ]
                    })

                | _ ->
                    raise (InvalidRuleException "`bench` expect an anonymous function and an integer literal.")

            | Symbol { Symbol = "show_decision_tree"; Children = [ Symbol { Symbol = s } ] } ->
                printfn "%s" (DecisionTreePrinter.prettyPrint globalEnv.DecisionTree.[s])
                Some term

            | Symbol { Symbol = "dot_decision_tree"; Children = [ Symbol { Symbol = s } ] } ->
                RenderDecisionTree.renderAndOpen globalEnv.DecisionTree.[s]
                Some term

            | _ -> None
            |> Option.map (fun r -> state, r)

        snd (loop state term)

    and private run (globalEnv: GlobalEnvironment) (entry: CoreTerm) =
        try
            let initialState = Environment.pushVariableScope RunningState.Empty
            normalize initialState globalEnv entry
        with
        | FreeVariableException s ->
            let msg = sprintf "Free variable detected: '%s." s
            immediateRuntimeError RuntimeInternal msg

        | VariableToUpdateNotFoundException s ->
            let msg = sprintf "Cannot update the unfound variable '%s." s
            immediateRuntimeError RuntimeInternal msg

        | WhenClauseException got ->
            let msg = sprintf "When-clause error: expected `true` or `false` but got `%s`." got
            immediateRuntimeError RuntimeInternal msg

        | NonApplicationSymbolException s ->
            let msg = sprintf "`%s` cannot be applicated." s
            immediateRuntimeError RuntimeInternal msg

        | CyclicBindingException s ->
            let msg = sprintf "Cyclic binding detected for the variable '%s" s
            immediateRuntimeError RuntimeInternal msg

        | PatternMatchFailedException(got, expected, where) ->
            let msg = sprintf "Pattern matching failed at %s: expected `%s` but got `%s`." where expected got
            immediateRuntimeError RuntimeInternal msg

        | NotBaseRecordException s ->
            let msg = sprintf "`%s` is not a record, and cannot be extended as a record." s
            immediateRuntimeError RuntimeInternal msg

        | WhileLoopPredicateException s ->
            let msg = sprintf "While-loop predicate error: expected `true` or `false` but got `%s`." s
            immediateRuntimeError RuntimeInternal msg

        | UncompletePatternMatchingException s ->
            let msg = sprintf "Uncomplete pattern matching for `%s`" s
            immediateRuntimeError RuntimeInternal msg

        | ArityMismatchException(expected, got, func) ->
            let msg = sprintf "Arity mismatch for `%s`: expected %d argumet(s) but got %d" func expected got
            immediateRuntimeError RuntimeInternal msg

        | InvalidRuleException msg ->
            let msg = sprintf "Invalid rule reached: %s" msg
            immediateRuntimeError Runtime msg

        | NonUnitFinalizerException got ->
            let msg = sprintf "Expected an unit return type for the finalizer but got `%s`." got
            immediateRuntimeError RuntimeInternal msg

        | UnboundExternalFunctionException(lib, fn) ->
            let msg = sprintf "Unfound external function: `%s` from the external library interface `%s`." fn lib
            immediateRuntimeError RuntimeInternal msg

        | ex -> raise ex

    and public interpret (definitions: CoreDefinition seq) (entry: CoreTerm option) =
        let r = run (buildGlobalEnvironment definitions) entry.Value
        //printRuleCallCounts ruleCallCounts
        r

