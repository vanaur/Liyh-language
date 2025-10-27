namespace Liyh.Execution.Core

//
// An interpreter for 'LiyhCore', i.e., a minimal (~ desugared) intermediate representation of Liyh.
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
    open Liyh.Execution.Core.Helper
    open Liyh.Execution.Core.Builtin
    open Liyh.Utils.ErrorReporter

    exception private InvalidRuleException of string
    exception private VariableToUpdateNotFoundException of string
    exception private WhenClauseException of got: string * where: string
    exception private NonApplicationSymbolException of string
    exception private CyclicBindingException of string
    exception private FreeVariableException of string
    exception private PatternMatchFailedException of got: string * expected: string * where: string
    exception private NotBaseRecordException of string
    exception private WhileLoopPredicateException of string
    exception private UncompletePatternMatchingException of string
    exception private ArityMismatchException of int * int * string

    #if DEBUG
    let private maxRecursionDepth = 443
    #else
    let private maxRecursionDepth = 1399
    #endif

    /// For debugging purpose, count each call to a specific rule
    let mutable private ruleCallCounts = Dictionary<string * int, int>()

    /// Display a table that shows how many time a given symbol was invoked.
    let private printRuleCallCounts (ruleCallCounts: IDictionary<(string * int), int>) =
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

    [<Struct>]
    type private RunningState =
        { VariableEnvironments: Substitution list
          RecursionDepth: int }

        static member Empty =
            { VariableEnvironments = List.empty
              RecursionDepth = 0 }

    module private Environment =

        /// Retrieves the variable given in the running state if found.
        let public lookupVariable (name: string) (state: RunningState) =
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
        let public pushVariableScope (state: RunningState) =
            { state with VariableEnvironments = Map.empty :: state.VariableEnvironments }

        /// Returns a new running state after removing the last added scope, if it exists, otherwise throws an exception.
        let public popVariableScope (state: RunningState) =
            match state.VariableEnvironments with
            | [] -> failwith "Cannot pop from empty environment stack"
        //    | [_] -> failwith "Cannot pop the global environment"
            | _ :: rest -> { state with VariableEnvironments = rest }

        /// Returns a new running state after adding a binding. New bindings overwrite old ones.
        let public addBindings (bindings: Substitution) (state: RunningState) =
            match state.VariableEnvironments with
            | [] -> failwith "No environment to bind to"
            | currentEnv :: rest ->
                let newEnv = Map.crushingMerge currentEnv bindings
                { state with VariableEnvironments = newEnv :: rest }

    type private GlobalEnvironment =
        { RulesMap: Map<string, CoreRule array>
          HandlersMap: Map<string, CoreHandler array> }

        member inline public this.GetRelevantRules (term: CoreTerm) =
            match term with
            | Symbol { Symbol = symbol } when Map.containsKey symbol this.RulesMap -> this.RulesMap.[symbol]
            | _ -> Array.empty

        member inline public this.GetRelevantHandlers (handler: string) =
            Map.tryFind handler this.HandlersMap
            |> Option.defaultValue Array.empty

    /// Builds the global runtime environment based on the given definitions.
    let private buildGlobalEnvironment (defs: CoreDefinition seq) =

        let inline projectSymbol (lhs: CoreTerm) =
            match lhs with
            | Symbol { Symbol = s } -> s
            | _ -> failwith "expected symbol on LHS"

        let rmInit: Map<string, CoreRule list> = Map.empty
        let hmInit: Map<string, CoreHandler list> = Map.empty

        let rulesLists, handlersLists =
            defs
            |> Seq.fold (fun (rm, hm) -> function
                | Rule r ->
                    let sym = projectSymbol r.LHS
                    let updated = r :: (Map.tryFind sym rm |> Option.defaultValue [])
                    Map.add sym updated rm, hm
                | Handler h ->
                    let sym = projectSymbol h.LHS
                    rm, Map.add sym (h :: (Map.tryFind sym hm |> Option.defaultValue [])) hm
            ) (rmInit, hmInit)

        let rulesMap = rulesLists |> Map.map (fun _ v -> v |> List.rev |> List.toArray)
        let handlersMap = handlersLists |> Map.map (fun _ v -> v |> List.rev |> List.toArray)

        { RulesMap = rulesMap; HandlersMap = handlersMap }

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
                let wc = applySubstitution subst' b

                if whenClauseStack.Contains wc then
                    None // Cycle detected in the when-clause, pattern failure
                else
                    whenClauseStack <- whenClauseStack.Add wc
                    try
                        let wcResult = normalize state globalEnv wc
                        match wcResult with
                        | Symbol { Symbol = "true" } -> Some subst'
                        | Symbol { Symbol = "false" } -> None
                        | _ -> raise (WhenClauseException (PrettyPrinter.prettyPrintExpr wcResult, "matchTerm"))
                    finally
                        // As it stands, the `try-finally` is unnecessary, but in case of doubt where the exception
                        // is caught and the interpreter is restarted, this is the step that must be taken.
                        whenClauseStack <- whenClauseStack.Remove wc

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
                    | _ -> Some (Map.add s1.Symbol (Symbol { s1 with Children = [] }) subst)

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

    and private applySubstitution (subst: Substitution) (term: CoreTerm) =

        let rec apply (term: CoreTerm) =
            match term with
            | Literal _ -> term

            | Variable v ->
                match subst.TryGetValue v with
                | true, term' -> term'
                | _ -> term

            | Symbol ({ IsVariable = true } as s) ->
                match subst.TryGetValue s.Symbol with
                | true, Symbol f ->
                    let newChildren = List.map apply s.Children
                    Symbol { f with Children = f.Children @ newChildren }

                | true, Closure closure ->
                    let newChildren = List.map apply s.Children
                    if newChildren.IsEmpty then Closure closure
                    else FunctionalApplication { Base = Closure closure; Arguments = newChildren }

                | true, f -> raise (NonApplicationSymbolException (PrettyPrinter.prettyPrintExpr f))

                | _ -> term

            | Symbol s ->
                let newChildren = List.map apply s.Children
                Symbol { s with Children = newChildren }

            | Closure closure ->
                let newEnv = Map.map (fun _ v -> apply v) closure.Env
                let newVal = apply closure.Value
                Closure { closure with Env = newEnv; Value = newVal }

            | Match match' ->
                Match {
                    ToMatch = apply match'.ToMatch
                    Cases = List.map (fun (a, b) -> apply a, apply b) match'.Cases }

            | WhileLoop whileLoop ->
                WhileLoop {
                    Predicate = apply whileLoop.Predicate
                    Body = apply whileLoop.Body }

            | Resume resume ->
                Resume {
                    Rewrite = apply resume.Rewrite
                    State = apply resume.State }

            | Handle handle ->
                Handle {
                    handle with
                        ToHandle = apply handle.ToHandle
                        State = apply handle.State }

            | UpdateVariable(s, upd) -> UpdateVariable(s, apply upd)
            | CoreLet l -> CoreLet { l with Value = apply l.Value }
            | RecordExtend { BaseRecord = o; Extension = fs } -> RecordExtend { BaseRecord = o; Extension = List.map (fun (a, b) -> a, apply b) fs }
            | FunctionalApplication { Base = f; Arguments = args } -> FunctionalApplication { Base = apply f; Arguments = List.map apply args }
            | TermSequence terms -> TermSequence (List.map apply terms)
            | WhenClause(a, b) -> WhenClause(apply a, apply b)
            | AsClause(a, b) -> AsClause(apply a, apply b)

            | Wildcard -> Wildcard

        apply term

    and private tryRule (loop: RunningState -> CoreTerm -> RunningState * CoreTerm) (state: RunningState) (globalEnv: GlobalEnvironment) (rule: CoreRule) (term: CoreTerm) =
        let result =
            match matchTerm state globalEnv rule.LHS term Map.empty with
            | None -> None
            | Some subst ->
                let evaluateWithBindings () =
                    let newState = Environment.addBindings subst state
                    loop newState rule.RHS

                match rule.WhenClause with
                | Some wc ->
                    let wc = applySubstitution subst wc
                    match normalize state globalEnv wc with
                    | Symbol { Symbol = "true" } -> Some evaluateWithBindings
                    | Symbol { Symbol = "false" } -> None
                    | _ -> raise (WhenClauseException(PrettyPrinter.prettyPrintExpr wc, "tryRule"))
                | _ ->
                    Some evaluateWithBindings

        match result with
        | None -> None
        | Some rewrite ->
            let result = rewrite()
            if rule.Strategy.IsInvalid then
                match snd result with
                | Literal (String msg) -> raise (InvalidRuleException msg)
                | other -> raise (InvalidRuleException (PrettyPrinter.prettyPrintExpr other))
            else
                Some result

    and private normalize (state: RunningState) (globalEnv: GlobalEnvironment) (term: CoreTerm) =

        let rec loop (state: RunningState) (term: CoreTerm) =
            let inline processNormalize () =
                match term with

                // Early return from the loop for irreducible terms
                | Literal _ -> (state, term)

                | Closure closure ->
                    let evaluatedEnv = Map.map (fun _ v -> snd (loop state v)) closure.Env
                    let evaluatedClosure = Closure { closure with Env = evaluatedEnv }
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
                    let scopedState = Environment.pushVariableScope state
                    let mutable currentState = scopedState
                    let mutable lastResult = simpleSymbol "unit"

                    for term in terms do
                        let newState, result = loop currentState term
                        currentState <- newState
                        lastResult <- result

                    let restoredState = Environment.popVariableScope currentState
                    (restoredState, lastResult)

                | RecordExtend { BaseRecord = Some baseRecord; Extension = extensionFields } ->
                    let state', evaluatedBaseRecord = loop state baseRecord
                    match evaluatedBaseRecord with
                    | RecordExtend { BaseRecord = None; Extension = originalFields } ->
                        let map1 = Map.ofList extensionFields
                        let map2 = Map.ofList originalFields
                        let map3 = Map.crushingMerge map2 map1
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
                        let newSymbol = Symbol { s with Children = s.Children @ normalizedArgs }
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
                        | Symbol { Symbol = "true" } ->
                            let bodyState, _ = loop newState whileLoop.Body
                            loopExecution bodyState

                        | Symbol { Symbol = "false" } -> (newState, simpleSymbol "unit")
                        | other -> raise (WhileLoopPredicateException (PrettyPrinter.prettyPrintExpr other))

                    loopExecution state

                | Match match' ->
                    let toMatch = snd (loop state match'.ToMatch) // innermost/strict

                    let inline chooser (pattern, value) =
                        matchTerm state globalEnv pattern toMatch Map.empty
                        |> Option.map (fun subst -> subst, value)

                    match List.tryPick chooser match'.Cases with
                    | None -> raise (UncompletePatternMatchingException (PrettyPrinter.prettyPrintExpr toMatch))
                    | Some (bindings, rewrite) ->
                        let newState = Environment.addBindings bindings state
                        loop newState rewrite

                | Symbol s -> processSymbol state s

                | Handle handle ->
                    failwith "TODO: handle"

                | Resume resume ->
                    failwith "TODO: resume"

                | _ ->
                    // Unevaluated value and unchanged state
                    (state, term)

            processNormalize()

        and processSymbol (state: RunningState) (symbol: CoreSymbol) =

            // Check the recursion depth and throw an error to avoid getting the .NET exception on stack overflow.
            if state.RecursionDepth >= maxRecursionDepth then
                let msg = sprintf "Maximum recursion depth exceeded (%d) while handling the symbol `%s`.\nThis is fixed and cannot be changed with this runtime." maxRecursionDepth symbol.Symbol
                immediateRuntimeError RuntimeInternal msg

            let state = { state with RecursionDepth = state.RecursionDepth + 1 }

            if symbol.IsVariable then
                match Environment.lookupVariable symbol.Symbol state with
                | None -> raise (FreeVariableException symbol.Symbol)
                | Some s ->
                    raise (NonApplicationSymbolException symbol.Symbol)
                    //failwithf "Applying a variable symbol without `FunctionalApplication`: %s" symbol.Symbol
                    //loop state (FunctionalApplication(s, newChildren))
            else

                // --- debug purpose --- //

                let key = symbol.Symbol, symbol.Children.Length
                match ruleCallCounts.TryGetValue key with
                | false, _ -> ruleCallCounts.Add(key, 1)
                | true, count -> ruleCallCounts.[key] <- count + 1

                //
                // If outermost rules exist for this symbol, then the children are not evaluated and only those
                // rules (only the outermost rules) are applied. If the result has changed, then it means the
                // rule applied, the outermost result is returned. If it has not changed, then the innermost
                // rules are applied, this time reducing the children and testing only the innermost rules.
                //

                let term = Symbol symbol
                let rules = globalEnv.GetRelevantRules term
                let outRules, inRules = rules |> Array.partition _.Strategy.IsOutermost
                let outermostResult = applyGivenRules state term outRules

                if snd outermostResult <> term
                then outermostResult
                else
                    let newChildren = List.map (loop state >> snd) symbol.Children
                    let newTerm = Symbol { symbol with Children = newChildren }
                    let innermostResult = applyGivenRules state newTerm inRules

                    if snd innermostResult <> newTerm
                    then innermostResult
                    else
                        match newTerm with
                        | Builtin state result -> result // in practice, we woul add them in `inRules`.
                        | _ -> state, newTerm

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
                        (fun r -> try tryRule loop state globalEnv r term with InvalidRuleException _ as ex -> raise ex)
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

        and (|Builtin|_|) (state: RunningState) (term: CoreTerm) =

            let inline literalBinaryOperation a b actionInt64 actionFloat64 =
                let a = snd (loop state a)
                let b = snd (loop state b)

                match a, b with
                | Literal (Integer a), Literal (Integer b) -> Some (Literal (Integer (actionInt64 a b)))
                | Literal (Float a), Literal (Float b) -> Some (Literal (Float (actionFloat64 a b)))
                | Literal (Integer a), Literal (Float b) -> Some (Literal (Float (actionFloat64 (double a) b)))
                | Literal (Float a), Literal (Integer b) -> Some (Literal (Float (actionFloat64 a (double b))))
                | _ -> None

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
                    | Symbol { Symbol = "true" } -> Some true
                    | Symbol { Symbol = "false" } -> Some false
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

            match term with
            | Plus(a, b) -> literalBinaryOperation a b ( + ) ( + )
            | Minus(a, b) -> literalBinaryOperation a b ( - ) ( - )
            | Asterisk(a, b) -> literalBinaryOperation a b ( * ) ( * )
            | Slash(a, b) -> literalBinaryOperation a b ( / ) ( / )
            | Percent(a, b) -> literalBinaryOperation a b ( % ) ( % )
            | DoubleAsterisk(a, b) ->
                let a = snd (loop state a)
                let b = snd (loop state b)

                match a, b with
                | Literal (Integer _), Literal (Integer b) when b < 0I -> None
                | Literal (Integer a), Literal (Integer b) -> Some (Literal (Integer (pown a (int b))))
                | Literal (Float a), Literal (Float b) -> Some (Literal (Float (System.Math.Pow(a, b))))
                | _ -> None

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
                | Symbol { Symbol = "true" } -> Some falseSymbol
                | Symbol { Symbol = "false" } -> Some trueSymbol
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
                    |> list
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
                    let oldCache = Dictionary<_, _>(ruleCallCounts)
                    
                    // Warm-up
                    for _ in 1 .. (min 5 (int n)) do
                        ruleCallCounts <- Dictionary(oldCache)
                        action() |> ignore

                    let _, result = action()

                    let times =
                        [| for _ in 1 .. int n ->
                            ruleCallCounts <- Dictionary(oldCache)
                            let sw = System.Diagnostics.Stopwatch.StartNew()
                            action() |> ignore
                            sw.Stop()
                            sw.Elapsed.TotalMilliseconds |]

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
                | _ -> raise (InvalidRuleException "`bench` expect an anonymous function and an integer literal.")

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

        | WhenClauseException(got, where) ->
            let msg = sprintf "When-clause error at %s: expected `true` or `false` but got `%s`." where got
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

        | ex -> raise ex

    and public interpret (definitions: CoreDefinition seq) (entry: CoreTerm option) =
        let r = run (buildGlobalEnvironment definitions) entry.Value
        //printRuleCallCounts ruleCallCounts
        r

