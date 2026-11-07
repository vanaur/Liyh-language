namespace Liyh.Semantic

open System.Collections.Generic
open Liyh.Syntax.SyntaxTree

/// This module operates as a pure syntactic pass prior to rule type checking and inference. It extracts
/// the symbols that are called (in bodies, guards and head patterns), constructs the directed graph
/// restricted to the module's rules, and calculates the topological order using Tarjan's algorithm.
module public DependencyAnalysis =

    /// Extracts all the identifiers referenced in the given pattern.
    let rec private collectPatternDependencies (pattWithPos: PatternWithPos) : Set<string> =
        match removePos pattWithPos with
        | ApplyPattern(phead, pargs) ->
            let head =
                match removePos phead with
                | IdentPattern id -> Set.singleton (string id)
                | _ -> collectPatternDependencies phead

            let args =
                pargs
                |> List.map collectPatternDependencies
                |> Set.unionMany

            head + args

        | (TuplePattern patts) | (ListPattern patts) ->
            patts
            |> List.map collectPatternDependencies
            |> Set.unionMany

        | RecordPattern fields ->
            fields
            |> List.map (snd >> collectPatternDependencies)
            |> Set.unionMany

        | AsPattern(p1, p2) ->
            collectPatternDependencies p1 + collectPatternDependencies p2

        | TypedPattern(p, _) ->
            collectPatternDependencies p

        | WhenPattern(p, cond) ->
            collectPatternDependencies p + collectExpressionDependencies cond

        | MixfixOperatorPattern(name, pargs) ->
            let args =
                pargs
                |> List.map collectPatternDependencies
                |> Set.unionMany
            
            Set.add (removePos name) args

        | _ -> Set.empty

    /// Extracts all the identifiers referenced in the given expression.
    and private collectExpressionDependencies (exprWithPos: ExpressionWithPos) : Set<string> =
        let collect = collectExpressionDependencies

        match removePos exprWithPos with
        | Identifier id ->
            Set.singleton (string id)

        | UFCS ufcs ->
            collect ufcs.LHS + collect ufcs.RHS

        | CollectionAccess ca ->
            collect ca.LHS + (ca.Indices |> List.map collect |> Set.unionMany)

        | (ExpressionSequence exprs | Tuple exprs | List exprs) ->
            exprs |> List.map collect |> Set.unionMany

        | Apply apply ->
            collect apply.LHS + (apply.Arguments |> List.map collect |> Set.unionMany)

        | MixfixOperator op ->
            Set.add (removePos op.Name) (op.Arguments |> List.map collect |> Set.unionMany)

        | Record fields ->
            fields |> List.map (snd >> collect) |> Set.unionMany

        | RecordUsing(baseExpr, updates) ->
            collect baseExpr + (updates |> List.map (snd >> collect) |> Set.unionMany)

        | ListComprehension lc ->
            let guardEffs = lc.IfPred |> Option.map collect |> Option.defaultValue Set.empty
            collect lc.ListExpr + collect lc.ItemValue + guardEffs + collectPatternDependencies lc.Pattern

        | Range r ->
            let stepDeps = r.RangeStep |> Option.map collect |> Option.defaultValue Set.empty
            collect r.RangeStart + collect r.RangeStop + stepDeps

        | While w ->
            collect w.Predicate + collect w.Body

        | ForIn fi ->
            collect fi.ListExpr + collect fi.Body + collectPatternDependencies fi.Pattern

        | ForTo ft
        | ForDownTo ft ->
            collect ft.InitialValue + collect ft.EndValue + collect ft.Body + collectPatternDependencies ft.Pattern

        | ReAssign(_, value) ->
            collect value

        | Let(p, expr)
        | Var(p, expr) ->
            collect expr + collectPatternDependencies p

        | Match m ->
            let casesDeps =
                m.Cases
                |> List.map (fun (p, b) -> collectPatternDependencies p + collect b)
                |> Set.unionMany

            collect m.ToMatch + casesDeps

        | IfThenElse ifte ->
            let elifsDeps =
                ifte.ElifBranches
                |> List.map (fun (c, b) -> collect c + collect b)
                |> Set.unionMany

            let elseDeps = ifte.ElseBranch |> Option.map collect |> Option.defaultValue Set.empty
            collect ifte.Condition + collect ifte.ThenBranch + elifsDeps + elseDeps

        | Lambda lam ->
            let pattsDeps = lam.Patterns |> List.map collectPatternDependencies |> Set.unionMany
            collect lam.Body + pattsDeps

        | HandleEffect h ->
            collect h.InitialState + collect h.Body

        | ResumeWith rw ->
            collect rw.Value + collect rw.HandlerState

        | Substitution(substs, target) ->
            let sDeps = substs |> List.map (snd >> collect) |> Set.unionMany
            sDeps + collect target

        | UsingContext uc ->
            collect uc.ContentExpr

        | Literal(InterpolatedString parts) ->
            parts
            |> List.choose (function Interpolation e -> Some (collect e) | _ -> None)
            |> Set.unionMany

        | _ -> Set.empty

    /// Implements the Tarjan's strongly connected components algorithm.
    /// https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm.
    /// 
    /// Inspired by https://github.com/spooky/Graph/blob/master/Graph/Tarjan.cs.
    let private tarjan (nodes: string list) (adj: Map<string, Set<string>>) : string list list =
        let mutable result = []

        let mutable index = 0
        let stack = Stack<string>()

        let indices = Dictionary<string, int>()
        let lowlinks = Dictionary<string, int>()
        let onStack = Dictionary<string, bool>()

        let rec strongConnect (v: string) =
            indices.[v] <- index
            lowlinks.[v] <- index

            index <- index + 1

            stack.Push v
            onStack.[v] <- true

            let neighbors = Option.defaultValue Set.empty (Map.tryFind v adj)

            for w in neighbors do
                if not (indices.ContainsKey w) then
                    strongConnect w
                    lowlinks.[v] <- min lowlinks.[v] lowlinks.[w]

                elif onStack.[w] then
                    lowlinks.[v] <- min lowlinks.[v] indices.[w]

            if lowlinks.[v] = indices.[v] then
                let rec loop scc =
                    let u = stack.Pop()
                    onStack.[u] <- false

                    let tmp = u :: scc
                    if u <> v then loop tmp else tmp

                result <- loop [] :: result

        for node in nodes do
            if not (indices.ContainsKey node) then
                strongConnect node

        List.rev result

    /// Given a list of rules, compute the Simply Connected Component analysis.
    let public computeRuleSCCs (rules: Rule list) : string list list =
        let ruleNames =
            rules
            |> List.map (fun r -> removePos r.Name)
            |> List.distinct

        let knownRulesSet = Set.ofList ruleNames

        let adj =
            rules
            |> List.groupBy (_.Name >> removePos)
            |> List.map (fun (name, clauses) ->
                let dependencies =
                    clauses
                    |> List.map (fun r ->
                        let pDeps = r.Patterns |> List.map collectPatternDependencies |> Set.unionMany
                        let wDeps = r.WhenClause |> Option.map collectExpressionDependencies |> Option.defaultValue Set.empty
                        let bDeps = collectExpressionDependencies r.Body

                        pDeps + wDeps + bDeps)
                    |> Set.unionMany
                    |> Set.filter (fun d -> Set.contains d knownRulesSet) // Only dependencies on the module’s internal rules are retained
            
                (name, dependencies))
            |> Map.ofList

        tarjan ruleNames adj


    // TODO: do the same for the handlers + contexts

