#nowarn "25"
namespace Liyh.LyVM

module public Optimizer =
    open Liyh.Core

    type private RuleInfo = string * int
    type private RuleDepMap = Map<RuleInfo, RuleInfo list>

    let private getRuleInfo (Rule rule) =
        match rule.LHS with
        | Symbol { Symbol = s; Children = children } -> s, List.length children
        | _ -> failwith "??" // this should not happens

    /// Collects each rules used in the given term (with the callable rules given by `rulesInfo`).
    let private collectRulesFromTerm (rulesInfo: RuleInfo list) (term: CoreTerm) =
        let rec loop =
            function
            | Symbol { Symbol = s; Children = children } ->
                let key = (s, List.length children)
                let a = if List.contains key rulesInfo then [ key ] else []
                let b = List.collect loop children

                a @ b

            | RecordExtend { BaseRecord = br; Extension = ext } ->
                let a = (Option.map loop >> Option.defaultValue []) br
                let b = List.collect (snd >> loop) ext

                a @ b

            | Match { ToMatch = toMatch; Cases = cases } ->
                let a = loop toMatch
                let b = List.collect (snd >> loop) cases

                a @ b
            
            | Closure { Value = value } ->
                loop value
            
            | FunctionalApplication { Base = b; Arguments = args } ->
                let a = loop b
                let b = List.collect loop args

                a @ b
            
            | Substitution { Env = env; InExpr = expr } ->
                let a = List.collect (snd >> loop) env
                let b = loop expr

                a @ b
            
            | TermSequence terms ->
                List.collect loop terms
            
            | CoreLet { Value = value } ->
                loop value
            
            | WhileLoop { Predicate = pred; Body = body } ->
                loop pred @ loop body
            
            | UpdateVariable(_, value) ->
                loop value
            
            | Resume { Rewrite = expr } ->
                loop expr
            
            | Handle { State = state; ToHandle = toHandle } ->
                loop state @ loop toHandle
            
            | WhenClause(_, pred) ->
                loop pred
            
            | _ -> []

        List.distinct (loop term)

    let private buildRuleDependencyMap (program: CoreProgram) =
        let rules = program |> List.filter _.IsRule
        let rulesInfo = List.map getRuleInfo rules

        let mutable result = Map.empty<RuleInfo, RuleInfo list> // rule : used rules

        for (Rule rule) as r in rules do
            let usedRulesInRHS = collectRulesFromTerm rulesInfo rule.RHS
            let usedRulesInWhenClause = (Option.map (collectRulesFromTerm rulesInfo) >> Option.defaultValue []) rule.WhenClause
            let usedRules = usedRulesInRHS @ usedRulesInWhenClause

            let currentRuleInfo = getRuleInfo r
            result <- Map.add currentRuleInfo usedRules result

        result

    /// Checks if the given rule is recursive or mutually recursive.
    let private isRecursive (targetRule: RuleInfo) (ruleDepMap: RuleDepMap) =

        // Depth-First Search
        let rec traverse visited current =
            match Map.tryFind current ruleDepMap with
            | None -> false
            | Some dependencies ->
                if List.contains targetRule dependencies then
                    true
                else
                    dependencies
                    |> List.filter (fun r -> not (Set.contains r visited))
                    |> List.exists (fun r -> traverse (Set.add r visited) r)

        traverse Set.empty targetRule

    /// Heuristic to evaluate the cost of a term, based on its structure.
    let rec private calculateTermCost (term: CoreTerm) =
        match term with
        | Symbol { Children = children } ->
            1 + (List.sumBy calculateTermCost children)

        | Match { ToMatch = toMatch; Cases = cases } ->
            let casesCost = List.sumBy (snd >> calculateTermCost) cases
            5 + (calculateTermCost toMatch + casesCost)

        | WhileLoop { Predicate = pred; Body = body } ->
            10 + (calculateTermCost pred + calculateTermCost body)

        | FunctionalApplication { Base = b; Arguments = args } ->
            2 + (calculateTermCost b + List.sumBy calculateTermCost args)

        | RecordExtend { BaseRecord = br; Extension = ext } ->
            2 + (Option.map calculateTermCost >> Option.defaultValue 0) br
              + (List.sumBy (snd >> calculateTermCost) ext)

        | TermSequence terms ->
            List.sumBy calculateTermCost terms

        | (CoreLet { Value = v } | UpdateVariable(_, v) | Closure { Value = v }) ->
            1 + calculateTermCost v

        | Substitution { InExpr = e } ->
            calculateTermCost e

        | Resume { Rewrite = e } ->
            5 + calculateTermCost e

        | Handle { State = s; ToHandle = h } ->
            10 + calculateTermCost s + calculateTermCost h

        | WhenClause(_, p) ->
            calculateTermCost p

        | _ -> 1

    let private shouldInline (ruleInfo: RuleInfo) (Rule rule) (ruleDepMap: RuleDepMap) =
        if rule.Strategy.IsStrict then
            if not (isRecursive ruleInfo ruleDepMap) then
                let cost = calculateTermCost rule.RHS
                cost < 20
            else
                false
        else
            false

    let public inlineOptimization (program: CoreProgram) =
        let ruleDepMap = buildRuleDependencyMap program

        for (Rule rule) as r in program do
            let currentRuleInfo = getRuleInfo r
            let si = shouldInline currentRuleInfo r ruleDepMap

            // printfn "Should inline %s : %b" (fst currentRuleInfo) si

            // Definitions by parts have to be managed.
            // `when` clauses have to be considered.
            // inline if we have anything other than strict, or better
            // if the LHS of a rule does not present the current symbol.
            // For example, one can define only strict rules but with
            // symbolics condieration : canceling outermost inlining is not enough.

            // INLINING is very effective for the performances of the VM!

            ()

        0
