namespace Liyh.Core

module public CoreTermSubstitution =
    open Liyh.Core.Helper

    /// Replace the given terms from the map.
    let rec public replaceCoreTerm (substitutions: Map<CoreTerm, CoreTerm>) (term: CoreTerm) =
        match Map.tryFind term substitutions with
        | Some replacement -> replacement
        | None ->
            match term with
            | Symbol sym ->
                let newChildren = List.map (replaceCoreTerm substitutions) sym.Children
                if newChildren = sym.Children then term
                else copySymbolWithNewChildren sym newChildren

            | Variable _ -> term
            | Literal _ -> term

            | RecordExtend ext ->
                let newBase = Option.map (replaceCoreTerm substitutions) ext.BaseRecord
                let newExtension = List.map (fun (k, v) -> (k, replaceCoreTerm substitutions v)) ext.Extension
                if newBase = ext.BaseRecord && newExtension = ext.Extension then
                    term
                else
                    RecordExtend { ext with BaseRecord = newBase; Extension = newExtension }

            | Match m ->
                let newToMatch = replaceCoreTerm substitutions m.ToMatch
                let newCases = List.map (fun (pat, body) ->
                    let newPat = replaceCoreTerm substitutions pat
                    let newBody = replaceCoreTerm substitutions body
                    (newPat, newBody)) m.Cases
                if newToMatch = m.ToMatch && newCases = m.Cases then
                    term
                else
                    Match { m with ToMatch = newToMatch; Cases = newCases }

            | Closure c ->
                let newEnv = Map.map (fun _ v -> replaceCoreTerm substitutions v) c.Env
                let newValue = replaceCoreTerm substitutions c.Value
                if newEnv = c.Env && newValue = c.Value then
                    term
                else
                    Closure { c with Env = newEnv; Value = newValue }

            | FunctionalApplication fa ->
                let newBase = replaceCoreTerm substitutions fa.Base
                let newArgs = List.map (replaceCoreTerm substitutions) fa.Arguments
                if newBase = fa.Base && newArgs = fa.Arguments then
                    term
                else
                    FunctionalApplication { fa with Base = newBase; Arguments = newArgs }

            | TermSequence terms ->
                let newTerms = List.map (replaceCoreTerm substitutions) terms
                if newTerms = terms then
                    term
                else
                    TermSequence newTerms

            | CoreLet l ->
                let newPattern = replaceCoreTerm substitutions l.Pattern
                let newValue = replaceCoreTerm substitutions l.Value
                if newPattern = l.Pattern && newValue = l.Value then
                    term
                else
                    CoreLet { l with Pattern = newPattern; Value = newValue }

            | WhileLoop w ->
                let newPred = replaceCoreTerm substitutions w.Predicate
                let newBody = replaceCoreTerm substitutions w.Body
                if newPred = w.Predicate && newBody = w.Body then
                    term
                else
                    WhileLoop { w with Predicate = newPred; Body = newBody }

            | UpdateVariable (name, expr) ->
                let newExpr = replaceCoreTerm substitutions expr
                if newExpr = expr then
                    term
                else
                    UpdateVariable (name, newExpr)

            | Resume r ->
                let newRewrite = replaceCoreTerm substitutions r.Rewrite
                let newState = replaceCoreTerm substitutions r.State
                if newRewrite = r.Rewrite && newState = r.State then
                    term
                else
                    Resume { r with Rewrite = newRewrite; State = newState }

            | Handle h ->
                let newState = replaceCoreTerm substitutions h.State
                let newToHandle = replaceCoreTerm substitutions h.ToHandle
                if newState = h.State && newToHandle = h.ToHandle then
                    term
                else
                    Handle { h with State = newState; ToHandle = newToHandle }

            | WhenClause (cond, body) ->
                let newCond = replaceCoreTerm substitutions cond
                let newBody = replaceCoreTerm substitutions body
                if newCond = cond && newBody = body then
                    term
                else
                    WhenClause (newCond, newBody)

            | AsClause (pat, body) ->
                let newPat = replaceCoreTerm substitutions pat
                let newBody = replaceCoreTerm substitutions body
                if newPat = pat && newBody = body then
                    term
                else
                    AsClause (newPat, newBody)

            | Substitution sub ->
                let newEnv = List.map (fun (a, b) -> (a, replaceCoreTerm substitutions b)) sub.Env
                let newInExpr = replaceCoreTerm substitutions sub.InExpr
                
                Substitution
                    { Env = newEnv
                      InExpr = newInExpr }

            | UsingContext ctx ->
                UsingContext { ctx with Expr = replaceCoreTerm substitutions ctx.Expr }

            | Wildcard -> term
