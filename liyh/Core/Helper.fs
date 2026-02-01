#nowarn "46"
namespace rec Liyh.Core

module public Helper =

    let private trueSymbol = simpleSymbol "true"
    let private falseSymbol = simpleSymbol "false"

    /// Reprsent the if-then-else operation.
    let public ifte (if': CoreTerm) (then': CoreTerm) (else': CoreTerm) =
        Match
            { ToMatch = if'
              Cases = [ (trueSymbol, then'); (falseSymbol, else') ] }

    /// Flattern each redoundant term sequence in the given term.
    let rec public flattenTermSequence (term: CoreTerm) =
        match term with
        | TermSequence terms ->
            let flattenedTerms =
                terms
                |> List.collect (fun t ->
                    match flattenTermSequence t with
                    | TermSequence nestedTerms -> nestedTerms
                    | other -> [ other ])

            TermSequence flattenedTerms

        | Symbol symbol ->
            copySymbolWithNewChildren symbol (List.map flattenTermSequence symbol.Children)

        | Variable _ -> term
        | Literal _ -> term
        | RecordExtend { BaseRecord = baseRecord
                         Extension = fields } ->
            RecordExtend
                { BaseRecord = Option.map flattenTermSequence baseRecord
                  Extension = fields |> List.map (fun (name, value) -> (name, flattenTermSequence value)) }

        | Closure { Env = env
                    Parameters = params
                    Value = body } ->
            Closure
                { Env = env
                  IsEvaluated = false
                  Parameters = params
                  Value = flattenTermSequence body }

        | FunctionalApplication { Base = func; Arguments = args } ->
            FunctionalApplication
                { Base = flattenTermSequence func
                  Arguments = args |> List.map flattenTermSequence }

        | CoreLet letExpr ->
            CoreLet
                { letExpr with
                    Pattern = flattenTermSequence letExpr.Pattern
                    Value = flattenTermSequence letExpr.Value }

        | WhileLoop whileExpr ->
            WhileLoop
                { whileExpr with
                    Predicate = flattenTermSequence whileExpr.Predicate
                    Body = flattenTermSequence whileExpr.Body }

        | UpdateVariable(var, value) -> UpdateVariable(var, flattenTermSequence value)
        | WhenClause(condition, consequence) ->
            WhenClause(flattenTermSequence condition, flattenTermSequence consequence)

        | AsClause(pattern, value) -> AsClause(flattenTermSequence pattern, flattenTermSequence value)
        | Match { ToMatch = toMatch; Cases = cases } ->
            Match
                { ToMatch = flattenTermSequence toMatch
                  Cases = List.map (fun (a, b) -> flattenTermSequence a, flattenTermSequence b) cases }

        | Resume { Rewrite = rewrite
                   State = state
                   FromHandler = fh } ->
            Resume
                { Rewrite = flattenTermSequence rewrite
                  State = flattenTermSequence state
                  FromHandler = fh }

        | Handle { Handler = handler
                   State = state
                   ToHandle = toHandle } ->
            Handle
                { Handler = handler
                  State = flattenTermSequence state
                  ToHandle = flattenTermSequence toHandle }

        | Substitution { Env = env
                         InExpr = inExpr } ->

            Substitution
                { Env = List.map (fun (a, b) -> (a, flattenTermSequence b)) env
                  InExpr = flattenTermSequence inExpr }

        | UsingContext ctx ->
            UsingContext { ctx with Expr = flattenTermSequence ctx.Expr }

        | Wildcard -> term

    /// Retrieves variables that are not defined in `term` nor present in `boundVars`.
    let public freeVariables (boundVars: Set<string>) (term: CoreTerm) =
        let mutable internalVars = Set.empty
        let mutable asDefined = Set.empty

        let rec loop =
            function
            | Variable v ->
                if not (Set.contains v boundVars) && not (Set.contains v internalVars) then
                    Set.singleton v
                else
                    Set.empty

            | CoreLet { Pattern = patt; Value = value } ->
                internalVars <- Set.union internalVars (loop patt)
                loop value

            | Symbol symbol ->
                if symbol.IsVariable then
                    loop (Variable symbol.Symbol)
                else
                    symbol.Children |> List.map loop |> Set.unionMany

            | TermSequence terms -> terms |> List.map loop |> Set.unionMany

            | RecordExtend { BaseRecord = baseRecord
                             Extension = fields } ->
                let a = baseRecord |> Option.map loop |> Option.defaultValue Set.empty
                let b = fields |> List.map (snd >> loop) |> Set.unionMany
                Set.union a b

            | Closure closure ->
                internalVars <- Set.union internalVars (Set.ofList closure.Parameters)
                loop closure.Value

            | FunctionalApplication { Base = fn; Arguments = args } ->
                let a = loop fn
                let b = args |> List.map loop |> Set.unionMany
                Set.union a b

            | WhenClause(patt, pred) ->
                let a = loop patt
                let b = loop pred
                Set.union a b

            | AsClause(patt, as') ->
                let a = loop patt
                let b = loop as'

                internalVars <- Set.union internalVars a
                internalVars <- Set.union internalVars b

                asDefined <- Set.union asDefined b

                a

            | Match match' ->
                let a = loop match'.ToMatch

                let casesVars, valuesVars =
                    match'.Cases
                    |> List.map (fun (patt, value) -> loop patt, loop value)
                    |> List.unzip

                let casesVars = Set.unionMany casesVars
                internalVars <- Set.union internalVars casesVars

                let valuesVars = Set.unionMany valuesVars
                let valuesVars = Set.difference valuesVars casesVars

                Set.union a valuesVars

            | WhileLoop whileLoop ->
                let a = loop whileLoop.Predicate
                let b = loop whileLoop.Body

                Set.union a b

            | UpdateVariable(v, value) ->
                // We can potentially detect here if an external variable (`v`) is updated, do we throw an error?
                // → Normally, this is handled in the previous phases.
                loop value

            | Resume resume ->
                let a = loop resume.Rewrite
                let b = loop resume.State
                Set.union a b

            | Handle handle ->
                let a = loop handle.State
                let b = loop handle.ToHandle
                Set.union a b

            | Substitution sub ->
                let a = List.foldBack (snd >> loop >> Set.union) sub.Env Set.empty
                let b = loop sub.InExpr
                Set.union a b

            | UsingContext ctx ->
                loop ctx.Expr

            | Wildcard
            | Literal _ -> Set.empty

        loop term, asDefined

