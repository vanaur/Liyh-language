namespace Liyh.Execution.Core

module AlphaConversion =
    open Liyh.Execution.Core

    let rec private boundVariables (term: CoreTerm) : Set<string> =
        match term with
        | Variable v ->
            Set.singleton v

        | Symbol symb ->
            symb.Children
            |> List.map boundVariables
            |> Set.unionMany

        | RecordExtend re ->
            let baseVars =
                re.BaseRecord
                |> Option.map boundVariables
                |> Option.defaultValue Set.empty

            let extVars =
                re.Extension
                |> List.map (snd >> boundVariables)
                |> Set.unionMany

            Set.union baseVars extVars

        | FunctionalApplication fa ->
            let args =
                fa.Arguments
                |> List.map boundVariables
                |> Set.unionMany

            Set.union (boundVariables fa.Base) args

        | WhenClause(p, _) -> boundVariables p
        | AsClause(p, asP) -> Set.union (boundVariables p) (boundVariables asP)
        | (Literal _ | Wildcard) -> Set.empty
        | _ -> failwithf "Unexpected bound variable: %A" term //Set.empty

    let rec private alphaConversion
        (getUniqueVariable: string -> string)
        (renaming: Map<string, string>)
        (term: CoreTerm)
        =
        let ac = alphaConversion getUniqueVariable

        match term with
        | Variable v ->
            Map.tryFind v renaming
            |> Option.map Variable
            |> Option.defaultValue term

        | Symbol symb ->
            let children = List.map (ac renaming) symb.Children
            Symbol { symb with Children = children }

        | Literal _ -> term

        | RecordExtend re ->
            RecordExtend
                { BaseRecord = Option.map (ac renaming) re.BaseRecord
                  Extension = List.map (fun (k, v) -> k, ac renaming v) re.Extension }

        | Match m ->
            let toMatch = ac renaming m.ToMatch

            let cases =
                m.Cases
                |> List.map (fun (patt, body) ->
                    let bound = boundVariables patt
                    let fresh = bound |> Seq.map (fun v -> v, getUniqueVariable v) |> Map.ofSeq
                    let extendedRenaming = Map.fold (fun acc k v -> Map.add k v acc) renaming fresh
                    let newPatt = ac extendedRenaming patt
                    let newBody = ac extendedRenaming body
                    newPatt, newBody)

            Match { ToMatch = toMatch; Cases = cases }

        | Closure c ->
            let fresh =
                c.Parameters
                |> List.map (fun p -> p, getUniqueVariable p)
                |> Map.ofList

            let extendedRenaming = Map.fold (fun acc k v -> Map.add k v acc) renaming fresh

            let newEnv =
                c.Env
                |> Map.toList
                |> List.map (fun (k, v) ->
                    let newK = Option.defaultValue k (Map.tryFind k renaming)
                    let newV = ac renaming v
                    (newK, newV))
                |> Map.ofList

            let newParams = List.map (fun p -> Map.find p fresh) c.Parameters
            let newValue = ac extendedRenaming c.Value

            Closure
                { Env = newEnv
                  IsEvaluated = c.IsEvaluated
                  Parameters = newParams
                  Value = newValue }

        | FunctionalApplication fa ->
            FunctionalApplication
                { Base = ac renaming fa.Base
                  Arguments = List.map (ac renaming) fa.Arguments }

        | TermSequence ts ->
            let rec processSeq accRenaming accTerms ts =
                match ts with
                | [] -> TermSequence(List.rev accTerms)
                | t :: rest ->
                    match t with
                    | CoreLet let' ->
                        let newValue = ac accRenaming let'.Value
                        let bound = boundVariables let'.Pattern

                        let fresh =
                            bound
                            |> Seq.map (fun v -> v, getUniqueVariable v)
                            |> Map.ofSeq

                        let extended = Map.fold (fun acc k v -> Map.add k v acc) accRenaming fresh
                        let newPattern = ac extended let'.Pattern

                        let newLet =
                            CoreLet
                                { Pattern = newPattern
                                  Value = newValue
                                  IsVariable = let'.IsVariable }

                        processSeq extended (newLet :: accTerms) rest

                    | WhileLoop w ->
                        let newPred = ac accRenaming w.Predicate
                        let newBody = ac accRenaming w.Body
                        let newWhile = WhileLoop { Predicate = newPred; Body = newBody }
                        processSeq accRenaming (newWhile :: accTerms) rest

                    | UpdateVariable(v, expr) ->
                        let newV = Map.tryFind v accRenaming |> Option.defaultValue v
                        let newExpr = ac accRenaming expr
                        let newUpdate = UpdateVariable(newV, newExpr)
                        processSeq accRenaming (newUpdate :: accTerms) rest

                    | _ ->
                        let newT = ac accRenaming t
                        processSeq accRenaming (newT :: accTerms) rest

            processSeq renaming [] ts

        | WhileLoop w ->
            WhileLoop
                { Predicate = ac renaming w.Predicate
                  Body = ac renaming w.Body }

        | UpdateVariable(v, expr) ->
            let newV = Map.tryFind v renaming |> Option.defaultValue v
            UpdateVariable(newV, ac renaming expr)

        | WhenClause(cond, cons) -> WhenClause(ac renaming cond, ac renaming cons)
        | AsClause(patt, value) -> AsClause(ac renaming patt, ac renaming value)

        | Resume r ->
            Resume
                { Rewrite = ac renaming r.Rewrite
                  State = ac renaming r.State }

        | Handle h ->
            Handle
                { Handler = h.Handler
                  State = ac renaming h.State
                  ToHandle = ac renaming h.ToHandle }

        | CoreLet l ->
            let bound = boundVariables l.Pattern
            let fresh = bound |> Seq.map (fun v -> v, getUniqueVariable v) |> Map.ofSeq
            let extendedRenaming = Map.fold (fun acc k v -> Map.add k v acc) renaming fresh

            CoreLet
                { Pattern = ac extendedRenaming l.Pattern
                  Value = ac renaming l.Value
                  IsVariable = l.IsVariable }

        | Wildcard -> term

    let public alphaConversionDefinition (getUniqueVariable: string -> string) (def: CoreDefinition) =
        let ac = alphaConversion getUniqueVariable

        match def with
        | Rule r ->
            let bound = boundVariables r.LHS

            let fresh =
                bound |> Set.toSeq |> Seq.map (fun v -> v, getUniqueVariable v) |> Map.ofSeq

            let newLHS = ac fresh r.LHS
            let newRHS = ac fresh r.RHS
            let newWhen = Option.map (ac fresh) r.WhenClause

            Rule
                { r with
                    LHS = newLHS
                    RHS = newRHS
                    WhenClause = newWhen }

        | Handler h ->
            let boundL = boundVariables h.LHS
            let boundS = boundVariables h.State
            let bound = Set.union boundL boundS

            let fresh =
                bound |> Set.toSeq |> Seq.map (fun v -> v, getUniqueVariable v) |> Map.ofSeq

            let newLHS = ac fresh h.LHS
            let newState = ac fresh h.State
            let newRHS = ac fresh h.RHS
            let newWhen = Option.map (ac fresh) h.WhenClause

            Handler
                { h with
                    LHS = newLHS
                    State = newState
                    RHS = newRHS
                    WhenClause = newWhen }

