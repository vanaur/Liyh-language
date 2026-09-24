namespace Liyh.Core

module AlphaConversion =

    let rec private boundVariables (term: CoreTerm) : Set<string> =
        match term with
        | Variable v ->
            Set.singleton v

        | VariableApply(v, args) ->
            let argsBound = args |> List.map boundVariables |> Set.unionMany
            Set.add v argsBound

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

        | WhenClause(p, _) -> boundVariables p
        | AsClause(p, asP) -> Set.union (boundVariables p) (boundVariables asP)
        | (Literal _ | Wildcard) -> Set.empty
        | _ -> failwithf "Unexpected bound variable: %A" term //Set.empty

    let private extendRenaming (getUniqueVariable: string -> string) (renaming: Map<string, string>) (vars: Set<string>) =
        let fresh = vars |> Seq.map (fun v -> v, getUniqueVariable v) |> Map.ofSeq
        let extended = Map.fold (fun acc k v -> Map.add k v acc) renaming fresh

        (fresh, extended)

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

        | VariableApply(v, args) ->
            let newV = Map.tryFind v renaming |> Option.defaultValue v
            let newArgs = List.map (ac renaming) args
            VariableApply(newV, newArgs)

        | RecordExtend re ->
            RecordExtend
                { BaseRecord = Option.map (ac renaming) re.BaseRecord
                  Extension = List.map (fun (k, v) -> k, ac renaming v) re.Extension }

        | Match m ->
            let toMatch = ac renaming m.ToMatch

            let cases =
                m.Cases
                |> List.map (fun (patt, body) ->
                    let _, extended = boundVariables patt |> extendRenaming getUniqueVariable renaming
                    ac extended patt, ac extended body)

            Match { ToMatch = toMatch; Cases = cases }

        | Closure c ->
            let fresh, extended = Set.ofList c.Parameters |> extendRenaming getUniqueVariable renaming
            let newEnv = c.Env |> Map.map (fun _ v -> ac renaming v)
            let newParams = List.map (fun p -> Map.find p fresh) c.Parameters

            Closure
                { Env = newEnv
                  IsEvaluated = c.IsEvaluated
                  Parameters = newParams
                  Value = ac extended c.Value }

        | FunctionalApplication fa ->
            FunctionalApplication
                { Base = ac renaming fa.Base
                  Arguments = List.map (ac renaming) fa.Arguments }

        | TermSequence ts ->
            let rec processSeq accRenaming accTerms = function
                | [] -> TermSequence(List.rev accTerms)
                | (CoreLet let') :: rest ->
                    let newValue = ac accRenaming let'.Value
                    let _, extended = boundVariables let'.Pattern |> extendRenaming getUniqueVariable accRenaming
                    let newLet =
                        CoreLet
                            { Pattern = ac extended let'.Pattern
                              Value = newValue
                              IsMutable = let'.IsMutable }
                    processSeq extended (newLet :: accTerms) rest
                | t :: rest ->
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
                  State = ac renaming r.State
                  FromHandler = r.FromHandler }

        | Handle h ->
            Handle
                { Handler = h.Handler
                  State = ac renaming h.State
                  ToHandle = ac renaming h.ToHandle }

        | CoreLet l ->
            let _, extended = boundVariables l.Pattern |> extendRenaming getUniqueVariable renaming
            CoreLet
                { Pattern = ac extended l.Pattern
                  Value = ac renaming l.Value
                  IsMutable = l.IsMutable }

        | Substitution sub ->
            Substitution
                { Env = List.map (fun (a, b) -> a, ac renaming b) sub.Env
                  InExpr = ac renaming sub.InExpr }

        | UsingContext ctx ->
            UsingContext { ctx with Expr = ac renaming ctx.Expr }

        | (Literal _ | Wildcard) -> term

    let rec public alphaConversionDefinition (getUniqueVariable: string -> string) (def: CoreDefinition) =
        let ac = alphaConversion getUniqueVariable

        match def with
        | Rule r ->
            let fresh, _ = boundVariables r.LHS |> extendRenaming getUniqueVariable Map.empty
            Rule
                { r with
                    LHS = ac fresh r.LHS
                    RHS = ac fresh r.RHS
                    WhenClause = Option.map (ac fresh) r.WhenClause }

        | Handler h ->
            let bound = Set.union (boundVariables h.LHS) (boundVariables h.State)
            let fresh, _ = bound |> extendRenaming getUniqueVariable Map.empty
            Handler
                { h with
                    LHS = ac fresh h.LHS
                    State = ac fresh h.State
                    RHS = ac fresh h.RHS
                    WhenClause = Option.map (ac fresh) h.WhenClause }

        | Context ctx ->
            let content = ctx.Content |> List.map (alphaConversionDefinition getUniqueVariable) 
            Context { ctx with Content = content }

