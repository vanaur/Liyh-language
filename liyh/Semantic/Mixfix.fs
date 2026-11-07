namespace Liyh.Semantic

module private Mixfix =
    open Liyh.Syntax.SyntaxTree

    /// Extracts the hole identifiers from a notation in the order in which they appear.
    let public getNotationHoles (notation: Notation) : string list =
        removePos notation.NotationPattern
        |> List.choose (function
            | HolePart h -> Some (removePos h)
            | _ -> None)

    /// Reconstructs a readable representation of the notation pattern.
    let public describeNotationPattern (notation: Notation) : string =
        removePos notation.NotationPattern
        |> List.map (fun part ->
            match part with
            | HolePart h -> sprintf "_%s" (removePos h)
            | other ->
                let _, fields = Reflection.FSharpValue.GetUnionFields(other, other.GetType())
                match fields with
                | [| (:? WithPos<string> as wp) |] -> wp.Node
                | [| (:? string as s) |] -> s
                | _ -> sprintf "%A" other)
        |> String.concat " "

    /// Check that no holes collide with the function heads called in the notation's rewrite.
    /// as well as the other properties that notations have to verify.
    let private validateNotationTemplate (tsCtx: TypecheckContext) (notation: Notation) =
        let holes = Set.ofList (getNotationHoles notation)

        // Check that commutative operators are of arity 2.
        if removePos notation.NotationCommutative = true && Set.count holes <> 2 then
            let desc = sprintf "Notation '%s' is marked as commutative, but expects %d operand(s). Only binary operators can be commutative." (removePos notation.NotationName) (Set.count holes)
            let hint = "Set 'commutative: false' or define a pattern with exactly two operands."
            tsCtx.ReportError ErrorCode.ArityMismatchError desc [] hint notation.NotationCommutative

        // Check that the rewrite target do not collide with the definition.
        let rec collectCallees (expr: ExpressionWithPos) =
            match expr.Node with
            | Apply { LHS = { Node = Identifier id } } when List.isEmpty id.Qualifier -> [ removePos id.Name ]
            | Apply apply -> collectCallees apply.LHS
            | _ -> []

        let callees = collectCallees notation.NotationIs
        for callee in callees do
            if Set.contains callee holes then
                let desc = sprintf "Notation hole '%s' clashes with the target rule '%s' in the rewrite expression." callee callee
                let hint = "Rename the notation hole to avoid capturing the rule identifier."
                tsCtx.ReportError ErrorCode.InvalidNotationError desc [] hint notation.NotationName

    /// Registers the module marks to the environment.
    let public registerNotations (tsCtx: TypecheckContext) (env: Env) (notations: Notation list) : Env =

        let rec loop (notationMap: Map<string, Notation>) (notations: Notation list) =
            match notations with
            | [] -> notationMap
            | nt :: rest ->
                let name = removePos nt.NotationName

                if Map.containsKey name notationMap then
                    let showPos = showInlinePosition notationMap.[name].NotationName
                    let desc = sprintf "Duplicate notation declaration: '%s' is already defined %s." name showPos

                    tsCtx.ReportError ErrorCode.DuplicateDeclarationError desc [] null nt.NotationName
                    loop notationMap rest
                else
                    validateNotationTemplate tsCtx nt
                    loop (Map.add name nt notationMap) rest

        { env with Notations = loop env.Notations notations }

    /// Replaces the holes in a notation expression with the actual expression arguments.
    let rec public substExpression
        (callSite: WithPos<_>)
        (subst: Map<string, ExpressionWithPos>)
        (exprWithPos: ExpressionWithPos)
        : ExpressionWithPos
        =

        // Uses the call site position for the given node.
        let reanchor = withPosOf callSite

        match exprWithPos.Node with
        | Identifier id when List.isEmpty id.Qualifier && Map.containsKey (removePos id.Name) subst ->
            subst.[removePos id.Name]

        | Identifier _ ->
            reanchor exprWithPos.Node

        | Literal _ ->
            reanchor exprWithPos.Node

        | Apply apply ->
            let newLhs = substExpression callSite subst apply.LHS
            let newArgs = List.map (substExpression callSite subst) apply.Arguments
            reanchor (Apply { LHS = newLhs; Arguments = newArgs })

        | Tuple items ->
            reanchor (Tuple (List.map (substExpression callSite subst) items))

        | List items ->
            reanchor (List (List.map (substExpression callSite subst) items))

        | Lambda lambda ->
            reanchor (Lambda { lambda with Body = substExpression callSite subst lambda.Body })

        | Match m ->
            let newCases = List.map (fun (p, b) -> p, substExpression callSite subst b) m.Cases
            reanchor (Match { ToMatch = substExpression callSite subst m.ToMatch; Cases = newCases })

        | IfThenElse ifte ->
            let newElifs =
                ifte.ElifBranches
                |> List.map (fun (c, b) -> substExpression callSite subst c, substExpression callSite subst b)
            let newElse = Option.map (substExpression callSite subst) ifte.ElseBranch

            reanchor (IfThenElse { Condition = substExpression callSite subst ifte.Condition
                                   ThenBranch = substExpression callSite subst ifte.ThenBranch
                                   ElifBranches = newElifs; ElseBranch = newElse })

        | ExpressionSequence exprs ->
            reanchor (ExpressionSequence (List.map (substExpression callSite subst) exprs))

        | Let(patt, value) ->
            reanchor (Let(patt, substExpression callSite subst value))

        | Var(patt, value) ->
            reanchor (Var(patt, substExpression callSite subst value))

        | ReAssign(name, value) ->
            reanchor (ReAssign(name, substExpression callSite subst value))

        | While w ->
            reanchor (While { Predicate = substExpression callSite subst w.Predicate
                              Body = substExpression callSite subst w.Body })

        | CollectionAccess ca ->
            reanchor (CollectionAccess { LHS = substExpression callSite subst ca.LHS
                                         Indices = List.map (substExpression callSite subst) ca.Indices })

        | Record fields ->
            reanchor (Record (List.map (fun (n, e) -> n, substExpression callSite subst e) fields))

        | RecordUsing(baseExpr, updates) ->
            reanchor (RecordUsing(substExpression callSite subst baseExpr, List.map (fun (n, e) -> n, substExpression callSite subst e) updates))

        | MixfixOperator mix ->
            reanchor (MixfixOperator { mix with Arguments = List.map (substExpression callSite subst) mix.Arguments })

        | UFCS ufcs ->
            reanchor (UFCS { LHS = substExpression callSite subst ufcs.LHS
                             RHS = substExpression callSite subst ufcs.RHS })

        | other -> reanchor other

    /// Converts a notation expression body to a pattern by substituting holes.
    let rec public exprToPatternWithSubst
        (tsCtx: TypecheckContext)
        (callSite: WithPos<_>)
        (subst: Map<string, PatternWithPos>)
        (exprWithPos: ExpressionWithPos)
        : PatternWithPos
        =

        let reanchor node =
            { Node = node
              StartPos = callSite.StartPos
              EndPos = callSite.EndPos }

        match exprWithPos.Node with
        | Identifier id when List.isEmpty id.Qualifier && Map.containsKey (removePos id.Name) subst ->
            subst.[removePos id.Name]

        | Identifier id ->
            reanchor (IdentPattern id)

        | Literal lit ->
            reanchor (LiteralPattern lit)

        | Tuple elements ->
            reanchor (TuplePattern (List.map (exprToPatternWithSubst tsCtx callSite subst) elements))

        | List elements ->
            reanchor (ListPattern (List.map (exprToPatternWithSubst tsCtx callSite subst) elements))

        | Apply apply ->
            let phead = exprToPatternWithSubst tsCtx callSite subst apply.LHS
            let pargs = List.map (exprToPatternWithSubst tsCtx callSite subst) apply.Arguments
            reanchor (ApplyPattern(phead, pargs))

        | Record fields ->
            let fieldPatts = List.map (fun (nameWp, e) -> nameWp, exprToPatternWithSubst tsCtx callSite subst e) fields
            reanchor (RecordPattern fieldPatts)

        | _ ->
            let desc = "Expression in notation expansion cannot be used as a pattern."
            tsCtx.ReportError ErrorCode.InvalidPatternError desc [] null callSite
            reanchor Wildcard

    /// Extracts the target rule name from a notation rewrite expression.
    /// This function expects that the notation rewrites to an identifier, else returns `None`.
    let public getNotationTargetSymbolName (notation: Notation) : string option =

        let rec extract (expr: ExpressionWithPos) =
            match removePos expr with
            | Apply { LHS = lhs } -> extract lhs
            | Identifier id -> Some (string id)
            | _ -> None

        extract notation.NotationIs

    /// Finds whether a given rule name corresponds to a commutative notation in the environment.
    let public tryFindCommutativeNotation (env: Env) (ruleName: string) : Notation option =
        env.Notations
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.tryFind (fun notation ->
            removePos notation.NotationCommutative = true
            && getNotationTargetSymbolName notation = Some ruleName)

