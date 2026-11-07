namespace Liyh.Semantic

module private Unification =
    open Liyh.Syntax.SyntaxTree
    open Liyh.FFI.GeneralFFI

    /// A step from the path taken while unifying.
    [<RequireQualifiedAccess>]
    type internal Step =
        | Parameter of int
        | ReturnType
        | TupleComponent of int
        | TypeArgument of int
        | Field of string
        | RecordRow
        | MeasureBase

        override this.ToString() =
            match this with
            | Parameter k -> sprintf "parameter %d" k
            | ReturnType -> "return type"
            | TupleComponent k -> sprintf "tuple component %d" k
            | TypeArgument k -> sprintf "argument %d" k
            | Field s -> sprintf "field `%s`" s
            | RecordRow -> "record row"
            | MeasureBase -> "measure base"


    //                      //
    // --- Some Helpers --- //
    //                      //


    exception private UnifyFailure of path: Step list * diagnostic: InternalDiagnostic

    let private failWithHint (path: Step list) (message: string) (infos: string list) (hint: string) =
        raise (UnifyFailure(path, { Message = message; Informations = infos; Hint = hint }))

    let private fail (path: Step list) (message: string) (infos: string list) =
        failWithHint path message infos null

    let private showEffects (effects: Set<string>) =
        if Set.isEmpty effects then "{ }" else sprintf "{ %s }" (String.concat ", " effects)

    let private formatPath (path: Step list) : string list =
        match path with
        | [] -> []
        | _ ->
            let steps =
                path
                |> List.rev
                |> List.map string
                |> String.concat " -> "

            [ sprintf "At: %s." steps ]


    //                                   //
    // --- Occur check & Unification --- //
    //                                   //


    /// Checks if the given DimVar is part of the given Dimension map.
    let private occursDim (v: DimVar ref) (d: Dimension) =
        Dimension.prune d
        |> Map.exists (fun atom _ ->
            match atom with
            | DimVar v' -> LanguagePrimitives.PhysicalEquality v v'
            | _ -> false)

    /// Try to unify the given two dimensions.
    /// Unifying two dimensions (`d₁ = d₂`) is equivalent to solve the equation `d₁ - d₂ = 0` over ℚ.
    let private unifyDim (tsCtx: TypecheckContext) (path: Step list) (d1: Dimension) (d2: Dimension) : unit =
        let diff = Dimension.prune (Dimension.div d1 d2)

        if Map.isEmpty diff then ()
        else
            // Search for a free variable to isolate: `c * v + rest = 0 <=> v = -rest/c`.

            let varOpt =
                Map.tryPick (fun atom coeff ->
                    match atom with
                    | DimVar({ contents = UnboundDim _ } as r) -> Some(r, coeff)
                    | _ -> None
                ) diff

            match varOpt with
            | Some(r, c) ->
                let rest = Map.remove (DimVar r) diff
                let isolated = Dimension.scale (Rational.Create(-c.Den, c.Num)) rest

                if occursDim r isolated then
                    fail path
                        (sprintf "Dimensional incompatibility: cannot unify [%s] with [%s]." (Dimension.toString d1) (Dimension.toString d2))
                        [ "The equation would define a dimension variable in terms of itself, which has no finite solution." ]

                tsCtx.BindDimVar r (LinkDim isolated)

            | None ->
                failWithHint path
                    (sprintf "Dimensional incompatibility: cannot unify [%s] with [%s]." (Dimension.toString d1) (Dimension.toString d2))
                    [ sprintf "Their ratio is [%s], which is not dimensionless." (Dimension.toString diff) ]
                    "Check that both sides of the operation use compatible units."

    /// Checks if the given `TVar` exists in the given type `t`.
    let rec private occursVar (v: TypeVar ref) (t: LiyhType) =
        match t.Prune() with
        | TVar v' -> LanguagePrimitives.PhysicalEquality v v'
        | TArrow(args, ret, _) -> List.exists (occursVar v) args || occursVar v ret
        | TTuple ts -> List.exists (occursVar v) ts
        | TRecord(fields, rest) -> Map.exists (fun _ t' -> occursVar v t') fields || occursVar v rest
        | TApp(_, args) -> List.exists (occursVar v) args
        | TMeasure(baseT, _) -> occursVar v baseT
        | _ -> false

    /// Updates the type variables relative to `t1` and `t2` when they unify.
    /// This function can raise an `UnifyException` exception containing detailed diagnostics.
    let rec private unifyRec (tsCtx: TypecheckContext) (path: Step list) (t1: LiyhType) (t2: LiyhType) =
        match t1.Prune(), t2.Prune() with
        | (t1, t2) when t1 = t2 -> ()

        | TVar({ contents = UnboundVar _ } as r), other
        | other, TVar({ contents = UnboundVar _ } as r) ->
            if occursVar r other then
                fail path "Infinite recursive type."
                    [ sprintf "`%s` occurs in `%s`, so the type would have to contain itself."
                        (string (TVar r)) (string other) ]

            tsCtx.BindTypeVar r (LinkVar other)

        | TArrow(args1, ret1, effs1), TArrow(args2, ret2, effs2) ->
            let (n1, n2) = List.length args1, List.length args2

            if n1 <> n2 then
                fail path "Function types take a different number of parameters."
                    [ sprintf "`%s` takes %d parameter(s), `%s` takes %d." (string t1) n1 (string t2) n2 ]

            if effs1 <> effs2 then
                fail path "Incompatible effects."
                    [ sprintf "Effect sets differ: %s vs %s." (showEffects effs1) (showEffects effs2) ]

            List.iteri2 (fun i -> unifyRec tsCtx (Step.Parameter (i + 1) :: path)) args1 args2
            unifyRec tsCtx (Step.ReturnType :: path) ret1 ret2

        | TTuple ts1, TTuple ts2 ->
            let (n1, n2) = List.length ts1, List.length ts2

            if n1 <> n2 then
                fail path "Tuples have a different number of components."
                    [ sprintf "`%s` has %d component(s), `%s` has %d." (string t1) n1 (string t2) n2 ]

            List.iteri2 (fun i -> unifyRec tsCtx (Step.TupleComponent (i + 1) :: path)) ts1 ts2

        | (TRecord _ as t1), (TRecord _ as t2) ->
            unifyRecords tsCtx path t1 t2

        | (TSymbolic, _) | (_, TSymbolic) ->
            ()

        | TApp(name1, args1), TApp(name2, args2) when name1 = name2 ->
            let (n1, n2) = List.length args1, List.length args2

            if n1 <> n2 then
                fail path (sprintf "Type `%s` is applied to a different number of arguments." name1)
                    [ sprintf "`%s` has %d argument(s), `%s` has %d." (string t1) n1 (string t2) n2 ]

            List.iteri2 (fun i -> unifyRec tsCtx (Step.TypeArgument (i + 1) :: path)) args1 args2

        | TMeasure(base1, dim1), TMeasure(base2, dim2) ->
            unifyRec tsCtx (Step.MeasureBase :: path) base1 base2
            unifyDim tsCtx path dim1 dim2

        | (TMeasure(b, d), other) | (other, TMeasure(b, d)) ->
            // A scalar is an undimensionned value

            unifyRec tsCtx (Step.MeasureBase :: path) b other
            unifyDim tsCtx path d Dimension.empty

        | THandlerInstance(h1, e1), THandlerInstance(h2, e2) when h1 = h2 && e1 = e2 ->
            ()

        | TEmptyRow, (TRecord _ as extra)
        | (TRecord _ as extra), TEmptyRow ->
            let msg = sprintf "Closed record does not allow unexpected field(s): `%s`." (string extra)
            fail path msg []

        | TCType (CType.Pointer p1), TCType (CType.Pointer p2) ->
            if p1 = CType.Void || p2 = CType.Void then
                ()
            else
                unifyRec tsCtx (Step.TypeArgument 1 :: path) (TCType p1) (TCType p2)

        | TCType cty, other
        | other, TCType cty ->
            match ForeignTypes.liyhCTypeCompatible cty with
            | Some compat when compat = other -> ()
            | _ ->
                let msg = sprintf "Type mismatch: `%s` is not compatible with `%s`." (string t1) (string t2)
                fail path msg []

        | (t1, t2) ->
            //let msg = sprintf "Cannot unify `%s` with `%s`." (string t1) (string t2)
            let msg = sprintf "Type mismatch: `%s` is not compatible with `%s`." (string t1) (string t2)
            fail path msg []

    /// This function normalises and flattens the fields of nested records that share an open row.
    /// The returned value is the tuple `(fields, row)`.
    ///
    /// A typed record looks like `{ x: int, y: string | ρ }` where `ρ` stands for the other possible fields
    /// of the record (the "row"). During type inference, this variable can be unified with another record
    /// given a nested structure, for example: `{ x: int | { y: string | { z: bool | ρ } } }`.
    /// Semantically, it is the same as `{x: int, y: string, z: bool | ρ}`, but represented in a nested form.
    ///
    /// In case of fields collision, we simply check that their types unify.
    and public flattenRecord
        (tsCtx: TypecheckContext)
        (path: Step list)
        (fields: Map<string, LiyhType>)
        (row: LiyhType)
        : Map<string, LiyhType> * LiyhType
        =
        match row.Prune() with
        | TRecord(fields', rest') ->
            let combined =
                Map.fold (fun acc k v ->
                    match Map.tryFind k acc with
                    | None -> Map.add k v acc
                    | Some existing ->
                        unifyRec tsCtx (Step.Field k :: path) existing v
                        acc
                ) fields fields'

            flattenRecord tsCtx path combined rest'

        | other ->
            (fields, other)

    and private unifyRecords (tsCtx: TypecheckContext) (path: Step list) (t1: LiyhType) (t2: LiyhType) =
        let (f1, r1) = match t1.Prune() with TRecord(f, r) -> flattenRecord tsCtx path f r | _ -> failwith "unreachable"
        let (f2, r2) = match t2.Prune() with TRecord(f, r) -> flattenRecord tsCtx path f r | _ -> failwith "unreachable"

        for KeyValue(k, v1) in f1 do
            match Map.tryFind k f2 with
            | Some v2 -> unifyRec tsCtx (Step.Field k :: path) v1 v2
            | None -> ()

        let only1 = Map.filter (fun k _ -> not (Map.containsKey k f2)) f1
        let only2 = Map.filter (fun k _ -> not (Map.containsKey k f1)) f2

        match Map.isEmpty only1, Map.isEmpty only2 with
        | true, true -> unifyRec tsCtx (Step.RecordRow :: path) r1 r2
        | false, true -> unifyRec tsCtx (Step.RecordRow :: path) r2 (TRecord(only1, r1))
        | true, false -> unifyRec tsCtx (Step.RecordRow :: path) r1 (TRecord(only2, r2))
        | false, false ->
            let freshRow = tsCtx.FreshVar "ρ"

            unifyRec tsCtx (Step.RecordRow :: path) r1 (TRecord(only2, freshRow))
            unifyRec tsCtx (Step.RecordRow :: path) r2 (TRecord(only1, freshRow))

    /// Updates the type variables relative to `t1` and `t2` when they unify.
    /// This function can raise an `UnifyException` exception containing detailed diagnostics.
    let public unify (tsCtx: TypecheckContext) (t1: LiyhType) (t2: LiyhType) : unit =
        try
            unifyRec tsCtx [] t1 t2
        with
        | UnifyFailure(path, diag) ->
            let context =
                match path with
                | [] -> []
                | _ -> formatPath path @ [ sprintf "While unifying `%s` with `%s`." (string t1) (string t2) ]

            raise (UnifyException { diag with Informations = diag.Informations @ context })

    /// Applies the `Unification.unify` function and handle the `UnifyException` using
    /// the error code `ErrorCode.TypeMismatchError` in the error report.
    let public unifyOrReportWithDesc (tsCtx: TypecheckContext) (t1: LiyhType) (t2: LiyhType) (desc: string) (node: WithPos<_>) =
        try
            unify tsCtx t1 t2
        with
        | UnifyException d ->
            let desc = if desc = null then d.Message else sprintf "%s: %s" desc d.Message
            tsCtx.ReportError ErrorCode.TypeMismatchError desc d.Informations d.Hint node

    /// Applies the `Unification.unify` function and handle the `UnifyException` using
    /// the error code `ErrorCode.TypeMismatchError` in the error report.
    let public unifyOrReport (tsCtx: TypecheckContext) (t1: LiyhType) (t2: LiyhType) (node: WithPos<_>) =
        unifyOrReportWithDesc tsCtx t1 t2 null node

