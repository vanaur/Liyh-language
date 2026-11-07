namespace Liyh.Semantic

open System
open Liyh.FFI.GeneralFFI

/// A type checker Liyh's type representation.
type public LiyhType =
    | TInt
    | TFloat
    | TBool
    | TChar
    | TString
    | TUnit
    | TTuple of LiyhType list
    | TArrow of LiyhType list * LiyhType * effects: Set<string>
    | TVar of TypeVar ref
    | TSymbolic
    | TRecord of Map<string, LiyhType> * LiyhType
    | TEmptyRow
    | TApp of string * LiyhType list // ADT
    | TCType of CType
    | TMeasure of baseType: LiyhType * dim: Dimension
    | THandlerInstance of handlerName: string * effectName: string

    /// Removes chains of type variables.
    member public this.Prune() =
        match this with
        | TVar({ contents = LinkVar linked } as r) ->
            let pruned = linked.Prune()
            r.Value <- LinkVar pruned
            pruned

        | _ -> this

    /// Removes the dimensions of the type.
    member public this.EraseDimensions() =
        match this.Prune() with
        | TMeasure(baseT, _) ->
            baseT.EraseDimensions()

        | TArrow(args, ret, effs) ->
            let args' = args |> List.map _.EraseDimensions()
            TArrow(args', ret.EraseDimensions(), effs)

        | TTuple ts ->
            TTuple(ts |> List.map _.EraseDimensions())

        | TRecord(fields, rest) ->
            let fields' = fields |> Map.map (fun _ v -> v.EraseDimensions())
            TRecord(fields', rest.EraseDimensions())

        | TApp(name, args) ->
            let args' = args |> List.map _.EraseDimensions()
            TApp(name, args')

        | other -> other

    /// Pretty print of the type.
    override this.ToString() =
        let letters = [| 'α'; 'β'; 'γ'; 'δ'; 'ε'; 'ζ'; 'η'; 'θ'; 'λ'; 'μ'; 'ξ'; 'π'; 'ρ'; 'σ'; 'τ'; 'φ'; 'ω' |]

        let showTv (index: int) =
            let letter = letters.[index % letters.Length]
            let suffix = index / letters.Length
            if suffix = 0 then sprintf "'%c" letter
            else sprintf "'%c%d" letter suffix

        let names = Collections.Generic.Dictionary<string, int>()

        let indexOf (name: string) =
            match names.TryGetValue name with
            | true, i -> i
            | _ ->
                let i = names.Count
                names.[name] <- i
                i

        let rec show (ty: LiyhType) : string =
            match ty with
            | TVar { contents = LinkVar t } -> show t
            | TVar { contents = UnboundVar name } -> showTv (indexOf name)

            | TInt -> "Int"
            | TFloat -> "Float"
            | TBool -> "Bool"
            | TChar -> "Char"
            | TString -> "String"
            | TUnit -> "Unit"
            | TSymbolic -> "Symbolic"
            | TEmptyRow -> "EmptyRow"

            | TCType CType.UInt8 -> "C.UInt8"
            | TCType CType.Int8 -> "C.Int8"
            | TCType CType.UInt16 -> "C.UInt16"
            | TCType CType.Int16 -> "C.Int16"
            | TCType CType.UInt32 -> "C.UInt32"
            | TCType CType.Int32 -> "C.Int32"
            | TCType CType.UInt64 -> "C.UInt64"
            | TCType CType.Int64 -> "C.Int64"
            | TCType CType.Float32 -> "C.Float32"
            | TCType CType.Float64 -> "C.Float64"
            | TCType CType.LongDouble -> "C.LongDouble"
            | TCType CType.Char -> "C.Char"
            | TCType CType.String -> "C.String"
            | TCType (CType.Pointer inner) -> sprintf "C.Ptr[%s]" (show (TCType inner))
            | TCType CType.Void -> "C.Void"

            | TTuple ts ->
                sprintf "(%s)" (ts |> List.map show |> String.concat ", ")

            | TArrow (args, ret, effects) ->
                let argsStr = args |> List.map show |> String.concat ", "
                if Set.isEmpty effects then
                    sprintf "[%s] -> %s" argsStr (show ret)
                else
                    sprintf "[%s] -> %s %% { %s }" argsStr (show ret) (String.concat ", " effects)

            | TRecord _ ->
                let rec collectFields (acc: Map<string, LiyhType>) (r: LiyhType) =
                    match r with
                    | TVar { contents = LinkVar t } -> collectFields acc t
                    | TRecord (fields, rest) ->
                        let merged = Map.fold (fun m k v -> Map.add k v m) acc fields
                        collectFields merged rest
                    | other -> acc, other

                let fields, tail = collectFields Map.empty ty
                let fieldsStr =
                    fields
                    |> Map.toList
                    |> List.map (fun (k, v) -> sprintf "%s: %s" k (show v))
                    |> String.concat ", "

                match tail with
                | TEmptyRow -> sprintf "{ %s }" fieldsStr
                | _ when Map.isEmpty fields -> "{ .. }"
                | _ -> sprintf "{ %s, .. }" fieldsStr

            | TApp (name, []) -> name
            | TApp (name, args) ->
                sprintf "%s[%s]" name (args |> List.map show |> String.concat ", ")

            | TMeasure (baseT, dim) ->
                let cleaned = Dimension.prune dim
                if Map.isEmpty cleaned then show baseT
                else sprintf "%s[%s]" (show baseT) (Dimension.toString cleaned)

            | THandlerInstance (handlerName, effectName) ->
                sprintf "%s/%s" effectName handlerName

        show this

/// A type variable representation: either unbound or linked. This representation with
/// two constructors is used for mutable in-place modifications while unifying.
and public TypeVar =
    | UnboundVar of name: string
    | LinkVar of ty: LiyhType

    override this.ToString() =
        match this with
        | UnboundVar name -> sprintf "'%s" name
        | LinkVar inner -> string inner

