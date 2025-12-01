namespace Liyh.Execution.Core

module FFI =
    open System
    open System.Reflection
    open Liyh.Execution.FFI.CFFI
    open Liyh.Execution

    exception public UnsupportedMarshalingTypeException of CoreTerm * CType
    exception public MarshalingOverflowErrorException of string
    exception public MarshalingErrorException of string

    let inline private canFitInt32 (x: bigint) =
        x >= bigint Int32.MinValue && x <= bigint Int32.MaxValue

    let inline private canFitInt64 (x: bigint) =
        x >= bigint Int64.MinValue && x <= bigint Int64.MaxValue

    let inline private canFitFloat32 (x: double) =
        Double.IsFinite x && abs x <= float Single.MaxValue

    let rec private typeToCType (ty: Type) =
        if ty = typeof<int32> then CType.Int32
        elif ty = typeof<int64> then CType.Int64
        elif ty = typeof<char> then CType.Char
        elif ty = typeof<float32> || ty = typeof<single> then CType.Float32
        elif ty = typeof<double> then CType.Float64
        elif ty = typeof<string> then CType.String
        elif ty.IsArray then
            let elemType = ty.GetElementType()
            let rank = ty.GetArrayRank()
            if rank = 1 && elemType = typeof<char>
            then raise (NotSupportedException "Dynamic arrays in structs not supported")
            else raise (NotSupportedException "Only fixed-size arrays supported in structs")
        elif ty.IsValueType && not ty.IsPrimitive && not (ty = typeof<nativeint>) then CType.Struct ty
        elif ty = typeof<nativeint> || ty.IsPointer then CType.Pointer CType.Void // ou CType.Pointer(CType.Struct ...) selon le contexte
        else raise (NotSupportedException $"Cannot map type '{ty.FullName}' to CType")

    /// Marshal a given term into a C-compatible value.
    let rec public coreMarshaling (term: CoreTerm) (ctype: CType) =

        let inline marshalingOverflowError x t =
            raise (MarshalingOverflowErrorException $"Integer {x} cannot fit in {t}")

        match term, ctype with
        | Literal (Integer x), CType.Int32 when canFitInt32 x -> int32 x :> obj
        | Literal (Integer x), CType.Int32 -> marshalingOverflowError x "Int32"

        | Literal (Integer x), CType.Int64 when canFitInt64 x -> int64 x :> obj
        | Literal (Integer x), CType.Int64 -> marshalingOverflowError x "Int64"

        | Literal (Float x), CType.Float32 when canFitFloat32 x -> float32 x :> obj
        | Literal (Float x), CType.Float32 -> marshalingOverflowError x "Float32"

        | Literal (Float x), CType.Single when canFitFloat32 x -> single x :> obj
        | Literal (Float x), CType.Single -> marshalingOverflowError x "Single"

        | Literal (Float x), CType.Float64 -> x :> obj
        | Literal (Char x), CType.Char -> x :> obj
        | Literal (String x), CType.String -> x :> obj

        | Literal (String x), CType.FixedArray(CType.Char, n) -> 
            let chars =
                if x.Length >= n then
                    x.Substring(0, n).ToCharArray()
                else
                    let padded = x + System.String('\u0000', n - x.Length)
                    padded.ToCharArray()
            chars :> obj

        | RecordExtend record, CType.Struct t ->
            let rec flattenFields acc =
                function
                | None -> acc
                | Some (RecordExtend { BaseRecord = baseRecord; Extension = ext }) ->
                    let acc' = List.fold (fun m (k, v) -> Map.add k v m) acc ext
                    flattenFields acc' baseRecord
                | Some term -> raise (UnsupportedMarshalingTypeException (term, CType.Struct t))

            let fields = flattenFields Map.empty (Some (RecordExtend record))

            let structFields =
                t.GetFields(BindingFlags.Public ||| BindingFlags.Instance)
                |> Array.map _.Name

            let fieldValues =
                structFields
                |> Array.choose (fun fieldName ->
                    match Map.tryFind fieldName fields with
                    | Some termValue ->
                        let fieldType = t.GetField(fieldName).FieldType
                        let fieldCType = typeToCType fieldType
                        let marshaledValue = coreMarshaling termValue fieldCType
                        Some (fieldName, marshaledValue)
                    | None ->
                        raise (MarshalingErrorException $"Missing field '{fieldName}' required by struct '{t.Name}'"))

            createStructInstance t fieldValues

        | Builtin.Ptr ptr, CType.Pointer _ -> ptr :> obj

        | _, CType.Void -> null
        | _ -> raise (UnsupportedMarshalingTypeException (term, ctype))

    /// Marshal a C-compatible value into a term.
    let rec public nativeToCore (value: obj) (ctype: CType) =

        let inline marshalingError value ctype =
            raise (MarshalingErrorException $"{value} is not a {ctype}")

        match ctype with
        | CType.Int32 ->
            match value with
            | :? int32 as x -> Literal (Integer (bigint x))
            | _ -> marshalingError value ctype

        | CType.Int64 ->
            match value with
            | :? int64 as x -> Literal (Integer (bigint x))
            | _ -> marshalingError value ctype

        | CType.Char ->
            match value with
            | :? char as x -> Literal (Char x)
            | _ -> marshalingError value ctype

        | CType.Float32 | CType.Single ->
            match value with
            | :? float32 as x -> Literal (Float (float x))
            | _ -> marshalingError value ctype

        | CType.Float64 ->
            match value with
            | :? double as x -> Literal (Float x)
            | _ -> marshalingError value ctype

        | CType.String ->
            match value with
            | null -> Literal (String "")
            | :? string as s -> Literal (String s)
            | _ -> marshalingError value ctype

        | CType.Struct t ->
            if value = null then raise (MarshalingErrorException $"Cannot unmarshal null into struct '{t.Name}'")
            let fields =
                t.GetFields(BindingFlags.Public ||| BindingFlags.Instance)
                |> Array.choose (fun field ->
                    try
                        let fieldValue = field.GetValue(value)
                        let fieldCType = typeToCType field.FieldType
                        let coreValue = nativeToCore fieldValue fieldCType
                        Some (field.Name, coreValue)
                    with ex ->
                        raise (MarshalingErrorException $"Error unmarshaling field '{field.Name}' of struct '{t.Name}': {ex.Message}"))
                |> List.ofArray
            RecordExtend { BaseRecord = None; Extension = fields }

        | CType.Void ->
            Symbol { Symbol = "unit"; Children = []; IsVariable = false; __hashCache = 0 }

        | CType.Pointer _ ->
            let ptrSymbol p =
                Symbol
                    { Symbol = "ptr"
                      Children = [ Literal (Integer (bigint (int64 p))) ]
                      IsVariable = false
                      __hashCache = 0 }

            match value with
            | :? nativeint as p -> ptrSymbol p
            | _ -> ptrSymbol 0

        | CType.FixedArray (ctype, size) ->
            if value = null then
                raise (MarshalingErrorException $"Cannot unmarshal null into fixed array of size {size} and element type {ctype}")

            match value with
            | :? System.Array as arr ->
                if arr.Rank <> 1 then
                    raise (MarshalingErrorException $"Expected one-dimensional array but got array of rank {arr.Rank} for fixed array of size {size}")

                if arr.Length <> size then
                    raise (MarshalingErrorException $"Expected array of size {size} but got {arr.Length} for fixed array of element type {ctype}")

                let elements =
                    [| 0 .. size - 1 |]
                    |> Array.map (fun i -> let elem = arr.GetValue i in nativeToCore elem ctype)
                    |> List.ofArray

                Symbol { Symbol = "array"; Children = elements; IsVariable = false; __hashCache = 0 }

            | _ ->
                marshalingError value ctype

    let inline public callExternalFunction (signature: FunctionSignature) (dynLib: DynLib) (args: CoreTerm list) =
        if signature.Parameters.Length <> args.Length then
            failwith $"Expected {signature.Parameters.Length} arguments but gor {args.Length} for the external call {signature.Name}."

        let marshaledArguments = Array.map2 coreMarshaling (Array.ofList args) signature.Parameters
        let result = dynLib.InvokeFunction signature.Name signature marshaledArguments

        nativeToCore result signature.ReturnType

