namespace Liyh.Semantic

module private ForeignTypes =
    open Liyh.Syntax.SyntaxTree
    open Liyh.FFI.GeneralFFI

    /// Returns the Liyh type compatible with the given C type, if one exists.
    let rec public liyhCTypeCompatible (ctype: CType) =
        match ctype with
        | CType.Int64 -> Some TInt
        | CType.Float64 -> Some TFloat
        | CType.Char -> Some TChar
        | CType.String -> Some TString
        | CType.Pointer (CType.Char | CType.Void) -> Some TString
        | CType.Pointer cty -> Option.map (fun _ -> TCType (CType.Pointer cty)) (liyhCTypeCompatible cty)
        | _ -> None

    /// Returns the C type compatible with the given Liyh type, if one exists.
    let public cTypeLiyhCompatible (ltype: LiyhType) =
        match ltype with
        | TInt -> Some CType.Int64
        | TFloat -> Some CType.Float64
        | TChar -> Some CType.Char
        | TString -> Some CType.String
        | _ -> None

    /// Peels nested `C.Ptr[...]` layers: returns the pointer depth and the innermost type.
    let rec public peelCPtr (depth: int) (twp: TypeWithPos) =
        match twp.Node with
        | ParametrizedType({ Node = { Qualifier = [ c ]; Name = ptr } }, [ inner ])
            when (removePos c = "C") && (removePos ptr = "ptr") -> peelCPtr (depth + 1) inner
        | _ -> depth, twp

    /// Rewraps a C type in `depth` pointer layers.
    let public wrapCPtr (depth: int) (cty: CType) =
        Seq.fold (fun acc _ -> CType.Pointer acc) cty (seq { 1 .. depth })

    /// Warns that a Liyh type has a C-compatible equivalent that should be used instead.
    /// `compatible` is the C type matching `liyhTy`; `suggested` is what the user should write
    /// (e.g. `compatible` wrapped in pointer layers, or `compatible` itself when there are none).
    let public warnLiyhTypeCompatibleWithC
        (tsCtx: TypecheckContext)
        (pos: TypeWithPos)
        (liyhTy: LiyhType)
        (compatible: CType)
        (suggested: CType)
        : unit
        =
        let desc =
            sprintf
                "Although Liyh type `%s` is compatible with C type `%s`, it is best to maintain consistency between native C types and Liyh types."
                (string liyhTy)
                (string compatible)
        let hint = sprintf "It is preferable to use `%s` instead, or the appropriate C type you intended to use." (string suggested)
        tsCtx.ReportWarning WarningCode.FfiTypeConsistencyWarning desc [] hint pos

    /// Reports that a C FFI type was expected but a Liyh-specific type was found,
    /// and returns a fresh error type.
    let public errorExpectedCType (tsCtx: TypecheckContext) (pos: TypeWithPos) (liyhTy: LiyhType) =
        let desc =
            sprintf
                "An FFI pointer type is expected to point to another C FFI type, but got a Liyh-specific `%s`."
                (string liyhTy)
        let hint = "The FFI expects native C types, not Liyh types: use a C type."
        tsCtx.ReportError ErrorCode.InvalidFfiTypeError desc [] hint pos
        tsCtx.FreshError ()

    /// Checks that `lty` is a native C type, or has a C-compatible equivalent,
    /// and wraps the result in `depth` pointer layers (`depth = 0` → no pointer).
    let public check tsCtx (pos: TypeWithPos) (depth: int) (lty: LiyhType) : CType option =
        match lty with
        | TCType cty -> Some (wrapCPtr depth cty)
        | other ->
            cTypeLiyhCompatible other
            |> Option.map (fun compatible ->
                let wrapped = wrapCPtr depth compatible
                warnLiyhTypeCompatibleWithC tsCtx pos other compatible wrapped
                wrapped)
