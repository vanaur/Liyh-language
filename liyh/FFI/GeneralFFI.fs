namespace Liyh.FFI

module public GeneralFFI =
    open System.Runtime.InteropServices
    open Liyh.Utils.ErrorReporter
    open Liyh.Syntax.SyntaxTree

    let private (|IdentifierParts|_|) (parts: string list) { Qualifier = qual; Name = name } =
        if (qual |> List.map _.Node) @ [ name.Node ] = parts then Some () else None

    let private tryLoadLibrary (libPath: string) =
        let mutable handle = nativeint 0
        if NativeLibrary.TryLoad(libPath, &handle) then Some handle else None

    let private canGetExport (handle: nativeint) (functionName: string) =
        let mutable ptr = nativeint 0
        NativeLibrary.TryGetExport(handle, functionName, &ptr)

    [<RequireQualifiedAccess>]
    type public CType =
        | UInt8
        | Int8
        | UInt16
        | Int16
        | UInt32
        | Int32
        | UInt64
        | Int64
        | Float32
        | Float64
        | LongDouble
        | Char
        | String // char*
        | Pointer of CType  // There is no compilation difference given a 'CType', this is used for type checking.
     // | Callback of arguments: CType list * retType: CType
     // | Struct of fields: (string * CType) list
        | Void

    let private aviableCTypes =
        [| "C.UInt8"
           "C.Int8"
           "C.UInt16"
           "C.Int16"
           "C.UInt32"
           "C.Int32"
           "C.UInt64"
           "C.Int64"
           "C.Float32"
           "C.Float64"
           "C.LongDouble"
           "C.Char"
           "C.String"
           "C.Pointer"
           "C.Void" |]

    /// Converts from an AST type to a C type.
    let rec private astTypeToCType (twp: TypeWithPos) =
        match removePos twp with
        | NamedType { Node = IdentifierParts [ "C"; "UInt8" ] } -> Some CType.UInt8
        | NamedType { Node = IdentifierParts [ "C"; "Int8" ] } -> Some CType.Int8
        | NamedType { Node = IdentifierParts [ "C"; "UInt16" ] } -> Some CType.UInt16
        | NamedType { Node = IdentifierParts [ "C"; "Int16" ] } -> Some CType.Int16
        | NamedType { Node = IdentifierParts [ "C"; "UInt32" ] } -> Some CType.UInt32
        | NamedType { Node = IdentifierParts [ "C"; "Int32" ] } -> Some CType.Int32
        | NamedType { Node = IdentifierParts [ "C"; "UInt64" ] } -> Some CType.UInt64
        | NamedType { Node = IdentifierParts [ "C"; "Int64" ] } -> Some CType.Int64
        | NamedType { Node = IdentifierParts [ "C"; "Float32" ] } -> Some CType.Float32
        | NamedType { Node = IdentifierParts [ "C"; "Float64" ] } -> Some CType.Float64
        | NamedType { Node = IdentifierParts [ "C"; "LongDouble" ] } -> Some CType.LongDouble
        | NamedType { Node = IdentifierParts [ "C"; "Char" ] } -> Some CType.Char
        | NamedType { Node = IdentifierParts [ "C"; "String" ] } -> Some CType.String
        | NamedType { Node = IdentifierParts [ "C"; "Ptr" ] } -> Some (CType.Pointer CType.Void)
        | NamedType { Node = IdentifierParts [ "C"; "Void" ] } -> Some CType.Void

        | ParametrizedType ({ Node = IdentifierParts [ "C"; "Ptr" ] }, [ ty ]) ->
            Option.map CType.Pointer (astTypeToCType ty)

        | _ -> None

    /// A record that contains information about an external foreign function from a dynamic library.
    type public FFIBinding =
        { ExternalQualifier: string     // the 'as name' part of the external definition (e.g. "LibC")
          LibraryPath: string           // the path of the library on the computer
          FunctionName: string          // the name of the external function
          Arity: int                    // number of arguments of the external function
          ArgumentsType: CType list     // list of expected types of the function's arguments
          ReturnType: CType }           // expected return type for the function

    let private makeReport errorType enclosing description allLines =
        { ErrorType = errorType
          ErrorCode = null
          EnclosingPosition  = enclosing
          Description = description
          AllLines = allLines
          Informations = Seq.empty
          Hint = null }

    let private addError (eq: ErrorQueue) (report: ErrorReport) =
        eq.AddError(report)
        None

    let private unknownCTypeReport (astTy: TypeWithPos) (allLines: string seq) =
        { makeReport ErrorType.Type (Some astTy.StartPos, Some astTy.EndPos) "Unknown or unsupported C type." allLines
          with
            Hint = sprintf "Available C types are: %s." (System.String.Join(", ", aviableCTypes)) }

    /// Converts from an AST return type to a C type.
    let private resolveReturnType (errorQueue: ErrorQueue) (allLines: string seq) (signature: Signature) =
        match signature.ReturnType with
        | None ->
            makeReport
                (Warning ErrorType.Type)
                (None, None)
                "An explicit C type is required for FFI. By default, this evaluates to `C.Void`, but it is preferable to make it explicit."
                allLines
            |> errorQueue.AddError
            Some CType.Void

        | Some rt ->
            match astTypeToCType rt with
            | Some ctype -> Some ctype
            | None ->
                let report = unknownCTypeReport rt allLines
                addError errorQueue report

    /// Converts from an AST type to a C type.
    let private resolveArgumentType (errorQueue: ErrorQueue) (allLines: string seq) (twp: TypeWithPos) =
        match astTypeToCType twp with
        | Some ctype -> Some ctype
        | None ->
            let report = unknownCTypeReport twp allLines
            addError errorQueue report

    /// Returns a FFI binding record given an external function' signature. The caller has to fulfill
    let private getSignatureInfo (errorQueue: ErrorQueue) (allLines: string seq) (extQual: string) (libPath: string) (signature: Signature) =
        let returnType = resolveReturnType errorQueue allLines signature
        let argumentsType = List.map (resolveArgumentType errorQueue allLines) signature.ArgumentsType
        let functionName = removePos signature.Name

        match returnType, List.choose id argumentsType with
        | Some rt, args when args.Length = argumentsType.Length ->
            Some
                { ExternalQualifier = extQual
                  LibraryPath = libPath
                  FunctionName = functionName
                  Arity = args.Length
                  ArgumentsType = args
                  ReturnType = rt }
        | _ -> None

    /// If `checkFFI` is `true`, then check of the library is found and check if all the external
    /// functions defined are present in this external library, otherwise always returns `true`.
    let private validateLibrary (errorQueue: ErrorQueue) (allLines: string seq) (ext: Extern) (checkFFI: bool) =
        if not checkFFI then true else

        // Checkinf if the library or the functions in the library does exist might be harmful:
        //
        //  - Maybe the lib is not compiled yet
        //  - Cross-compilation is a problem
        //  - Dependency at the build environment

        let libPath = removePos ext.Library

        match tryLoadLibrary libPath with
        | None ->
            makeReport
                (ErrorType.Warning ErrorType.Type)
                (Some ext.Library.StartPos, Some ext.Library.EndPos)
                (sprintf "The library '%s' was not found." libPath)
                allLines
            |> errorQueue.AddError
            false

        | Some handle ->
            let isValid =
                ext.Content
                |> List.fold (fun ok { Node = { Name = fn } } ->
                    if canGetExport handle (removePos fn) then ok
                    else
                        makeReport
                            (ErrorType.Warning ErrorType.Type)
                            (Some fn.StartPos, Some fn.EndPos)
                            (sprintf "The function '%s' was not found in the dynamic library '%s'." (removePos fn) libPath)
                            allLines
                        |> errorQueue.AddError
                        false) true

            NativeLibrary.Free(handle)
            isValid

    /// If `checkFFI` is `true`, then check of the library is found and check if all the external
    /// functions defined are present in this external library.
    let private collectExternBindings (errorQueue: ErrorQueue) (allLines: string seq) (checkFFI: bool) (tlwp: TopLevelWithPos) =
        match removePos tlwp with
        | Extern ext ->
            let libPath = removePos ext.Library             // path of the library
            let extQual = string (removePos ext.AsName)     // name given for the interface ('as MyLib')
            let bindings = List.map (removePos >> getSignatureInfo errorQueue allLines extQual libPath) ext.Content

            if validateLibrary errorQueue allLines ext checkFFI && List.forall Option.isSome bindings
            then Some (List.map Option.get bindings)
            else None

        | _ -> failwith "??" // this should not happen

    /// Returns the list of FFI bindings from the given AST's external definitions.
    /// 
    /// If `checkFFI` is `true`, then check of the library is found and check if all the external
    /// functions defined are present in this external library.
    let public getFFIBindingsFromAST (astExterns: TopLevelWithPos list) (errorQueue: ErrorQueue) (allLines: string seq) (checkFFI: bool) =

        let rawBindings =
            List.map (collectExternBindings errorQueue allLines checkFFI) astExterns

        if List.forall Option.isSome rawBindings then
            rawBindings
            |> List.choose id
            |> List.concat

        else
            List.empty
