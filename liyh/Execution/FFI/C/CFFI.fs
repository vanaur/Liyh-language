namespace Liyh.Execution.FFI

/// Loads useful functions for Windows.
module private Kernel32 =
    open System.Runtime.InteropServices

    [<DllImport("kernel32", SetLastError = true)>]
    extern nativeint LoadLibrary(string path)

    [<DllImport("kernel32", SetLastError = true)>]
    extern nativeint GetProcAddress(nativeint handle, string procName)

    [<DllImport("kernel32", SetLastError = true)>]
    extern bool FreeLibrary(nativeint handle)

/// Loads useful functions for Unix-like systems (Linux, macOS).
module private LibDl =
    open System.Runtime.InteropServices

    let private libName =
        if RuntimeInformation.IsOSPlatform OSPlatform.OSX then
            "libdl.dylib"
        else
            "libdl.so.2"

    // Note: RTLD_NOW is standard for immediate symbol resolution
    let RTLD_NOW = 2

    [<DllImport("libdl", EntryPoint = "dlopen")>]
    extern nativeint dlopen_unix(string path, int flags)

    [<DllImport("libdl", EntryPoint = "dlsym")>]
    extern nativeint dlsym_unix(nativeint handle, string symbol)

    [<DllImport("libdl", EntryPoint = "dlerror")>]
    extern nativeint dlerror_unix()

    [<DllImport("libdl", EntryPoint = "dlclose")>]
    extern int dlclose_unix(nativeint handle)

    let dlopen path flags = dlopen_unix (path, flags)
    let dlsym handle symbol = dlsym_unix (handle, symbol)
    let dlerror () = dlerror_unix ()
    let dlclose handle = dlclose_unix (handle)

module private DelegateBuilder =
    open System
    open System.Runtime.InteropServices
    open System.Reflection
    open System.Reflection.Emit

    let private assemblyBuilder =
        AssemblyBuilder.DefineDynamicAssembly(AssemblyName("DynamicDelegates"), AssemblyBuilderAccess.Run)

    let private moduleBuilder =
        assemblyBuilder.DefineDynamicModule("DynamicDelegateModule")

    let public BuildDelegateType (parameterTypes: Type[], returnType: Type) =
        let typeBuilder =
            moduleBuilder.DefineType(
                sprintf "DynamicDelegate_%d" (Guid.NewGuid().GetHashCode()),
                TypeAttributes.Class
                ||| TypeAttributes.Public
                ||| TypeAttributes.Sealed
                ||| TypeAttributes.AnsiClass
                ||| TypeAttributes.AutoClass,
                typeof<MulticastDelegate>
            )

        let attrCtor =
            typeof<UnmanagedFunctionPointerAttribute>
                .GetConstructor([| typeof<CallingConvention> |])

        let attrBuilder =
            CustomAttributeBuilder(attrCtor, [| CallingConvention.Cdecl :> obj |])

        typeBuilder.SetCustomAttribute(attrBuilder)

        let ctor =
            typeBuilder.DefineConstructor(
                MethodAttributes.RTSpecialName
                ||| MethodAttributes.HideBySig
                ||| MethodAttributes.Public,
                CallingConventions.Standard,
                [| typeof<obj>; typeof<IntPtr> |]
            )

        ctor.SetImplementationFlags(MethodImplAttributes.Runtime ||| MethodImplAttributes.Managed)

        let invokeMethod =
            typeBuilder.DefineMethod(
                "Invoke",
                MethodAttributes.Public
                ||| MethodAttributes.HideBySig
                ||| MethodAttributes.NewSlot
                ||| MethodAttributes.Virtual,
                returnType,
                parameterTypes
            )

        invokeMethod.SetImplementationFlags(MethodImplAttributes.Runtime ||| MethodImplAttributes.Managed)

        typeBuilder.CreateType()

module private StructureMarshaller =
    open System
    open System.Reflection
    open System.Reflection.Emit
    open System.Runtime.InteropServices

    let private assemblyBuilder =
        AssemblyBuilder.DefineDynamicAssembly(AssemblyName("DynamicStructures"), AssemblyBuilderAccess.Run)

    let private moduleBuilder =
        assemblyBuilder.DefineDynamicModule("DynamicStructureModule")

    [<Struct>]
    type public StructField =
        { name: string
          fieldType: Type
          offset: int option
          // NOUVEAU : On spécifie le type de marshalling (ByValArray ou ByValTStr)
          marshalType: UnmanagedType option
          sizeConst: int option }

    let public CreateStructureType (name: string) (fields: StructField[]) (layoutKind: LayoutKind) =
        let typeBuilder =
            moduleBuilder.DefineType(
                sprintf "DynamicStruct_%s_%d" name (Guid.NewGuid().GetHashCode()),
                TypeAttributes.Public
                ||| TypeAttributes.Sealed
                ||| TypeAttributes.SequentialLayout,
                typeof<ValueType>
            )

        let structLayoutCtor =
            typeof<StructLayoutAttribute>.GetConstructor([| typeof<LayoutKind> |])

        let structLayoutBuilder =
            CustomAttributeBuilder(structLayoutCtor, [| layoutKind :> obj |])

        typeBuilder.SetCustomAttribute(structLayoutBuilder)

        fields
        |> Array.iter (fun field ->
            let fieldBuilder =
                typeBuilder.DefineField(field.name, field.fieldType, FieldAttributes.Public)

            // 1. Offset explicite
            match field.offset with
            | Some offset when layoutKind = LayoutKind.Explicit ->
                let fieldOffsetCtor = typeof<FieldOffsetAttribute>.GetConstructor([| typeof<int> |])

                let fieldOffsetBuilder =
                    CustomAttributeBuilder(fieldOffsetCtor, [| offset :> obj |])

                fieldBuilder.SetCustomAttribute(fieldOffsetBuilder)
            | _ -> ()

            // 2. Marshalling (Tableaux fixes et Strings fixes)
            match field.marshalType, field.sizeConst with
            | Some mType, Some size ->
                // On construit : [MarshalAs(UnmanagedType.X, SizeConst = size)]
                let marshalAsCtor =
                    typeof<MarshalAsAttribute>.GetConstructor([| typeof<UnmanagedType> |])

                let sizeConstField = typeof<MarshalAsAttribute>.GetField("SizeConst")

                let marshalAsBuilder =
                    CustomAttributeBuilder(marshalAsCtor, [| mType :> obj |], [| sizeConstField |], [| size :> obj |])

                fieldBuilder.SetCustomAttribute(marshalAsBuilder)
            | _ -> ())

        typeBuilder.CreateType()

    let public marshalFromNative (ptr: nativeint) (targetType: Type) : obj =
        if ptr = 0n then
            null
        else
            Marshal.PtrToStructure(ptr, targetType)

module private CallbackBuilder =
    open System
    open System.Reflection
    open System.Reflection.Emit

    let private assemblyBuilder =
        AssemblyBuilder.DefineDynamicAssembly(AssemblyName("DynamicCallbacks"), AssemblyBuilderAccess.Run)

    let private moduleBuilder =
        assemblyBuilder.DefineDynamicModule("DynamicCallbackModule")

    let CreateCallbackShim (delegateType: Type) (parameterTypes: Type[]) (returnType: Type) =
        let typeBuilder =
            moduleBuilder.DefineType(
                sprintf "CallbackShim_%d" (Guid.NewGuid().GetHashCode()),
                TypeAttributes.Class ||| TypeAttributes.Public
            )

        let funcField = typeBuilder.DefineField("targetFunc", typeof<Func<obj[], obj>>, FieldAttributes.Public)

        let methodBuilder =
            typeBuilder.DefineMethod(
                "Invoke",
                MethodAttributes.Public ||| MethodAttributes.HideBySig,
                returnType,
                parameterTypes
            )

        let il = methodBuilder.GetILGenerator()

        let localArr = il.DeclareLocal(typeof<obj[]>)
        
        il.Emit(OpCodes.Ldc_I4, parameterTypes.Length)
        il.Emit(OpCodes.Newarr, typeof<obj>)
        il.Emit(OpCodes.Stloc, localArr)

        for i in 0 .. parameterTypes.Length - 1 do
            il.Emit(OpCodes.Ldloc, localArr)
            il.Emit(OpCodes.Ldc_I4, i)
            il.Emit(OpCodes.Ldarg, i + 1)

            if parameterTypes.[i].IsValueType then
                il.Emit(OpCodes.Box, parameterTypes.[i])

            il.Emit(OpCodes.Stelem_Ref)

        il.Emit(OpCodes.Ldarg_0)
        il.Emit(OpCodes.Ldfld, funcField)
        il.Emit(OpCodes.Ldloc, localArr)
        il.Emit(OpCodes.Callvirt, typeof<Func<obj[], obj>>.GetMethod("Invoke"))

        if returnType = typeof<System.Void> then
            il.Emit(OpCodes.Pop)
        else
            if returnType.IsValueType then
                il.Emit(OpCodes.Unbox_Any, returnType)
            else
                il.Emit(OpCodes.Castclass, returnType)

        il.Emit(OpCodes.Ret)

        let shimType = typeBuilder.CreateType()
        (shimType, shimType.GetField("targetFunc"), shimType.GetMethod("Invoke"))

module public CFFI =
    open System
    open System.IO
    open System.Runtime.InteropServices
    open System.Collections.Concurrent

    exception public UnknownErrorLoadingLibraryException of path: string
    exception public ErrorLoadingLibraryException of path: string * msg: string
    exception public FunctionNotFoundException of libName: string * fname: string * msg: string
    exception public IncorrectNumberOfArgumentsException of libName: string * fname: string * expect: int * given: int
    exception public StructureDefinitionException of structName: string * msg: string

    /// Pattern-match a native pointer.
    let inline private (|ZeroIntPtr|_|) (n: nativeint) = if n = 0n then true else false

    [<RequireQualifiedAccess>]
    type public CType =
        | Int32
        | Int64
        | Char
        | Float32
        | Single
        | Float64
        | String // char*
        | FixedArray of CType * int
        | Pointer of CType
        | Struct of Type
        | Void

    [<Struct>]
    type public FunctionSignature =
        { Name: string
          ReturnType: CType
          Parameters: CType[] }

    [<Struct>]
    type public StructFieldDefinition =
        { Name: string
          FieldType: CType
          Offset: int option }

    [<RequireQualifiedAccess>]
    type public StructLayout =
        | Sequential
        | Explicit

    // -- Conversion helpers --

    let inline private convertIntPtrToStringObj (value: obj) =
        match value :?> nativeint with
        | ZeroIntPtr -> null
        | ptr ->
            try
                Marshal.PtrToStringUTF8 ptr :> obj
            with _ ->
                Marshal.PtrToStringAnsi ptr :> obj

    let inline private convertIntPtrToPtrObj (value: obj) =
        match value :?> nativeint with
        | ZeroIntPtr -> null
        | ptr -> ptr :> obj

    let rec private cTypeToParamType =
        function
        | CType.Int32 -> typeof<int32>
        | CType.Int64 -> typeof<int64>
        | CType.Char -> typeof<char>
        | CType.Float32 -> typeof<float>
        | CType.Single -> typeof<float32>
        | CType.Float64 -> typeof<double>
        | CType.String -> typeof<string>
        | CType.FixedArray(CType.Char, _) -> typeof<string>
        | CType.FixedArray(elemType, _) -> (cTypeToParamType elemType).MakeArrayType()
        | CType.Pointer _ -> typeof<nativeint>
        | CType.Struct structType -> structType
        | CType.Void -> typeof<Void>

    let rec private cTypeToReturnType =
        function
        | CType.String -> typeof<nativeint>
        | CType.FixedArray(CType.Char, _) -> typeof<string>
        | CType.FixedArray(elemType, _) -> (cTypeToParamType elemType).MakeArrayType()
        | ctype -> cTypeToParamType ctype

    let rec private cTypeToFieldType =
        function
        | CType.Struct structType -> structType
        | CType.FixedArray(CType.Char, _) -> typeof<string>
        | CType.FixedArray(elemType, _) -> (cTypeToParamType elemType).MakeArrayType()
        | ctype -> cTypeToParamType ctype

    let private isUnixLike () =
        RuntimeInformation.IsOSPlatform OSPlatform.Linux
        || RuntimeInformation.IsOSPlatform OSPlatform.OSX

    type private StructureRegistry() =
        let structures = ConcurrentDictionary<string, Type>()

        member this.Register (name: string) (structType: Type) =
            structures.TryAdd(name, structType) |> ignore

        member this.TryGet(name: string) =
            match structures.TryGetValue(name) with
            | true, t -> Some t
            | false, _ -> None

    let private structRegistry = StructureRegistry()

    let public defineStruct (name: string) (fields: StructFieldDefinition[]) (layout: StructLayout) =
        try
            match structRegistry.TryGet name with
            | Some existingType -> existingType
            | None ->
                let layoutKind =
                    match layout with
                    | StructLayout.Sequential -> LayoutKind.Sequential
                    | StructLayout.Explicit -> LayoutKind.Explicit

                let structFields =
                    fields
                    |> Array.map (fun field ->
                        let (marshalType, sizeConst) =
                            match field.FieldType with
                            | CType.FixedArray(CType.Char, size) -> (Some UnmanagedType.ByValTStr, Some size)
                            | CType.FixedArray(_, size) -> (Some UnmanagedType.ByValArray, Some size)
                            | _ -> (None, None)

                        let sd: StructureMarshaller.StructField =
                            { name = field.Name
                              fieldType = cTypeToFieldType field.FieldType
                              offset = field.Offset
                              marshalType = marshalType
                              sizeConst = sizeConst }

                        sd)

                let structType =
                    StructureMarshaller.CreateStructureType name structFields layoutKind

                structRegistry.Register name structType
                structType
        with ex ->
            raise (StructureDefinitionException(name, ex.Message))

    let public createStructInstance (structType: Type) (fieldValues: (string * obj)[]) =
        try
            let instance = Activator.CreateInstance(structType)

            fieldValues
            |> Array.iter (fun (fieldName, value) ->
                let field = structType.GetField(fieldName)

                if field <> null then
                    field.SetValue(instance, value))

            instance
        with ex ->
            raise (StructureDefinitionException(structType.Name, sprintf "Failed to create instance: %s" ex.Message))

    let public getStructField (structInstance: obj) (fieldName: string) =
        let structType = structInstance.GetType()
        let field = structType.GetField(fieldName)

        if field = null then
            raise (StructureDefinitionException(structType.Name, sprintf "Field '%s' not found" fieldName))

        field.GetValue(structInstance)

    let public setStructField (structInstance: obj) (fieldName: string) (value: obj) =
        let structType = structInstance.GetType()
        let field = structType.GetField(fieldName)

        if field = null then
            raise (StructureDefinitionException(structType.Name, sprintf "Field '%s' not found" fieldName))

        field.SetValue(structInstance, value)

    type public DynLib private (handle: nativeint, libName: string) =
        let mutable disposed = false
        let methodCache = ConcurrentDictionary<string * FunctionSignature, Delegate>()
        let callbackRegistry = ConcurrentDictionary<nativeint, Delegate>()

        static member private NormalizeLibraryPath(path: string) =
            let fileName = Path.GetFileName path
            let directory = Path.GetDirectoryName path

            if RuntimeInformation.IsOSPlatform OSPlatform.Windows then
                if not (fileName.EndsWith(".dll", StringComparison.OrdinalIgnoreCase)) then
                    Path.Combine(directory, fileName + ".dll")
                else
                    path

            elif RuntimeInformation.IsOSPlatform OSPlatform.OSX then
                if not (fileName.Contains(".")) then
                    Path.Combine(directory, "lib" + fileName + ".dylib")
                else
                    path

            else if
                not (fileName.Contains("."))
            then
                Path.Combine(directory, "lib" + fileName + ".so")
            else
                path

        /// Load the dynamic library if it exists.
        static member public Load(path: string) =
            let normalizedPath = DynLib.NormalizeLibraryPath path
            let libName = Path.GetFileNameWithoutExtension normalizedPath

            let fileExists = File.Exists normalizedPath
            let isSystemLibAttempt = not (Path.IsPathRooted normalizedPath)

            if not fileExists && not isSystemLibAttempt then
                 raise (
                    FileNotFoundException(
                        sprintf "The library '%s' has not been found at '%s'." libName normalizedPath,
                        normalizedPath
                    )
                )

            if isUnixLike () then
                LibDl.dlerror () |> ignore

                let handle = LibDl.dlopen normalizedPath LibDl.RTLD_NOW
                
                match handle with
                | ZeroIntPtr ->
                    match LibDl.dlerror () with
                    | ZeroIntPtr -> raise (UnknownErrorLoadingLibraryException normalizedPath)
                    | errorPtr -> 
                        let errorMsg = Marshal.PtrToStringAnsi errorPtr
                        raise (ErrorLoadingLibraryException(normalizedPath, errorMsg))
                | h -> new DynLib(h, libName)

            else
                // Windows
                let handle = Kernel32.LoadLibrary normalizedPath
                match handle with
                | ZeroIntPtr ->
                    raise (ErrorLoadingLibraryException(normalizedPath, Marshal.GetLastWin32Error() |> string))
                | h -> new DynLib(h, libName)

        /// Creates a C function pointer that redirects to an F# function.
        /// The returned pointer can be passed to a C function awaiting a callback.
        member public this.CreateCallback (func: obj[] -> obj) (signature: FunctionSignature) : nativeint =
            let parameterTypes = Array.map cTypeToParamType signature.Parameters
            let returnType = cTypeToReturnType signature.ReturnType
            let delegateType = DelegateBuilder.BuildDelegateType(parameterTypes, returnType)

            let (shimType, fieldInfo, methodInfo) = 
                CallbackBuilder.CreateCallbackShim delegateType parameterTypes returnType

            let shimInstance = Activator.CreateInstance(shimType)

            let funcWrapper = Func<obj[], obj>(func)
            fieldInfo.SetValue(shimInstance, funcWrapper)

            let callbackDelegate = Delegate.CreateDelegate(delegateType, shimInstance, methodInfo)
            let ptr = Marshal.GetFunctionPointerForDelegate(callbackDelegate)

            // Save the delegate so that the GC does not collect it!
            callbackRegistry.TryAdd(ptr, callbackDelegate) |> ignore
            ptr

        member private this.CreateDynamicDelegate(signature: FunctionSignature) =
            let parameterTypes = Array.map cTypeToParamType signature.Parameters
            let returnType = cTypeToReturnType signature.ReturnType
            DelegateBuilder.BuildDelegateType(parameterTypes, returnType)

        member private this.PrepareArguments (signature: FunctionSignature) (args: obj[]) =
            Array.zip signature.Parameters args
            |> Array.map (fun (ctype, arg) -> if arg = null then null else arg)

        member private this.ProcessReturnValue (signature: FunctionSignature) (result: obj) =
            match signature.ReturnType with
            | CType.String -> convertIntPtrToStringObj result
            | CType.Pointer _ -> convertIntPtrToPtrObj result
            | _ -> result

        member public this.InvokeFunction (fname: string) (signature: FunctionSignature) (args: obj[]) =
            if disposed then
                invalidOp "The library has been disposed"

            if Array.length args <> Array.length signature.Parameters then
                raise (
                    IncorrectNumberOfArgumentsException(
                        libName,
                        fname,
                        Array.length signature.Parameters,
                        Array.length args
                    )
                )

            let procAddr =
                if isUnixLike () then
                    LibDl.dlsym handle fname
                else
                    Kernel32.GetProcAddress(handle, fname)

            if procAddr = 0n then
                let error =
                    if isUnixLike () then
                        match LibDl.dlerror () with
                        | ZeroIntPtr -> "Unknown error"
                        | ptr -> Marshal.PtrToStringAnsi ptr
                    else
                        Marshal.GetLastWin32Error() |> string

                raise (FunctionNotFoundException(libName, fname, error))

            let key = (fname, signature)

            let delegate' =
                methodCache.GetOrAdd(
                    key,
                    fun _ ->
                        let delegateType = this.CreateDynamicDelegate signature
                        Marshal.GetDelegateForFunctionPointer(procAddr, delegateType)
                )

            let preparedArgs = this.PrepareArguments signature args
            let result = delegate'.DynamicInvoke preparedArgs
            this.ProcessReturnValue signature result

        interface IDisposable with
            member this.Dispose() =
                if not disposed then
                    if isUnixLike () then
                        LibDl.dlclose handle |> ignore
                    else
                        Kernel32.FreeLibrary handle |> ignore

                    disposed <- true
