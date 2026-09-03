namespace Liyh.LyVM

/// Bindings for the Runtime Core Library (RCL), a C-based library that provides an execution environment
/// for the Liyh language, implementing the LyVM (Liyh Virtual Machine), which runs Liyh programs.
module public BindingRCL =
    open System
    open System.Runtime.InteropServices

    type public EnvPtr = IntPtr
    type public VMPtr = IntPtr

    let public SYM_STRING_NATIVE = int 0xFFFFFFFBu
    let public SYM_RECORD_NATIVE = int 0xFFFFFFFCu
    let public SYM_FLOAT_NATIVE = int 0xFFFFFFFDu
    let public SYM_CLOSURE = int 0xFFFFFFFEu
    let public SYM_INT_NATIVE = int 0xFFFFFFFFu
    let public SYM_CHAR_NATIVE = int 0xFFFFFFF0u
    let public SYM_BOOL_NATIVE = int 0xFFFFFFF5u
    let public SYM_NUM_NATIVE = int 0xFFFFFFF4u
    let public SYM_PTR_NATIVE = int 0xFFFFFFEFu

    let inline isSystemTag (id: int) = (uint32 id) >= 0xFFFFFFF0u

    /// This have to be found in the compilation path of the compiler.
    [<Literal>]
    let private librcl = "librcl"

    /// Initializes the garbage collector.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public gc_init()

    /// Creates an execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern EnvPtr public create_env()

    /// Disposes the given execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public destroy_env(EnvPtr env)

    /// Sets a label to the execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public set_label(EnvPtr env, int id)

    /// Interns the given symbol name to the execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern uint32 public intern_symbol(EnvPtr env, string name)

    /// Adds a function (given a name (sym) and a label) to the execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public intern_function(EnvPtr env, uint32 sym, int arity, int label)

    /// Adds a string to the pool of strings in the execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)>]
    extern int public intern_string(EnvPtr env, string s)

    /// Emits a literal float in the given destination register.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public emit_load_float(EnvPtr env, int dstReg, double value)

    /// Emits an instruction. An instruction consists of an operand and at most four parameters, so
    /// the bytecode instructions are "Four-address code" (4AC) but most of them are at most 3AC.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public emit(EnvPtr env, int op, int a, int b, int c, int d)

    /// Loads a dynamic library into the VM.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)>]
    extern bool public rcl_env_load_library(EnvPtr env, string path)

    /// Loads an external function from a dynamic library via the FFI.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)>]
    extern int public rcl_env_register_ffi(EnvPtr env, string qual_name, string func_name, int arity, int[] arg_types, int ret_type)

    /// Creates a new virtual machine given an execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern VMPtr public create_vm(EnvPtr env)

    /// Disposes the given virtual machine.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public destroy_vm(VMPtr vm)

    /// Creates a symbolic string list from an array of strings.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)>]
    extern IntPtr public rcl_make_string_list(VMPtr vm, int argc, string[] argv)

    /// Execute the program at the given starting point.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern int public run_vm(VMPtr vm, int entryLabel, IntPtr programArgs)

[<RequireQualifiedAccess>]
type public RclType =
    | UINT8 = 0         // uint8
    | INT8 = 1          // int8
    | UINT16 = 2        // uint16
    | INT16 = 3         // int16
    | UINT32 = 4        // uint32
    | INT32 = 5         // int32
    | UINT64 = 6        // uint64
    | INT64 = 7         // int64
    | FLOAT32 = 8       // float32
    | FLOAT64 = 9       // float64
    | LONGDOUBLE = 10   // long double (precision depends on architecture)
    | CHAR = 11         // char (32 bits unicode in Liyh)
    | STRING = 12       // string (ptr)
    | PTR = 13          // void* (opaque pointer / buffer)
    | VOID = 14         // void

module public RclType =

    let public RclTypeToInt32 (rclType: RclType) =
        int32 rclType

type public RCLFFIBinding =
    { Library: string
      QualifiedName: string
      FunctionName: string
      Arity: int
      ArgTypes: RclType[]
      RetType: RclType }

type public OpCode =
    | Halt = 0
    | Jump = 1
    | JumpFalse = 2
    | JumpTrue = 3
    | Reserve = 4
    | Call = 5
    | Tailcall = 6
    | Ret = 7
    | Apply = 8
    | Mov = 9
    | LoadInt = 10
    | LoadAtom = 11
    | LoadFloat = 12
    | LoadChar = 13
    | LoadString = 14
    | LoadBool = 15
    | Add = 16
    | Sub = 17
    | Mul = 18
    | Div = 19
    | Mod = 20
    | Neg = 21
    | Equal = 22
    | NotEqual = 23
    | Not = 24
    | Leq = 25
    | Le = 26
    | Ge = 27
    | Geq = 28
    | StrCat = 29
    | MkRecord = 30
    | ExtendRecord = 31
    | GetField = 32
    | Alloc = 33
    | Subst = 34
    | Closure = 35
    | CallClosure = 36
    | GetUpvalue = 37
    | TestTag = 38
    | Deconstruct = 39
    | Arity = 40
    | DeconstructDyn = 41
    | Delay = 42
    | Force = 43
    | Cast = 44
    | CallFFI = 45
    | BufferAlloc = 46
    | BufferGet = 47
    | BufferSet = 48
    | BufferRealloc = 49
    | BufferLength = 50
    | BufferToString = 51
    | StringToBuffer = 52
    | PPShow = 53
    | Print = 54

[<Struct>]
type public ByteCodeInstr =
    | Label of label: int
    | Comment of comment: string * newline: bool
    | Instr of OpCode * int * int * int * int

[<Struct>]
type public Reg =
    val Index: int
    new(idx) = { Index = idx }
    override this.ToString() = sprintf "r%d" this.Index

[<AutoOpen>]
module public Reg =
    let public (|Reg|) (reg: Reg) = reg.Index

[<Struct>]
type public Strategy =
    | Strict
    | Lazy
    | Outermost
    | Invalid
    | Memoize

    static member FromAST (astStrat: Liyh.Syntax.SyntaxTree.RewritingStrategy) =
        match astStrat with
        | Liyh.Syntax.SyntaxTree.RewritingStrategy.Strict -> Strict
        | Liyh.Syntax.SyntaxTree.RewritingStrategy.Lazy -> Lazy
        | Liyh.Syntax.SyntaxTree.RewritingStrategy.Outermost -> Outermost
        | Liyh.Syntax.SyntaxTree.RewritingStrategy.Invalid -> Invalid
        | Liyh.Syntax.SyntaxTree.RewritingStrategy.Memoize -> Memoize

[<Struct>]
type public RuleInfo =
    { Name: string
      Arity: int
      Strategy: Strategy
      ContextName: string option }

type public LabelIndex = int
type public DispatchTable = Map<RuleInfo, LabelIndex>  // rule info : label

[<RequireQualifiedAccess>]
module public DispatchTable =

    /// Lookup an element in the dispatch table, returning a `Some(label, strategy)` value if the
    /// element is in the domain of the map and `None` if not.
    let public tryFindByNameArity (name: string, arity: int) (dispatchTable: DispatchTable) =
        dispatchTable
        |> Map.tryPick (fun ruleInfo label ->
            if (name, arity) = (ruleInfo.Name, ruleInfo.Arity)
            then Some (label, ruleInfo.Strategy)
            else None)

    /// Assuming the given key is present in the dispatch table, returns its associated value.
    let public get (name: string, arity: int) (dispatchTable: DispatchTable) =
        match tryFindByNameArity (name, arity) dispatchTable with
        | Some value -> value
        | None -> failwithf "Unfound key in the dispatch table: %A" (name, arity)

    /// Checks if the given key is found in the given dispatch table.
    let public contains (name: string, arity: int) (dispatchTable: DispatchTable) =
        dispatchTable
        |> tryFindByNameArity (name, arity)
        |> Option.isSome

    /// Checks if the given dispatch table contains an entry with the given name.
    let public containsByName (name: string) (dispatchTable: DispatchTable) =
        dispatchTable
        |> Map.exists (fun ruleInfo _ -> ruleInfo.Name = name)

    /// Gets the number of entry in the given dispatch table.
    let public count (dispatchTable: DispatchTable) =
        dispatchTable.Count

type public CompiledProgram =
    { Program: ByteCodeInstr[]          // the compiled program
      EntryPointLabel: LabelIndex       // the entry point of the program (label)
      DispatchTable: DispatchTable      // dispatch table (RuleInfo : LabelIndex)
      FFIBinding: RCLFFIBinding[] }     // bindings for the foreign function interface
