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

    /// Creates a new virtual machine given an execution environment.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern VMPtr public create_vm(EnvPtr env)

    /// Disposes the given virtual machine.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public destroy_vm(VMPtr vm)

    /// Execute the program at the given starting point.
    [<DllImport(librcl, CallingConvention = CallingConvention.Cdecl)>]
    extern void public run_vm(VMPtr vm, int entryLabel)

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
    | Add = 15
    | Sub = 16
    | Mul = 17
    | Div = 18
    | Mod = 19
    | Neg = 20
    | Equal = 21
    | NotEqual = 22
    | Not = 23
    | Leq = 24
    | Le = 25
    | Ge = 26
    | Geq = 27
    | StrCat = 28
    | MkRecord = 29
    | ExtendRecord = 30
    | GetField = 31
    | Alloc = 32
    | Subst = 33
    | Closure = 34
    | CallClosure = 35
    | GetUpvalue = 36
    | TestTag = 37
    | Deconstruct = 38
    | Delay = 39
    | Force = 40
    | PPShow = 41
    | Print = 42

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
      Strategy: Strategy }

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

    /// Checks if the given key is found in the given dispatch table.
    let public contains (name: string, arity: int) (dispatchTable: DispatchTable) =
        dispatchTable
        |> tryFindByNameArity (name, arity)
        |> Option.isSome

type public CompiledProgram =
    { Program: ByteCodeInstr[]          // the compiled program
      EntryPointLabel: LabelIndex       // the entry point of the program (label)
      DispatchTable: DispatchTable }

