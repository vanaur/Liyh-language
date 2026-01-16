#nowarn "20"
namespace Liyh.LyVM

open BindingRCL
open System

module private InternTable =
    open System.Collections.Concurrent
    open System.Threading

    type public Table() =
        let table = ConcurrentDictionary<string, int>()
        let mutable reverse = Array.Empty<string>()
        let mutable nextId = 0
        let mutable lockObj = obj()

        member public _.Intern(str: string) =
            match table.TryGetValue str with
            | true, id -> id
            | _ ->
                let currentId = Interlocked.Increment(&nextId) - 1
                match table.TryAdd(str, currentId) with
                | false -> table.[str]
                | true ->
                    lock lockObj (fun () ->
                        if currentId >= reverse.Length then
                            let newReverse = Array.zeroCreate (currentId + 1)
                            Array.blit reverse 0 newReverse 0 reverse.Length
                            newReverse.[currentId] <- str
                            reverse <- newReverse
                        elif reverse.[currentId] <> str then
                            invalidOp "Inconsistent intern table state."
                    )
                    currentId

        member _.Get(id: int) =
            if id < 0 || id >= reverse.Length then
                invalidArg "id" "Invalid identifier."

            reverse.[id]

    let public StringTable = Table()
    let public AtomTable = Table()

/// Type helper for building and compiling bytecode for the LyVM.
type public ByteCodeBuilder() =
    let instructions = ResizeArray<ByteCodeInstr>()

    let mutable maxStackTop = 0
    let mutable stackTop = 0

    /// Allocates a new register.
    member public __.Alloc() =
        let reg = Reg stackTop
        stackTop <- stackTop + 1

        if stackTop > maxStackTop then
            maxStackTop <- stackTop

        reg

    /// Allocates a continuous block of registers.
    member public __.AllocBlock (count: int) =
        if count <= 0 then
            Reg stackTop
        else
            let start = Reg stackTop
            stackTop <- stackTop + count

            if stackTop > maxStackTop
                then maxStackTop <- stackTop

            start

    /// Prepare a list of registers with `mov` instructions.
    member private this.PrepareBlock (regs: Reg list) =
        match regs with
        | [] -> (Reg 0, 0)
        | _ ->
            let start = this.AllocBlock regs.Length
            List.iteri (fun i (Reg src) -> instructions.Add(Instr(OpCode.Mov, start.Index + i, src, 0, 0))) regs
            (start, List.length regs)

    member private __.CompactStack (blockStart: Reg, blockSize: int, result: Reg) =
        if blockSize > 0 then
            let (Reg startIndex) = blockStart
            let (Reg resultIndex) = result

            instructions.Add(Instr(OpCode.Mov, startIndex, resultIndex, 0, 0))
            stackTop <- startIndex + 1

            Reg startIndex
        else
            result

    /// Helper to prepare a function-like block, given a number of expected arguments.
    member public this.DefineFunction (argCount: int) =
        let savedMaxStackTop = maxStackTop

        stackTop <- 0
        maxStackTop <- 0

        let patchIndex = instructions.Count
        instructions.Add(Instr(OpCode.Reserve, 0, 0, 0, 0))

        let regs = List.init argCount (fun _ -> this.Alloc())
        (regs, patchIndex, savedMaxStackTop)

    /// Helper to finalize a fuction-like block, the arguments to pass are those returned from `DefineFunction`.
    member public __.FinalizeFunction (patchIndex: int, savedMaxStackTop: int) =
        if patchIndex <> -1 then
            instructions.[patchIndex] <- Instr(OpCode.Reserve, maxStackTop, 0, 0, 0)
        
        maxStackTop <- savedMaxStackTop

    /// Defines a scope and apply the given function within it.
    member public __.Scope (f: unit -> Reg) =
        let savedTop = stackTop
        let result = f()
        let (Reg resultIndex) = result

        if resultIndex >= savedTop then
            let newReg = Reg savedTop

            if savedTop <> resultIndex then
                instructions.Add(Instr(OpCode.Mov, savedTop, resultIndex, 0, 0))

            stackTop <- savedTop + 1
            newReg
        else
            stackTop <- savedTop
            result

    /// Defines a scope and apply the given function within it.
    member public __.Scope (f: unit -> unit) =
        let savedTop = stackTop in f()
        stackTop <- savedTop


    // --- Instructions --- //


    /// Adds a comment to the generate bytecode (this won't be compiled in the final executable bytecode).
    member public __.Comment (comment: string) =
        instructions.Add(Comment (comment, false))

    /// Sames as `Comment`, but adds a new line _before_ the comment.
    member public __.CommentNewLine (comment: string) =
        instructions.Add(Comment (comment, true))

    member public __.SetLabel (labelId: int) =

        // Little optimization: if the last instruction was a jump to this label, it is deleted.
        if instructions.Count > 0 then
            match instructions.[instructions.Count - 1] with
            | Instr(OpCode.Jump, target, _, _, _) when target = labelId ->
                instructions.RemoveAt(instructions.Count - 1)
            | _ -> ()

        instructions.Add(Label labelId)

    member public __.Halt () =
        instructions.Add(Instr(OpCode.Halt, 0, 0, 0, 0))

    member public __.Jump (label: int) =
        instructions.Add(Instr(OpCode.Jump, label, 0, 0, 0))

    member public __.JumpFalse (Reg cond, label: int) =
        instructions.Add(Instr(OpCode.JumpFalse, cond, label, 0, 0))

    member public __.JumpTrue (Reg cond, label: int) =
        instructions.Add(Instr(OpCode.JumpTrue, cond, label, 0, 0))

    member public __.Ret (Reg r) =
        instructions.Add(Instr(OpCode.Ret, r, 0, 0, 0))
    
    member public __.Mov (Reg dst, Reg src) =
        instructions.Add(Instr(OpCode.Mov, dst, src, 0, 0))

    member public this.Call (label: int, args: Reg list) =
        let (blockStart, count) = this.PrepareBlock args
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.Call, label, blockIdx, count, dstIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.Tailcall (label: int, args: Reg list) =
        let (blockStart, count) = this.PrepareBlock args
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.Tailcall, label, blockIdx, count, 0))

    member public this.Apply (Reg fnReg, args: Reg list) =
        let (blockStart, count) = this.PrepareBlock(args)
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.Apply, fnReg, blockIdx, count, dstIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.LoadInt (value: int) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.LoadInt, dstIdx, value, 0, 0))
        dst

    member public this.LoadChar (c: char) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.LoadChar, dstIdx, int c, 0, 0))
        dst

    member public this.LoadFloat (value: float) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst
        let bits = BitConverter.DoubleToInt64Bits value

        instructions.Add(Instr(OpCode.LoadFloat, dstIdx, int bits, int (bits >>> 32), 0))
        dst

    member public this.LoadString (s: string) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst
        let strId = InternTable.StringTable.Intern s

        instructions.Add(Instr(OpCode.LoadString, dstIdx, strId, 0, 0))
        dst

    member public this.LoadAtom (name: string) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst
        let atomId = InternTable.AtomTable.Intern name

        instructions.Add(Instr(OpCode.LoadAtom, dstIdx, atomId, 0, 0))
        dst

    /// Used when the end of a computation require a register but no value. This method allows to avoid
    /// allocating the symbol unit for nothing.
    member public this.Unit () =
        this.Alloc()

    member private this.BinOp (opcode: OpCode, Reg left, Reg right) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(opcode, dstIdx, left, right, 0))
        dst

    member private this.UnOp (opcode: OpCode, Reg src) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(opcode, dstIdx, src, 0, 0))
        dst

    member public this.Add (l, r) = this.BinOp(OpCode.Add, l, r)
    member public this.Sub (l, r) = this.BinOp(OpCode.Sub, l, r)
    member public this.Mul (l, r) = this.BinOp(OpCode.Mul, l, r)
    member public this.Div (l, r) = this.BinOp(OpCode.Div, l, r)
    member public this.Mod (l, r) = this.BinOp(OpCode.Mod, l, r)
    member public this.Neg (src) = this.UnOp(OpCode.Neg, src)

    member public this.Eq (l, r) = this.BinOp(OpCode.Equal, l, r)
    member public this.NotEqual (l, r) = this.BinOp(OpCode.NotEqual, l, r)
    member public this.Leq (l, r) = this.BinOp(OpCode.Leq, l, r)
    member public this.Le (l, r) = this.BinOp(OpCode.Le, l, r)
    member public this.Geq (l, r) = this.BinOp(OpCode.Geq, l, r)
    member public this.Ge (l, r) = this.BinOp(OpCode.Ge, l, r)
    member public this.Not (src) = this.UnOp(OpCode.Not, src)

    member public this.StrCat (l, r) =
        this.BinOp(OpCode.StrCat, l, r)

    member public this.MkRecord (fields: Reg list) =
        let (blockStart, count) = this.PrepareBlock fields
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.MkRecord, dstIdx, count, blockIdx, 0))
        this.CompactStack(blockStart, count, dst)

    member public this.ExtendRecord (Reg baseReg, newFields: Reg list) =
        let (blockStart, count) = this.PrepareBlock newFields
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.ExtendRecord, dstIdx, baseReg, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.GetField (Reg record, fieldName: string, failLabel: int) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        let fieldId = InternTable.AtomTable.Intern fieldName
        instructions.Add(Instr(OpCode.GetField, dstIdx, record, fieldId, failLabel))
        dst

    member public this.AllocData (tagName: string, children: Reg list) =
        let (blockStart, count) = this.PrepareBlock children
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst
        let tagId = InternTable.AtomTable.Intern tagName

        instructions.Add(Instr(OpCode.Alloc, dstIdx, tagId, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.Closure (label: int, captures: Reg list) =
        let (blockStart, count) = this.PrepareBlock captures
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.Closure, dstIdx, label, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.CallClosure (Reg closure, args: Reg list) =
        let (blockStart, count) = this.PrepareBlock args
        let dst = this.Alloc()
        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.CallClosure, closure, blockIdx, count, dstIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.GetUpvalue (index: int) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.GetUpvalue, dstIdx, index, 0, 0))
        dst

    member public __.TestTag (Reg term, tagName: string, failLabel: int) =
        let tagId = InternTable.AtomTable.Intern tagName
        instructions.Add(Instr(OpCode.TestTag, term, tagId, failLabel, 0))

    member public __.TestRecord (Reg term, failLabel: int) =
        instructions.Add(Instr(OpCode.TestTag, term, SYM_RECORD, failLabel, 0))

    member public this.Delay (label: int, captures: Reg list) =
        let (blockStart, count) = this.PrepareBlock captures
        let dst = this.Alloc()

        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.Delay, dstIdx, label, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member this.Force (Reg thunkReg) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.Force, dstIdx, thunkReg, 0, 0))
        dst

    member public this.Deconstruct (Reg term, childIndex: int) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst
        instructions.Add(Instr(OpCode.Deconstruct, dstIdx, term, childIndex, 0))
        dst

    member public __.Print (Reg r) =
        instructions.Add(Instr(OpCode.Print, r, 0, 0, 0))

    /// Assuming registers containing strings, return the register containing their concatenation.
    /// This method is mainly used for runtime error message generation.
    member public this.ConcatMany (regs: Reg list) =
        match regs with
        | [] -> this.LoadString ""
        | [ x ] -> x
        | head :: tail -> List.fold (fun acc next -> this.StrCat(acc, next)) head tail

    /// Handle a runtime error printting and halt the VM.
    member public this.RuntimeError (msg: string) =
        let sb = new Text.StringBuilder()

        sb.Append(Liyh.Utils.ColorTerm.colorize (Liyh.Utils.ColorTerm.Color.Basic "red") "Runtime Error: ")
        sb.AppendLine($"{msg}")
        sb.AppendLine($"\nStopped the programme's execution.")

        let formatMsg = sb.ToString()

        this.Print(this.LoadString $"{formatMsg}")
        this.Halt()

        this.LoadInt(-1) // dummy

    member public this.RuntimeError (messageReg: Reg) =
        let sbPrefix = new Text.StringBuilder()
        sbPrefix.Append(Liyh.Utils.ColorTerm.colorize (Liyh.Utils.ColorTerm.Color.Basic "red") "Runtime Error: ") |> ignore
        let prefixReg = this.LoadString(sbPrefix.ToString())

        let sbSuffix = new Text.StringBuilder()
        sbSuffix.AppendLine()
        sbSuffix.AppendLine("Stopped the programme's execution.")
        let suffixReg = this.LoadString(sbSuffix.ToString())

        let finalMsg = this.ConcatMany([prefixReg; messageReg; suffixReg])

        this.Print(finalMsg)
        this.Halt()

        this.LoadInt(-1) // dummy

    member public this.PPShow (Reg src) =
        let dst = this.Alloc()
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.PPShow, dstIdx, src, 0, 0))
        dst

    /// Generates F#-wise version of the final bytecode.
    member public __.Compile(entryLabel: int, dispatchTable: DispatchTable) =
        { Program = instructions.ToArray()
          EntryPointLabel = entryLabel
          DispatchTable = dispatchTable }

/// A pretty printer for the bytecode.
module public PrettyPrinter =
    open System.Text
    open System.IO

    let private reg r = $"r{r}"
    let private lbl l = $".L{l}"

    let public prettyPrintInstr (last: ByteCodeInstr option) (instr: ByteCodeInstr) =
        match instr with
        | Comment (comment, true) ->
            $"\n; {comment}"

        | Comment (comment, false) ->
            $"; {comment}"

        | Label(l) ->
            match last with
            | Some(Comment _) -> $"{lbl l}:"
            | _ -> $"\n{lbl l}:"

        | Instr(OpCode.Halt, _, _, _, _) ->
            "    halt"

        | Instr(OpCode.Jump, target, _, _, _) ->
            $"    jump {lbl target}"

        | Instr(OpCode.JumpFalse, cond, target, _, _) ->
            $"    jf {reg cond}, {lbl target}"

        | Instr(OpCode.JumpTrue, cond, target, _, _) ->
            $"    jt {reg cond}, {lbl target}"

        | Instr(OpCode.Reserve, s, _, _, _) ->
            $"    reserve {s}"

        | Instr(OpCode.Ret, r, _, _, _) ->
            $"    ret {reg r}"

        | Instr(OpCode.Call, label, argsStart, argCount, dst) ->
            $"    {reg dst} = call {lbl label}({reg argsStart}..+{argCount})"

        | Instr(OpCode.Tailcall, label, argsStart, argCount, _) ->
            $"    tailcall {lbl label}({reg argsStart}..+{argCount})"

        | Instr(OpCode.Apply, fn, argsStart, argCount, dst) ->
            $"    {reg dst} = apply {reg fn}({reg argsStart}..+{argCount})"

        | Instr(OpCode.Mov, dst, src, _, _) ->
            $"    {reg dst} = mov {reg src}"

        | Instr(OpCode.LoadInt, dst, value, _, _) ->
            $"    {reg dst} = int {value}"

        | Instr(OpCode.LoadChar, dst, value, _, _) ->
            $"    {reg dst} = char '{char value}'"

        | Instr(OpCode.LoadFloat, dst, lo, hi, _) ->
            let bits = (int64 lo) ||| ((int64 hi) <<< 32)
            let value = System.BitConverter.Int64BitsToDouble(bits)
            $"    {reg dst} = float {value}"

        | Instr(OpCode.LoadString, dst, strId, _, _) ->
            let str = InternTable.StringTable.Get(strId)
            $"    {reg dst} = string \"{str}\""

        | Instr(OpCode.LoadAtom, dst, atomId, _, _) ->
            let atom = InternTable.AtomTable.Get(atomId)
            $"    {reg dst} = atom :{atom}"

        | Instr(OpCode.Add, dst, l, r, _) ->
            $"    {reg dst} = add {reg l}, {reg r}"

        | Instr(OpCode.Sub, dst, l, r, _) ->
            $"    {reg dst} = sub {reg l}, {reg r}"

        | Instr(OpCode.Mul, dst, l, r, _) ->
            $"    {reg dst} = mul {reg l}, {reg r}"

        | Instr(OpCode.Div, dst, l, r, _) ->
            $"    {reg dst} = div {reg l}, {reg r}"

        | Instr(OpCode.Mod, dst, l, r, _) ->
            $"    {reg dst} = mod {reg l}, {reg r}"

        | Instr(OpCode.Neg, dst, src, _, _) ->
            $"    {reg dst} = neg {reg src}"

        | Instr(OpCode.Equal, dst, l, r, _) ->
            $"    {reg dst} = eq {reg l}, {reg r}"

        | Instr(OpCode.NotEqual, dst, l, r, _) ->
            $"    {reg dst} = neq {reg l}, {reg r}"

        | Instr(OpCode.Leq, dst, l, r, _) ->
            $"    {reg dst} = leq {reg l}, {reg r}"

        | Instr(OpCode.Le, dst, l, r, _) ->
            $"    {reg dst} = le {reg l}, {reg r}"

        | Instr(OpCode.Geq, dst, l, r, _) ->
            $"    {reg dst} = geq {reg l}, {reg r}"

        | Instr(OpCode.Ge, dst, l, r, _) ->
            $"    {reg dst} = ge {reg l}, {reg r}"

        | Instr(OpCode.Not, dst, src, _, _) ->
            $"    {reg dst} = not {reg src}"

        | Instr(OpCode.StrCat, dst, l, r, _) ->
            $"    {reg dst} = strcat {reg l}, {reg r}"

        | Instr(OpCode.MkRecord, dst, count, fieldsStart, _) ->
            $"    {reg dst} = mkrecord({reg fieldsStart}..+{count})"

        | Instr(OpCode.ExtendRecord, dst, base', count, fieldsStart) ->
            $"    {reg dst} = extend {reg base'} with ({reg fieldsStart}..+{count})"

        | Instr(OpCode.GetField, dst, record, fieldId, failLabel) ->
            let field = InternTable.AtomTable.Get(fieldId)
            $"    {reg dst} = getfield {reg record}.{field} or {lbl failLabel}"

        | Instr(OpCode.Alloc, dst, tagId, count, childrenStart) ->
            let tag = InternTable.AtomTable.Get(tagId)
            $"    {reg dst} = alloc :{tag}({reg childrenStart}..+{count})"

        | Instr(OpCode.Closure, dst, label, count, capturesStart) ->
            $"    {reg dst} = closure {lbl label}[{reg capturesStart}..+{count}]"

        | Instr(OpCode.CallClosure, closure, argsStart, argCount, dst) ->
            $"    {reg dst} = callclosure {reg closure}({reg argsStart}..+{argCount})"

        | Instr(OpCode.GetUpvalue, dst, index, _, _) ->
            $"    {reg dst} = upvalue[{index}]"

        | Instr(OpCode.TestTag, term, tagId, failLabel, _) when tagId = SYM_RECORD ->
            $"    testtype {reg term} is record or {lbl failLabel}"

        | Instr(OpCode.TestTag, term, tagId, failLabel, _) ->
            let tag = InternTable.AtomTable.Get(tagId)
            $"    testtag {reg term} is {tag} or {lbl failLabel}"

        | Instr(OpCode.Deconstruct, dst, term, index, _) ->
            $"    {reg dst} = deconstruct {reg term}[{index}]"

        | Instr(OpCode.Delay, dst, label, count, capturesStart) ->
            $"    {reg dst} = delay {lbl label}[{reg capturesStart}..+{count}]"

        | Instr(OpCode.Force, dst, src, _, _) ->
            $"    {reg dst} = force {reg src}"

        | Instr(OpCode.PPShow, dst, src, _, _) ->
            $"    {reg dst} = ppshow {reg src}"

        | Instr(OpCode.Print, r, _, _, _) ->
            $"    print {reg r}"

        | _ -> failwith "??"

    /// Generate a textual representation of the given compiled program.
    let public prettyPrint { Program = instructions } =
        let sb = StringBuilder()
        let mutable last = None

        for instr in instructions do
            sb.AppendLine(prettyPrintInstr last instr)
            last <- Some instr

        sb.ToString()

    /// Writes the compiled program into a file.
    let public saveToFile (cp: CompiledProgram) (path: string) =
        use file = File.Create(path)
        let bytes = Encoding.UTF8.GetBytes(prettyPrint cp)

        file.Write(bytes)

/// Wrapper for LyVM.
type public VM() =
    let env = create_env()
    let mutable isDisposed = false
    let mutable entryPointLabel = None

    interface IDisposable with
        member __.Dispose() =
            if not isDisposed then
                destroy_env env
                isDisposed <- true

    /// Emits the compiled program to LyVM.
    member public __.EmitFromCompiledProgram
        { Program = instructions
          EntryPointLabel = entryLabel
          DispatchTable = dispatchTable } =

        entryPointLabel <- Some entryLabel

        // we have to internate some of the heap-allocated values

        for KeyValue(ruleInfo, label) in dispatchTable do
            let symId = intern_symbol(env, ruleInfo.Name)
            intern_function(env, symId, ruleInfo.Arity, label)

        for instr in instructions do
            match instr with
            | Comment _ -> ()
            | Label labelId -> 
                set_label (env, labelId)

            | Instr(OpCode.LoadFloat, dst, lo, hi, _) ->
                let bits = (int64 (uint32 lo)) ||| ((int64 hi) <<< 32)
                let value = BitConverter.Int64BitsToDouble(bits)
                emit_load_float (env, dst, value)

            | Instr(OpCode.LoadString, dst, strId, _, _) ->
                let str = InternTable.StringTable.Get(strId)
                let idx = intern_string (env, str)
                emit (env, int OpCode.LoadString, dst, idx, 0, 0)

            | Instr(OpCode.LoadAtom, dst, atomId, _, _) ->
                let atom = InternTable.AtomTable.Get(atomId)
                let sym = intern_symbol (env, atom)
                emit (env, int OpCode.LoadAtom, dst, int sym, 0, 0)

            | Instr(OpCode.GetField, dst, record, fieldId, failLabel) ->
                let field = InternTable.AtomTable.Get(fieldId)
                let sym = intern_symbol (env, field)
                emit (env, int OpCode.GetField, dst, record, int sym, failLabel)

            | Instr(OpCode.Alloc, dst, tagId, count, childrenStart) ->
                let tag = InternTable.AtomTable.Get(tagId)
                let sym = intern_symbol (env, tag)
                emit (env, int OpCode.Alloc, dst, int sym, count, childrenStart)

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) when tagId = SYM_RECORD ->
                emit (env, int OpCode.TestTag, term, tagId, failLabel, 0)

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) ->
                let tag = InternTable.AtomTable.Get(tagId)
                let sym = intern_symbol (env, tag)
                emit (env, int OpCode.TestTag, term, int sym, failLabel, 0)

            | Instr(opcode, arg1, arg2, arg3, arg4) ->
                emit (env, int opcode, arg1, arg2, arg3, arg4)

    /// Runs the program and returns the elapsed time in milliseconds.
    member public _.Run() =
        let vm = create_vm env
        gc_init()

        try
            match entryPointLabel with
            | None -> failwith "The program does not present any entry point"
            | Some entryLabel ->
                let sw = Diagnostics.Stopwatch.StartNew()
                run_vm (vm, entryLabel)
                sw.Stop()
                sw.ElapsedMilliseconds

        finally
            destroy_vm vm
(*


/// A ridiculous set of optimizations for the bytecode.
module public Optimize =
    open System.Collections.Generic

    module private Peephole =

        /// Attempts to consume a sequence of Movs that correspond to a contiguous block.
        let private tryCollapseBlock 
            (targetStart: int)              // The register expected for the start of the block
            (count: int)                    // The size of the actual block
            (instrs: ByteCodeInstr list) =

            // Search for Movs by counting up from (count-1) to 0.
            let rec scan currentIdx currentStream =
                if currentIdx < 0 then
                    None 
                else
                    match currentStream with
                    | Instr(OpCode.Mov, dst, src, _, _) :: rest ->
                        if dst = targetStart + currentIdx then

                            // The Mov writes to the expected slot (base + offset)

                            let baseReg = src - currentIdx

                            match scan (currentIdx - 1) rest with
                            | Some (foundBase, finalStream) ->
                                if foundBase = baseReg then Some (baseReg, finalStream)
                                else None

                            | None ->
                                if currentIdx = 0 then Some (baseReg, rest)
                                else None
                        else
                            None
                    | _ ->
                        None

            if count <= 0 then None
            else scan (count - 1) instrs

        let private peepholeReversePass (instrs: ByteCodeInstr list) =
            let rec loop input =
                match input with

                // --- Mov redundancies --- //

                | Instr(op, dst, a, count, start) :: rest 
                    when (op = OpCode.Alloc || op = OpCode.Closure || op = OpCode.ExtendRecord) ->

                    match tryCollapseBlock start count rest with
                    | Some (newBase, newRest) -> Instr(op, dst, a, count, newBase) :: loop newRest
                    | None -> Instr(op, dst, a, count, start) :: loop rest

                | Instr(op, a, start, count, dst) :: rest 
                    when (op = OpCode.Call || op = OpCode.Tailcall || op = OpCode.Apply || op = OpCode.CallClosure) ->
                    
                    match tryCollapseBlock start count rest with
                    | Some (newBase, newRest) -> Instr(op, a, newBase, count, dst) :: loop newRest
                    | None -> Instr(op, a, start, count, dst) :: loop rest

                | Instr(OpCode.MkRecord, dst, count, start, ignored) :: rest ->
                    
                    match tryCollapseBlock start count rest with
                    | Some (newBase, newRest) -> Instr(OpCode.MkRecord, dst, count, newBase, ignored) :: loop newRest
                    | None -> Instr(OpCode.MkRecord, dst, count, start, ignored) :: loop rest

                | Instr(OpCode.Mov, rA, rB, _, _) :: Instr(OpCode.Mov, rB_dup, rC, _, _) :: rest 
                    when rB = rB_dup ->

                    loop (Instr(OpCode.Mov, rA, rC, 0, 0) :: Instr(OpCode.Mov, rB, rC, 0, 0) :: rest)

                // --- Standard peephole optimisations --- //

                | Instr(OpCode.Mov, dst, src, _, _) :: rest
                    when dst = src ->
                        loop rest

                | Instr(OpCode.Ret, retReg, _, _, _) :: Instr(OpCode.Mov, dst, src, _, _) :: rest 
                    when retReg = dst ->
                        loop (Instr(OpCode.Ret, src, 0, 0, 0) :: rest)

                | (Label l1 as lbl) :: Instr(OpCode.Jump, target, _, _, _) :: rest 
                    when l1 = target ->

                    lbl :: loop rest

                | Instr(OpCode.JumpFalse, cond, lbl, _, _) :: Instr(OpCode.Not, dst, src, _, _) :: rest 
                    when cond = dst ->

                    loop (Instr(OpCode.JumpTrue, src, lbl, 0, 0) :: rest)

                | Instr(OpCode.JumpTrue, cond, lbl, _, _) :: Instr(OpCode.Not, dst, src, _, _) :: rest 
                    when cond = dst ->

                    loop (Instr(OpCode.JumpFalse, src, lbl, 0, 0) :: rest)

                | (Label _ as lbl) :: rest -> lbl :: loop rest
                | head :: rest -> head :: loop rest
                | [] -> []

            loop instrs

        let public apply (cp: CompiledProgram) =
            { cp with
                Program =
                    cp.Program
                    |> List.ofArray
                    |> List.rev
                    |> peepholeReversePass
                    |> List.rev
                    |> Array.ofList }

    module private DeadCodeElimination =

        /// Checks whether the instruction contains indirections in the bytecode.
        let private hasControlFlowSideEffects (instr: ByteCodeInstr) =
            match instr with
            | Label _ -> true
            | Comment _ -> false
            | Instr(op, _, _, _, d) ->
                match op with
                | OpCode.Reserve
                | OpCode.Halt 
                | OpCode.Ret 
                | OpCode.Print 
                | OpCode.Jump 
                | OpCode.JumpTrue 
                | OpCode.JumpFalse 
                | OpCode.Call 
                | OpCode.Tailcall 
                | OpCode.CallClosure 
                | OpCode.Apply
                | OpCode.TestTag -> true 
                | OpCode.GetField when d <> 0 -> true
                | _ -> false

        /// Performs a dead code elimination onto the unused instructions.
        let private removeDeadInstructions (cp: CompiledProgram) =
            let program = cp.Program
            let n = program.Length
            let keep = Array.create n false

            // Map: Label ID -> Set of registers alive at the start of this label
            // This allows information to be transmitted through Jumps
            let mutable labelLiveIn = Map.empty<int, Set<int>>

            // Fixed point iteration
            let mutable changed = true

            while changed do
                let mutable currentLive = Set.empty
                changed <- false

                for i = n - 1 downto 0 do
                    let instr = program.[i]

                    match instr with
                    | Label l ->

                        // We arrive at the beginning of a block.
                        // `currentLive` now contains the registers needed to enter this block.
                        // We save this information for jumps that target this label.

                        let knownLive =
                            labelLiveIn
                            |> Map.tryFind l
                            |> Option.defaultValue Set.empty

                        if currentLive <> knownLive then
                            labelLiveIn <- labelLiveIn |> Map.add l currentLive
                            changed <- true

                    | Instr(OpCode.Jump, target, _, _, _) ->

                        // Unconditional jump: what follows physically is ignored.

                        currentLive <-
                            labelLiveIn
                            |> Map.tryFind target
                            |> Option.defaultValue Set.empty

                    | Instr(OpCode.JumpTrue, _, target, _, _)
                    | Instr(OpCode.JumpFalse, _, target, _, _)
                    | Instr(OpCode.TestTag, _, _, target, _) ->

                        // Conditional jump: Vivacity = (Rest of block) U (Jump target)

                        let targetLive =
                            labelLiveIn
                            |> Map.tryFind target
                            |> Option.defaultValue Set.empty

                        currentLive <- Set.union currentLive targetLive

                    | Instr(OpCode.GetField, _, _, _, failLabel) when failLabel <> 0 ->

                        // GetField may jump if it fails

                        let targetLive =
                            labelLiveIn
                            |> Map.tryFind failLabel
                            |> Option.defaultValue Set.empty

                        currentLive <- Set.union currentLive targetLive

                    | _ -> ()

                    /// Decides whether to keep or delete the instruction.
                    let isNeeded =
                        if hasControlFlowSideEffects instr then 
                            true
                        else
                            match classifyRegisterUsage instr with
                            | Some { Dest = d } when d >= 0 -> 
                                // The instruction is useful if it defines a register that is alive (expected later).
                                Set.contains d currentLive
                            | _ -> false

                    if isNeeded then
                        keep.[i] <- true

                        // Standard backward pass:
                        // - Remove what the 'Define' statement defines (because it is produced here, so it is not needed before)
                        // - Add what the 'Use' statement uses (because it is consumed here, so it is needed before)

                        classifyRegisterUsage instr
                        |> Option.iter (fun { Dest = d; Used = used } ->
                            if d >= 0 then
                                currentLive <- Set.remove d currentLive

                            for u in used do
                                currentLive <- Set.add u currentLive)

                    else
                        // Dead instruction
                        ()

            { cp with
                Program =
                    program 
                    |> Array.mapi (fun i instr -> if keep.[i] then Some instr else None)
                    |> Array.choose id }

        let private removeUnreachableCode (cp: CompiledProgram) =
            let root = [| cp.EntryPointLabel |] // Could there be other elements here in the future?

            let labelIndices = Dictionary<int, int>()
            for i = 0 to cp.Program.Length - 1 do
                match cp.Program.[i] with
                | Label l -> labelIndices.[l] <- i
                | _ -> ()

            let visited = HashSet<int>()
            let queue = Queue<int>()

            // Initialisation
            for root in root do
                if labelIndices.ContainsKey root && visited.Add root then
                    queue.Enqueue root

            while queue.Count > 0 do
                let label = queue.Dequeue()
                let idx = labelIndices.[label]
                let mutable i = idx
                let mutable running = true
                
                while running && i < cp.Program.Length do
                    let instr = cp.Program.[i]

                    if i > idx then 
                        match instr with 
                        | Label nextLabel -> 
                            running <- false 
                            let prevInstr = cp.Program.[i - 1]
                            let isTerminator = 
                                match prevInstr with
                                | Instr(OpCode.Jump, _, _, _, _)
                                | Instr(OpCode.Ret, _, _, _, _)
                                | Instr(OpCode.Halt, _, _, _, _) -> true
                                | _ -> false

                            if not isTerminator then
                                if labelIndices.ContainsKey nextLabel && visited.Add nextLabel then
                                    queue.Enqueue nextLabel

                        | _ -> ()
                    
                    if running then
                        i <- i + 1
                        match instr with
                        | Instr(OpCode.Jump, target, _, _, _) 
                        | Instr(OpCode.JumpTrue, _, target, _, _)
                        | Instr(OpCode.JumpFalse, _, target, _, _)
                        | Instr(OpCode.TestTag, _, _, target, _)
                        | Instr(OpCode.Call, target, _, _, _)
                        | Instr(OpCode.Tailcall, target, _, _, _)
                        | Instr(OpCode.Closure, _, target, _, _) ->
                            if labelIndices.ContainsKey target && visited.Add target then
                                queue.Enqueue target

                        | Instr(OpCode.GetField, _, _, _, failLabel) when failLabel <> 0 ->
                            if labelIndices.ContainsKey failLabel && visited.Add failLabel then
                                queue.Enqueue failLabel

                        | _ -> ()
            
            // Reconstruct the compild program

            let result = ResizeArray<ByteCodeInstr>()
            let mutable keeping = false

            for instr in cp.Program do
                match instr with
                | Label l ->
                    if visited.Contains l then
                        keeping <- true
                        result.Add instr
                    else
                        keeping <- false
                | _ ->
                    if keeping then
                        result.Add instr

            let newDispatchTable =
                cp.DispatchTable
                |> Map.filter (fun _ label -> visited.Contains label)

            { cp with
                Program = result.ToArray()
                DispatchTable = newDispatchTable }

        /// Performs a dead code elimination.
        /// (https://en.wikipedia.org/wiki/Dead-code_elimination#Dynamic_dead-code_elimination).
        let public apply (cp: CompiledProgram) =

            let cpClean =
                { cp with
                    Program =
                        cp.Program
                        |> Array.filter (not << _.IsComment) }

            let rec applyUntilFixpoint cp =
                let cpDead = removeDeadInstructions cpClean
                let cpReachable = removeUnreachableCode cpDead

                if cpReachable = cp then cpReachable
                else applyUntilFixpoint cpReachable

            applyUntilFixpoint cpClean

    /// Apply a (very) basic pass of optimization onto the program.
    /// 
    /// This does not have a measurable impact on performance, but it slightly
    /// cleans up the generated bytecode and very slightly improves certain patterns.
    let public apply =
        Peephole.apply >> DeadCodeElimination.apply

*)

[<RequireQualifiedAccess>]
module public AOT =
    open System.Text
    open System.IO
    open System.Diagnostics
    open System.Reflection
    open System.Collections.Generic

    let private readEmbeddedResource resourceName =
        let assembly = Assembly.GetExecutingAssembly()
        use stream = assembly.GetManifestResourceStream(resourceName)
        use reader = new StreamReader(stream)
        reader.ReadToEnd()

    let private escapeCString (s: string) =
        s.Replace("\\", "\\\\")
         .Replace("\"", "\\\"")
         .Replace("\n", "\\n")
         .Replace("\r", "\\r")
         .Replace("\t", "\\t")

    /// Produces an executable at the given path.
    /// This executable contains the whole runtime and the compiled bytecode embedded as static arrays.
    let public compile (cp: CompiledProgram) (fileName: string) =
        let sb = StringBuilder()

        let inline appendLine (line: string) =
            sb.AppendLine(line)
            |> ignore

        // --- Pre-calculation: Filter instructions and map labels to real indices --- //

        let labelOffsets = Dictionary<int, int>()
        let realInstructions = ResizeArray<ByteCodeInstr>()
        let mutable instructionIndex = 0

        for instr in cp.Program do
            match instr with
            | Label id -> 
                // A label points to the next "real" instruction index
                if not (labelOffsets.ContainsKey id) then
                    labelOffsets.Add(id, instructionIndex)
            | Comment _ -> () // Comments are stripped
            | _ -> 
                realInstructions.Add(instr)
                instructionIndex <- instructionIndex + 1

        // Scan to find Max IDs for Strings and Atoms
        // We need to know the size of the pools. We scan the used instructions to find the max ID.

        let mutable maxStringId = -1
        let mutable maxAtomId = -1
        let mutable maxLabelId = -1
        
        // Update max label from offsets
        for k in labelOffsets.Keys do
            if k > maxLabelId then maxLabelId <- k

        // Scan instructions
        for instr in realInstructions do
            match instr with
            | Instr(OpCode.LoadString, _, id, _, _) -> if id > maxStringId then maxStringId <- id
            | Instr(OpCode.LoadAtom, _, id, _, _) -> if id > maxAtomId then maxAtomId <- id
            | Instr(OpCode.Alloc, _, id, _, _) -> if id > maxAtomId then maxAtomId <- id
            | Instr(OpCode.GetField, _, _, id, _) -> if id > maxAtomId then maxAtomId <- id
            | Instr(OpCode.TestTag, _, id, _, _) -> if id > maxAtomId then maxAtomId <- id
            | _ -> ()

        // Also ensure symbols from DispatchTable are included (even if not used in bytecode)
        for KeyValue(ruleInfo, _) in cp.DispatchTable do
             let id = InternTable.AtomTable.Intern ruleInfo.Name 
             if id > maxAtomId then maxAtomId <- id

        // --- Generate C Static Arrays --- //

        appendLine("    // --- Static Data Embed ---")
        appendLine("    static const char* static_strings[] = {")
        for i = 0 to maxStringId do
            try 
                let s = InternTable.StringTable.Get(i)
                appendLine($"        \"{escapeCString s}\",")
            with _ -> 
                appendLine("        \"\",") // Fallback for gaps
        appendLine("    };")

        // Symbols
        appendLine("\n    static const char* static_symbols[] = {")
        for i = 0 to maxAtomId do
            try
                let s = InternTable.AtomTable.Get(i)
                appendLine($"        \"{escapeCString s}\",")
            with _ ->
                appendLine("        \"\",")
        appendLine("    };")

        // Labels
        appendLine("\n    static const int static_labels[] = {")
        for i = 0 to maxLabelId do
            if labelOffsets.ContainsKey i then
                sb.Append($"{labelOffsets.[i]}, ")
            else
                sb.Append("-1, ")

            if (i + 1) % 20 = 0 then sb.AppendLine() |> ignore
        appendLine("\n    };")

        // Bytecode
        appendLine("\n    static const instr_t static_program[] = {")
        for instr in realInstructions do
            match instr with
            | Instr(op, a, b, c, d) ->
                let opInt = int op

                // F# frontend for `LoadFloat` considers `b = Lo` and `c = Hi`
                // C runtime (rcl.c) expects `b = Hi` and `c = Lo`
                // We must swap b and c here. I don't know why we did that... We shall update.
                if op = OpCode.LoadFloat then
                     appendLine($"        {{ {opInt}, {a}, {c}, {b}, {d} }},")
                else
                     appendLine($"        {{ {opInt}, {a}, {b}, {c}, {d} }},")
            | _ -> ()
        appendLine("    };")


        // --- Initialization Logic --- //

        appendLine("\n    // --- Runtime Initialization ---")

        // Load Strings
        appendLine("    size_t num_strings = sizeof(static_strings) / sizeof(char*);")
        appendLine("    for (size_t i = 0; i < num_strings; i++) {")
        appendLine("        intern_string(env_ptr, static_strings[i]);")
        appendLine("    }")

        // Load Symbols
        appendLine("    size_t num_symbols = sizeof(static_symbols) / sizeof(char*);")
        appendLine("    for (size_t i = 0; i < num_symbols; i++) {")
        appendLine("        intern_symbol(env_ptr, static_symbols[i]);")
        appendLine("    }")

        // Load Program
        appendLine("    size_t prog_size = sizeof(static_program) / sizeof(instr_t);")
        appendLine("    env_ptr->program = (instr_t*)GC_MALLOC_ATOMIC(prog_size * sizeof(instr_t));")
        appendLine("    memcpy(env_ptr->program, static_program, sizeof(static_program));")
        appendLine("    env_ptr->program_size = prog_size;")
        appendLine("    env_ptr->program_capacity = prog_size;")

        // Load Labels
        appendLine("    size_t labels_count = sizeof(static_labels) / sizeof(int);")
        appendLine("    env_ptr->labels = (int*)GC_MALLOC_ATOMIC(labels_count * sizeof(int));")
        appendLine("    memcpy(env_ptr->labels, static_labels, sizeof(static_labels));")
        appendLine("    env_ptr->labels_capacity = labels_count;")

        // Init Dispatch Table
        appendLine("\n    // --- Dispatch Table ---")
        for KeyValue(ruleInfo, label) in cp.DispatchTable do
            let name = ruleInfo.Name
            let arity = ruleInfo.Arity
            appendLine($"    intern_function(env_ptr, intern_symbol(env_ptr, \"{name}\"), {arity}, {label});")

        // --- Final Assembly and Compilation --- //

        let embed = readEmbeddedResource "liyh.C.rcl.c"
        let result =
            embed
                .Replace("<ENTRY-POINT>", string cp.EntryPointLabel)
                .Replace("<FILL-PROGRAM>", sb.ToString())

        let tempCFile = Path.GetTempFileName() + ".c"
        File.WriteAllText(tempCFile, result)

        let outputFile = Path.Combine(Directory.GetCurrentDirectory(), fileName)

        let flags =
            [ "-lm"              // Link math library (libm)
              "-lgc"             // Link Boehm garbage collector
              "-DEMBEDDED"       // Define EMBEDDED macro for standalone executable compilation
              "-O3"              // Aggressive optimization
              "-flto"            // Link-time optimization (whole-program analysis)
              "-fno-plt"         // Avoid PLT indirection for shared libraries (faster calls)
              "-march=native" ]  // Optimize for the current CPU architecture

            |> String.concat " "

        let compileArgs =
            $"-o {outputFile} {flags} {tempCFile}"

        let processInfo = ProcessStartInfo("cc", compileArgs)
        processInfo.UseShellExecute <- false
        processInfo.RedirectStandardOutput <- true
        processInfo.RedirectStandardError <- true

        use proc = Process.Start(processInfo)
        proc.WaitForExit()

        if proc.ExitCode <> 0 then
            let error = proc.StandardError.ReadToEnd()
            failwith $"Compilation failed: {error}"

        File.Delete(tempCFile)
        printfn $"Compiled successfully to: {outputFile}"

