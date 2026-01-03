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
    member public __.Compile(entryLabel: int, dispatchTable: Map<string * int, int>) =
        { Program = instructions.ToArray()
          EntryPointLabel = entryLabel
          DispatchTable = dispatchTable }

/// A pretty printer for the bytecode.
module public PrettyPrinter =
    open System.Text
    open System.IO

    let private reg r = $"r{r}"
    let private lbl l = $".L{l}"

    /// Generate a textual representation of the given compiled program.
    let public prettyPrint { Program = instructions } =
        let sb = StringBuilder()
        
        let mutable last = None

        for instr in instructions do
            match instr with
            | Comment (comment, true) -> sb.AppendLine($"\n; {comment}")
            | Comment (comment, false) -> sb.AppendLine($"; {comment}")

            | Label(l) ->
                match last with
                | Some(Comment _) -> sb.AppendLine($"{lbl l}:")
                | _ -> sb.AppendLine($"\n{lbl l}:")

            | Instr(OpCode.Halt, _, _, _, _) ->
                sb.AppendLine("    halt")

            | Instr(OpCode.Jump, target, _, _, _) ->
                sb.AppendLine($"    jump {lbl target}")

            | Instr(OpCode.JumpFalse, cond, target, _, _) ->
                sb.AppendLine($"    jf {reg cond}, {lbl target}")

            | Instr(OpCode.JumpTrue, cond, target, _, _) ->
                sb.AppendLine($"    jt {reg cond}, {lbl target}")

            | Instr(OpCode.Reserve, s, _, _, _) ->
                sb.AppendLine($"    reserve {s}")

            | Instr(OpCode.Ret, r, _, _, _) ->
                sb.AppendLine($"    ret {reg r}")

            | Instr(OpCode.Call, label, argsStart, argCount, dst) ->
                sb.AppendLine($"    {reg dst} = call {lbl label}({reg argsStart}..+{argCount})")

            | Instr(OpCode.Tailcall, label, argsStart, argCount, _) ->
                sb.AppendLine($"    tailcall {lbl label}({reg argsStart}..+{argCount})")

            | Instr(OpCode.Apply, fn, argsStart, argCount, dst) ->
                sb.AppendLine($"    {reg dst} = apply {reg fn}({reg argsStart}..+{argCount})")

            | Instr(OpCode.Mov, dst, src, _, _) ->
                sb.AppendLine($"    {reg dst} = mov {reg src}")

            | Instr(OpCode.LoadInt, dst, value, _, _) ->
                sb.AppendLine($"    {reg dst} = int {value}")

            | Instr(OpCode.LoadChar, dst, value, _, _) ->
                sb.AppendLine($"    {reg dst} = char '{char value}'")

            | Instr(OpCode.LoadFloat, dst, lo, hi, _) ->
                let bits = (int64 lo) ||| ((int64 hi) <<< 32)
                let value = System.BitConverter.Int64BitsToDouble(bits)
                sb.AppendLine($"    {reg dst} = float {value}")

            | Instr(OpCode.LoadString, dst, strId, _, _) ->
                let str = InternTable.StringTable.Get(strId)
                sb.AppendLine($"    {reg dst} = string \"{str}\"")

            | Instr(OpCode.LoadAtom, dst, atomId, _, _) ->
                let atom = InternTable.AtomTable.Get(atomId)
                sb.AppendLine($"    {reg dst} = atom :{atom}")

            | Instr(OpCode.Add, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = add {reg l}, {reg r}")

            | Instr(OpCode.Sub, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = sub {reg l}, {reg r}")

            | Instr(OpCode.Mul, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = mul {reg l}, {reg r}")

            | Instr(OpCode.Div, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = div {reg l}, {reg r}")

            | Instr(OpCode.Mod, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = mod {reg l}, {reg r}")

            | Instr(OpCode.Neg, dst, src, _, _) ->
                sb.AppendLine($"    {reg dst} = neg {reg src}")

            | Instr(OpCode.Equal, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = eq {reg l}, {reg r}")

            | Instr(OpCode.NotEqual, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = neq {reg l}, {reg r}")

            | Instr(OpCode.Leq, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = leq {reg l}, {reg r}")

            | Instr(OpCode.Le, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = le {reg l}, {reg r}")

            | Instr(OpCode.Geq, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = geq {reg l}, {reg r}")

            | Instr(OpCode.Ge, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = ge {reg l}, {reg r}")

            | Instr(OpCode.Not, dst, src, _, _) ->
                sb.AppendLine($"    {reg dst} = not {reg src}")

            | Instr(OpCode.StrCat, dst, l, r, _) ->
                sb.AppendLine($"    {reg dst} = strcat {reg l}, {reg r}")

            | Instr(OpCode.MkRecord, dst, count, fieldsStart, _) ->
                sb.AppendLine($"    {reg dst} = mkrecord({reg fieldsStart}..+{count})")

            | Instr(OpCode.ExtendRecord, dst, base', count, fieldsStart) ->
                sb.AppendLine($"    {reg dst} = extend {reg base'} with ({reg fieldsStart}..+{count})")

            | Instr(OpCode.GetField, dst, record, fieldId, failLabel) ->
                let field = InternTable.AtomTable.Get(fieldId)
                sb.AppendLine($"    {reg dst} = getfield {reg record}.{field} or {lbl failLabel}")

            | Instr(OpCode.Alloc, dst, tagId, count, childrenStart) ->
                let tag = InternTable.AtomTable.Get(tagId)
                sb.AppendLine($"    {reg dst} = alloc :{tag}({reg childrenStart}..+{count})")

            | Instr(OpCode.Closure, dst, label, count, capturesStart) ->
                sb.AppendLine($"    {reg dst} = closure {lbl label}[{reg capturesStart}..+{count}]")

            | Instr(OpCode.CallClosure, closure, argsStart, argCount, dst) ->
                sb.AppendLine($"    {reg dst} = callclosure {reg closure}({reg argsStart}..+{argCount})")

            | Instr(OpCode.GetUpvalue, dst, index, _, _) ->
                sb.AppendLine($"    {reg dst} = upvalue[{index}]")

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) when tagId = SYM_RECORD ->
                sb.AppendLine($"    testtype {reg term} is record or {lbl failLabel}")

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) ->
                let tag = InternTable.AtomTable.Get(tagId)
                sb.AppendLine($"    testtag {reg term} is {tag} or {lbl failLabel}")

            | Instr(OpCode.Deconstruct, dst, term, index, _) ->
                sb.AppendLine($"    {reg dst} = deconstruct {reg term}[{index}]")

            | Instr(OpCode.PPShow, dst, src, _, _) ->
                sb.AppendLine($"    {reg dst} = ppshow {reg src}")

            | Instr(OpCode.Print, r, _, _, _) ->
                sb.AppendLine($"    print {reg r}")

            | _ -> failwith "??"

            |> ignore

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

        for KeyValue((name, arity), label) in dispatchTable do
            let symId = intern_symbol(env, name)
            intern_function(env, symId, arity, label)

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

/// A ridiculous peephole optimizer for the bytecode.
[<RequireQualifiedAccess>]
module public Peephole =

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

            // --- Standard peephole optimisations --- //

            // MOV rX, rX -> /
            | Instr(OpCode.Mov, dst, src, _, _) :: rest
                when dst = src ->
                    loop rest

            // Mov rA, rB ; Ret rA -> Ret rB
            | Instr(OpCode.Ret, retReg, _, _, _) :: Instr(OpCode.Mov, dst, src, _, _) :: rest 
                when retReg = dst ->
                    loop (Instr(OpCode.Ret, src, 0, 0, 0) :: rest)

            | (Label _ as lbl) :: rest -> lbl :: loop rest
            | head :: rest -> head :: loop rest
            | [] -> []

        loop instrs

    /// Apply a (very) basic pass of peephole optimization onto the program.
    /// 
    /// This does not have a measurable impact on performance, but it slightly
    /// cleans up the generated bytecode and very slightly improves certain patterns.
    let public apply (cp: CompiledProgram) =
        { cp with
            Program =
                cp.Program
                |> List.ofArray
                |> List.rev
                |> peepholeReversePass
                |> List.rev
                |> Array.ofList }

[<RequireQualifiedAccess>]
module public AOT =
    open System.Globalization
    open System.Diagnostics
    open System.Text
    open System.IO
    open System.Reflection

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

    /// Produces an executable at the given path. This executable contains the whole runtime and
    /// the compiled bytecode. This executable is standalone but is _still_ a VM running bytecode.
    let public compile (cp: CompiledProgram) (fileName: string) =
        let embed = readEmbeddedResource "liyh.C.rcl.c"
        let sb = new StringBuilder();

        let inline appendLine s =
            sb.AppendLine($"    {s};")
            |> ignore

        for KeyValue((name, arity), label) in cp.DispatchTable do
            appendLine $"intern_function(env_ptr, intern_symbol(env_ptr, \"{name}\" ), {arity}, {label})"

        for instr in cp.Program do
            match instr with
            | Comment (comment, true) -> 
                appendLine $"\n// {comment} "

            | Comment (comment, false) ->
                appendLine $"// {comment} "

            | Label labelId ->  
                appendLine $"set_label(env_ptr, {labelId})"

            | Instr(OpCode.LoadFloat, dst, lo, hi, _) ->
                let bits = (int64 (uint32 lo)) ||| ((int64 hi) <<< 32)
                let value = BitConverter.Int64BitsToDouble(bits)
                appendLine $"emit_load_float(env_ptr, {dst}, {value.ToString(CultureInfo.InvariantCulture)})"

            | Instr(OpCode.LoadString, dst, strId, _, _) ->
                let str = InternTable.StringTable.Get(strId) |> escapeCString
                appendLine $"emit(env_ptr, {int OpCode.LoadString}, {dst}, intern_string(env_ptr, \"{str}\"), 0, 0)"

            | Instr(OpCode.LoadAtom, dst, atomId, _, _) ->
                let atom = InternTable.AtomTable.Get(atomId)
                appendLine $"emit(env_ptr, {int OpCode.LoadAtom}, {dst}, (int)intern_symbol(env_ptr, \"{atom}\"), 0, 0)"

            | Instr(OpCode.GetField, dst, record, fieldId, failLabel) ->
                let field = InternTable.AtomTable.Get(fieldId)
                appendLine $"emit(env_ptr, {int OpCode.GetField}, {dst}, {record}, (int)intern_symbol(env_ptr, \"{field}\"), {failLabel})"

            | Instr(OpCode.Alloc, dst, tagId, count, childrenStart) ->
                let tag = InternTable.AtomTable.Get(tagId)
                appendLine $"emit(env_ptr, {int OpCode.Alloc}, {dst}, (int)intern_symbol(env_ptr, \"{tag}\"), {count}, {childrenStart})"

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) when tagId = SYM_RECORD ->
                appendLine $"emit(env_ptr, {int OpCode.TestTag}, {term}, {SYM_RECORD}, {failLabel}, 0)"

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) ->
                let tag = InternTable.AtomTable.Get(tagId)
                appendLine $"emit(env_ptr, {int OpCode.TestTag}, {term}, (int)intern_symbol(env_ptr, \"{tag}\"), {failLabel}, 0)"

            | Instr(opcode, arg1, arg2, arg3, arg4) ->
                appendLine $"emit(env_ptr, {int opcode}, {arg1}, {arg2}, {arg3}, {arg4})"

        let result =
            embed
                .Replace($"<ENTRY-POINT>", string cp.EntryPointLabel)   // replaces the flag by the actual entry point
                .Replace($"<FILL-PROGRAM>", string sb)                  // replaces the flag by the actual bytecode

        let tempCFile = Path.GetTempFileName() + ".c"
        File.WriteAllText(tempCFile, result)

        let outputFile = Path.Combine(Directory.GetCurrentDirectory(), fileName)
        let compileArgs = $"-o {outputFile} {tempCFile} -lm -lgc -O3 -DEMBEDDED -march=native"

        //                                                //
        // For now, we suppose an UNIX/LINUX environment. //
        //                                                //

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

