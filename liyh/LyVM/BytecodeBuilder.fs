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

    member private this.IsUnreachable() =
        if instructions.Count = 0 then false
        else
            match instructions.[instructions.Count - 1] with
            | Instr(OpCode.Ret, _, _, _, _)
            | Instr(OpCode.Halt, _, _, _, _)
            | Instr(OpCode.Tailcall, _, _, _, _) 
            | Instr(OpCode.Jump, _, _, _, _) -> true
            | _ -> false

    /// Checks whether a list of registers forms a contiguous block (rᵢ, rᵢ₊₁, ...).
    /// Returns the starting register if this is the case, otherwise None.
    member private __.TryGetContiguousBlock (regs: Reg list) =
        match regs with
        | [] -> Some (Reg 0)
        | (Reg first) :: tail ->
            let rec check current rest =
                match rest with
                | [] -> true
                | (Reg next) :: xs -> 
                    if next = current + 1 then check next xs
                    else false
            
            if check first tail then Some (Reg first)
            else None

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

    /// Compacts the stack by removing unused slots between block start and result, moving the
    /// result value down and updating stack top. This is mainly used at the end of blocks.
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

    member public __.Halt (returnValue: int) =
        instructions.Add(Instr(OpCode.Halt, returnValue, 0, 0, 0))

    member public this.Halt () =
        this.Halt(0)

    member public __.Jump (label: int) =
        instructions.Add(Instr(OpCode.Jump, label, 0, 0, 0))

    member public __.JumpFalse (Reg cond, label: int) =
        instructions.Add(Instr(OpCode.JumpFalse, cond, label, 0, 0))

    member public __.JumpTrue (Reg cond, label: int) =
        instructions.Add(Instr(OpCode.JumpTrue, cond, label, 0, 0))

    member public this.Ret (Reg r) =
        // Sometime, the compiler emit a `ret` instruction, but it is unreachable.
        if not (this.IsUnreachable()) then
            instructions.Add(Instr(OpCode.Ret, r, 0, 0, 0))

    member public __.Mov (Reg dst, Reg src) =
        instructions.Add(Instr(OpCode.Mov, dst, src, 0, 0))

    member public this.Call (label: int, args: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        // The VM needs the arguments to be continious, so we detect if the given registers
        // are already continious not the emit useless `mov` instructions.
        match this.TryGetContiguousBlock args with
        | Some (Reg startIdx) ->
            instructions.Add(Instr(OpCode.Call, label, startIdx, args.Length, dst.Index))
            dst

        | None ->
            let (blockStart, count) = this.PrepareBlock args
            let (Reg blockIdx) = blockStart

            instructions.Add(Instr(OpCode.Call, label, blockIdx, count, dst.Index))
            this.CompactStack(blockStart, count, dst)

    member public this.Tailcall (label: int, args: Reg list) =
        // The VM needs the arguments to be continious, so we detect if the given registers
        // are already continious not the emit useless `mov` instructions.
        match this.TryGetContiguousBlock args with
        | Some (Reg startIdx) ->
            instructions.Add(Instr(OpCode.Tailcall, label, startIdx, args.Length, 0))

        | None ->
            let (blockStart, count) = this.PrepareBlock args
            let (Reg blockIdx) = blockStart

            instructions.Add(Instr(OpCode.Tailcall, label, blockIdx, count, 0))

    member public this.Apply (Reg fnReg, args: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        // The VM needs the arguments to be continious, so we detect if the given registers
        // are already continious not the emit useless `mov` instructions.
        match this.TryGetContiguousBlock args with
        | Some (Reg startIdx) ->
            instructions.Add(Instr(OpCode.Apply, fnReg, startIdx, args.Length, dst.Index))
            dst

        | None ->
            let (blockStart, count) = this.PrepareBlock args
            let (Reg blockIdx) = blockStart

            instructions.Add(Instr(OpCode.Apply, fnReg, blockIdx, count, dst.Index))
            this.CompactStack(blockStart, count, dst)

    member public this.LoadInt (value: int, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.LoadInt, dst.Index, value, 0, 0))
        dst

    member public this.LoadChar (c: char, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.LoadChar, dst.Index, int c, 0, 0))
        dst

    member public this.LoadFloat (value: float, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let bits = BitConverter.DoubleToInt64Bits value

        instructions.Add(Instr(OpCode.LoadFloat, dst.Index, int bits, int (bits >>> 32), 0))
        dst

    member public this.LoadString (s: string, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let strId = InternTable.StringTable.Intern s

        instructions.Add(Instr(OpCode.LoadString, dst.Index, strId, 0, 0))
        dst

    member public this.LoadAtom (name: string, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let atomId = InternTable.AtomTable.Intern name

        instructions.Add(Instr(OpCode.LoadAtom, dst.Index, atomId, 0, 0))
        dst

    member public this.LoadBool (value: bool, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.LoadBool, dst.Index, (if value then 1 else 0), 0, 0))
        dst

    member public this.Cast (src: Reg, targetType: int, srcType: int, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.Cast, dst.Index, src.Index, targetType, srcType))
        dst

    /// Used when the end of a computation require a register but no value. This method allows to avoid
    /// allocating the symbol unit for nothing.
    member public this.Unit (?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let atomId = InternTable.AtomTable.Intern "unit" // A free (unallocated) `unit` would be required at the VM level...

        instructions.Add(Instr(OpCode.LoadAtom, dst.Index, atomId, 0, 0))
        dst

    member private this.BinOp (opcode: OpCode, Reg left, Reg right, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(opcode, dst.Index, left, right, 0))
        dst

    member private this.UnOp (opcode: OpCode, Reg src, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(opcode, dst.Index, src, 0, 0))
        dst

    member public this.Add (l, r, ?target: Reg) = this.BinOp(OpCode.Add, l, r, ?target = target)
    member public this.Sub (l, r, ?target: Reg) = this.BinOp(OpCode.Sub, l, r, ?target = target)
    member public this.Mul (l, r, ?target: Reg) = this.BinOp(OpCode.Mul, l, r, ?target = target)
    member public this.Div (l, r, ?target: Reg) = this.BinOp(OpCode.Div, l, r, ?target = target)
    member public this.Mod (l, r, ?target: Reg) = this.BinOp(OpCode.Mod, l, r, ?target = target)
    member public this.Neg (src, ?target: Reg) = this.UnOp(OpCode.Neg, src, ?target = target)

    member public this.Eq (l, r, ?target: Reg) = this.BinOp(OpCode.Equal, l, r, ?target = target)
    member public this.NotEqual (l, r, ?target: Reg) = this.BinOp(OpCode.NotEqual, l, r, ?target = target)
    member public this.Leq (l, r, ?target: Reg) = this.BinOp(OpCode.Leq, l, r, ?target = target)
    member public this.Le (l, r, ?target: Reg) = this.BinOp(OpCode.Le, l, r, ?target = target)
    member public this.Geq (l, r, ?target: Reg) = this.BinOp(OpCode.Geq, l, r, ?target = target)
    member public this.Ge (l, r, ?target: Reg) = this.BinOp(OpCode.Ge, l, r, ?target = target)
    member public this.Not (src, ?target: Reg) = this.UnOp(OpCode.Not, src, ?target = target)

    member public this.StrCat (l, r, ?target: Reg) =
        this.BinOp(OpCode.StrCat, l, r, ?target = target)

    member public this.MkRecord (fields: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let (blockStart, count) = this.PrepareBlock fields
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.MkRecord, dst.Index, count, blockIdx, 0))
        this.CompactStack(blockStart, count, dst)

    member public this.ExtendRecord (Reg baseReg, newFields: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let (blockStart, count) = this.PrepareBlock newFields
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.ExtendRecord, dst.Index, baseReg, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.GetField (Reg record, fieldName: string, failLabel: int, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        let fieldId = InternTable.AtomTable.Intern fieldName
        instructions.Add(Instr(OpCode.GetField, dst.Index, record, fieldId, failLabel))
        dst

    member public this.AllocData (tagName: string, children: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let (blockStart, count) = this.PrepareBlock children
        let (Reg blockIdx) = blockStart
        let tagId = InternTable.AtomTable.Intern tagName

        instructions.Add(Instr(OpCode.Alloc, dst.Index, tagId, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public __.Subst (dst: Reg, src: Reg, toRep: Reg, value: Reg) =
        instructions.Add(Instr(OpCode.Subst, dst.Index, src.Index, toRep.Index, value.Index))

    member public this.Closure (label: int, captures: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let (blockStart, count) = this.PrepareBlock captures
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.Closure, dst.Index, label, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.CallClosure (Reg closure, args: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let (blockStart, count) = this.PrepareBlock args
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.CallClosure, closure, blockIdx, count, dst.Index))
        this.CompactStack(blockStart, count, dst)

    member public this.GetUpvalue (index: int, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.GetUpvalue, dst.Index, index, 0, 0))
        dst

    /// Test tag for user defined symbols.
    member public __.TestTag (Reg term, tagName: string, failLabel: int) =
        let tagId = InternTable.AtomTable.Intern tagName
        instructions.Add(Instr(OpCode.TestTag, term, tagId, failLabel, 0))

    /// Test tag for system symbols.
    member public __.TestTag (Reg term, tagId: int, failLabel: int) =
        instructions.Add(Instr(OpCode.TestTag, term, tagId, failLabel, 0))

    member public __.TestRecord (Reg term, failLabel: int) =
        instructions.Add(Instr(OpCode.TestTag, term, SYM_RECORD_NATIVE, failLabel, 0))

    member public this.Delay (label: int, captures: Reg list, ?target: Reg) =
        let (blockStart, count) = this.PrepareBlock captures
        let dst = defaultArg target (this.Alloc())
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.Delay, dst.Index, label, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.Force (Reg thunkReg, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.Force, dst.Index, thunkReg, 0, 0))
        dst

    member public this.Deconstruct (Reg term, childIndex: int, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.Deconstruct, dst.Index, term, childIndex, 0))
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

    member public this.PPShow (Reg src, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())

        instructions.Add(Instr(OpCode.PPShow, dst.Index, src, 0, 0))
        dst

    member public this.CallFFI (ffiIndex: int, args: Reg list, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        let (blockStart, count) = this.PrepareBlock args
        let (Reg blockIdx) = blockStart

        instructions.Add(Instr(OpCode.CallFFI, dst.Index, ffiIndex, blockIdx, 0))
        this.CompactStack(blockStart, count, dst)

    member public this.BufferAlloc (sizeReg: Reg, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        instructions.Add(Instr(OpCode.BufferAlloc, dst.Index, sizeReg.Index, 0, 0))
        dst

    member public this.BufferGet (bufReg: Reg, indexReg: Reg, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        instructions.Add(Instr(OpCode.BufferGet, dst.Index, bufReg.Index, indexReg.Index, 0))
        dst

    member public this.BufferSet (bufReg: Reg, indexReg: Reg, valReg: Reg) =
        instructions.Add(Instr(OpCode.BufferSet, bufReg.Index, indexReg.Index, valReg.Index, 0))

    member public this.BufferRealloc (bufReg: Reg, newSizeReg: Reg) =
        instructions.Add(Instr(OpCode.BufferRealloc, bufReg.Index, newSizeReg.Index, 0, 0))

    member public this.BufferLength (bufReg: Reg, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        instructions.Add(Instr(OpCode.BufferLength, dst.Index, bufReg.Index, 0, 0))
        dst

    member public this.BufferToString (bufReg: Reg, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        instructions.Add(Instr(OpCode.BufferToString, dst.Index, bufReg.Index, 0, 0))
        dst

    member public this.StringToBuffer (bufReg: Reg, ?target: Reg) =
        let dst = defaultArg target (this.Alloc())
        instructions.Add(Instr(OpCode.StringToBuffer, dst.Index, bufReg.Index, 0, 0))
        dst

    /// A smol peephole optimizer for a very common pattern that arise in the compiler.
    member private __.OptimizePeephole() =
        let mutable i = 0
        while i < instructions.Count - 1 do
            match instructions.[i], instructions.[i + 1] with
            
            // Pattern: r_x = op(...); r_y = mov r_x  =>  r_y = op(...)
            | Instr(op, dst1, b, c, d), Instr(OpCode.Mov, dst2, src, _, _) 
                when dst1 = src && op <> OpCode.Mov ->
                instructions.[i] <- Instr(op, dst2, b, c, d)
                instructions.RemoveAt(i + 1)

            | _ -> i <- i + 1

    /// Generates F#-wise version of the final bytecode.
    member public this.Compile(entryLabel: int, dispatchTable: DispatchTable, ffiBindings: RCLFFIBinding[]) =
        //this.OptimizePeephole() // it doesn't work well (example of `integral[3 * cos[x]]`)

        { Program = instructions.ToArray()
          EntryPointLabel = entryLabel
          DispatchTable = dispatchTable
          FFIBinding = ffiBindings }

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

        | Instr(OpCode.Halt, r, _, _, _) ->
            $"    halt({r})"

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
            $"    {reg dst} = float {value.ToString(System.Globalization.CultureInfo.InvariantCulture)}"

        | Instr(OpCode.LoadString, dst, strId, _, _) ->
            let str = InternTable.StringTable.Get(strId)
            $"    {reg dst} = string \"{str}\""

        | Instr(OpCode.LoadAtom, dst, atomId, _, _) ->
            let atom = InternTable.AtomTable.Get(atomId)
            $"    {reg dst} = atom :{atom}"

        | Instr(OpCode.LoadBool, dst, value, _, _) ->
            let b = if value <> 0 then "true" else "false"
            $"    {reg dst} = bool {b}"

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

        | Instr(OpCode.Subst, dst, src, toRep, value) ->
            $"    {reg dst} = subst {reg src}({reg toRep} -> {reg value})"

        | Instr(OpCode.Closure, dst, label, count, capturesStart) ->
            $"    {reg dst} = closure {lbl label}[{reg capturesStart}..+{count}]"

        | Instr(OpCode.CallClosure, closure, argsStart, argCount, dst) ->
            $"    {reg dst} = callclosure {reg closure}({reg argsStart}..+{argCount})"

        | Instr(OpCode.GetUpvalue, dst, index, _, _) ->
            $"    {reg dst} = upvalue[{index}]"

        | Instr(OpCode.TestTag, term, tagId, failLabel, _) when tagId < 0 ->
            let tagName = 
                match tagId with
                | tagId when tagId = SYM_INT_NATIVE -> "INT"
                | tagId when tagId = SYM_FLOAT_NATIVE -> "FLOAT"
                | tagId when tagId = SYM_STRING_NATIVE -> "STRING"
                | tagId when tagId = SYM_RECORD_NATIVE -> "RECORD"
                | tagId when tagId = SYM_CHAR_NATIVE -> "CHAR"
                | tagId when tagId = SYM_BOOL_NATIVE -> "BOOL"
                | tagId when tagId = SYM_NUM_NATIVE -> "NUMERIC"
                | other -> failwithf "testtag with %A" other    // this may not happen

            $"    testtag {reg term} is {tagName} or {lbl failLabel}"

        | Instr(OpCode.TestTag, term, tagId, failLabel, _) ->
            let tag = InternTable.AtomTable.Get(tagId)
            $"    testtag {reg term} is atom :{tag} or {lbl failLabel}"

        | Instr(OpCode.Deconstruct, dst, term, index, _) ->
            $"    {reg dst} = deconstruct {reg term}[{index}]"

        | Instr(OpCode.Delay, dst, label, count, capturesStart) ->
            $"    {reg dst} = delay {lbl label}[{reg capturesStart}..+{count}]"

        | Instr(OpCode.Force, dst, src, _, _) ->
            $"    {reg dst} = force {reg src}"

        | Instr(OpCode.Cast, dst, src, targetType, srcType) ->
            let nativeTypeToString =
                function
                | n when n = BindingRCL.SYM_INT_NATIVE -> "Int"
                | n when n = BindingRCL.SYM_CHAR_NATIVE -> "Char"
                | n when n = BindingRCL.SYM_FLOAT_NATIVE -> "Float"
                | n when n = BindingRCL.SYM_STRING_NATIVE -> "String"
                | _ -> "??" // this may not happen

            let srcTypeStr = nativeTypeToString srcType
            let dstTypeStr = nativeTypeToString targetType

            $"    {reg dst} = cast {reg src} from {srcTypeStr} into {dstTypeStr}"

        | Instr(OpCode.CallFFI, dst, ffiIndex, argsStart, _) ->
            $"    {reg dst} = call_ffi [{ffiIndex}]({reg argsStart}..)"

        | Instr(OpCode.BufferAlloc, dst, sizeReg, _, _) ->
            $"    {reg dst} = buffer_alloc({reg sizeReg})"

        | Instr(OpCode.BufferGet, dst, bufReg, indexReg, _) ->
            $"    {reg dst} = buffer_get({reg bufReg}) at {reg indexReg}"

        | Instr(OpCode.BufferSet, bufReg, indexReg, valReg, _) ->
            $"    buffer {reg bufReg}[{reg indexReg}] = {reg valReg}"

        | Instr(OpCode.BufferRealloc, bufReg, newSizeReg, _, _) ->
            $"    buffer_realloc({reg bufReg}, {reg newSizeReg})"

        | Instr(OpCode.BufferLength, dstReg, bufReg, _, _) ->
            $"    {reg dstReg} = buffer_length({reg bufReg})"

        | Instr(OpCode.BufferToString, dstReg, bufReg, _, _) ->
            $"    {reg dstReg} = buffer_to_string({reg bufReg})"

        | Instr(OpCode.StringToBuffer, dstReg, bufReg, _, _) ->
            $"    {reg dstReg} = string_to_buffer({reg bufReg})"

        | Instr(OpCode.PPShow, dst, src, _, _) ->
            $"    {reg dst} = ppshow {reg src}"

        | Instr(OpCode.Print, r, _, _, _) ->
            $"    print {reg r}"

        | other -> $"TODO: {other}"

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
          DispatchTable = dispatchTable
          FFIBinding = ffiBinding } =

        entryPointLabel <- Some entryLabel

        // we have to internate some of the heap-allocated values

        for KeyValue(ruleInfo, label) in dispatchTable do
            let symId = intern_symbol(env, ruleInfo.Name)
            intern_function(env, symId, ruleInfo.Arity, label)

        for ffi in ffiBinding do
            let argTypesInt32 = Array.map RclType.RclTypeToInt32 ffi.ArgTypes
            let retTypeInt32 = RclType.RclTypeToInt32 ffi.RetType

            rcl_env_load_library(env, ffi.Library)
            rcl_env_register_ffi(env, ffi.QualifiedName, ffi.FunctionName, ffi.Arity, argTypesInt32, retTypeInt32)

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

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) when isSystemTag tagId ->
                emit (env, int OpCode.TestTag, term, tagId, failLabel, 0)

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) ->
                let tag = InternTable.AtomTable.Get(tagId)
                let sym = intern_symbol (env, tag)
                emit (env, int OpCode.TestTag, term, int sym, failLabel, 0)

            | Instr(opcode, arg1, arg2, arg3, arg4) ->
                emit (env, int opcode, arg1, arg2, arg3, arg4)

    /// Runs the program and returns the elapsed time in milliseconds.
    member public _.Run(programArgs: string list) =
        let vm = create_vm env
        gc_init()

        try
            match entryPointLabel with
            | None -> failwith "The program does not present any entry point"
            | Some entryLabel ->
                let argsArray = Array.ofList programArgs
                let argsTerm = rcl_make_string_list(vm, argsArray.Length, argsArray)
                let sw = Diagnostics.Stopwatch.StartNew()

                run_vm (vm, entryLabel, argsTerm)

                sw.Stop()
                sw.ElapsedMilliseconds

        finally
            destroy_vm vm

[<RequireQualifiedAccess>]
module public AOT =
    open Liyh.Utils.ErrorReporter
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

    let private tryFindExecutable (name: string) =
        if Path.IsPathRooted(name) then
            if File.Exists(name) then Some name else None
        else
            let envPath = Environment.GetEnvironmentVariable("PATH")
            let isWin = Environment.OSVersion.Platform = PlatformID.Win32NT
            let separator = if isWin then ";" else ":"

            let extensions =
                if isWin && String.IsNullOrEmpty(Path.GetExtension(name)) then
                    [| ""; ".exe"; ".cmd"; ".bat" |]
                else
                    [| "" |]

            if String.IsNullOrWhiteSpace(envPath) then
                None
            else
                envPath.Split(separator, StringSplitOptions.RemoveEmptyEntries)
                |> Seq.collect (fun dir ->
                    extensions |> Seq.map (fun ext ->
                        try Path.Combine(dir.Trim('"', ' '), name + ext)
                        with _ -> ""
                    )
                )
                |> Seq.tryFind File.Exists

    /// Produces an executable at the given path.
    /// This executable contains the whole runtime and the compiled bytecode embedded as static arrays.
    let public compile (cp: CompiledProgram) (fileName: string) (cc: string option) (optimize: bool) =
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
            | Instr(OpCode.TestTag, _, id, _, _) -> if id >= 0 && id > maxAtomId then maxAtomId <- id
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
        appendLine("    free(env_ptr->program);")
        appendLine("    env_ptr->program = (instr_t*)malloc(prog_size * sizeof(instr_t));")
        appendLine("    memcpy(env_ptr->program, static_program, sizeof(static_program));")
        appendLine("    env_ptr->program_size = prog_size;")
        appendLine("    env_ptr->program_capacity = prog_size;")

        // Load Labels
        appendLine("    size_t labels_count = sizeof(static_labels) / sizeof(int);")
        appendLine("    free(env_ptr->labels);")
        appendLine("    env_ptr->labels = (int*)malloc(labels_count * sizeof(int));")
        appendLine("    memcpy(env_ptr->labels, static_labels, sizeof(static_labels));")
        appendLine("    env_ptr->labels_capacity = labels_count;")

        // Init Dispatch Table
        appendLine("\n    // --- Dispatch Table ---")
        for KeyValue(ruleInfo, label) in cp.DispatchTable do
            let name = ruleInfo.Name
            let arity = ruleInfo.Arity
            appendLine($"    intern_function(env_ptr, intern_symbol(env_ptr, \"{name}\"), {arity}, {label});")

        // Init FFI
        appendLine("\n    // --- FFI Setup ---")
        for i = 0 to cp.FFIBinding.Length - 1 do
            let ffi = cp.FFIBinding.[i]
            let lib = escapeCString ffi.Library
            let qual = escapeCString ffi.QualifiedName
            let func = escapeCString ffi.FunctionName

            appendLine($"    rcl_env_load_library(env_ptr, \"{lib}\");")

            if ffi.Arity > 0 then
                let typesStr = ffi.ArgTypes |> Array.map (int >> string) |> String.concat ", "
                appendLine($"    enum rcl_type ffi_args_{i}[] = {{ {typesStr} }};")
                appendLine($"    rcl_env_register_ffi(env_ptr, \"{qual}\", \"{func}\", {ffi.Arity}, ffi_args_{i}, {int ffi.RetType});") 
            else
                appendLine($"    rcl_env_register_ffi(env_ptr, \"{qual}\", \"{func}\", 0, NULL, {int ffi.RetType});")

        // Note: maybe, for AOT compilation, launching the FFI can be avoided.


        // --- Final Assembly and Compilation --- //

        let embed = readEmbeddedResource "liyh.C.rcl.c"
        let result =
            embed
                .Replace("<ENTRY-POINT>", string cp.EntryPointLabel)
                .Replace("<FILL-PROGRAM>", sb.ToString())

        let tempCFile = Path.GetTempFileName() + ".c"
        File.WriteAllText(tempCFile, result)

        let baseDir = AppDomain.CurrentDomain.BaseDirectory
        let configPath = Path.Combine(baseDir, ".compiler_config")

        let mutable ccPath = Option.defaultValue "cc" cc
        let mutable ffiFlags = "-lffi"

        if File.Exists(configPath) then
            let config =
                File.ReadAllLines(configPath)
                |> Array.map _.Split([|'='|], 2)
                |> Array.filter (fun p -> p.Length = 2)
                |> Array.map (fun p -> (p.[0], p.[1]))
                |> Map.ofArray

            if config.ContainsKey("CC_PATH") && cc.IsNone then
                ccPath <- config.["CC_PATH"]
            
            if config.ContainsKey("FFI_INCLUDE_DIR") && config.ContainsKey("FFI_LIB_DIR") then
                let incDir = config.["FFI_INCLUDE_DIR"]
                let libDir = config.["FFI_LIB_DIR"]

                ffiFlags <- sprintf "-I\"%s\" -L\"%s\" -lffi" incDir libDir

        let outputFile = Path.Combine(Directory.GetCurrentDirectory(), fileName)
        let isWin = Environment.OSVersion.Platform = PlatformID.Win32NT

        let flags =
            [ if not isWin then "-lm"                           // Link math library (libm)
              ffiFlags                                          // Link libffi
              "-DEMBEDDED"                                      // Define EMBEDDED macro for standalone executable compilation

              if not optimize then "-g"                         // Activate debug information if not not optimize
              if not optimize
                 && not isWin then "-fsanitize=address"         // Activate asan if not optimize

              if optimize then "-O3"                            // Aggressive optimization
              if optimize then "-flto"                          // Link-time optimization (whole-program analysis)
              if optimize && not isWin then "-fno-plt"          // Avoid PLT indirection for shared libraries (faster calls)
              if optimize && not isWin then "-march=native" ]   // Optimize for the current CPU architecture

            |> String.concat " "

        let compileArgs =
            sprintf "-o \"%s\" \"%s\" %s" outputFile tempCFile flags

        match tryFindExecutable ccPath with
        | None ->
            if File.Exists(tempCFile) then File.Delete(tempCFile)
            
            let report =
                { ErrorType = Package
                  ErrorCode = null
                  EnclosingPosition = (None, None)
                  Description = sprintf "The specified C compiler (`%s`) was not found on the system." ccPath
                  AllLines = Seq.empty
                  Informations = List.empty
                  Hint = "Generally, the default option is preferable to a custom C compiler." }

            let errQ = ErrorQueue()
            errQ.AddError(report)
            errQ.ReportAll Console.Out true

            false

        | Some resolvedCcPath ->
            let processInfo = ProcessStartInfo(resolvedCcPath, compileArgs)

            processInfo.UseShellExecute <- false
            processInfo.RedirectStandardOutput <- true
            processInfo.RedirectStandardError <- true

            let compilationSucceeded =
                try
                    use proc = Process.Start(processInfo)
                    proc.OutputDataReceived.Add(fun _ -> ())
                    proc.ErrorDataReceived.Add(fun _ -> ())
                    proc.BeginOutputReadLine()
                    proc.BeginErrorReadLine()
                    proc.WaitForExit()
                    proc.ExitCode = 0
                with
                | _ -> false

            if not compilationSucceeded then
                let report =
                    { ErrorType = Package
                      ErrorCode = null
                      EnclosingPosition = (None, None)
                      Description = sprintf "The AOT compilation failed due to the external code-generation tool (`%s`)." ccPath
                      AllLines = Seq.empty
                      Informations = [ sprintf "It is likely that `%s` is not a valid C compiler." ccPath ]
                      Hint = null }

                let errQ = ErrorQueue()
                errQ.AddError(report)
                errQ.ReportAll Console.Out true

            File.Delete(tempCFile)
            compilationSucceeded

