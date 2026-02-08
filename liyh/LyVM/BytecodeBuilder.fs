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
        instructions.Add(Instr(OpCode.Halt, returnValue, 0, 0, 0));

    member public this.Halt () =
        this.Halt(0);

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

    member public this.Call (label: int, args: Reg list) =
        // The VM needs the arguments to be continious, so we detect if the given registers
        // are already continious not the emit useless `mov` instructions.
        match this.TryGetContiguousBlock args with
        | Some (Reg startIdx) ->
            let dst = this.Alloc()
            let (Reg dstIdx) = dst

            instructions.Add(Instr(OpCode.Call, label, startIdx, args.Length, dstIdx))
            dst

        | None ->
            let (blockStart, count) = this.PrepareBlock args
            let dst = this.Alloc()
            let (Reg blockIdx) = blockStart
            let (Reg dstIdx) = dst

            instructions.Add(Instr(OpCode.Call, label, blockIdx, count, dstIdx))
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

    member public this.Apply (Reg fnReg, args: Reg list) =
        // The VM needs the arguments to be continious, so we detect if the given registers
        // are already continious not the emit useless `mov` instructions.
        match this.TryGetContiguousBlock args with
        | Some (Reg startIdx) ->
            let dst = this.Alloc()
            let (Reg dstIdx) = dst

            instructions.Add(Instr(OpCode.Apply, fnReg, startIdx, args.Length, dstIdx))
            dst

        | None ->
            let (blockStart, count) = this.PrepareBlock args
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

    member public this.Cast (src: Reg, targetType: int, srcType: int) =
        let dst = this.Alloc()

        instructions.Add(Instr(OpCode.Cast, dst.Index, src.Index, targetType, srcType))
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

    member public __.Subst (dst: Reg, src: Reg, toRep: Reg, value: Reg) =
        instructions.Add(Instr(OpCode.Subst, dst.Index, src.Index, toRep.Index, value.Index))

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

    /// Test tag for user defined symbols.
    member public __.TestTag (Reg term, tagName: string, failLabel: int) =
        let tagId = InternTable.AtomTable.Intern tagName
        instructions.Add(Instr(OpCode.TestTag, term, tagId, failLabel, 0))

    /// Test tag for system symbols.
    member public __.TestTag (Reg term, tagId: int, failLabel: int) =
        instructions.Add(Instr(OpCode.TestTag, term, tagId, failLabel, 0))

    member public __.TestRecord (Reg term, failLabel: int) =
        instructions.Add(Instr(OpCode.TestTag, term, SYM_RECORD_NATIVE, failLabel, 0))

    member public this.Delay (label: int, captures: Reg list) =
        let (blockStart, count) = this.PrepareBlock captures
        let dst = this.Alloc()

        let (Reg blockIdx) = blockStart
        let (Reg dstIdx) = dst

        instructions.Add(Instr(OpCode.Delay, dstIdx, label, count, blockIdx))
        this.CompactStack(blockStart, count, dst)

    member public this.Force (Reg thunkReg) =
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
    member public this.Compile(entryLabel: int, dispatchTable: DispatchTable) =
        this.OptimizePeephole() // this is cheap

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

            | Instr(OpCode.TestTag, term, tagId, failLabel, _) when isSystemTag tagId ->
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

