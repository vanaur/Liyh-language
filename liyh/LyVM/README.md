# LyVM

LyVM is an attempt for a virtual machine for Liyh. The runtime and the library as such are known as "**RCL**" (Runtime Core Library). The RCL is written in C (see [rcl.c](/C/rcl.c)) and designed for ease of use for symbolic/rules-based/functionnal languages and also for good performances (to compensate for the slower nature of the paradigms mentioned).

> [!NOTE]
> Historically, RCL was another very old project (older than the idea of the Liyh language itself, you can see it [here](https://github.com/vanaur/RCL-C) but it is not compilable and not worth your time). It has been completely redesigned for this project. Originally, the RCL was designed to offer an attractive alternative to other existing runtimes and VMs, ticking the following three boxes:
> 
> - [x] expressive and capable
> - [x] easy to use
> - [x] deliver decent performances given the last two points
>
> These points remain unchanged, at least we hope so!

### Characteristics

 - The VM is register-based and does not have an explicit stack (or, similarly, a stack maps each register, but the stack is not accessible as such). The number of registers is arbitrary, fixed for each case by the compiler (using instruction `reverse`).
 - Integers (`int`) and characters (`char`) are unboxed (using pointer tagging). Integers are of 62 bits size because of pointer tagging.
 - Automatic Reference Counting (ARC), managed by the VM without the need for intervention from the user or the compiler.
 - Deep adaptive stack frame, up to 256 MB of stack frame allowed. This allows deep recursion and traverse of deep structures.
 - Tailcall optimisation via a `tailcall` instruction.
 - Abstract symbols/constructors (via `alloc` and `atom` instructions) for constructing symbolic data or functional data structures.
 - Structural symbolic substitution (via the `subst` instruction) to substitute symbols with expressions. No overflow will occurs.
 - Structural equality (with `eq` instruction) of values/symbolic data. No overflow will occurs.
 - Contiguous register calling convention (each call to a function label requires the arguments to be in the form of contiguous registers from the caller).
 - Support for floats (64 bits), closures, records, immuable strings (and string concatenation) and pattern matching.
 - Support for lazy evaluation (using the `delay` and `force` instructions) and [black-holes](https://downloads.haskell.org/~ghc/0.29/docs/users_guide/user_86.html) detection.
 - Quite small.

### Supported paradigms

The VM was designed with Liyh in mind, so it is naturally capable of supporting the imperative paradigm, the functional paradigm, and the symbolic paradigm.

At the moment, though, there is no support for concurrency.

### Performances

Given that the very nature of dynamic functional languages or symbolic term rewriting languages generally makes execution slower than more traditional languages, the VM was designed to compensate somewhat for this slowness in order to provide something useful for the host compiler and something fast for the execution engine.

A good compiler for this VM may produce bytecode that is roughly on par with what we would expect from Python or Lua in the few performance tests we have done. Our compiler is still non-optimising.

> [!IMPORTANT]
> Please note, however (if anyone happens to pass by and read this...), that this VM is just as young as the project itself; the goal is not to compete with established runtimes, but only to compensate for our own interpreter (what has already been  achieved) and offer something usable in practice.

### Using RCL elsewhere

The RCL has been written with Liyh in mind and the library is not documented and will change a lot. In the not-too-distant future, it is conceivable that RCL could be used by others.

### Example of compiled bytecode

The actual compiler compiles
```
main[] ->
    { 1 .. 1_000_000 }
    |> fold[['acc, 'a] -> 'acc + 'a, 0]

fold[{}, _, 'acc] -> 'acc
fold['x :: 'xs, 'f, 'acc] -> fold['xs, 'f, 'f['acc, 'x]]
```
into (without showing the generation of the list)
```
; --- plus/2 ---

.L1025:
    reserve 3
    r2 = add r0, r1
    ret r2

; --- main/0 ---

.L1018:
    reserve 10
    r0 = int 1
    r1 = alloc none(r0..+0)
    r2 = int 1000000
    r6 = call .L1026(r0..+3)
    r3 = mov r6
    jump .L1078

.L1077:
    reserve 4
    tailcall .L1025(r0..+2)
    ret r0

.L1078:
    r4 = closure .L1077[r0..+0]
    r5 = int 0
    r9 = call .L1010(r3..+3)
    r6 = mov r9
    print r6
    halt

; --- fold/3 ---

.L1010:
    reserve 14
    testtag r0 is cons or .L1063
    r4 = deconstruct r0[0]
    r5 = deconstruct r0[1]
    r6 = mov r2
    r7 = mov r4
    r8 = apply r1(r6..+2)
    r6 = mov r8
    r7 = mov r5
    r8 = mov r1
    r9 = mov r6
    tailcall .L1010(r7..+3)
    r3 = mov r0
    jump .L1062

.L1063:
    testtag r0 is nil or .L1064
    r3 = mov r2
    jump .L1062

.L1064:
    r13 = alloc fold(r0..+3)
    r10 = mov r13
    r3 = mov r10

.L1062:
    ret r3
```

and runs (on a i9-13900H) in an average between `90ms` to `195ms`.

### AOT compilation

The compiler can produce an executable embedding the virtual machine and the produced bytecode for fast startup and better ease of distribution. It does require a C compiler from the host system.

Technically, it is AOT (because it compiles the result into an executable), but the executable remains just a VM that executes bytecode.

