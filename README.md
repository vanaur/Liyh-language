<div align="center"><a href="">
    <img width="150" src="assets/logo.png">
</a>
    <h1>ＬＩＹＨ</h1>
</div>

<center>
    <i>Liyh</i> is a modern, statically typed, general-purpose programming language based on the symbolic rewriting paradigm but extended to support a functional and imperative style, featuring one-shot algebraic effects as well as a flexible syntax thanks to indentation and mixfix operators.
</center>

# Description & features

> [!NOTE]
> All information can be found [on the project website](/TODO)!

<br/>

Liyh is a quite flexible language. Its core is based on [term rewriting](https://en.wikipedia.org/wiki/Rewriting#Term_rewriting_systems) and abstract, undefined symbols are first class citizen. For a language to be useful, it may be extended with a pleasant syntax and some more features. This is what was done with Liyh, featuring overall

 - rules and term rewriting as the execution strategy and main paradigm
 - `innermost` ("strict") and `outermost` ("lazy") evaluation
 - closures / lambda functions and functional application
 - `let`-expressions and mutables (but not shared) variables
 - powerful pattern matching (via `match`, `let` and equational style function definition), including
   - non-linear patterns
   - `as` patterns
   - conditional patterns
   - types as patterns
   - custom notation as patterns
   - alternative patterns
   - pattern matching on almost every expressions the language provide
   - pattern matching on functions (and their parameters)
 - mixfix operators (called `notation`) with explicit definition, precedence and associativity
 - loops (`for` and `while`)
 - list and list comprehensions
 - one-shot algebraic effect & handlers
 - Static type-checking and strongly typed, with
   - compile-time type checking
   - type inference (and optional type annotations)
   - ad-hoc and parametric polymorphism
   - algebraic data types
   - row-polymorphic records
 - indentation sensitive syntax
 - simple module system (one file = one module, private members by default)
 - frontend implementation efforts
   - efforts to ensure that the compiler returns meaningful error messages
   - incremental and parallel compilation between files (still to be done, but the foundation has been laid)
   - small, readable code base

as well as other details...

In short, Liyh is designed as a modern general-purpose language built around a lightweight and consistent core. All features, with a few exceptions, flow naturally from the basic paradigm and are simply made more accessible through the language.

The language is inspired by F#, Python, Mathematica, Erlang, Haskell and others. The language is intended to be very accessible to anyone, but no less capable, allowing it to be adapted to the preferred or appropriate style.

To learn more, visit [the website](/TODO)! 🧙

# Basic examples

> [!NOTE]
> So that you are not too confused by the notations, here are the basic rules:
> - `'a` designates a variable binding for pattern matching.
> - `foo[x₁, x₂, ..., xₙ]` is is basically a function call.
> - `bar[x₁, x₂, ..., xₙ] -> ...` define a function/rule.
>
> Everything else should be understandable!

<details><summary><b>Hello, world</b></summary>

```
use Liyh

main[] ->
    using terminal() handle
        println["Hello, world!"]
```

This example use algebraic effect to print something to the terminal. All effects are handled by algebraic effects & handlers, up to some debugging-purpose native functions. That's why this "hello, world" can seem cumbersome. The language provides access to native IO functions for debugging, without having to go through algebraic effects, in order to have a quick way to test things:

 - `log['x]` : displays a language element on the screen; it is equivalent to `printfn "%A" x` in F# for example.
 - `bench['action, 'n]` : performs a benchmark `'n` times of the application of `'action` (which must be a closure) and returns a record `{ result = ..., time = ... }`.

</details>

<details><summary><b>Symbolic Peano arithmetic</b></summary>

```
use Liyh

peano_add[zero, 'n] -> 'n
peano_add[succ['n], 'm] -> succ[peano_add['n, 'm]]

to_int[zero] -> 0
to_int[succ['n]] -> 1 + to_int['n]

main[] ->
    let n1 = succ[succ[succ[zero]]]
    let n2 = succ[zero]
    let n3 = to_int[peano_add[n1, n2]]

    using terminal() handle
        println["{n1} + {n2} = {n3}"]
```

This example illustrate the symbolic term rewriting process in action by defining the _rules_ `peano_add` and `to_int` up to some patterns. Note that _no_ definition of the symbols have to be provided, only the relation between them is relevant.

</details>

<details><summary><b>Counter algebraic effect</b></summary>

```
use Liyh

my_counter('state)[increment] -> () with 'state + 1
my_counter('state)[get_count] -> 'state

main[] ->
    let initial_count = 28

    using my_counter(initial_count) handle
        increment[]
        increment[]
        let result = get_count[]

        using terminal() handle
            println["The counter gives {result}!"]
```

... and this would display `"The counter gives 30!"`. This example shows how to define handlers for the _de facto_ effects `increment` and `get_count` that manage a counter, nammed `state` in each handler. The continuation, often

Continuation, which is usually manipulated directly in effect languages, is implicit here, and handlers are just an extension of basic rewriting rules. Note that this can be achieved because Liyh's algebraic effects are _one-shot_, meaning that continuation can only be launched once at most. This has advantages and limitations.

</details>

<details><summary><b>Some pattern matching</b></summary>

```
eq['a, 'a] -> true
eq[_, _] -> false

fib[(0 | 1) as 'n] -> 'n
fib['n] -> fib['n - 1] + fib['n - 2]

incr['n] -> 'n + 1
decr['n] -> 'n - 1
incr[decr['n]] outermost -> 'n
decr[incr['n]] outermost -> 'n

length[{}] -> 0
length[_ :: 'xs] -> 1 + length['xs]

animal_name[simba] -> lion
animal_name[nemo] -> fish
animal_name[dumbo] -> elephant
```

This example illustrate some pattern-matching capabilities of the language. Note that each function is defined as a rule that must match a pattern.

</details>

<details><summary><b>State effect & handlers</b></summary>

```
use Liyh

my_state('state)[puts['new_state]] -> () with 'new_state
my_state('state)[get] -> 'state

update_with['n] when 'n % 2 == 0 -> puts['n :: get]
update_with[_] -> ()

main[] ->
    using my_state({}) handle
        for k = 0 to 20 do
            update_with[k]
        
        using terminal() handle
            let result = get[]
            println["Result: {result}"]
```

... and this would display `{ 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20 }`. This illustrate that, within an handled environment, we can call functions that use effects (regardless of the handler) and that effects are composable: we use `puts`, `get`, and `println` in a layered manner.

</details>

<details><summary><b>Mixfix notations</b></summary>


```
use Liyh

notation |'x| -> abs['x]
    name: "absolute-value"
    associativity: none
    precedence: 10

notation <'x|'y> -> braket['x, 'y]
    name: "bra-ket"
    associativity: none
    precedence: 10

notation schedule 'what inviting 'who at 'time near 'place -> schedule['what, 'who, 'time, 'place]
    name: "scheduling"
    associativity: none
    precedence: 8

notation 't pm -> hour['t, pm]
    name: "pm-hour"
    associativity: none
    precedence: 12

main[] ->
    let example1 = <17|21>
    let example2 = |3 - 7|
    let example3 = schedule dinner inviting Alice at 18pm near fountain
```

This example illustrates some definitions of notations, or so-called "mixfix" operators. In particular, we see that the definition consists of alternating variables and fixed parts, which allows us to define useful notations, such as the absolute value, specific to the domain, such as the Dirac Bra-Ket notation, or more natural ones such as the scheduling.

Note also, once again, that undefined symbols are first-class values, which is why we can write "`schedule dinner inviting Alice at 18pm near fountain`" where `dinner`, `Alice`, `18pm` and `fountain` are symbols but not part of the notation.

It should be noted that notations are _not_ macros.

</details>

## Every contribution is worthwhile 💪
The project is in the development and reflexion phase, so many things are

- subject to change
- not yet implemented
- may be more effectively implemented

Don't hesitate to make your contribution to the project. Even the smallest report of spelling mistakes will be appreciated. If you have any other suggestions for the project, we will be happy to hear from you.

## Credits & acknowledgements
Persons:

 - [Mesa le bg 🐱](https://github.com/Mesabloo) for his ideas, valuable advice, encouragement and presence.
 - My cat 🐈 for his purrs and his sweet little face. So cute!

# License 📜

**Liyh** is licensed under [Apache-2.0 License](/LICENSE) but uses the following third-party libraries:

 - [FParsec](https://github.com/stephan-tolksdorf/fparsec) — A parser combinator library for F#.
 - [BenchShark](https://github.com/JamesMenetrey/BenchShark) —  A lightweight library for benchmarking performance of your .NET applications.

