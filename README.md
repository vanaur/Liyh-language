<div align="center"><a href="">
    <img width="150" src="assets/logo.png">
</a>
    <h1>ＬＩＹＨ</h1>
</div>

<div align="center">
    Liyh is a modern, <b>statically typed</b>, <b>general-purpose</b> programming language rooted in a <b>rule-based symbolic term rewriting</b> paradigm, extended to support both <b>functional</b> and <b>imperative</b> styles. It features <b>one-shot algebraic effects</b> and offers a <b>flexible</b> and <b>light</b> syntax, thanks to indentation and mixfix operators.
</div>

<div align="center">
    <h4><a href="TODO">Website</a> | <a href = "TODO">Try it out</a></h4>
</div>

<div align="right">
    <sub>— Built with ❤︎ by <a href="https://github.com/vanaur">vanaur</a></sub>
</div>

## Description
Liyh is a programming language project exploring the paradigm based on symbolic rewriting rules. It is not new, but it is not popular either, and is often too specific, too academic, or not really explored in the context of general programming. The aim is to make it fun, practical and original to use.

It is worth noting that Liyh was not designed "top-down" but "bottom-up": starting solely from a "symbolic term rewriting system" to arrive at a feature-rich programming language, without breaking the foundations. This, we hope, makes Liyh consistent and "harmonious".

### Key features
The language has several features, but the most interesting ones are probably...

 - **Rule-based:** your programme defines a system of rewriting rules (with priorities, strategies and fancy syntax);
 - **Powerful pattern matching:** beyond the usual pattern matching, you can use non-linear patterns, conditional patterns, operator patterns, disjoint patterns, symbol patterns, etc.
 - **Functional:** the declarative style lends itself well to functional programming, notably there are no references, everything is immutable by default, recursion is idiomatic, and there are closures and first-class functions. There is no support for currying.
 - **Imperative:** it would be foolish to do without loops and local, not shared mutable variables in order to be a "purist"; loops and mutable variables are useful, so they have been added.
 - **One-shot algebraic effects:** control flow is extended with one-shot algebraic effects, in a relatively original and practical form. Side effects are encapsulated under algebraic effects.
 - **Statically typed:** your programme will be statically checked for type consistency; rules are also typed and offer ad-hoc and parametric polymorphism.
 - **Measure's unit system:** you can write a programme that manipulates values with units of measurement; Liyh guarantees their consistency at compile-time and their conversion at runtime. You can define your own systems.
 - **Symbolic-wise:** it is not possible to combine "static typing" and "abstract/undefined symbols", but it is possible to frame pure symbolic behaviour to achieve a programme that is ultimately statically typed and flexible. We invented what we call "symbolic effects" to address this problem.
 - **Mixfix operators:** the language supports the definition of mixfix operators. You can define fancy notations!
 - **Simple Foreign Function Interface:** Liyh provides a simple-to-use (unidirectional) FFI for C, supporting the basic literal types, pointers, structures, and arrays.

One thing that was very important to us during the design process was consistency: we want a consistent language, not just a collection of cool features. We hope that this desire is reflected in the final product.

### Hello, world!
Visit the website for a more interesting overview of the language, but in the meantime, here is an example of program:

```
use Liyh

greeting[name] ->
    "Oh, hello {name}! And welcome to Liyh!"

main[] ->
    using Terminal() handle
        let greet = greeting["awesome user"]
        println["Message: {greet}"]
```

This example illustrates the use of algebraic effects to display information on the screen, as well as the syntax of the language and the definition of two rules, `greeting` and `main`.

## Every contribution is worthwhile 💪
The project is in the development and reflexion phase, so many things are

- subject to change
- not yet implemented
- may be more effectively implemented

Don't hesitate to make your contribution to the project. Even the smallest report of spelling mistakes will be appreciated. If you have any other suggestions for the project, we will be happy to hear from you.

Furthermore, the greatest contribution you can make to the project is to use it. If you would like to share what you have done with Liyh, please do not hesitate to let us know.

## Credits & acknowledgements
Persons:

 - [Mesa le bg 🐱](https://github.com/Mesabloo) for his ideas, valuable advice, encouragement and presence.
 - My cat 🐈 for his purrs and his sweet little face. So cute!

# License 📜

**Liyh** is licensed under [Apache-2.0 License](/LICENSE) but uses the following third-party libraries:

 - [FParsec](https://github.com/stephan-tolksdorf/fparsec) — A parser combinator library for F#.
 - [BenchShark](https://github.com/JamesMenetrey/BenchShark) —  A lightweight library for benchmarking performance of your .NET applications.
 - [bdwgc](https://github.com/bdwgc/bdwgc) —  The Boehm-Demers-Weiser conservative C/C++ Garbage Collector (bdwgc, also known as bdw-gc, boehm-gc, libgc).
