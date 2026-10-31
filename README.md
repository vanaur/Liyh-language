<div align="center"><a href="">
    <img width="150" src="assets/logo.png">
</a>
    <h1>ＬＩＹＨ</h1>
</div>

<div align="center">
    Liyh is a modern, <b>statically typed</b>, <b>general-purpose</b> programming language rooted in a <b>rule-based symbolic term rewriting</b> paradigm, extended to support both <b>functional</b> and <b>imperative</b> styles. It features <b>one-shot algebraic effects</b> and offers a <b>flexible</b> and <b>light</b> syntax, thanks to indentation and mixfix operators.
</div>

<div align="center">
    <h4><a href="https://vanaur.github.io/Liyh-website/">Website</a> | <a href = "https://vanaur.github.io/Liyh-website/">Try it out</a></h4>
</div>

<div align="right">
    <sub>— Built with ❤︎ by <a href="https://github.com/vanaur">vanaur</a></sub>
</div>

## Description
Liyh is a programming language project exploring the paradigm based on symbolic [rewriting rules](https://en.wikipedia.org/wiki/Category:Term-rewriting_programming_languages). It is not new, but it is not popular either, and is often too specific, too academic, or not really explored in the context of general programming. The aim is to make it fun, practical and original to use.

```
use Liyh

greeting[name: String] ->
    "Oh, hello { name }! And welcome to Liyh!"

main[] ->
    using Terminal() handle
        let greet = greeting["awesome user"]
        println["Message: { greet }"]
```

More examples are available on the [website](https://vanaur.github.io/Liyh-website/).

### Rule-based?
Yes. In theory, rather than applying functions to arguments, evaluation involves rewriting terms: one searches the expression for a sub-term that matches a pattern, and replaces it with the corresponding term. This process continues until no further rules apply (when termination occurs) or continues ad infinitum.

This implies...
 - a declarative and equational programming style
 - a pattern matching oriented programming style
 - different rewriting strategies
 - purity, no need for global mutable states or references

In practice, the language is more concrete and pragmatic. At the end of the day, the aim is to enjoy using it!

### Symbolic?
Also, yes. According to our definition, this conveys the general idea that any symbol can exist without needing to be defined or represent a value in memory. You can think about [Mathematica](https://en.wikipedia.org/wiki/Wolfram_Mathematica), for example!

In practice, it is complicated with a global static type system, but preserved on a more local and defined scale.

</br>

> [!NOTE]
> Liyh was designed bottom-up: starting solely from a _symbolic term rewriting system_ to arrive at a feature-rich programming language, without breaking the foundations. This, we hope, makes Liyh consistent and harmonious.

### Language Features

 The language has [several features](https://vanaur.github.io/Liyh-website/), such as: 

- **Rule-based system** (priorities, strategies, and rewriting rules)
- **Advanced pattern matching** (non-linear, conditional, disjoint, and operator patterns)
- **Hybrid paradigm:** functional style by default, with local mutable state and loops
- **One-shot algebraic effects**
- **Static typing** with a compile-time unit of measure system
- **Symbolic terms** and substitution
- **Custom mixfix operators**
- **C Foreign Function Interface (FFI)**

> [!IMPORTANT]
> Not everything has been implemented yet!
> 
> The features designed for the language have been conceived to integrate seamlessly into it, but it is possible that we may have been mistaken about certain aspects of feasibility.
> 
> The project is still in its early stages and subject to changes and redesigns.

### Runtime
Liyh compiles to a specialised bytecode VM written in C. If you want to learn more about the current runtime, you can check out this [description](liyh/LyVM/README.md).

## Installing and using Liyh
You can refer to the instructions on the [website](https://vanaur.github.io/Liyh-website) or in [this Markdown file](Installation.md) to find out how to install Liyh. All dependencies are managed by the installer.

> [!IMPORTANT]
> The project cannot be used as it stands at present, as it is still in the development phase! There is no standard library and not all features have been implemented yet.

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

**Liyh** is licensed under the [Apache-2.0 License](LICENSE).

This project uses the following third-party libraries:

| Library | License | Description |
| :--- | :--- | :--- |
| [FParsec](https://github.com/stephan-tolksdorf/fparsec) | 2-clause BSD | A parser combinator library for F#. |
| [BenchShark](https://github.com/JamesMenetrey/BenchShark) | MIT | A lightweight library for benchmarking performance of your .NET applications. |
| [Argu](https://github.com/fsprojects/Argu) | MIT | A declarative CLI argument parser for F#. |
| [libffi](https://github.com/libffi/libffi) | MIT |  A portable foreign-function interface library. |

