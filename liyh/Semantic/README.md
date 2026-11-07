# Semantic

This folder implements the static type checking and type inference engine for the Liyh language.

It translates the raw Syntax Tree into an elaborated Typed Syntax Tree (TAST), resolving all identifiers and overloads for compilation to LiyhCore.

> [!IMPORTANT]
> Some of the language's announced features have not yet been implemented, or have not been fully implemented, in particular:
>  - Units systems
>  - Algebraic effects
>  - Contexts and symbolic contexts
>
> These features will be added later, but most of the other announced features have been implemented in the type checker.

## Description

The goal of the type system of Liyh is to make programming through rewriting just as natural as
if the type system did not exist, whilst protecting against type errors, semantic inconsistencies
and ambiguous overloading; it is flexible for the user, and errors are handled in such a way as to
be as clear as possible. It (normally) works using:

 1. Bidirectional Type Checking & Type Inference:
     - Combines Hindley–Milner inference with directional type checking (`infer*` and `check`),
       enabling inference for higher-order constructs, overloaded rules, application and lambda.
     - Rule-definition (LHS -> RHS) using pattern matching as LHS naturally implies bidirectional
       type checking and bindings with the RHS.
     - Chooses appropriate overloads based on context-dependent and context-independent partitioning.

 2. Backtracking:
     - Managed by `TypecheckContext`. Uses an undo stack for both type variables (`TypeVar`)
       and dimension variables (`DimVar`).
     - Provides primitives (`Attempt`, `Probe`, `Checkpoint`) to test candidate overloads, mixfix
       rewrites, and constructors before committing or backtracking the state and diagnostics.

 3. Unit of Measure:
     - Dimension arithmetic modeled over the field of rational numbers (ℚ).
     - Unification solves linear systems over dimension exponents and isolates free dimension variables.

 4. Row Polymorphism & Records:
     - Open record types with implicit row variables supporting record extensions,
       type-agnostic updates and row unifications via flattening (`flattenRecord`).

 5. Algebraic Effects:
     - Effect tracking carried on arrow (`TArrow(..., effects)`) as simple set of effects names.
     - Propagates latent effects and validates them against declared effect sets.

 6. Mutually Recursive Groups & Overloaded Rules and Constructors:
     - Partitioning rules by arity and compatible signatures (`partitionRules`).
     - Resolving SCC dependencies (via module `DependencyAnalysis`) in two passes:
        (a) Assign provisional monomorphic signatures and unify clause patterns.
        (b) Infer bodies under constrained parameters, followed by joint generalization, and computes definitive static specialization names (`RULE@[...]`).

 7. Mixfix Notations
     - Expands user-defined notation templates into expressions and patterns (`Mixfix` module).
     - Validates template consistency, preventing collisions, and enforcing commutativity constraints.

 8. Extended Semantics & Diagnostics:
     - Non-linear pattern matching with binding unification (`mergeBindings`).
     - Symbolic computing scopes (`TSymbolic`) with relaxed unification rules.
     - Resilient typing with error-recovery variables and Damerau–Levenshtein suggestions.

## Side notes & History
Prior to this type checker, the language was regarded as _"dynamically typed with a static type checker in sight"_. Several attempts at type systems and type checking were developed throughout the project, right from the very start. Each attempt was carried out in parallel to the rest of the project, and locally. It was notoriously difficult to reconcile the language's features and ambitions with a static type system, and certain ambitions had to be scaled back, particularly with regard to the symbolic framework. This new type checker is the result of lessons learnt from all the previous ones.

