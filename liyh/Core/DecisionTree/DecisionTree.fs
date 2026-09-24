namespace Liyh.Core.DecisionTree

open Liyh.Core

/// Describes how to reach a sub-value inside the scrutinee of a pattern match,
/// as a sequence of steps starting from the root.
type public Path =

    /// The `position`-th positional argument of the constructor/symbol found at the `parent` path.
    | Child of parent: Path * position: int

    /// The record field named `name` of the given value found at the `parent` path.
    | Field of parent: Path * name: string

    /// The head symbol of the value found at the `parentè path.
    | Tag of parent: Path

    /// The scrutinee itself: the starting point of evry path.
    | Root

    /// Returns the path to the child at position `index` of this path.
    member public this.Extend(index: int) =
        Child(this, index)

    /// Returns the path to the record field `field` of this path.
    member public this.Access(field: string) =
        Field(this, field)

    override this.ToString() =
        let rec build path acc =
            match path with
            | Root -> if List.isEmpty acc then "." else String.concat "" acc
            | Child(parent, idx) -> build parent (sprintf "[%d]" idx :: acc)
            | Field(parent, name) -> build parent (sprintf ".%s" name :: acc)
            | Tag parent -> build parent (sprintf ":" :: acc)
        build this []

/// The decision tree used to compile pattern matching.
type public DecisionTree =

    /// Tests the constructor/symbol (tag and arity) of the value found at `_path`,
    /// then continues with the subtree matching that constructor/symbol.
    /// Falls back to `_default` when no case matches.
    | Switch of
        _path: Path *
        _cases: Map<string * int, DecisionTree> *
        _default: DecisionTree option

    /// Tests the value found at `_path` against a set of literal constants,
    /// then continues with the matching subtree.
    /// Falls back to `_default` when no literal matches.
    | SwitchLiteral of
        _path: Path *
        _cases: Map<CoreLiteral, DecisionTree> *
        _default: DecisionTree option

    /// Checks that the value found at `_path` is a record (e.g. that the
    /// expected fields are present), then continues with `_success`.
    /// Falls back to `_default` if the check fails.
    | RecordCheck of
        _path: Path *
        _success: DecisionTree *
        _default: DecisionTree option

    /// Evaluates the guard expression `_guard` (a `when`-clause) with the
    /// variables given in `bindings`. Continues with `_success` if it
    /// evaluates to true, otherwise with `_failure` if any.
    | WhenGuard of
        _guard: CoreTerm *
        _bindings: Map<string, Path> *
        _success: DecisionTree *
        _failure: DecisionTree option

    /// Terminal node: the match succeeded and the rule at `_ruleIndex` is
    /// selected. `_bindings` maps each pattern variable to the path of the
    /// sub-value it captures, for use in the rule's body.
    | Leaf of
        _ruleIndex: int *
        _bindings: Map<string, Path>

    /// Terminal node: no rules matches, i.e. the match is non-exhaustive
    /// along this branch.
    | Fail

