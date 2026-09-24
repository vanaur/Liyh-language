#nowarn "25"
namespace Liyh.TypeCheck

module rec TypeCheck =
    open Liyh.Utils.ErrorReporter
    open Liyh.Syntax.SyntaxTree

    [<RequireQualifiedAccess>]
    module private ErrorCodes =

        // E-XYZ
        // E=ERROR, X=COMPILER-CURRENT-PASS, YZ=ERROR-CODE
        // TypeCheck : pass 3

        type public ErrorCode =

            /// A rule was invoked, but it is explicitly invalid given the arguments provided.
            | MatchedInvalidRuleError = 1

            /// Too many constraints and not enough values: need help from the user with a type annotation.
            | NeedTypeAnnotationError = 2

            /// Invalid type unification.
            | TypeMismatchError = 3

            /// Invalid alternative pattern (unexpected type).
            | BadAlternativeTypeError = 4

            /// Two rules have the same pattern and are indistinguishable.
            | RedundantRuleError = 5

            /// A rule can never be achieved due to the associated previous definitions.
            | UnreachableRuleError = 6

            /// Variable (constant or mutable) does not exist in the current scope.
            | UnfoundVariableError = 7

            /// Variable applied to one or more arguments, but the type of the variable is not a function.
            | NotApplicableVariableError = 8

            /// An intermediate expression in an expression block is not of type Unit.
            | BadIntermediateExpressionSequenceTypeError = 9

            /// A value is reassigned to a variable marked as immutable.
            | ImmutableVariableMutationError = 10

            /// The return type of a while loop is non-Unit.
            | LoopReturnTypeError = 11

            /// A variable in a nonlinear pattern has a different type from its first instance.
            | IncompatibleNonLinearVariablesError = 12

            /// The collection has not the required dimension.
            | InvalidRankCollectionAccess = 13

            /// An external variable is mutated inside a lambda expression.
            | ReadOnlyLambdaError = 14

        let inline public format (code: ErrorCode) =
            sprintf "E3%02d" (int code)

    let public run (modules: Liyh.Module.ModuleInfo list) (errorQueue: ErrorQueue) =
        failwith "todo"

