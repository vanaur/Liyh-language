namespace Liyh.Semantic

[<AutoOpen>]
module public ErrorCodes =

    // E-XYZ / W-XYZ
    // E=ERROR, W=WARNING, X=COMPILER-CURRENT-PASS, YZ=DIAGNOSTIC-CODE
    // TypeCheck : pass 3

    type public ErrorCode =

        /// Type mismatch or unification failure between two types.
        | TypeMismatchError = 0

        /// An identifier, variable, or constructor was not found in the current scope.
        | UnboundIdentifierError = 1

        /// A type identifier is not defined.
        | UnknownTypeError = 2

        /// A function, constructor pattern, or rule clause was given an unexpected number of arguments.
        | ArityMismatchError = 3

        /// A type constructor was applied to an unexpected number of type arguments.
        | TypeArityMismatchError = 4

        /// No overload of a rule matches the provided argument types or expected type.
        | NoMatchingOverloadError = 5

        /// An overloaded rule was referenced as a first-class value without an explicit type annotation.
        | AmbiguousOverloadError = 6

        /// An expression was invoked as a function, but its type is not callable.
        | NonCallableExpressionError = 7

        /// A non-linear pattern contains multiple occurrences of a variable with conflicting types.
        | IncompatibleNonLinearVariablesError = 8

        /// An invalid or unsupported construct was used in pattern matching.
        | InvalidPatternError = 9

        /// A record operation (such as 'using') was attempted on a non-record type.
        | NonRecordTypeError = 10

        /// Attempted reassignment of an immutable variable.
        | ImmutableVariableMutationError = 11

        /// Attempted reassignment of a variable defined outside the current lambda closure.
        | CapturedVariableMutationError = 12

        /// The right-hand side of a UFCS method call does not evaluate to an application.
        | InvalidMethodCallError = 13

        /// Multiple clauses of a rule have overlapping argument patterns with incompatible return types.
        | ConflictingRuleReturnTypesError = 14

        /// An effect identifier is not defined in the environment.
        | UnknownEffectError = 15

        /// An effect annotation was applied to a non-function type.
        | InvalidEffectAnnotationError = 16

        /// A rule body produces effects that are not declared in its signature.
        | UnhandledEffectError = 17

        /// A top-level declaration (type, alias, notation) shares a name with an existing declaration.
        | DuplicateDeclarationError = 18

        /// Multiple top-level type declaration share the same name.
        | DuplicateTypeDeclarationError = 18

        /// A type or type alias declaration contains duplicate type parameter names.
        | DuplicateTypeParameterError = 19

        /// A type variable in a type alias definition is not bound in its parameter list.
        | UnboundTypeVariableError = 20

        /// A type alias directly or indirectly expands to itself.
        | CyclicTypeAliasError = 21

        /// A notation definition is invalid or a notation hole clashes with a rewrite target rule.
        | InvalidNotationError = 22

        /// Indexing was attempted on a non-collection or unconstrained type.
        | NonIndexableTypeError = 23

        /// A type is not a valid native C type in an FFI boundary.
        | InvalidFfiTypeError = 24

        /// A record's value has duplicate fields in its definition.
        | DuplicateRecordFields = 25

        /// A module's exported symbol contains private types.
        | PublicExposedSymbolLeak = 26

    type public WarningCode =

        /// Compatible Liyh type used where a native C FFI type is preferred for consistency.
        | FfiTypeConsistencyWarning = 0

        /// Pointless let-binding in expression tail whose bound variable immediately goes out of scope.
        | PointlessBindingWarning = 1

        /// Non-unit expression in a sequence whose result is discarded without being used or ignored.
        | UnusedResultWarning = 2

        /// A rule pattern matches a reducible rule or higher-order variable under default innermost rewriting.
        | NonOutermostPatternWarning = 3

        /// An outermost rule group lacks a non-outermost fallback clause.
        | MissingFallbackClauseWarning = 4

        /// A `var`-clause defining a binding that has not been reassigned.
        | MutableBindingUnmodified = 5

        /// A variable was declared but its value is never read.
        | UnusedVariable = 6

    let inline public format (code: ErrorCode) =
        sprintf "E3%02d" (int code)

    let inline public formatWarning (code: WarningCode) =
        sprintf "W3%02d" (int code)

