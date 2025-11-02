namespace Liyh.Execution.Core

//
// The 'core' (LiyhCore) is a minimalist version of the language used for
// execution, optimization, some analysis, and compilation.
//
// At this level, there is no real distinction between a "term" and
// a "pattern", the same structure is used for both.
//

type public CoreTerm =

    // --- basic terms --- //

    | Symbol of CoreSymbol
    | Variable of string
    | Literal of CoreLiteral
    | RecordExtend of CoreRecordExtend
    | Match of CoreTermMatch

    // --- functional features --- //

    | Closure of Closure
    | FunctionalApplication of FunctionalApplication

    // --- imperative features --- //

    | TermSequence of CoreTerm list
    | CoreLet of CoreLet
    | WhileLoop of CoreWhile
    | UpdateVariable of string * CoreTerm

    // --- effect system --- //

    | Resume of CoreResume
    | Handle of CoreHandle

    // --- pattern matching specific --- //

    | WhenClause of CoreTerm * CoreTerm
    | AsClause of CoreTerm * CoreTerm
    | Wildcard

and public CoreSymbol =
    { Symbol: string
      Children: CoreTerm list
      IsVariable: bool }

and public CoreLiteral =
    | Integer of bigint
    | Float of double
    | String of string
    | Char of char

and public CoreRecordExtend =
    { BaseRecord: CoreTerm option
      Extension: (string * CoreTerm) list }

and public CoreTermMatch =
    { ToMatch: CoreTerm
      Cases: (CoreTerm * CoreTerm) list }

and public Closure =
    { Env: Map<string, CoreTerm>
      IsEvaluated: bool
      Parameters: string list
      Value: CoreTerm }

and public FunctionalApplication =
    { Base: CoreTerm
      Arguments: CoreTerm list }

and public CoreLet =
    { Pattern: CoreTerm
      Value: CoreTerm
      IsVariable: bool }

and public CoreWhile =
    { Predicate: CoreTerm
      Body: CoreTerm }

and public CoreResume =
    { Rewrite: CoreTerm
      State: CoreTerm
      FromHandler: string }

and public CoreHandle =
    { Handler: string
      State: CoreTerm
      ToHandle: CoreTerm }

type public CoreDefinition =
    | Rule of CoreRule
    | Handler of CoreHandler

and public CoreRule =
    { LHS: CoreTerm
      RHS: CoreTerm
      WhenClause: CoreTerm option
      Strategy: Liyh.Syntax.SyntaxTree.RewritingStrategy }

and public CoreHandler =
    { HandlerName: string
      LHS: CoreTerm
      RHS: CoreTerm
      State: CoreTerm
      WhenClause: CoreTerm option
      Strategy: Liyh.Syntax.SyntaxTree.RewritingStrategy }

type public CoreProgram = CoreDefinition list

