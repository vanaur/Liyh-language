namespace rec Liyh.Core

//
// The 'core' (LiyhCore) is a minimalist version of the language used for
// execution, optimization, some analysis, and compilation.
//
// At this level, there is no real distinction between a "term" and
// a "pattern", the same structure is used for both.
//

[<CustomEquality; CustomComparison>]
type public CoreSymbol =
    internal
        { Symbol: string
          Children: CoreTerm list
          IsVariable: bool
          Hash: int }

    override this.GetHashCode() = this.Hash

    override this.Equals(other: obj) =
        match other with
        | :? CoreSymbol as otherSym ->
            if System.Object.ReferenceEquals(this, otherSym) then
                true
            else
                this.Hash = otherSym.Hash &&
                this.IsVariable = otherSym.IsVariable &&
                this.Symbol = otherSym.Symbol &&
                this.Children = otherSym.Children
        | _ -> false

    interface System.IEquatable<CoreSymbol> with
        member this.Equals(other) = this.Equals(other)

    interface System.IComparable with
        member this.CompareTo(other) =
            match other with
            | :? CoreSymbol as otherSym ->
                let c = compare this.Hash otherSym.Hash
                if c <> 0 then c
                else
                    let c = compare this.IsVariable otherSym.IsVariable
                    if c <> 0 then c
                    else
                        let c = compare this.Symbol otherSym.Symbol
                        if c <> 0 then c
                        else compare this.Children otherSym.Children
            | _ -> 1

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

    // --- symbolic features --- //

    | Substitution of CoreSubstitution
    | UsingContext of CoreUsingContext

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

and public CoreSubstitution =
    { Env: (CoreSymbol * CoreTerm) list
      InExpr: CoreTerm }

and public CoreUsingContext =
    { Context: string
      Expr: CoreTerm }

type public CoreDefinition =
    | Rule of CoreRule
    | Handler of CoreHandler
    | Extern of CoreExtern
    | Context of CoreContext

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

and public CoreExtern =
    { LibraryName: string
      Library: Liyh.FFI.CFFI.DynLib
      Functions: Map<string, Liyh.FFI.CFFI.FunctionSignature> }

and public CoreContext =
    { ContextName: string
      Content: CoreDefinition list
      Using: string list }

type public CoreProgram = CoreDefinition list

[<AutoOpen>]
module public SymbolHelper =

    let private computeSymbolHash (symbol: string) (isVariable: bool) (children: CoreTerm list) =
        let mutable hash = symbol.GetHashCode()
        hash <- System.HashCode.Combine(hash, (if isVariable then 1 else 0))

        for child in children do
            hash <- System.HashCode.Combine(hash, child.GetHashCode())

        if hash = 0 then 1 else hash

    let public symbol (name: string) (args: CoreTerm list) =
        Symbol
            { Symbol = name
              Children = args
              IsVariable = false
              Hash = computeSymbolHash name false args }

    let public variableSymbol (name: string) (args: CoreTerm list) =
        Symbol
            { Symbol = name
              Children = args
              IsVariable = true
              Hash = computeSymbolHash name true args }

    let public copySymbolWithNewChildren (symb: CoreSymbol) (children: CoreTerm list) =
        Symbol 
            { symb with 
                Children = children
                Hash = computeSymbolHash symb.Symbol symb.IsVariable children }

    let public simpleSymbol (name: string) =
        symbol name []

