namespace Liyh.Semantic

/// Typed Syntax Tree (TAST): the output of the type checker and the input of the Core compiler.
///
/// Unlike the syntax tree, this tree is *elaborated*:
///   - every expression and pattern carries its (metavariable-free) `LiyhType`;
///   - identifiers are resolved to symbols (`ResolvedIdent`);
///   - whatever the checker decided (e.g. the function behind a UFCS call) is stored in the tree, so that
///     the Core compiler never has to redo any resolution or inference;
///   - syntactic types are replaced by semantic ones (`LiyhType`);
///   - `ParseError` and any error found while checking become `TError` nodes, so that the tree stays
///     complete (and usable by the LSP) even on invalid programs.
///
/// The tree intentionally stays close to the AST (no desugaring): that is the job of the Core
/// compiler, which has all the type information at hand. Effects are expected to be part of `LiyhType`.

module TypedSyntaxTree =
    open FParsec
    open Liyh.Syntax.SyntaxTree

    /// A position range in a source file.
    type public Span =
        { Start: Position
          End: Position }

        static member Empty =
            { Start = Position("synth", 0L, 1L, 1L)
              End = Position("synth", 0L, 1L, 1L) }

    /// Unique identifier of a symbol (a variable, a constructor, a rule, a type...), allocated by the resolver.
    [<Struct>]
    type public SymbolId = SymbolId of int

    [<RequireQualifiedAccess>]
    type public SymbolKind =
        | LocalVariable
        | RuleReference of mangledName: string
        | Constructor of typeName: string
        | ExternFunction of library: string
        | PureSymbol

    /// A reference to a symbol, as resolved by the checker.
    /// 
    /// Each identifier records where it was written, which unique symbol (`SymbolId`) was assigned to it,
    /// and where its original definition is located.
    /// 
    /// An unresolvable reference is reported as an error and replaced by a `TError`/`TPatError` node, so a
    /// `ResolvedIdent` always points to an actual symbol.
    type public ResolvedIdent =
        { Symbol: SymbolId

          Kind: SymbolKind

          /// The identifier exactly as written in the source (qualifiers included), for diagnostics and renaming.
          Written: Identifier

          /// Where the symbol is defined (go-to-definition); `None` for built-in or synthesized symbols.
          DefinedAt: Span option }

    [<RequireQualifiedAccess>]
    type public ForDirection =
        | Upwards   // `for x = a to b`
        | Downwards // `for x = a downto b`

    [<RequireQualifiedAccess>]
    type public Mutability =
        | Immutable // `let`
        | Mutable   // `var`


    //                                  //
    // --- Expressions and patterns --- //
    //                                  //


    /// Wraps a node of the typed tree with its type and its location.
    /// (`Kind`, `Ty` and `Span` are named so as not to collide with `WithPos.Node` or with `Type` in `Rule`/`Handler`.)
    type public TTyped<'n> =
        { Kind: 'n
          Type: LiyhType
          Span: Span }

    and public TExpression = TTyped<TExpressionNode>
    and public TPattern = TTyped<TPatternNode>
    and public TLiteral = TTyped<TLiteralNode>

    /// An association between a name written in the source and a value: a record field, a record update or
    /// a substitution. The name keeps its position for hovering and renaming.
    and public TBinding<'v> =
        { BindingName: NameWithPos
          BindingValue: 'v }

    and [<RequireQualifiedAccess>] public TLiteralNode =
        | TLitUnit
        | TLitInteger of int64
        | TLitFloat of double
        | TLitString of string
        | TLitChar of char

    and [<RequireQualifiedAccess>] public TInterpolatedPart =
        | TStringPart of string WithPos
        | TInterpolation of TExpression

    and [<RequireQualifiedAccess>] public TExpressionNode =
        | TError of Liyh.Utils.ErrorReporter.ErrorReport
        | TUFCS of TUFCS
        | TIdentifier of ResolvedIdent
        | TCollectionAccess of TCollectionAccess
        | TLit of TLiteralNode
        | TInterpolatedString of TInterpolatedPart list
        | TSequence of TExpression list
        | TApply of TApply
        | TMixfixOperator of TMixfixOperator
        | TTuple of TExpression list
        | TList of TExpression list
        | TRecord of TBinding<TExpression> list
        | TRecordUsing of TRecordUsing
        | TListComprehension of TListComprehension
        | TRange of TRange
        | TWhile of TWhile
        | TForIn of TForIn
        | TForTo of TForTo
        | TReAssign of TReAssign
        | TLet of TLet
        | TMatch of TMatch
        | TIfThenElse of TIfThenElse
        | TLambda of TLambda
        | TSubstitution of TSubstitution

    and public TUFCS =
        { UfcsReceiver: TExpression
          UfcsCall: TApply }

    and public TCollectionAccess =
        { AccessTarget: TExpression
          AccessIndices: TExpression list }

    and public TApply =
        { ApplyCallee: TExpression
          ApplyArguments: TExpression list }

    and public TMixfixOperator =
        { MixfixSymbol: ResolvedIdent
          MixfixOperands: TExpression list
          MixfixExpanded: TExpression }

    and public TRecordUsing =
        { RecordBase: TExpression
          RecordUpdates: TBinding<TExpression> list }

    and public TListComprehension =
        { CompItem: TExpression
          CompPattern: TPattern
          CompSource: TExpression
          CompFilter: TExpression option }

    and public TRange =
        { RangeFrom: TExpression
          RangeBy: TExpression option
          RangeTo: TExpression }

    and public TWhile =
        { WhileCondition: TExpression
          WhileBody: TExpression }

    and public TForIn =
        { ForInPattern: TPattern
          ForInSource: TExpression
          ForInBody: TExpression }

    and public TForTo =
        { ForToPattern: TPattern
          ForToInitial: TExpression
          ForToLimit: TExpression
          ForToDirection: ForDirection
          ForToBody: TExpression }

    and public TReAssign =
        { ReAssignTarget: ResolvedIdent
          ReAssignValue: TExpression }

    and public TLet =
        { LetPattern: TPattern
          LetValue: TExpression
          LetMutability: Mutability }

    and public TMatch =
        { MatchScrutinee: TExpression
          MatchCases: TMatchCase list }

    and public TMatchCase =
        { CasePattern: TPattern
          CaseBody: TExpression }

    and public TIfThenElse =
        { IfCondition: TExpression
          IfThen: TExpression
          IfElifs: TElifBranch list
          IfElse: TExpression option }

    and public TElifBranch =
        { ElifCondition: TExpression
          ElifBody: TExpression }

    and public TLambda =
        { LambdaParameters: TPattern list
          LambdaBody: TExpression }

    and public TSubstitution =
        { SubstReplacements: TBinding<TExpression> list
          SubstTarget: TExpression }

    and [<RequireQualifiedAccess>] public TPatternNode =
        | TPatError of Liyh.Utils.ErrorReporter.ErrorReport
        | TPatVariable of ResolvedIdent      // introduces a binding, e.g. `'x`
        | TPatConstructor of ResolvedIdent   // refers to an existing constructor, e.g. `none`
        | TPatApply of TPatApply
        | TPatLiteral of TLiteralNode
        | TPatTuple of TPattern list
        | TPatList of TPattern list
        | TPatRecord of TBinding<TPattern> list
        | TPatMixfix of TPatMixfix
        | TPatAs of TPatAs
        | TPatWhen of TPatWhen
        | TPatTyped of TPatTyped
        | TPatAlternative of TLiteral list
        | TPatWildcard

    and public TPatApply =
        { PatApplyHead: TPattern
          PatApplyArguments: TPattern list }

    and public TPatMixfix =
        { PatMixfixSymbol: ResolvedIdent
          PatMixfixOperands: TPattern list
          PatMixfixExpanded: TPattern }

    and public TPatAs =
        { PatAsBase: TPattern
          PatAsAlias: TPattern }

    and public TPatWhen =
        { PatWhenBase: TPattern
          PatWhenGuard: TExpression }

    and public TPatTyped =
        { PatTypedInner: TPattern
          PatTypedAnnotation: LiyhType
          PatTypedAnnotationSpan: Span }


    //                                //
    // --- Top-level declarations --- //
    //                                //


    /// Declarations have no type of their own (the types live inside them), hence `WithPos` and not `TTyped`.
    and public TTopLevel = WithPos<TTopLevelNode>
    and public TSignatureWithPos = WithPos<TSignature>

    and [<RequireQualifiedAccess>] public TTopLevelNode =
        | TTopLevelError of Liyh.Utils.ErrorReporter.ErrorReport
        | TUse of Use
        | TRuleDef of TRule
        | TLetRuleDef of TRule
        | TTypeDef of TSumType
        | TTypeAliasDef of TTypeAlias
        | TNotationDef of Notation
        | TExternDef of TExtern
        | TModuleExport of ResolvedIdent list

    and public TRule =
        { RuleSymbol: ResolvedIdent
          RulePatterns: TPattern list
          RuleWhen: TExpression option
          RuleType: LiyhType
          RuleStrategy: RewritingStrategy WithPos option
          RuleBody: TExpression }

    and public TSignature =
        { SigSymbol: ResolvedIdent
          SigArguments: LiyhType list
          SigReturn: LiyhType option }

    and public TSumType =
        { SumSymbol: ResolvedIdent
          SumTypeVars: NameWithPos list
          SumConstructors: TSignatureWithPos list }

    and public TTypeAlias =
        { AliasSymbol: ResolvedIdent
          AliasTypeVars: NameWithPos list
          AliasTarget: LiyhType }

    and public TExtern =
        { ExternLanguage: ExternLanguageTarget
          ExternLibrary: string WithPos
          ExternSymbol: ResolvedIdent
          ExternSignatures: TSignatureWithPos list }

    and public TModule =
        { Description: string option
          Declarations: TTopLevel list }


    //                 //
    // --- Helpers --- //
    //                 //


    /// Gets the span of a position-wrapped syntax node.
    let inline public spanOf (node: WithPos<'a>) : Span =
        { Start = node.StartPos; End = node.EndPos }

    /// The smallest span covering both `first` (which must start first) and `last`.
    let inline public spanBetween (first: Span) (last: Span) : Span =
        { Start = first.Start; End = last.End }

    /// Builds a typed node.
    let inline public mkTyped (ty: LiyhType) (span: Span) (kind: 'n) : TTyped<'n> =
        { Kind = kind; Type = ty; Span = span }

