namespace Liyh.Syntax

/// Concrete Syntax Tree (including positions and no sugar) of the language.
module SyntaxTree =
    open FParsec

    type public Associativity = FParsec.Associativity

    type public MixfixPatternPart =
        | Fixed of string
        | Hole

    type public MixfixPattern = MixfixPatternPart list

    /// Wraps a given type (expected: an AST) with its starting and ending positions.
    type public WithPos<'t> =
        { Node: 't
          StartPos: Position
          EndPos: Position }

        member public this.Line = this.StartPos.Line
        member public this.Col = this.StartPos.Column
        member public this.File = this.StartPos.StreamName
        member public this.PosTuple = (this.StartPos, this.EndPos)

    and public MixfixOperator =
        { Name: NameWithPos
          Pattern: MixfixPattern
          BindingPatterns: NotationPattern list
          Precedence: uint
          Associativity: Associativity
          IsCommutative: bool // default: false
          RewritesTo: ExpressionWithPos }

    and public NameWithPos = string WithPos
    and public IdentifierWithPos = Identifier WithPos
    and public ExpressionWithPos = Expression WithPos
    and public PatternWithPos = Pattern WithPos
    and public TypeWithPos = Type WithPos
    and public LiteralWithPos = Literal WithPos
    and public TopLevelWithPos = TopLevel WithPos

    and public Identifier =
        { Qualifier: NameWithPos list
          Name: NameWithPos }

        override this.ToString() =
            let qualifiers = this.Qualifier |> List.map _.Node
            String.concat "." (qualifiers @ [ this.Name.Node ])

    and public Expression =
        | ParseError of Liyh.Utils.ErrorReporter.ErrorReport   // To be able to accumulate parsing errors and continue
                                                               // parsing, so as not to stop at the first error encountered.
        | UFCS of UFCS
        | Identifier of IdentifierWithPos
        | BindingVariable of string
        | CollectionAccess of CollectionAccess
        | Literal of LiteralWithPos
        | ExpressionSequence of ExpressionWithPos list
        | Apply of Apply
        | MixfixOperator of ApplyOperator
        | Tuple of ExpressionWithPos list
        | List of ExpressionWithPos list
        | Record of (NameWithPos * ExpressionWithPos) list
        | RecordUsing of (ExpressionWithPos * (NameWithPos * ExpressionWithPos) list)
        | ListComprehension of ListComprehension
        | Range of Range
        | While of While
        | ForIn of ForIn
        | ForTo of ForTo
        | ForDownTo of ForTo
        | ReAssign of NameWithPos * ExpressionWithPos
        | Let of PatternWithPos * ExpressionWithPos
        | Var of PatternWithPos * ExpressionWithPos
        | Match of Match
        | IfThenElse of IfThenElse
        | Lambda of Lambda
        | HandleEffect of Handle
        | ResumeWith of ResumeWith
        | Substitution of (NameWithPos * ExpressionWithPos) list * ExpressionWithPos
        | UsingContext of UsingContext

    and public UsingContext =
        { ContextName: IdentifierWithPos
          ContentExpr: ExpressionWithPos }

    and public UFCS =
        { LHS: ExpressionWithPos
          RHS: ExpressionWithPos }

    and public CollectionAccess =
        { LHS: ExpressionWithPos
          Indices: ExpressionWithPos list }

    and public Apply =
        { LHS: ExpressionWithPos
          Arguments: ExpressionWithPos list }

    and public ApplyOperator =
        { Name: NameWithPos
          Arguments: ExpressionWithPos list }

    and public ListComprehension =
        { ItemValue: ExpressionWithPos
          Pattern: PatternWithPos
          ListExpr: ExpressionWithPos
          IfPred: ExpressionWithPos option }

    and public Range =
        { RangeStart: ExpressionWithPos
          RangeStep: ExpressionWithPos option
          RangeStop: ExpressionWithPos }

    and public While =
        { Predicate: ExpressionWithPos
          Body: ExpressionWithPos }

    and public ForIn =
        { Pattern: PatternWithPos
          ListExpr: ExpressionWithPos
          Body: ExpressionWithPos }

    and public Match =
        { ToMatch: ExpressionWithPos
          Cases: (PatternWithPos * ExpressionWithPos) list }

    and public IfThenElse =
        { Condition: ExpressionWithPos
          ThenBranch: ExpressionWithPos
          ElifBranches: (ExpressionWithPos * ExpressionWithPos) list
          ElseBranch: ExpressionWithPos option }

    and public ForTo =
        { Pattern: PatternWithPos
          InitialValue: ExpressionWithPos
          EndValue: ExpressionWithPos
          Body: ExpressionWithPos }

    and public Lambda =
        { Patterns: PatternWithPos list
          Body: ExpressionWithPos }

    and public Handle =
        { Handler: IdentifierWithPos
          InitialState: ExpressionWithPos
          Body: ExpressionWithPos }

    and public Pattern =
        | VariablePattern of string                                 // e.g. 'z
        | SymbolPattern of Identifier                               // e.g. none
        | ApplyPattern of PatternWithPos * PatternWithPos list      // e.g. succ[zero]
        | LiteralPattern of LiteralWithPos                          // e.g. 8
        | TuplePattern of PatternWithPos list                       // e.g. (1, 2, 3)
        | ListPattern of PatternWithPos list                        // e.g. { 1, 2, 3 }
        | RecordPattern of (NameWithPos * PatternWithPos) list      // e.g. { result = some['result], opt = 'x }
        | MixfixOperatorPattern of string WithPos * PatternWithPos list     // e.g. 'x :: 'xs, 'x + 10
        | AsPattern of PatternWithPos * PatternWithPos              // e.g. succ['n] as num
        | WhenPattern of PatternWithPos * ExpressionWithPos         // e.g. 'x when 'x > 0
        | TypedPattern of PatternWithPos * TypeWithPos              // e.g. 'n : Int
        | AlternativePattern of LiteralWithPos list                 // e.g. 1 | 2 | 3 | 4       -- TODO: extend to SymbolPattern too?
        | Wildcard                                                  // _

    and public Type =
        | NamedType of IdentifierWithPos                             // e.g. Int, Bool, String
        | VariableType of string                                     // e.g. 't
        | RuleType of TypeWithPos list * TypeWithPos                 // e.g. [Int, Int] -> Int
        | TupleType of TypeWithPos list                              // e.g. (Int, String, Bool)
        | RowRecordType of (NameWithPos * TypeWithPos) list          // e.g. { a: Int, b: Int, ... }
        | ParametrizedType of IdentifierWithPos * TypeWithPos list   // e.g. List['t]
        | ModuloEffectType of TypeWithPos * IdentifierWithPos list   // e.g. Int % { State, Counter }
        | WildcardType

    and public Literal =
        | Unit                                          // ()
        | Integer of int64                              // e.g. 42
        | Float of double                               // e.g. 9.81
        | String of string                              // e.g. "mesabloo"
        | InterpolatedString of InterpolatedPart list   // e.g. "hello {name}, you are {date - birth} years old!"
        | Char of char                                  // e.g. 'c'

    and public InterpolatedPart =
        | Str of string WithPos
        | Interpolation of ExpressionWithPos

    and public TopLevel =
        | ParseError of Liyh.Utils.ErrorReporter.ErrorReport   // To be able to accumulate parsing errors and continue
                                                               // parsing, so as not to stop at the first error encountered
        | Use of Use
        | Rule of Rule
        | LetRule of Rule       // a rule with no pattern is sugared into a `let`-like expression
        | Handler of Handler
        | Effect of NameWithPos * vartypes: NameWithPos list * (Signature WithPos) list
        | Type of SumType
        | TypeAlias of name: NameWithPos * vartypes: NameWithPos list * TypeWithPos
        | Notation of Notation
        | Context of Context
        | Extern of Extern
        | Measure
        | Unit
        | UnitSystem
        | UnitConversion
        | ModuleExport of NameWithPos list

    and public Context =
        { Name: NameWithPos
          Using: IdentifierWithPos list
          Content: TopLevelWithPos list } // NOTE: not all top levels are valids, but we can detect this after parsing

    and public Extern =
        { Language: ExternLanguageTarget
          Library: string WithPos
          AsName: IdentifierWithPos
          Content: (Signature WithPos) list }

    and public ExternLanguageTarget =
        | C     // there is just C for now and maybe forever

    and public SumType =
        { Name: NameWithPos
          VarTypes: NameWithPos list
          Constructors: (Signature WithPos) list }

    and public Handler =
        { Name: NameWithPos
          State: PatternWithPos
          Pattern: PatternWithPos
          WhenClause: ExpressionWithPos option
          Type: TypeWithPos option
          Strategy: RewritingStrategy WithPos option
          Body: ExpressionWithPos }

    and public Rule =
        { Name: NameWithPos
          Patterns: PatternWithPos list
          WhenClause: ExpressionWithPos option
          Type: TypeWithPos option
          Strategy: RewritingStrategy WithPos option
          Body: ExpressionWithPos }

    and public Notation =
        { NotationName: NameWithPos
          NotationPattern: NotationPattern list WithPos
          NotationPrecedence: uint WithPos
          NotationAssociativity: Associativity WithPos
          NotationCommutative: bool WithPos
          NotationIs: ExpressionWithPos }

    and public NotationPattern =
        | FixedPart of string WithPos
        | HolePart of string WithPos

        member public this.toMixFixPattern =
            match this with
            | FixedPart { Node = s } -> Fixed s
            | HolePart _ -> Hole

    and public ResumeWith =
        { Value: ExpressionWithPos
          HandlerState: ExpressionWithPos }

    and public Signature =
        { Name: NameWithPos
          ArgumentsType: TypeWithPos list
          ReturnType: TypeWithPos option }

    and public Use =
        { Lib: IdentifierWithPos
          Qualifier: NameWithPos option }

        override this.ToString() =
            string this.Lib.Node

    and public RewritingStrategy =
        /// Applies the rewrite rules starting with the deepest sub-expressions (leaves) before moving
        /// up towards the root of the syntax tree.
        | Strict

        /// Applies the rewriting rules without evaluating the arguments until they are needed.
        | Lazy

        /// Applies the rewriting rules starting from the root of the syntax tree before moving down
        /// to deeper sub-expressions.
        | Outermost

        /// No rewriting is possible; this is an exceptional case (compile time or runtime).
        | Invalid

        /// Cache results for future uses.
        //| Memoize

    and public Module =
        { ModuleDescription: string option
          ModuleContent: TopLevelWithPos list }

    module public NodeInfo =
        open System.Collections.Concurrent
        open System.IO

        let private cache = ConcurrentDictionary<string, string seq>()

        /// Gets the lines of the given string.
        let public getLines (source: string) : string seq =
            cache.GetOrAdd(source, fun s ->
                use reader = new StringReader(s)
                let lines = ResizeArray()
                let mutable line = reader.ReadLine()

                while not (isNull line) do
                    lines.Add line
                    line <- reader.ReadLine()

                lines |> seq
            )

    /// Wraps the given parser result in the `WithPos` type.
    let inline public parseWithPos (p: Parser<'a, 'u>) : Parser<WithPos<'a>, 'u> =
        pipe3 getPosition p getPosition (fun startPos node endPos ->
            { StartPos = startPos; Node = node; EndPos = endPos })

    /// Wraps a node with the position of another position-wrapped node.
    let inline public withPosOf (b: WithPos<'a>) (a: 'b) : WithPos<'b> =
        { Node = a; StartPos = b.StartPos; EndPos = b.EndPos }

    /// Gets the node without the position.
    let inline public removePos { Node = node } =
        node

    /// Converts the parser's defined notation into the mixfix representaztion.
    let public notationPatternToMixfixOperator (notation: Notation) =
        { Name = notation.NotationName
          Pattern = removePos notation.NotationPattern |> List.map _.toMixFixPattern
          BindingPatterns = removePos notation.NotationPattern
          Precedence = removePos notation.NotationPrecedence
          Associativity = removePos notation.NotationAssociativity
          IsCommutative = removePos notation.NotationCommutative
          RewritesTo = notation.NotationIs }

