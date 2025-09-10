namespace Liyh.Syntax

/// Concrete Syntax Tree (including positions and no sugar) of the language.
module SyntaxTree =
    open FParsec

    type public Associativity = FParsec.Associativity
    type public MixfixPatternPart = Fixed of string | Hole
    type public MixfixPattern = MixfixPatternPart list

    type public MixfixOperator =
        { Name: string
          Pattern: MixfixPattern
          Precedence: uint
          Associativity: Associativity }

    type public WithPos<'t> =
        { Node: 't
          Pos: Position     // starting position
          Pos': Position }  // ending position

        member public this.Line = this.Pos.Line
        member public this.Col = this.Pos.Column
        member public this.File = this.Pos.StreamName
        member public this.PosTuple = (this.Pos, this.Pos')

    and public IdentifierWithPos = Identifier WithPos
    and public ExpressionWithPos = Expression WithPos
    and public PatternWithPos = Pattern WithPos
    and public TypeWithPos = Type WithPos
    and public LiteralWithPos = Literal WithPos
    and public TopLevelWithPos = TopLevel WithPos

    and public Identifier =
        { Qualifier: string WithPos list
          Name: string WithPos }

        override this.ToString() =
            let qualifiers = this.Qualifier |> List.map _.Node
            String.concat "." (qualifiers @ [ this.Name.Node ])

    and public Expression =
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
        | Record of (string * ExpressionWithPos) list
        | RecordUsing of (ExpressionWithPos * (string * ExpressionWithPos) list)
        | ListComprehension of ListComprehension
        | Range of Range
        | While of While
        | ForIn of ForIn
        | ForTo of ForTo
        | ForDownTo of ForTo
        | ReAssign of string * ExpressionWithPos
        | Let of PatternWithPos * ExpressionWithPos
        | Var of PatternWithPos * ExpressionWithPos
        | Match of Match
        | Lambda of Lambda
        | HandleEffect of Handle
        | ResumeWith of ResumeWith WithPos

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
        { Name: string
          Arguments: ExpressionWithPos list }

    and public ListComprehension =
        { ItemValue: ExpressionWithPos
          Pattern: string
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
        | RecordPattern of (string * PatternWithPos) list           // e.g. { result = some['result], opt = 'x }
        | MixfixOperatorPattern of string * PatternWithPos list     // e.g. 'x :: 'xs, 'x + 10
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
        | RowRecordType of (string * TypeWithPos) list               // e.g. { a: Int, b: Int, ... }
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
        | Str of string
        | Interpolation of ExpressionWithPos

    and public TopLevel =
        | Use of Use WithPos
        | Rule of Rule
        | Handler of Handler
        | Effect of string * vartypes: string list * (Signature WithPos) list
        | Type of SumType
        | TypeAlias of name: string * vartypes: string list * TypeWithPos
        | Notation of Notation
        | Measure
        | Unit
        | UnitSystem
        | UnitConversion
        | ModuleExport of string list

    and public SumType =
        { Name: string
          VarTypes: string list
          Constructors: (Signature WithPos) list }

    and public Handler =
        { Name: string
          State: PatternWithPos
          Pattern: PatternWithPos
          WhenClause: ExpressionWithPos option
          Type: TypeWithPos option
          Strategy: RewritingStrategy option
          Body: ExpressionWithPos
        }

    and public Rule =
        { Name: string WithPos
          Patterns: PatternWithPos list
          WhenClause: ExpressionWithPos option
          Type: TypeWithPos option
          Strategy: RewritingStrategy option
          Body: ExpressionWithPos }

    and public Notation =
        { NotationName: string WithPos
          NotationPattern: NotationPattern list WithPos
          NotationPrecedence: uint WithPos
          NotationAssociativity: Associativity WithPos
          NotationIs: ExpressionWithPos }

    and public NotationPattern =
        | FixedPart of string
        | HolePart of string

        member public this.toMixFixPattern =
            match this with
            | FixedPart s -> Fixed s
            | HolePart _ -> Hole

    and public ResumeWith =
        { Value: ExpressionWithPos
          HandlerState: ExpressionWithPos }

    and public Signature =
        { Name: string
          ArgumentsType: TypeWithPos list
          ReturnType: TypeWithPos option }

    and public Use =
        { Lib: IdentifierWithPos
          Qualifier: string option }

        override this.ToString() =
            string this.Lib.Node

    and public RewritingStrategy =
        /// Applies the rewrite rules starting with the deepest sub-expressions (leaves) before moving
        /// up towards the root of the syntax tree.
        | Innermost

        /// Applies the rewriting rules starting from the root of the syntax tree before moving down
        /// to deeper sub-expressions.
        | Outermost

        /// No rewriting is possible; this is an exceptional case (compile time or runtime).
        | Invalid

    and public Module =
        { ModuleDescription: string option
          ModuleContent: TopLevelWithPos list }

    module public NodeInfo =
        open System.Collections.Concurrent
        open System.IO

        let private cache = ConcurrentDictionary<string, string seq>()

        let public getLines (source: string) : string seq =
            cache.GetOrAdd(source, fun s ->
                use reader = new StringReader(s)
                let lines = ResizeArray()
                let mutable line = reader.ReadLine()
                while not (isNull line) do
                    lines.Add line
                    line <- reader.ReadLine()
                lines |> seq)

    /// Wrap the given parser result in the `WithPos` type.
    let inline public parseWithPos (p: Parser<_, _>) =
        //pipe2 getPosition p (fun pos node -> { Pos = pos; Node = node })
        pipe3 getPosition p getPosition (fun pos node pos' -> { Pos = pos; Node = node; Pos' = pos' })

    let inline public withoutPos (p: Parser<_ WithPos, _>) =
        p |>> _.Node

    let inline public withPosOf (b: WithPos<'t>) (a: 't) =
        { b with Node = a }

    let inline public removePos { Node = node } = node

    let public notationPatternToMixfixOperator (notation: Notation) =
        { Name = removePos notation.NotationName
          Pattern = removePos notation.NotationPattern |> List.map _.toMixFixPattern
          Precedence = removePos notation.NotationPrecedence
          Associativity = removePos notation.NotationAssociativity }

