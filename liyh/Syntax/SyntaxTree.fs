namespace Liyh.Syntax

/// Concrete Syntax Tree (including positions and no sugar) of the language.
module SyntaxTree =
    open FParsec

    type public Associativity = FParsec.Associativity
    type public MixfixPatternPart = Fixed of string | Hole
    type public MixfixPattern = MixfixPatternPart list

    type public WithPos<'t> =
        { Node: 't
          Pos: Position     // starting position
          Pos': Position }  // ending position

        member public this.Line = this.Pos.Line
        member public this.Col = this.Pos.Column
        member public this.File = this.Pos.StreamName
        member public this.PosTuple = (this.Pos, this.Pos')

    and public MixfixOperator =
        { Name: string
          Pattern: MixfixPattern
          BindingPatterns: NotationPattern list
          Precedence: uint
          Associativity: Associativity
          RewritesTo: ExpressionWithPos }

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
        | IfThenElse of IfThenElse
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

    and public IfThenElse =
        { Condition: ExpressionWithPos
          ThenBranch: ExpressionWithPos
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

    let inline public withPosOf (b: WithPos<'a>) (a: 'b) =
        { Node = a; Pos = b.Pos; Pos' = b.Pos' }

    let inline public removePos { Node = node } = node

    let inline public removePosList (xs: List<_ WithPos>) = List.map removePos xs

    let inline public withPosOverride (b: WithPos<'t>) (a: WithPos<'t>) =
        withPosOf b (removePos a)

    let public notationPatternToMixfixOperator (notation: Notation) =
        { Name = removePos notation.NotationName
          Pattern = removePos notation.NotationPattern |> List.map _.toMixFixPattern
          BindingPatterns = removePos notation.NotationPattern
          Precedence = removePos notation.NotationPrecedence
          Associativity = removePos notation.NotationAssociativity
          RewritesTo = notation.NotationIs }

module Replace =
    open SyntaxTree

    let rec public replaceVariable (map: Map<string, ExpressionWithPos>) (expwp: ExpressionWithPos) : ExpressionWithPos =
        let replaceExpr = replaceVariable map
        let replacePattern pat = replacePatternVariable map pat
        
        match expwp.Node with
        | BindingVariable name ->
            match Map.tryFind name map with
            | Some replacement -> replacement
            | None -> expwp
        | UFCS ufcs ->
            { expwp with Node = UFCS { LHS = replaceExpr ufcs.LHS; RHS = replaceExpr ufcs.RHS } }
        | Identifier _ -> expwp
        | CollectionAccess ca ->
            { expwp with Node = CollectionAccess { LHS = replaceExpr ca.LHS; Indices = List.map replaceExpr ca.Indices } }
        | Literal _ -> expwp
        | ExpressionSequence exprs ->
            { expwp with Node = ExpressionSequence (List.map replaceExpr exprs) }
        | Apply apply ->
            { expwp with Node = Apply { LHS = replaceExpr apply.LHS; Arguments = List.map replaceExpr apply.Arguments } }
        | MixfixOperator op ->
            { expwp with Node = MixfixOperator { Name = op.Name; Arguments = List.map replaceExpr op.Arguments } }
        | Tuple exprs ->
            { expwp with Node = Tuple (List.map replaceExpr exprs) }
        | List exprs ->
            { expwp with Node = List (List.map replaceExpr exprs) }
        | Record fields ->
            { expwp with Node = Record (List.map (fun (name, expr) -> (name, replaceExpr expr)) fields) }
        | RecordUsing (baseExpr, fields) ->
            { expwp with Node = RecordUsing (replaceExpr baseExpr, List.map (fun (name, expr) -> (name, replaceExpr expr)) fields) }
        | ListComprehension lc ->
            { expwp with Node = ListComprehension { ItemValue = replaceExpr lc.ItemValue; Pattern = lc.Pattern; ListExpr = replaceExpr lc.ListExpr; IfPred = Option.map replaceExpr lc.IfPred } }
        | Range range ->
            { expwp with Node = Range { RangeStart = replaceExpr range.RangeStart; RangeStep = Option.map replaceExpr range.RangeStep; RangeStop = replaceExpr range.RangeStop } }
        | While w ->
            { expwp with Node = While { Predicate = replaceExpr w.Predicate; Body = replaceExpr w.Body } }
        | ForIn forIn ->
            { expwp with Node = ForIn { Pattern = replacePattern forIn.Pattern; ListExpr = replaceExpr forIn.ListExpr; Body = replaceExpr forIn.Body } }
        | ForTo forTo ->
            { expwp with Node = ForTo { Pattern = replacePattern forTo.Pattern; InitialValue = replaceExpr forTo.InitialValue; EndValue = replaceExpr forTo.EndValue; Body = replaceExpr forTo.Body } }
        | ForDownTo forTo ->
            { expwp with Node = ForDownTo { Pattern = replacePattern forTo.Pattern; InitialValue = replaceExpr forTo.InitialValue; EndValue = replaceExpr forTo.EndValue; Body = replaceExpr forTo.Body } }
        | ReAssign (name, expr) ->
            { expwp with Node = ReAssign (name, replaceExpr expr) }
        | Let (pattern, expr) ->
            { expwp with Node = Let (replacePattern pattern, replaceExpr expr) }
        | Var (pattern, expr) ->
            { expwp with Node = Var (replacePattern pattern, replaceExpr expr) }
        | Match m ->
            { expwp with Node = Match { ToMatch = replaceExpr m.ToMatch; Cases = List.map (fun (pat, expr) -> (replacePattern pat, replaceExpr expr)) m.Cases } }
        | IfThenElse ifte ->
            { expwp with Node = IfThenElse { Condition = replaceExpr ifte.Condition; ThenBranch = replaceExpr ifte.ThenBranch; ElseBranch = Option.map replaceExpr ifte.ElseBranch } }
        | Lambda lambda ->
            { expwp with Node = Lambda { Patterns = List.map replacePattern lambda.Patterns; Body = replaceExpr lambda.Body } }
        | HandleEffect handle ->
            { expwp with Node = HandleEffect { Handler = handle.Handler; InitialState = replaceExpr handle.InitialState; Body = replaceExpr handle.Body } }
        | ResumeWith rw ->
            { expwp with Node = ResumeWith { rw with Node = { rw.Node with Value = replaceExpr rw.Node.Value; HandlerState = replaceExpr rw.Node.HandlerState } } }

    and public replacePatternVariable (map: Map<string, ExpressionWithPos>) (patwp: PatternWithPos) : PatternWithPos =
        let replaceExpr = replaceVariable map
        let replacePattern = replacePatternVariable map
        let replaceType typ = replaceTypeVariable map typ
        
        match patwp.Node with
        | VariablePattern _ -> patwp
        | SymbolPattern _ -> patwp
        | ApplyPattern (pat, pats) ->
            { patwp with Node = ApplyPattern (replacePattern pat, List.map replacePattern pats) }
        | LiteralPattern _ -> patwp
        | TuplePattern pats ->
            { patwp with Node = TuplePattern (List.map replacePattern pats) }
        | ListPattern pats ->
            { patwp with Node = ListPattern (List.map replacePattern pats) }
        | RecordPattern fields ->
            { patwp with Node = RecordPattern (List.map (fun (name, pat) -> (name, replacePattern pat)) fields) }
        | MixfixOperatorPattern (name, pats) ->
            { patwp with Node = MixfixOperatorPattern (name, List.map replacePattern pats) }
        | AsPattern (pat1, pat2) ->
            { patwp with Node = AsPattern (replacePattern pat1, replacePattern pat2) }
        | WhenPattern (pat, expr) ->
            { patwp with Node = WhenPattern (replacePattern pat, replaceExpr expr) }
        | TypedPattern (pat, typ) ->
            { patwp with Node = TypedPattern (replacePattern pat, replaceType typ) }
        | AlternativePattern _ -> patwp
        | Wildcard -> patwp

    and public replaceTypeVariable (map: Map<string, ExpressionWithPos>) (typwp: TypeWithPos) : TypeWithPos =
        let replaceType = replaceTypeVariable map
        
        match typwp.Node with
        | NamedType _ -> typwp
        | VariableType _ -> typwp
        | RuleType (argTypes, retType) ->
            { typwp with Node = RuleType (List.map replaceType argTypes, replaceType retType) }
        | TupleType types ->
            { typwp with Node = TupleType (List.map replaceType types) }
        | RowRecordType fields ->
            { typwp with Node = RowRecordType (List.map (fun (name, typ) -> (name, replaceType typ)) fields) }
        | ParametrizedType (ident, types) ->
            { typwp with Node = ParametrizedType (ident, List.map replaceType types) }
        | ModuloEffectType (typ, effects) ->
            { typwp with Node = ModuloEffectType (replaceType typ, effects) }
        | WildcardType -> typwp

