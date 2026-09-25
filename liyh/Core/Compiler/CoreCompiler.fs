#nowarn "25"
#nowarn "26"
#nowarn "46"
namespace Liyh.Core

[<RequireQualifiedAccess>]
module private FreshName =
    open System.Threading

    let private counter = ref 0

    let inline public get (baseName: string) =
        let id = Interlocked.Increment(counter)
        sprintf "_%s:%d" baseName id

[<RequireQualifiedAccess>]
module CoreCompiler =
    open Liyh.Module
    open Liyh.Syntax.SyntaxTree
    open Liyh.Core.Helper
    open LiyhPackage

    type private WhileLoopVariableSource =
        | FromPattern of PatternWithPos
        | FromString of string

    let private tryGetVariable (patt: PatternWithPos) =
        match removePos patt with
        | VariablePattern varName -> Some varName
        | Wildcard -> None
        | other -> failwithf "Expected variable or wildcard, got `%A`." other

    /// Helper to compile while loops.
    let private whileLoop
        (variableNameSource: WhileLoopVariableSource)
        (initVal: CoreTerm)
        (endVal: CoreTerm)
        (body: CoreTerm)
        (incrementation: string)
        (comparison: string)
        (stepValue: CoreTerm option)
        =

        let runningVariableName =
            match variableNameSource with
            | FromPattern pattern -> Option.defaultValue (FreshName.get "itr") (tryGetVariable pattern)
            | FromString name -> name

        let runningVariable = Variable runningVariableName

        let runningVariableDeclaration =
            CoreLet
                { Pattern = runningVariable
                  Value = initVal
                  IsMutable = true }

        // Evaluate the end value once before the loop.
        let limitName = FreshName.get "limit"
        let limitVariable = Variable limitName

        let limitDeclaration = 
            CoreLet
                { Pattern = limitVariable
                  Value = endVal
                  IsMutable = false }

        // Evaluate the step value once before the loop
        let stepName = FreshName.get "step"
        let stepVariable = Variable stepName

        let stepDeclaration = 
            CoreLet 
                { Pattern = stepVariable
                  Value = stepValue |> Option.defaultValue (CoreTerm.Literal(CoreLiteral.Integer 1I))
                  IsMutable = false }

        let incrementExpr = 
            symbol incrementation [ runningVariable; stepVariable ]

        let whileLoopBody =
            TermSequence
                [ body
                  UpdateVariable(runningVariableName, incrementExpr) ]

        let whileLoop =
            WhileLoop
                { Predicate = symbol comparison [ runningVariable; limitVariable ]
                  Body = whileLoopBody }

        TermSequence 
            [ limitDeclaration
              stepDeclaration
              runningVariableDeclaration
              whileLoop ]

    type private State =
        { Notations: Notation list
          CurrentHandler: string option }

        static member Empty =
            { Notations = List.empty
              CurrentHandler = None }

    let rec private compileExpression (cstate: State) (expr: ExpressionWithPos) =
        match removePos expr with
        | UFCS ufcs -> compileUFCS cstate ufcs
        | Identifier id -> simpleSymbol (string (removePos id))
        | BindingVariable var -> Variable var
        | CollectionAccess ca -> compileCollectionAccess cstate ca
        | Apply apply -> compileApply cstate apply
        | Literal { Node = InterpolatedString lstr } -> compileInterpolatedString cstate lstr
        | Literal l -> compileLiteral l
        | MixfixOperator mixfix -> compileMixFix cstate mixfix
        | Tuple xs -> Builtin.symbolTuple (List.map (compileExpression cstate) xs)
        | List xs -> Builtin.symbolList (List.map (compileExpression cstate) xs)
        | ListComprehension listComprehension -> compileListComprehension cstate listComprehension
        | Range range -> compileRange cstate range
        | Let(patt, value) -> compileLetVar cstate patt value false
        | Var(patt, value) -> compileLetVar cstate patt value true
        | ExpressionSequence xs -> TermSequence (List.map (compileExpression cstate) xs)
        | While while' -> compileWhile cstate while'
        | ForIn forin -> compileForIn cstate forin
        | ForTo forto -> compileForTo cstate forto false
        | ForDownTo forto -> compileForTo cstate forto true
        | Lambda lambda -> compileLamda cstate lambda
        | Match match' -> compileMatch cstate match'
        | IfThenElse ifte -> compileIfThenElse cstate ifte
        | Record fields -> compileRecord cstate fields
        | RecordUsing(baseRecord, fields) -> compileRecordExtend cstate baseRecord fields
        | ReAssign(v, e) -> UpdateVariable(v.Node, compileExpression cstate e)
        | HandleEffect handle -> compileHandleEffect cstate handle
        | ResumeWith resume -> compileResume cstate resume
        | Substitution(env, inExpr) -> compileSubstitution cstate env inExpr
        | UsingContext ctx -> compileUsingContext cstate ctx
        | other -> failwithf "Todo: %A" other

        |> flattenTermSequence

    and private compileUFCS (cstate: State) (ufcs: UFCS) =
        let inline apply converted child =
            match converted with
            | Symbol symb -> Symbol { symb with Children = child :: symb.Children }
            | Variable _ -> FunctionalApplication { Base = converted; Arguments = [ child ] }
            | Closure _ -> FunctionalApplication { Base = converted; Arguments = [ child ] }
            | _ -> failwith "Application on non-applicable term"

        let rec collectChain current acc =
            match current with
            | UFCS { LHS = head; RHS = tail } -> collectChain (removePos tail) (removePos head :: acc)
            | finalExpr -> List.rev (finalExpr :: acc)

        match collectChain (UFCS ufcs) [] with
        | [] -> failwith "Cannot process an empty UFCS chain"
        | head :: tail ->
            let firstVal = compileExpression cstate (withPosOf ufcs.LHS head)
            List.fold (fun acc expr -> apply (compileExpression cstate (withPosOf ufcs.LHS expr)) acc) firstVal tail

    and private compileCollectionAccess (cstate: State) { LHS = expr; Indices = indices } =
        let indices = List.map (compileExpression cstate) indices
        Builtin.symbolCollectionAccess (compileExpression cstate expr) (List.rev indices)

    and private compileListComprehension (cstate: State) (lc: ListComprehension) =

        // If the range is an actual syntactic range, we can transform it into a while loop
        // that iters only on numbers, without creating any list

        match removePos lc.ListExpr with
        | Range range -> listComprehensionOverRange cstate range lc
        | _ ->
            let compiledItem = compileExpression cstate lc.ItemValue
            let compiledPattern = compilePattern cstate lc.Pattern
            let compiledList = compileExpression cstate lc.ListExpr
            let compiledCond = lc.IfPred |> Option.map (compileExpression cstate)

            let cursorVarName = FreshName.get "lc_cursor"
            let tailVarName = FreshName.get "lc_tail"
            let resultVarName = FreshName.get "lc_result"
            let nilVarName = FreshName.get "lc_nil"
            
            let cursorVar = Variable cursorVarName
            let tailVar = Variable tailVarName
            let resultVar = Variable resultVarName
            let nilVar = Variable nilVarName

            let bindCursor = CoreLet { Pattern = cursorVar; Value = compiledList; IsMutable = true }
            let bindResult = CoreLet { Pattern = resultVar; Value = Builtin.symbolNil; IsMutable = true }
            let bindNil = CoreLet { Pattern = nilVar; Value = Builtin.symbolNil; IsMutable = false }

            let appendExpr = Builtin.symbolCons compiledItem resultVar

            let updateResult =
                match compiledCond with
                | Some cond -> ifte cond (UpdateVariable(resultVarName, appendExpr)) (Builtin.symbolUnit)
                | None -> UpdateVariable(resultVarName, appendExpr)

            let loopBody =
                TermSequence [
                    CoreLet { 
                        Pattern = Builtin.symbolCons compiledPattern tailVar
                        Value = cursorVar
                        IsMutable = false 
                    }
                    updateResult
                    UpdateVariable(cursorVarName, tailVar)
                ]

            let whileLoop =
                WhileLoop {
                    Predicate = symbol Internals.Neq [ cursorVar; nilVar ]
                    Body = loopBody
                }

            TermSequence [
                bindCursor
                bindResult
                bindNil
                whileLoop
                Builtin.symbolReverse resultVar
            ]

    /// Specific optimized `for-in` loops over syntactic ranges.
    and private listComprehensionOverRange (cstate: State) (range: Range) (lc: ListComprehension) =
        let bind name value isVar =
            let varName = FreshName.get name
            let varTerm = Variable varName
            let binding = CoreLet { Pattern = varTerm; Value = value; IsMutable = isVar }
            (varName, varTerm, binding)

        let startExpr = compileExpression cstate range.RangeStart
        let stopExpr = compileExpression cstate range.RangeStop
        
        let _, startVar, bindStart = bind "lc_start" startExpr false
        let _, stopVar, bindStop   = bind "lc_stop"  stopExpr false
        let resultName, resultVar, bindResult = bind "lc_result" Builtin.symbolNil true
        
        let loopName = FreshName.get "lc_i"
        let loopCounterVar = Variable loopName

        let loopBody =
            let compiledPattern = compilePattern cstate lc.Pattern
            let compiledItem = compileExpression cstate lc.ItemValue
            
            let appendExpr = Builtin.symbolCons compiledItem resultVar
            let updateLogic = 
                match lc.IfPred with
                | Some pred -> 
                    ifte (compileExpression cstate pred) 
                        (UpdateVariable(resultName, appendExpr)) 
                        (Builtin.symbolUnit)
                | None -> UpdateVariable(resultName, appendExpr)

            TermSequence [
                CoreLet { Pattern = compiledPattern; Value = loopCounterVar; IsMutable = false }
                updateLogic 
            ]

        let makeLoop startTerm stopTerm op cmp stepOpt =
            whileLoop (FromString loopName) startTerm stopTerm loopBody op cmp stepOpt

        match range.RangeStep with
        | None ->
            let loopBackwardsFromStop = makeLoop stopVar startVar Internals.Sub Internals.Geq None
            let loopForwardsFromStop = makeLoop stopVar startVar Internals.Add Internals.Leq None

            let dirCondition = symbol Internals.Leq [ startVar; stopVar ]

            TermSequence [
                bindStart; bindStop; bindResult
                ifte dirCondition loopBackwardsFromStop loopForwardsFromStop
                resultVar 
            ]

        | Some stepExpr ->
            let stepCompiled = compileExpression cstate stepExpr
            let _, stepVar, bindStep = bind "lc_step" stepCompiled false

            let loopUp = makeLoop startVar stopVar Internals.Add Internals.Leq (Some stepVar)
            let loopDown = makeLoop startVar stopVar Internals.Add Internals.Geq (Some stepVar)

            let stepIsPositive = symbol Internals.Geq [ stepVar; CoreTerm.Literal(CoreLiteral.Integer 0I) ]

            TermSequence [
                bindStart; bindStop; bindStep; bindResult
                ifte stepIsPositive loopUp loopDown
                Builtin.symbolReverse resultVar
            ]

    and private compileApply (cstate: State) (apply: Apply) =
        let args = List.map (compileExpression cstate) apply.Arguments

        match removePos apply.LHS with
        | Identifier id -> symbol (string (removePos id)) args
        | _ ->
            let lhsTerm = compileExpression cstate apply.LHS
            FunctionalApplication { Base = lhsTerm; Arguments = args }

    //    and private compileApply (cstate: State) { LHS = lhs; Arguments = args } =
    //        let lhs = compileExpression cstate lhs
    //        let args = List.map (compileExpression cstate) args
    //
    //        match lhs with
    //        | Symbol symb ->
    //            if symb.Children.IsEmpty then copySymbolWithNewChildren symb args
    //            else FunctionalApplication { Base = lhs; Arguments = args }
    //
    //        | Closure _ -> FunctionalApplication { Base = lhs; Arguments = args }
    //        | x -> FunctionalApplication { Base = x; Arguments = args }

    and private compileInterpolatedString (cstate: State) (lstr: InterpolatedPart list) =

        let rec compileInterpolationPart cstate result =
            function
            | [] -> result
            | Str s :: rest ->
                let part = CoreTerm.Literal (CoreLiteral.String s.Node)
                compileInterpolationPart cstate (part :: result) rest

            | Interpolation e :: rest ->
                let e = compileExpression cstate e
                let spart = symbol Internals.Ppshow [ e ] //showSymbol e
                compileInterpolationPart cstate (spart :: result) rest

        let parts = compileInterpolationPart cstate [] (List.rev lstr)
        List.reduce (fun acc a -> symbol Internals.Strcat [ acc; a ]) parts

    and private compileLiteral (lit: LiteralWithPos) =
        match removePos lit with
        | Literal.Char c -> CoreTerm.Literal (CoreLiteral.Char c)
        | Literal.Float f -> CoreTerm.Literal (CoreLiteral.Float f)
        | Literal.Integer i -> CoreTerm.Literal (CoreLiteral.Integer (bigint i))
        | Literal.String s -> CoreTerm.Literal (CoreLiteral.String s)
        | Literal.Unit -> Builtin.symbolUnit

    and private compileMixFix (cstate: State) (mixfix: ApplyOperator) =
        match cstate.Notations |> List.tryFind (fun x -> removePos x.NotationName = mixfix.Name.Node) with
        | None -> failwithf "Unknown notation: %s" mixfix.Name.Node
        | Some notation ->
            let args = List.map (compileExpression cstate) mixfix.Arguments
            notationBinding cstate args notation

    and private compileRange (cstate: State) { RangeStart = start; RangeStep = step; RangeStop = stop } =
        let start = compileExpression cstate start
        let step = Option.map (compileExpression cstate) step
        let stop = compileExpression cstate stop

        let step = Option.defaultValue Builtin.symbolNone (Option.map Builtin.symbolSome step)

        Builtin.symbolRange start step stop

    and private compileLetVar (cstate: State) (patt: PatternWithPos) (value: ExpressionWithPos) (isVar: bool) =
        let patt = compilePattern cstate patt
        let value = compileExpression cstate value

        CoreLet
            { Pattern = patt
              Value = value
              IsMutable = isVar }

    and private compileWhile (cstate: State) { Predicate = pred; Body = body } =
        let pred = compileExpression cstate pred
        let body = compileExpression cstate body

        WhileLoop { Predicate = pred; Body = body }

    and private compileForTo (cstate: State) (forto: ForTo) (isDownTo: bool) =
        let initialValue = compileExpression cstate forto.InitialValue
        let endValue = compileExpression cstate forto.EndValue
        let body = compileExpression cstate forto.Body

        whileLoop
            (FromPattern forto.Pattern)
            initialValue
            endValue
            body
            (if isDownTo then Internals.Sub else Internals.Add)
            (if isDownTo then Internals.Geq else Internals.Leq)
            None

    and private compileForIn (cstate: State) (loop: ForIn) =

        // If the range is an actual syntactic range, we can transform it into a while loop
        // that iters only on numbers, without creating any list

        match removePos loop.ListExpr with
        | Range range -> loopOverRange cstate range loop.Body (FromPattern loop.Pattern)
        | _ ->

            // We use an iterator.

            let compiledPattern = compilePattern cstate loop.Pattern
            let compiledList = compileExpression cstate loop.ListExpr
            let compiledBody = compileExpression cstate loop.Body

            let cursorName = FreshName.get "iter_cursor"
            let tailName = FreshName.get "iter_tail"
            let nilName = FreshName.get "iter_nil"

            let cursorVar = Variable cursorName
            let tailVar = Variable tailName
            let nilVar = Variable nilName

            let bindCursor =
                CoreLet {
                    Pattern = cursorVar
                    Value = compiledList
                    IsMutable = true }

            let bindNil =
                CoreLet {
                    Pattern = nilVar
                    Value = Builtin.symbolNil
                    IsMutable = false }

            let consPattern = Builtin.symbolCons compiledPattern tailVar

            let loopBody =
                TermSequence [
                    CoreLet { 
                        Pattern = consPattern
                        Value = cursorVar
                        IsMutable = false }
                    compiledBody
                    UpdateVariable(cursorName, tailVar) ]

            let whileLoop = 
                WhileLoop {
                    Predicate = symbol Internals.Neq [ cursorVar; nilVar ]
                    Body = loopBody }

            TermSequence [
                bindCursor
                bindNil
                whileLoop ]

    /// Specific optimized `for-in` loops over syntactic ranges.
    and private loopOverRange
        (cstate: State)
        (range: Range)
        (loopBody: ExpressionWithPos)
        (loopPattern: WhileLoopVariableSource)
        =
        let startExpr = compileExpression cstate range.RangeStart
        let stopExpr = compileExpression cstate range.RangeStop
        let bodyExpr = compileExpression cstate loopBody

        let bind name baseExpr =
            let varName = FreshName.get name
            let varTerm = Variable varName
            let binding = CoreLet { Pattern = varTerm; Value = baseExpr; IsMutable = false }
            (varTerm, binding)

        let startVar, bindStart = bind "range_start" startExpr
        let stopVar, bindStop = bind "range_stop" stopExpr

        let makeLoop op cmp stepOpt =
            whileLoop loopPattern startVar stopVar bodyExpr op cmp stepOpt

        let stepBindings, loopLogic =
            match range.RangeStep with
            | None ->
                let loopUp = makeLoop Internals.Add Internals.Leq None
                let loopDown = makeLoop Internals.Sub Internals.Geq None

                let condition = symbol Internals.Leq [ startVar; stopVar ]
                
                ([], ifte condition loopUp loopDown)

            | Some stepExpr ->
                let stepCompiled = compileExpression cstate stepExpr
                let stepVar, bindStep = bind "range_step" stepCompiled

                let loopUp = makeLoop Internals.Add Internals.Leq (Some stepVar)
                let loopDown = makeLoop Internals.Add Internals.Geq (Some stepVar)
                
                let condition = symbol Internals.Geq [ stepVar; CoreTerm.Literal(CoreLiteral.Integer 0I) ]

                ([bindStep], ifte condition loopUp loopDown)

        TermSequence ([bindStart; bindStop] @ stepBindings @ [loopLogic])

    and private compileLamda (cstate: State) (lambda: Lambda) =
        let compiledPatterns = 
            lambda.Patterns 
            |> List.map (compilePattern cstate)

        let (parameters, bindings) =
            compiledPatterns
            |> List.map (fun patt ->
                match patt with
                | Variable v -> (v, None)
                | other ->
                    let freshArgName = FreshName.get "lam_arg"
                    let binding =
                        CoreLet
                            { Pattern = other
                              Value = Variable freshArgName
                              IsMutable = false }
                    freshArgName, Some binding)
            |> List.unzip

        let originalBody = compileExpression cstate lambda.Body
        let bindingStmts = List.choose id bindings

        let newBody =
            if List.isEmpty bindingStmts then
                originalBody
            else
                match originalBody with
                | TermSequence seq -> TermSequence (bindingStmts @ seq)
                | _ -> TermSequence (bindingStmts @ [ originalBody ])

        let boundParameters = Set.ofList parameters
        let freeVars, asDefined = freeVariables boundParameters newBody
        let freeVars = freeVars - asDefined

        let capturedEnv =
            freeVars
            |> Set.fold (fun env var -> Map.add var (Variable var) env) Map.empty

        Closure
            { Env = capturedEnv
              IsEvaluated = false
              Parameters = parameters
              Value = newBody }

    and private compileMatch (cstate: State) (match': Match) =
        let toMatch = compileExpression cstate match'.ToMatch
        let cases =
            match'.Cases
            |> List.map (fun (patt, value) -> compilePattern cstate patt, compileExpression cstate value)

        CoreTerm.Match
            { ToMatch = toMatch
              Cases = cases }

    and private compileIfThenElse (cstate: State) (ifte: IfThenElse) =
        let condition = compileExpression cstate ifte.Condition
        let thenBranch = compileExpression cstate ifte.ThenBranch

        let rec buildElseChain elifBranches finalElse =
            match elifBranches with
            | [] -> 
                Option.map (compileExpression cstate) finalElse
                |> Option.defaultValue Builtin.symbolUnit

            | (elifCond, elifThen) :: rest ->
                let elifCondCompiled = compileExpression cstate elifCond
                let elifThenCompiled = compileExpression cstate elifThen
                let restChain = buildElseChain rest finalElse

                CoreTerm.Match
                    { ToMatch = elifCondCompiled
                      Cases = 
                        [ (Builtin.symbolTrue, elifThenCompiled)
                          (Builtin.symbolFalse, restChain) ] }

        let elseBranch = buildElseChain ifte.ElifBranches ifte.ElseBranch

        let toMatch = condition
        let cases =
            [ (Builtin.symbolTrue, thenBranch)
              (Builtin.symbolFalse, elseBranch) ]

        CoreTerm.Match
            { ToMatch = toMatch
              Cases = cases }

    and private compileRecord (cstate: State) (fields: List<NameWithPos * ExpressionWithPos>) =
        let fields = List.map (fun (name, value) -> removePos name, compileExpression cstate value) fields
        RecordExtend { BaseRecord = None; Extension = fields }

    and private compileRecordExtend (cstate: State) (baseRecord: ExpressionWithPos) (fields: List<NameWithPos * ExpressionWithPos>) =
        let baseRecord = compileExpression cstate baseRecord
        let fields = List.map (fun (name, value) -> removePos name, compileExpression cstate value) fields

        RecordExtend { BaseRecord = Some baseRecord; Extension = fields }

    and private compileHandleEffect (cstate: State) (handle: Handle) =
        let handler = string (removePos handle.Handler)
        let state = compileExpression cstate handle.InitialState
        let body = compileExpression cstate handle.Body
        
        Handle { Handler = handler; State = state; ToHandle = body }

    and private compileResume (cstate: State) (resume: ResumeWith) =
        let state = compileExpression cstate resume.HandlerState
        let value = compileExpression cstate resume.Value

        Resume {
            Rewrite = value
            State = state
            FromHandler = cstate.CurrentHandler.Value }

    and private compileSubstitution (cstate: State) (env: list<NameWithPos * ExpressionWithPos>) (inExpr: ExpressionWithPos) =
        let env = List.map (fun (a, b) -> let (Symbol sym) = simpleSymbol (removePos a) in sym, compileExpression cstate b) env
        let inExpr = compileExpression cstate inExpr

        CoreTerm.Substitution
            { Env = env
              InExpr = inExpr }

    and private compileUsingContext (cstate: State) (ctx: UsingContext) =
        CoreTerm.UsingContext
            { Context = string (removePos ctx.ContextName)
              Expr = compileExpression cstate ctx.ContentExpr }

    // --- Patterns --- //

    and private compilePattern (cstate: State) (pattern: PatternWithPos) =
        match removePos pattern with
        | VariablePattern v -> Variable v
        | SymbolPattern s -> simpleSymbol (string s)
        | ApplyPattern(lhs, args) -> compileApplyPattern cstate lhs args
        | LiteralPattern lit -> compileLiteral lit
        | TuplePattern xs -> Builtin.symbolTuple (List.map (compilePattern cstate) xs)
        | ListPattern xs -> Builtin.symbolList (List.map (compilePattern cstate) xs)
        | AsPattern(basePatt, asPatt) -> compileAsPattern cstate basePatt asPatt
        | WhenPattern(basePatt, pred) -> compileWhenPattern cstate basePatt pred
        | Wildcard -> CoreTerm.Wildcard
        | MixfixOperatorPattern(name, args) -> compileMixFixPattern cstate name.Node args
        | RecordPattern fields -> compileRecordPattern cstate fields
        | AlternativePattern xs -> compileAlternativePattern xs
        | TypedPattern(patt, ty) -> compileTypedPattern cstate patt ty
        | other -> failwithf "Todo: %A" other

    and private compileApplyPattern (cstate: State) (lhs: PatternWithPos) (args: PatternWithPos list) =
        let lhs = compilePattern cstate lhs
        let args = List.map (compilePattern cstate) args

        let raiseException () =
            failwithf "Application on non-applicable symbol: %s" (PrettyPrinter.prettyPrintExpr lhs)

        match lhs with
        | Symbol symb ->
            if symb.Children.IsEmpty then Symbol { symb with Children = args }
            else raiseException ()

        | Variable v ->
            VariableApply(v, args)

        | _ ->
            raiseException ()

    and private compileAsPattern (cstate: State) (basePatt: PatternWithPos) (asPatt: PatternWithPos) =
        let basePatt = compilePattern cstate basePatt
        let asPatt = compilePattern cstate asPatt

        AsClause(basePatt, asPatt)

    and private compileMixFixPattern (cstate: State) (name: string) (args: PatternWithPos list) =
        match cstate.Notations |> List.tryFind (fun x -> removePos x.NotationName = name) with
        | None -> failwithf "Unknown notation: %s" name
        | Some notation ->
            let args = List.map (compilePattern cstate) args
            notationBinding cstate args notation

    and private compileWhenPattern (cstate: State) (basePatt: PatternWithPos) (pred: ExpressionWithPos) =
        let basePatt = compilePattern cstate basePatt
        let pred = compileExpression cstate pred

        WhenClause(basePatt, pred)

    and private compileAlternativePattern (alternatives: LiteralWithPos list) =
        // (A | B | C) -> 'x when 'x ∈ { A, B, C }
        let alternatives = Builtin.symbolList (List.map compileLiteral alternatives)
        let uv = Variable (FreshName.get "altp")

        WhenClause(uv, Builtin.symbolContains alternatives uv)

    and private compileRecordPattern (cstate: State) (fields: (NameWithPos * PatternWithPos) list) =
        let fields = List.map (fun (name, value) -> removePos name, compilePattern cstate value) fields
        RecordExtend { BaseRecord = None; Extension = fields }

    and private compileTypedPattern (cstate: State) (patt: PatternWithPos) (ty: TypeWithPos) =
        // TODO
        compilePattern cstate patt

    and private notationBinding (cstate: State) (args: CoreTerm list) (notation: Notation) =
        let pattern = removePos notation.NotationPattern
        let rewrite = compileExpression cstate notation.NotationIs

        let holes =
            pattern
            |> List.choose (function
                | HolePart h -> Some (Variable h.Node)
                | _ -> None)

        let subst = Map.ofList (List.zip holes args)
        CoreTermSubstitution.replaceCoreTerm subst rewrite

    // --- Types --- //

    and private compileType (ty: Type) =
        failwith "Todo" // Symbolic or not ? Est-ce qu'on fait une branche spécifique pour les types ?
                        // c'est sans doute mieux.

    // --- Top Level --- //

    and private compileDefinition (cstate: State) (definition: TopLevelWithPos) =
        let compiled =
            match removePos definition with
            | TopLevel.Rule rule -> Some (compileRule cstate rule)
            | TopLevel.LetRule letRule -> Some (compileRule cstate letRule)
            | TopLevel.Handler handler -> Some (compileHandler cstate handler)
            | TopLevel.Extern extrn -> None
            | TopLevel.Context context -> Some (compileContext cstate context)
            | other -> failwithf "Todo: %A" other

        Option.map (AlphaConversion.alphaConversionDefinition FreshName.get) compiled

    and private compileRule (cstate: State) (rule: Rule) =
        let body = compileExpression cstate rule.Body
        let name = removePos rule.Name
        let patterns = List.map (compilePattern cstate) rule.Patterns
        let whenClause = Option.map (compileExpression cstate) rule.WhenClause
        let strategy = Option.defaultValue Strict (Option.map removePos rule.Strategy)

        let lhs = symbol name patterns

        CoreDefinition.Rule
            { LHS = lhs
              RHS = body
              WhenClause = whenClause
              Strategy = strategy }

    and private compileHandler (cstate: State) (handler: Handler) =
        let cstate = { cstate with CurrentHandler = Some handler.Name.Node }

        let body = compileExpression cstate handler.Body
        let name = handler.Name
        let hstate = compilePattern cstate handler.State
        let pattern = compilePattern cstate handler.Pattern
        let whenClause = Option.map (compileExpression cstate) handler.WhenClause
        let strategy = Option.defaultValue Strict (Option.map removePos handler.Strategy)

        let lhs = pattern

        CoreDefinition.Handler
            { HandlerName = name.Node
              LHS = lhs
              RHS = body
              State = hstate
              WhenClause = whenClause
              Strategy = strategy }

    and private compileContext (cstate: State) (context: Context) =
        CoreDefinition.Context
            { ContextName = string (removePos context.Name)
              Content = List.choose (compileDefinition cstate) context.Content
              Using = List.map (removePos >> string) context.Using }

    // --- Module --- //

    type public CoreNotationInfo =
        { Name: string
          Associativity: Associativity
          IsCommutative: bool }

    /// Dictionary between notation's name/arity and their core informations.
    type public NotationEnv = Map<string * int, CoreNotationInfo>

    let private compileModule (modl: ModuleInfo) =
        let definitions = Definitions.classifyDefinitions modl

        let notations =
            definitions
            |> Map.tryFind Definitions.DefinitionType.Notation
            |> Option.map (List.map (removePos >> function Notation notation -> notation))
            |> Option.defaultValue []

        let cstate = { State.Empty with Notations = notations }
        let definitions = Map.remove Definitions.DefinitionType.Notation definitions

        let notationsInfo =
            notations
            |> List.map (fun nt ->
                let key =
                    match compileExpression cstate nt.NotationIs with
                    | Symbol { Symbol = symb; Children = children } -> (symb, children.Length)
                    | other -> failwithf "Notations can only rewrite to symbols, but got `%A`." other

                key,
                    { Name = removePos nt.NotationName
                      Associativity = removePos nt.NotationAssociativity
                      IsCommutative = removePos nt.NotationCommutative })
            |> Map.ofList

        let compiledModule =
            definitions.Values
            |> List.ofSeq
            |> List.concat
            |> List.choose (compileDefinition cstate)

        (compiledModule, notationsInfo)

    type public LayeredCompilationEnv =
        { Definitions: CoreDefinition list
          NotationEnv: NotationEnv }

    /// Compiles each modules of the list to the LiyhCore intermediate representation.
    /// The compilation is done in parallel for each modules.
    let public compileModules (modules: ModuleInfo list) : LayeredCompilationEnv =
        let compiledResults =
            modules
            |> Array.ofList
            |> Array.Parallel.map compileModule

        let compiledModuleDefinitions, notationsMaps = Array.unzip compiledResults
        let mergedModuleDefinitions =  List.concat compiledModuleDefinitions

        // Some upstream checks verify for collisions, so we do not
        // have to handle this here for the map's keys.

        let mergedNotations =
            notationsMaps
            |> Seq.collect Map.toSeq
            |> Map.ofSeq

        { Definitions = mergedModuleDefinitions
          NotationEnv = mergedNotations }

    type public GlobalCompilationEnv =
        { FFIBindings: GlobalFFIBindings
          Definitions: CoreDefinition list
          NotationEnv: NotationEnv }

    /// Merges compilation environment tables for each layer into a global environment.
    /// Assumes no collisions between definitions across layers.
    let public getGlobalCompilationEnv
        (ffiBindings: GlobalFFIBindings)
        (compilationEnvLayers: LayeredCompilationEnv array)
        : GlobalCompilationEnv =

        let coreDefinitions =
            compilationEnvLayers
            |> Array.map _.Definitions
            |> List.concat

        let allNotationsInformation =
            compilationEnvLayers
            |> Seq.collect (_.NotationEnv >> Map.toSeq)
            |> Map.ofSeq

        { Definitions = coreDefinitions
          NotationEnv = allNotationsInformation
          FFIBindings = ffiBindings }

