namespace Liyh.Core

[<RequireQualifiedAccess>]
module private FreshName =
    open System.Threading

    let mutable private counter = 0L

    /// Creates a new unique variable. This function is thread-safe.
    let public get (baseName: string) =
        let id = Interlocked.Increment(&counter)
        $"_{baseName}:{id}"

module public CoreCompiler =
    open Liyh.Module
    open Liyh.Syntax.SyntaxTree
    open Liyh.Semantic.TypedSyntaxTree
    open Liyh.Core.Helper
    open Liyh.FFI
    open LiyhPackage


    //                      //
    // --- Some Helpers --- //
    //                      //


    type private WhileLoopVariableSource =
        | FromPattern of TPattern
        | FromString of string

    let rec private tryGetVariable (patt: TPattern) =
        match patt.Kind with
        | TPatternNode.TPatVariable ident -> Some (removePos ident.Written.Name)
        | TPatternNode.TPatWildcard -> None
        | TPatternNode.TPatTyped typed -> tryGetVariable typed.PatTypedInner
        | other -> failwithf "Expected variable or wildcard, got `%A`." other

    /// Helper to compile imperative while loops.
    let private whileLoop
        (variableNameSource: WhileLoopVariableSource)
        (initialValue: CoreTerm)
        (endValue: CoreTerm)
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
                  Value = initialValue
                  IsMutable = true }

        let limitName = FreshName.get "limit"
        let limitVariable = Variable limitName

        let limitDeclaration =
            CoreLet
                { Pattern = limitVariable
                  Value = endValue
                  IsMutable = false }

        let stepName = FreshName.get "step"
        let stepVariable = Variable stepName
        let stepValue = Option.defaultValue (CoreTerm.Literal(CoreLiteral.Integer 1I)) stepValue

        let stepDeclaration =
            CoreLet
                { Pattern = stepVariable
                  Value = stepValue
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


    //                               //
    // --- Compiling Expressions --- //
    //                               //


    let rec private compileExpression (cstate: State) (expr: TExpression) : CoreTerm =
        match expr.Kind with
        | TExpressionNode.TError err ->
            failwithf "Cannot compile AST containing error: %s" err.Description

        | TExpressionNode.TUFCS ufcs ->
            compileUFCS cstate ufcs

        | TExpressionNode.TIdentifier ident ->
            match ident.Kind with
            | SymbolKind.LocalVariable ->
                Variable (removePos ident.Written.Name)

            | SymbolKind.Constructor _ ->
                simpleSymbol (removePos ident.Written.Name)

            | SymbolKind.RuleReference mangledName ->
                simpleSymbol mangledName

            | SymbolKind.ExternFunction _ ->
                simpleSymbol (string ident.Written)

            | SymbolKind.PureSymbol ->
                simpleSymbol (string ident.Written)

        | TExpressionNode.TCollectionAccess ca ->
            compileCollectionAccess cstate ca

        | TExpressionNode.TApply apply ->
            compileApply cstate apply

        | TExpressionNode.TLit lit ->
            compileLiteralNode lit

        | TExpressionNode.TInterpolatedString parts ->
            compileInterpolatedString cstate parts

        | TExpressionNode.TMixfixOperator mixfix ->
            compileMixFix cstate mixfix

        | TExpressionNode.TTuple xs ->
            Builtin.symbolTuple (List.map (compileExpression cstate) xs)

        | TExpressionNode.TList xs ->
            Builtin.symbolList (List.map (compileExpression cstate) xs)

        | TExpressionNode.TListComprehension lc ->
            compileListComprehension cstate lc

        | TExpressionNode.TRange range ->
            compileRange cstate range

        | TExpressionNode.TLet l ->
            CoreLet
                { Pattern = compilePattern cstate l.LetPattern
                  Value = compileExpression cstate l.LetValue
                  IsMutable = (l.LetMutability = Mutability.Mutable) }

        | TExpressionNode.TSequence xs ->
            TermSequence (List.map (compileExpression cstate) xs)

        | TExpressionNode.TWhile w ->
            WhileLoop
                { Predicate = compileExpression cstate w.WhileCondition
                  Body = compileExpression cstate w.WhileBody }

        | TExpressionNode.TForIn forin ->
            compileForIn cstate forin

        | TExpressionNode.TForTo forto ->
            compileForTo cstate forto

        | TExpressionNode.TReAssign ra ->
            UpdateVariable(removePos ra.ReAssignTarget.Written.Name, compileExpression cstate ra.ReAssignValue)

        | TExpressionNode.TMatch m ->
            compileMatch cstate m

        | TExpressionNode.TIfThenElse ifte ->
            compileIfThenElse cstate ifte

        | TExpressionNode.TLambda lambda ->
            compileLambda cstate lambda

        | TExpressionNode.TRecord fields ->
            compileRecord cstate fields

        | TExpressionNode.TRecordUsing ru ->
            compileRecordUsing cstate ru

        | TExpressionNode.TSubstitution s ->
            compileSubstitution cstate s

        |> flattenTermSequence

    and private compileLiteralNode (lit: TLiteralNode) =
        match lit with
        | TLiteralNode.TLitInteger i -> CoreTerm.Literal (CoreLiteral.Integer (bigint i))
        | TLiteralNode.TLitFloat f -> CoreTerm.Literal (CoreLiteral.Float f)
        | TLiteralNode.TLitChar c -> CoreTerm.Literal (CoreLiteral.Char c)
        | TLiteralNode.TLitString s -> CoreTerm.Literal (CoreLiteral.String s)
        | TLiteralNode.TLitUnit -> Builtin.symbolUnit

    and private compileUFCS (cstate: State) (ufcs: TUFCS) =
        compileApply cstate ufcs.UfcsCall

    and private compileApply (cstate: State) (apply: TApply) =
        let args = List.map (compileExpression cstate) apply.ApplyArguments

        match apply.ApplyCallee.Kind with
        | TExpressionNode.TIdentifier ident ->
            match ident.Kind with
            | SymbolKind.LocalVariable ->
                FunctionalApplication { Base = Variable (removePos ident.Written.Name); Arguments = args }

            | SymbolKind.Constructor _ ->
                symbol (removePos ident.Written.Name) args

            | SymbolKind.RuleReference name ->
                symbol name args

            | SymbolKind.ExternFunction _ ->
                symbol (string ident.Written) args

            | SymbolKind.PureSymbol ->
                symbol (string ident.Written) args

        | _ ->
            let lhsTerm = compileExpression cstate apply.ApplyCallee
            FunctionalApplication { Base = lhsTerm; Arguments = args }

    and private compileCollectionAccess (cstate: State) (ca: TCollectionAccess) =
        let indices = List.map (compileExpression cstate) ca.AccessIndices
        Builtin.symbolCollectionAccess (compileExpression cstate ca.AccessTarget) (List.rev indices)

    and private compileInterpolatedString (cstate: State) (parts: TInterpolatedPart list) =
        let compiledParts =
            List.map (function
                | TInterpolatedPart.TStringPart s -> CoreTerm.Literal (CoreLiteral.String s.Node)
                | TInterpolatedPart.TInterpolation e ->
                    let ce = compileExpression cstate e
                    symbol Internals.Ppshow [ ce ]) parts

        match compiledParts with
        | [] -> CoreTerm.Literal (CoreLiteral.String "")
        | [ single ] -> single
        | _ -> List.reduce (fun acc a -> symbol Internals.Strcat [ acc; a ]) compiledParts

    /// Helper to compile range lists.
    and private compileRangeIteration
        (cstate: State)
        (range: TRange)
        (loopVarSource: WhileLoopVariableSource)
        (makeBody: CoreTerm -> CoreTerm)
        : CoreTerm
        =

        let isFloat = range.RangeFrom.Type.Prune().IsTFloat
        let zero = if isFloat then CoreTerm.Literal(CoreLiteral.Float 0.0) else CoreTerm.Literal(CoreLiteral.Integer 0I)
        let one = if isFloat then CoreTerm.Literal(CoreLiteral.Float 1.0) else CoreTerm.Literal(CoreLiteral.Integer 1I)

        let bind name value =
            let varName = FreshName.get name
            let varTerm = Variable varName
            let binding = CoreLet { Pattern = varTerm; Value = value; IsMutable = false }
            (varTerm, binding)

        let startExpr = compileExpression cstate range.RangeFrom
        let stopExpr = compileExpression cstate range.RangeTo

        let startVar, bindStart = bind "range_start" startExpr
        let stopVar, bindStop = bind "range_stop" stopExpr

        let runningVariableName =
            match loopVarSource with
            | FromPattern pattern -> Option.defaultValue (FreshName.get "itr") (tryGetVariable pattern)
            | FromString name -> name

        let runningVariable = Variable runningVariableName
        let loopBody = makeBody runningVariable

        let makeLoop op cmp stepTerm =
            whileLoop (FromString runningVariableName) startVar stopVar loopBody op cmp (Some stepTerm)

        match range.RangeBy with
        | None ->
            let loopUp = makeLoop Internals.Add Internals.Leq one
            let loopDown = makeLoop Internals.Sub Internals.Geq one
            let condition = symbol Internals.Leq [ startVar; stopVar ]

            TermSequence [
                bindStart
                bindStop
                ifte condition loopUp loopDown ]

        | Some stepExpr ->
            let stepCompiled = compileExpression cstate stepExpr
            let stepVar, bindStep = bind "range_step" stepCompiled

            let loopUp   = makeLoop Internals.Add Internals.Leq stepVar
            let loopDown = makeLoop Internals.Add Internals.Geq stepVar
            let stepIsPositive = symbol Internals.Geq [ stepVar; zero ]

            TermSequence [
                bindStart
                bindStop
                bindStep
                ifte stepIsPositive loopUp loopDown ]

    and private compileRange (cstate: State) (range: TRange) : CoreTerm =
        let resultName = FreshName.get "range_res"
        let resultVar = Variable resultName
        let bindResult = CoreLet { Pattern = resultVar; Value = Builtin.symbolNil; IsMutable = true }

        let loopName = FreshName.get "range_i"
        let rangeLoop =
            compileRangeIteration cstate range (FromString loopName) (fun counterVar ->
                UpdateVariable(resultName, Builtin.symbolCons counterVar resultVar))

        TermSequence [
            bindResult
            rangeLoop
            Builtin.symbolReverse resultVar ]

    and private compileForTo (cstate: State) (forto: TForTo) =
        let initialValue = compileExpression cstate forto.ForToInitial
        let limitValue = compileExpression cstate forto.ForToLimit
        let body = compileExpression cstate forto.ForToBody
        let isDownTo = (forto.ForToDirection = ForDirection.Downwards)

        whileLoop
            (FromPattern forto.ForToPattern)
            initialValue
            limitValue
            body
            (if isDownTo then Internals.Sub else Internals.Add)     // we could use the real internal
            (if isDownTo then Internals.Geq else Internals.Leq)     // we could use the real internal
            None

    and private compileForIn (cstate: State) (loop: TForIn) =
        match loop.ForInSource.Kind with
        | TExpressionNode.TRange range ->
            loopOverRange cstate range loop.ForInBody (FromPattern loop.ForInPattern)

        | _ ->
            let compiledPattern = compilePattern cstate loop.ForInPattern
            let compiledList = compileExpression cstate loop.ForInSource
            let compiledBody = compileExpression cstate loop.ForInBody

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

    and private loopOverRange
        (cstate: State)
        (range: TRange)
        (loopBody: TExpression)
        (loopPattern: WhileLoopVariableSource)
        =
        let bodyExpr = compileExpression cstate loopBody
        compileRangeIteration cstate range loopPattern (fun _ -> bodyExpr)

    and private compileListComprehension (cstate: State) (lc: TListComprehension) =
        match lc.CompSource.Kind with
        | TExpressionNode.TRange range ->
            listComprehensionOverRange cstate range lc

        | _ ->
            let compiledItem = compileExpression cstate lc.CompItem
            let compiledPattern = compilePattern cstate lc.CompPattern
            let compiledList = compileExpression cstate lc.CompSource
            let compiledCond = lc.CompFilter |> Option.map (compileExpression cstate)

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
                | Some cond -> ifte cond (UpdateVariable(resultVarName, appendExpr)) Builtin.symbolUnit
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

    and private listComprehensionOverRange (cstate: State) (range: TRange) (lc: TListComprehension) =
        let resultName = FreshName.get "lc_res"
        let resultVar = Variable resultName
        let bindResult = CoreLet { Pattern = resultVar; Value = Builtin.symbolNil; IsMutable = true }

        let loopName = FreshName.get "lc_i"
        let compiledPattern = compilePattern cstate lc.CompPattern
        let compiledItem = compileExpression cstate lc.CompItem

        let appendExpr = Builtin.symbolCons compiledItem resultVar
        let updateLogic =
            match lc.CompFilter with
            | Some pred ->
                ifte (compileExpression cstate pred)
                    (UpdateVariable(resultName, appendExpr))
                    Builtin.symbolUnit
            | None -> UpdateVariable(resultName, appendExpr)

        let rangeLoop =
            compileRangeIteration cstate range (FromString loopName) (fun counterVar ->
                TermSequence [
                    CoreLet { Pattern = compiledPattern; Value = counterVar; IsMutable = false }
                    updateLogic
                ])

        TermSequence [
            bindResult
            rangeLoop
            Builtin.symbolReverse resultVar ]

    and private compileLambda (cstate: State) (lambda: TLambda) =
        let compiledPatterns = lambda.LambdaParameters |> List.map (compilePattern cstate)

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

        let originalBody = compileExpression cstate lambda.LambdaBody
        let bindingStmts = List.choose id bindings

        let newBody =
            if List.isEmpty bindingStmts then originalBody
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

    and private compileMatch (cstate: State) (match': TMatch) =
        let toMatch = compileExpression cstate match'.MatchScrutinee
        let cases =
            match'.MatchCases
            |> List.map (fun c -> compilePattern cstate c.CasePattern, compileExpression cstate c.CaseBody)

        CoreTerm.Match
            { ToMatch = toMatch
              Cases = cases }

    and private compileIfThenElse (cstate: State) (ifte: TIfThenElse) =
        let condition = compileExpression cstate ifte.IfCondition
        let thenBranch = compileExpression cstate ifte.IfThen

        let rec buildElseChain elifBranches finalElse =
            match elifBranches with
            | [] -> 
                Option.map (compileExpression cstate) finalElse
                |> Option.defaultValue Builtin.symbolUnit

            | elifBr :: rest ->
                let elifCondCompiled = compileExpression cstate elifBr.ElifCondition
                let elifThenCompiled = compileExpression cstate elifBr.ElifBody
                let restChain = buildElseChain rest finalElse

                CoreTerm.Match
                    { ToMatch = elifCondCompiled
                      Cases = 
                        [ (Builtin.symbolTrue, elifThenCompiled)
                          (Builtin.symbolFalse, restChain) ] }

        let elseBranch = buildElseChain ifte.IfElifs ifte.IfElse

        CoreTerm.Match
            { ToMatch = condition
              Cases =
                [ (Builtin.symbolTrue, thenBranch)
                  (Builtin.symbolFalse, elseBranch) ] }

    and private compileRecord (cstate: State) (fields: TBinding<TExpression> list) =
        let compiledFields = List.map (fun b -> removePos b.BindingName, compileExpression cstate b.BindingValue) fields
        RecordExtend { BaseRecord = None; Extension = compiledFields }

    and private compileRecordUsing (cstate: State) (ru: TRecordUsing) =
        let baseRecord = compileExpression cstate ru.RecordBase
        let updates = List.map (fun b -> removePos b.BindingName, compileExpression cstate b.BindingValue) ru.RecordUpdates
        RecordExtend { BaseRecord = Some baseRecord; Extension = updates }

    and private compileSubstitution (cstate: State) (s: TSubstitution) =
        let env =
            List.map (fun b ->
                ({ Symbol = removePos b.BindingName; Children = [] }, compileExpression cstate b.BindingValue))
                s.SubstReplacements

        let inExpr = compileExpression cstate s.SubstTarget
        CoreTerm.Substitution { Env = env; InExpr = inExpr }

    and private compileMixFix (cstate: State) (mixfix: TMixfixOperator) =
        compileExpression cstate mixfix.MixfixExpanded


    //                          //
    // --- Compile Patterns --- //
    //                          //


    and private compilePattern (cstate: State) (pattern: TPattern) : CoreTerm =
        match pattern.Kind with
        | TPatternNode.TPatError err -> failwithf "Cannot compile AST containing error: %s" err.Description

        | TPatternNode.TPatWildcard ->
            CoreTerm.Wildcard

        | TPatternNode.TPatLiteral lit ->
            compileLiteralNode lit

        | TPatternNode.TPatVariable ident ->
            Variable (removePos ident.Written.Name)

        | TPatternNode.TPatConstructor ident ->
            match ident.Kind with
            | SymbolKind.RuleReference name -> simpleSymbol name
            | _ -> simpleSymbol (removePos ident.Written.Name)

        | TPatternNode.TPatApply apply ->
            compileApplyPattern cstate apply.PatApplyHead apply.PatApplyArguments

        | TPatternNode.TPatTuple xs ->
            Builtin.symbolTuple (List.map (compilePattern cstate) xs)

        | TPatternNode.TPatList xs ->
            Builtin.symbolList (List.map (compilePattern cstate) xs)

        | TPatternNode.TPatRecord fields ->
            let compiledFields = List.map (fun b -> removePos b.BindingName, compilePattern cstate b.BindingValue) fields
            RecordExtend { BaseRecord = None; Extension = compiledFields }

        | TPatternNode.TPatMixfix mixfix ->
            compileMixFixPattern cstate mixfix

        | TPatternNode.TPatAs asPatt ->
            let baseTerm = compilePattern cstate asPatt.PatAsBase
            let aliasTerm = compilePattern cstate asPatt.PatAsAlias
            AsClause(baseTerm, aliasTerm)

        | TPatternNode.TPatWhen whenPatt ->
            let baseTerm = compilePattern cstate whenPatt.PatWhenBase
            let guardTerm = compileExpression cstate whenPatt.PatWhenGuard
            WhenClause(baseTerm, guardTerm)

        | TPatternNode.TPatTyped typed ->
            // The compiler is static, so we have a type erasure here.
            compilePattern cstate typed.PatTypedInner

        | TPatternNode.TPatAlternative alts ->
            compileAlternativePattern alts

    and private compileApplyPattern (cstate: State) (lhs: TPattern) (args: TPattern list) =
        let lhsTerm = compilePattern cstate lhs
        let argsTerms = List.map (compilePattern cstate) args

        match lhsTerm with
        | Symbol symb ->
            if symb.Children.IsEmpty then Symbol { symb with Children = argsTerms }
            else failwithf "Application on non-applicable symbol: %s" symb.Symbol

        | Variable v ->
            VariableApply(v, argsTerms)

        | _ ->
            failwithf "Application on non-applicable pattern term: %A" lhsTerm

    and private compileMixFixPattern (cstate: State) (mix: TPatMixfix) =
        compilePattern cstate mix.PatMixfixExpanded

    and private compileAlternativePattern (alts: TLiteral list) =
        let altTerms = alts |> List.map (fun lit -> compileLiteralNode lit.Kind)
        let uv = Variable (FreshName.get "altp")

        let cond =
            match altTerms with
            | [] -> Builtin.symbolFalse
            | [ single ] -> symbol Internals.Eq [ uv; single ]
            | first :: rest ->
                let firstEq = symbol Internals.Eq [ uv; first ]
                List.fold (fun acc lit -> symbol Internals.Or [ acc; symbol Internals.Eq [ uv; lit ] ]) firstEq rest

        WhenClause(uv, cond)


    //                                 //
    // --- Handle Mixfix Notations --- //
    //                                 //


    and private compileNotationExpression (holes: Set<string>) (expr: ExpressionWithPos) : CoreTerm =
        match removePos expr with
        | Identifier id when List.isEmpty id.Qualifier && Set.contains (removePos id.Name) holes ->
            Variable (removePos id.Name)

        | Identifier id ->
            simpleSymbol (string id)

        | Apply { LHS = lhs; Arguments = args } ->
            match removePos lhs with
            | Identifier id ->
                symbol (string id) (List.map (compileNotationExpression holes) args)

            | _ ->
                FunctionalApplication
                    { Base = compileNotationExpression holes lhs
                      Arguments = List.map (compileNotationExpression holes) args }

        | Literal lit ->
            match lit with
            | Literal.Integer i -> CoreTerm.Literal (CoreLiteral.Integer (bigint i))
            | Literal.Float f   -> CoreTerm.Literal (CoreLiteral.Float f)
            | Literal.Char c    -> CoreTerm.Literal (CoreLiteral.Char c)
            | Literal.String s  -> CoreTerm.Literal (CoreLiteral.String s)
            | Literal.Unit      -> Builtin.symbolUnit
            | _ -> failwith "Unsupported literal in notation rewrite"

        | Tuple xs -> Builtin.symbolTuple (List.map (compileNotationExpression holes) xs)
        | List xs  -> Builtin.symbolList (List.map (compileNotationExpression holes) xs)
        | other    -> failwithf "Unsupported expression in notation rewrite: %A" other


    //                                          //
    // --- Top Level Declarations & Modules --- //
    //                                          //


    and private compileTopLevel (cstate: State) (topLevel: TTopLevel) : CoreDefinition option =
        let compiled =
            match topLevel.Node with
            | TTopLevelNode.TRuleDef rule
            | TTopLevelNode.TLetRuleDef rule -> Some (compileRule cstate rule)
            | _ -> None // todo or not compilable

        Option.map (AlphaConversion.alphaConversionDefinition FreshName.get) compiled

    and private compileRule (cstate: State) (rule: TRule) : CoreDefinition =
        let name =
            match rule.RuleSymbol.Kind with
            | SymbolKind.RuleReference mangled when not (System.String.IsNullOrEmpty mangled) -> mangled
            | _ -> removePos rule.RuleSymbol.Written.Name

        let patterns = List.map (compilePattern cstate) rule.RulePatterns
        let lhs = symbol name patterns
        let body = compileExpression cstate rule.RuleBody
        let whenClause = Option.map (compileExpression cstate) rule.RuleWhen
        let strategy = Option.defaultValue Strict (Option.map removePos rule.RuleStrategy)

        CoreDefinition.Rule
            { LHS = lhs
              RHS = body
              WhenClause = whenClause
              Strategy = strategy }

    type public CoreNotationInfo =
        { Name: string
          Associativity: Associativity
          IsCommutative: bool }

    type public NotationEnv = Map<string * int, CoreNotationInfo>

    let private compileModule (modl: TModule) =
        let notations =
            modl.Declarations
            |> List.choose (fun d ->
                match d.Node with
                | TTopLevelNode.TNotationDef nt -> Some nt
                | _ -> None )

        let cstate = { Notations = notations; CurrentHandler = None }

        let notationsInfo =
            notations
            |> List.map (fun nt ->
                let holes =
                    removePos nt.NotationPattern
                    |> List.choose (function HolePart h -> Some h.Node | _ -> None)
                    |> Set.ofList

                let key =
                    match compileNotationExpression holes nt.NotationIs with
                    | Symbol { Symbol = symb; Children = children } -> (symb, children.Length)
                    | other -> failwithf "Notations can only rewrite to symbols, but got `%A`." other

                let value =
                    { Name = removePos nt.NotationName
                      Associativity = removePos nt.NotationAssociativity
                      IsCommutative = removePos nt.NotationCommutative }

                (key, value))
            |> Map.ofList

        let compiledDefs =
            modl.Declarations
            |> List.choose (compileTopLevel cstate)

        (compiledDefs, notationsInfo)

    type public LayeredCompilationEnv =
        { Definitions: CoreDefinition list
          NotationEnv: NotationEnv }

    let public compileModules (modules: TModule list) : LayeredCompilationEnv =
        let compiledResults =
            modules
            |> Array.ofList
            |> Array.Parallel.map compileModule

        let compiledModuleDefinitions, notationsMaps = Array.unzip compiledResults
        let mergedModuleDefinitions = List.concat compiledModuleDefinitions

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

    let public getGlobalCompilationEnv
        (ffiBindings: GlobalFFIBindings)
        (compilationEnvLayers: LayeredCompilationEnv array)
        : GlobalCompilationEnv
        =

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

