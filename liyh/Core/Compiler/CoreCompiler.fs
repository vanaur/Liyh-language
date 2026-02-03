#nowarn "25"
#nowarn "26"
#nowarn "46"
namespace Liyh.Core

[<RequireQualifiedAccess>]
module private UniqueName =
    open System.Collections.Concurrent
    open System.Text

    let private counters = ConcurrentDictionary<string,int>()

    let private sanitize (s: string) =
        if System.String.IsNullOrWhiteSpace s then "x"
        else
            let sb = StringBuilder()
            for c in s do
                if System.Char.IsLetterOrDigit c || c = '_' then sb.Append(c) |> ignore
                else sb.Append('_') |> ignore
            sb.ToString()

    let public get (baseName: string) =
        let baseName = sanitize baseName
        let id = counters.AddOrUpdate(baseName, 1, fun _ old -> old + 1)
        sprintf "_v%s%d" baseName id

module ExternTypes =
    open System
    open System.Text
    open System.Security.Cryptography
    open System.Collections.Concurrent
    open Liyh.Syntax.SyntaxTree
    open Liyh.FFI.CFFI

    let private structCache = ConcurrentDictionary<string, System.Type>()

    let private hashShort (s: string) =
        use sha = SHA256.Create()
        let bytes = Encoding.UTF8.GetBytes(s)
        let hash = sha.ComputeHash(bytes)

        BitConverter.ToString(hash, 0, 8).Replace("-", "").ToLowerInvariant()

    let rec private typeSignature (t: WithPos<Type>) =
        let rec qnameToString { Node = { Qualifier = qual; Name = { Node = name } } } =
            let qualPart = String.concat "." (qual |> List.map (fun q -> q.Node))
            if String.IsNullOrEmpty qualPart then name else qualPart + "." + name

        match removePos t with
        | NamedType idwp ->
            qnameToString idwp

        | ParametrizedType(idwp, args) ->
            let baseName = qnameToString idwp
            let argsS = args |> List.map typeSignature |> String.concat ","
            $"{baseName}<{argsS}>"

        | RowRecordType fields ->
            let fieldsS =
                fields
                |> List.map (fun (fname, fty) -> $"{fname}:{typeSignature fty}")
                |> String.concat ";"
            $"record{{{fieldsS}}}"

        | other ->
            failwithf "Unsupported AST type in signature: %A" other

    let rec public externTypeToCType (externType: WithPos<Type>) =
        match removePos externType with
        | NamedType idwp ->
            match idwp.Node.Qualifier with
            | [{ Node = "C" }] ->
                match idwp.Node.Name.Node with
                | "Int32"   -> CType.Int32
                | "Int64"   -> CType.Int64
                | "Char"    -> CType.Char
                | "Float32" -> CType.Float32
                | "Single"  -> CType.Single
                | "Float64" -> CType.Float64
                | "String"  -> CType.String
                | "Void"    -> CType.Void
                | "Ptr"     -> CType.Pointer CType.Void
                | unknown   -> failwithf "Unknown C type: %s" unknown
            | _ ->
                failwithf "Invalid type for external signature: %s" (string idwp.Node)

        | ParametrizedType(idwp, ps) ->
            let mainType = externTypeToCType (withPosOf externType (NamedType idwp))
            let argTypes = List.map externTypeToCType ps

            match mainType, argTypes with
            | CType.Pointer _, [a] -> CType.Pointer a
            | _ -> failwithf "Unsupported parametrized type: main=%A, args=%A" mainType argTypes

        | RowRecordType fields ->
            let sigStr = typeSignature externType
            structCache.GetOrAdd(sigStr, Func<string, System.Type>(fun _ ->
                let mapper (name, ty) =
                    { Name = name
                      FieldType = externTypeToCType ty
                      Offset = None }

                let fieldArray = fields |> List.toArray |> Array.map mapper
                let shortHash = hashShort sigStr
                let structName = $"struct_{shortHash}"
                defineStruct structName fieldArray StructLayout.Sequential
            ))
            |> CType.Struct

        | RuleType _ -> CType.Pointer CType.Void
        | other -> failwithf "Unsupported type in extern declaration: %s" (string other)

[<RequireQualifiedAccess>]
module CoreCompiler =
    open Liyh.Module
    open Liyh.Syntax.SyntaxTree
    open Liyh.FFI.CFFI
    open Liyh.Core.Helper

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
            | FromPattern pattern -> Option.defaultValue (UniqueName.get "itr") (tryGetVariable pattern)
            | FromString name -> name

        let runningVariable = Variable runningVariableName

        let runningVariableDeclaration =
            CoreLet
                { Pattern = runningVariable
                  Value = initVal
                  IsVariable = true }

        // Evaluate the end value once before the loop.
        let limitName = UniqueName.get "limit"
        let limitVariable = Variable limitName

        let limitDeclaration = 
            CoreLet
                { Pattern = limitVariable
                  Value = endVal
                  IsVariable = false }

        // Evaluate the step value once before the loop
        let stepName = UniqueName.get "step"
        let stepVariable = Variable stepName

        let stepDeclaration = 
            CoreLet 
                { Pattern = stepVariable
                  Value = stepValue |> Option.defaultValue (CoreTerm.Literal(CoreLiteral.Integer 1I))
                  IsVariable = false }

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
        | ReAssign(v, e) -> UpdateVariable(v, compileExpression cstate e)
        | HandleEffect handle -> compileHandleEffect cstate handle
        | ResumeWith resume -> compileResume cstate (removePos resume)
        | Substitution(env, inExpr) -> compileSubstitution cstate env inExpr
        | UsingContext ctx -> compileUsingContext cstate ctx
        | other -> failwithf "Todo: %A" other

        |> flattenTermSequence

    and private compileUFCS (cstate: State) (ufcs: UFCS) =
        let inline apply converted child =
            match converted with
            | Symbol symb -> copySymbolWithNewChildren symb (child :: symb.Children)
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

            let cursorVarName = UniqueName.get "lc_cursor"
            let tailVarName = UniqueName.get "lc_tail"
            let resultVarName = UniqueName.get "lc_result"
            let nilVarName = UniqueName.get "lc_nil"
            
            let cursorVar = Variable cursorVarName
            let tailVar = Variable tailVarName
            let resultVar = Variable resultVarName
            let nilVar = Variable nilVarName

            let bindCursor = CoreLet { Pattern = cursorVar; Value = compiledList; IsVariable = true }
            let bindResult = CoreLet { Pattern = resultVar; Value = Builtin.symbolNil; IsVariable = true }
            let bindNil = CoreLet { Pattern = nilVar; Value = Builtin.symbolNil; IsVariable = false }

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
                        IsVariable = false 
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
            let varName = UniqueName.get name
            let varTerm = Variable varName
            let binding = CoreLet { Pattern = varTerm; Value = value; IsVariable = isVar }
            (varName, varTerm, binding)

        let startExpr = compileExpression cstate range.RangeStart
        let stopExpr = compileExpression cstate range.RangeStop
        
        let _, startVar, bindStart = bind "lc_start" startExpr false
        let _, stopVar, bindStop   = bind "lc_stop"  stopExpr false
        let resultName, resultVar, bindResult = bind "lc_result" Builtin.symbolNil true
        
        let loopName = UniqueName.get "lc_i"
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
                CoreLet { Pattern = compiledPattern; Value = loopCounterVar; IsVariable = false }
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

    and private compileApply (cstate: State) { LHS = lhs; Arguments = args } =
        let lhs = compileExpression cstate lhs
        let args = List.map (compileExpression cstate) args

        match lhs with
        | Symbol symb ->
            if symb.Children.IsEmpty then copySymbolWithNewChildren symb args
            else FunctionalApplication { Base = lhs; Arguments = args }

        | Closure _ -> FunctionalApplication { Base = lhs; Arguments = args }
        | x -> FunctionalApplication { Base = x; Arguments = args }

    and private compileInterpolatedString (cstate: State) (lstr: InterpolatedPart list) =

        let rec compileInterpolationPart cstate result =
            function
            | [] -> result
            | Str s :: rest ->
                let part = CoreTerm.Literal (CoreLiteral.String s)
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
        match cstate.Notations |> List.tryFind (fun x -> removePos x.NotationName = mixfix.Name) with
        | None -> failwithf "Unknown notation: %s" mixfix.Name
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
              IsVariable = isVar }

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

            let cursorName = UniqueName.get "iter_cursor"
            let tailName = UniqueName.get "iter_tail"
            let nilName = UniqueName.get "iter_nil"

            let cursorVar = Variable cursorName
            let tailVar = Variable tailName
            let nilVar = Variable nilName

            let bindCursor =
                CoreLet {
                    Pattern = cursorVar
                    Value = compiledList
                    IsVariable = true }

            let bindNil =
                CoreLet {
                    Pattern = nilVar
                    Value = Builtin.symbolNil
                    IsVariable = false }

            let consPattern = Builtin.symbolCons compiledPattern tailVar

            let loopBody =
                TermSequence [
                    CoreLet { 
                        Pattern = consPattern
                        Value = cursorVar
                        IsVariable = false }
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
            let varName = UniqueName.get name
            let varTerm = Variable varName
            let binding = CoreLet { Pattern = varTerm; Value = baseExpr; IsVariable = false }
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
                    let freshArgName = UniqueName.get "lam_arg"
                    let binding =
                        CoreLet
                            { Pattern = other
                              Value = Variable freshArgName
                              IsVariable = false }
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
        let elseBranch = Option.map (compileExpression cstate) ifte.ElseBranch

        let toMatch = condition
        let cases =
            [ (Builtin.symbolTrue, thenBranch)
              (Builtin.symbolFalse, Option.defaultValue (Builtin.symbolUnit) elseBranch) ]

        CoreTerm.Match
            { ToMatch = toMatch
              Cases = cases }

    and private compileRecord (cstate: State) (fields: List<string * ExpressionWithPos>) =
        let fields = List.map (fun (name, value) -> name, compileExpression cstate value) fields
        RecordExtend { BaseRecord = None; Extension = fields }

    and private compileRecordExtend (cstate: State) (baseRecord: ExpressionWithPos) (fields: List<string * ExpressionWithPos>) =
        let baseRecord = compileExpression cstate baseRecord
        let fields = List.map (fun (name, value) -> name, compileExpression cstate value) fields

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

    and private compileSubstitution (cstate: State) (env: list<string * ExpressionWithPos>) (inExpr: ExpressionWithPos) =
        let env = List.map (fun (a, b) -> let (Symbol sym) = simpleSymbol a in sym, compileExpression cstate b) env
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
        | MixfixOperatorPattern(name, args) -> compileMixFixPattern cstate name args
        | RecordPattern fields -> compileRecordPattern cstate fields
        | AlternativePattern xs -> compileAlternativePattern xs
        | TypedPattern(patt, ty) -> compileTypedPattern cstate patt ty
        | other -> failwithf "Todo: %A" other

    and private compileApplyPattern (cstate: State) (lhs: PatternWithPos) (args: PatternWithPos list) =
        let lhs = compilePattern cstate lhs
        let args = List.map (compilePattern cstate) args

        match lhs with
        | Symbol symb ->
            if symb.Children.IsEmpty then copySymbolWithNewChildren symb args
            else failwithf "Application on non-applicable symbol: %s" (PrettyPrinter.prettyPrintExpr lhs)
        | Variable v -> variableSymbol v args
        | _ -> failwithf "Application on non-applicable symbol: %s" (PrettyPrinter.prettyPrintExpr lhs)

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
        let uv = Variable (UniqueName.get "altp")

        WhenClause(uv, Builtin.symbolContains alternatives uv)

    and private compileRecordPattern (cstate: State) (fields: (string * PatternWithPos) list) =
        let fields = List.map (fun (name, value) -> name, compilePattern cstate value) fields
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
                | HolePart h -> Some (Variable h)
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
            | TopLevel.Rule rule -> compileRule cstate rule
            | TopLevel.Handler handler -> compileHandler cstate handler
            | TopLevel.Extern extrn -> compileExtern extrn
            | TopLevel.Context context -> compileContext cstate context
            | other -> failwithf "Todo: %A" other

        AlphaConversion.alphaConversionDefinition UniqueName.get compiled

    and private compileRule (cstate: State) (rule: Rule) =
        let body = compileExpression cstate rule.Body
        let name = removePos rule.Name
        let patterns = List.map (compilePattern cstate) rule.Patterns
        let whenClause = Option.map (compileExpression cstate) rule.WhenClause
        let strategy = Option.defaultValue Strict rule.Strategy

        let lhs = symbol name patterns

        CoreDefinition.Rule
            { LHS = lhs
              RHS = body
              WhenClause = whenClause
              Strategy = strategy }

    and private compileHandler (cstate: State) (handler: Handler) =
        let cstate = { cstate with CurrentHandler = Some handler.Name }

        let body = compileExpression cstate handler.Body
        let name = handler.Name
        let hstate = compilePattern cstate handler.State
        let pattern = compilePattern cstate handler.Pattern
        let whenClause = Option.map (compileExpression cstate) handler.WhenClause
        let strategy = Option.defaultValue Strict handler.Strategy

        let lhs = pattern

        CoreDefinition.Handler
            { HandlerName = name
              LHS = lhs
              RHS = body
              State = hstate
              WhenClause = whenClause
              Strategy = strategy }

    and private compileExtern (extrn: Extern) =
        let lib = DynLib.Load extrn.Library.Node
        let functions =
            extrn.Content
            |> List.map (fun sgn ->
                let returnType =
                    sgn.ReturnType
                    |> Option.map ExternTypes.externTypeToCType
                    |> Option.defaultValue CType.Void

                let parameters =
                    sgn.ArgumentsType
                    |> List.map ExternTypes.externTypeToCType
                    |> Array.ofList

                let funSig =
                    { Name = sgn.Name
                      ReturnType = returnType
                      Parameters = parameters }

                sgn.Name, funSig)

            |> Map.ofList

        CoreDefinition.Extern
            { LibraryName = string (removePos extrn.AsName)
              Library = lib
              Functions = functions }

    and private compileContext (cstate: State) (context: Context) =
        CoreDefinition.Context
            { ContextName = string (removePos context.Name)
              Content = List.map (compileDefinition cstate) context.Content
              Using = List.map (removePos >> string) context.Using }

    // --- Module --- //

    and private compileModule (modl: ModuleInfo) =
        let definitions = Definitions.classifyDefinitions modl

        let notations =
            definitions
            |> Map.tryFind Definitions.DefinitionType.Notation
            |> Option.map (List.map (removePos >> function Notation notation -> notation))
            |> Option.defaultValue []

        let cstate = { State.Empty with Notations = notations }
        let definitions = Map.remove Definitions.DefinitionType.Notation definitions

        definitions.Values
        |> List.ofSeq
        |> List.concat
        |> List.map (compileDefinition cstate)

    /// Compiles each modules of the list to the LiyhCore intermediate representation.
    /// The compilation is done in parallel.
    and public compileModules (modules: ModuleInfo list) =
        modules
        |> Array.ofList
        |> Array.Parallel.collect (compileModule >> Array.ofList)

