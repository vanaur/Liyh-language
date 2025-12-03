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
        =

        let runningVariableName =
            match variableNameSource with
            | FromPattern pattern -> tryGetVariable pattern |> Option.defaultValue (UniqueName.get "")
            | FromString name -> name

        let runningVariable = Variable runningVariableName

        let runningVariableDeclaration =
            CoreLet
                { Pattern = runningVariable
                  Value = initVal
                  IsVariable = true }

        let whileLoopBody =
            TermSequence
                [ body
                  UpdateVariable(
                      runningVariableName,
                      symbol incrementation [ runningVariable; CoreTerm.Literal(CoreLiteral.Integer 1I) ]
                  ) ]

        let whileLoop =
            WhileLoop
                { Predicate = symbol comparison [ runningVariable; endVal ]
                  Body = whileLoopBody }

        TermSequence [ runningVariableDeclaration; whileLoop ]

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
        | Tuple xs -> tupleSymbol (List.map (compileExpression cstate) xs)
        | List xs -> listSymbol (List.map (compileExpression cstate) xs)
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
        collectionAccessSymbol (compileExpression cstate expr) (List.rev indices)

    and private compileListComprehension (cstate: State) (lc: ListComprehension) =
        let compiledItem = compileExpression cstate lc.ItemValue
        let compiledPattern = compilePattern cstate lc.Pattern
        let compiledList = compileExpression cstate lc.ListExpr
        let compiledCond = lc.IfPred |> Option.map (compileExpression cstate)

        let listVar = UniqueName.get "lc_list"
        let lenVar = UniqueName.get "lc_length"
        let indexVar = UniqueName.get "lc_index"
        let resultVar = UniqueName.get "lc_result"

        let bindList =
            CoreLet { Pattern = Variable listVar; Value = compiledList; IsVariable = false }

        let bindLen =
            CoreLet { Pattern = Variable lenVar; Value = symbol "length" [ Variable listVar ]; IsVariable = false }

        let bindResult =
            CoreLet { Pattern = Variable resultVar; Value = symbol "nil" []; IsVariable = true }

        let elementBinding =
            CoreLet { Pattern = compiledPattern; Value = collectionAccessSymbol (Variable listVar) [ Variable indexVar ]; IsVariable = false }

        let appendExpr =
            symbol "cons" [ compiledItem; Variable resultVar ]

        let conditionalAppend =
            match compiledCond with
            | Some cond -> ifte cond appendExpr (Variable resultVar)
            | None -> appendExpr

        let loopBody =
            TermSequence [ elementBinding; UpdateVariable(resultVar, conditionalAppend) ]
            |> flattenTermSequence

        TermSequence [
            bindList
            bindLen
            bindResult
            whileLoop
                (FromString indexVar)
                (symbol "minus" [ Variable lenVar; CoreTerm.Literal (CoreLiteral.Integer 1I) ])
                (CoreTerm.Literal (CoreLiteral.Integer (-1I)))  // Changé de 0 à -1
                loopBody
                "minus"
                "ge"
            Variable resultVar ]

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
                let spart = showSymbol e
                compileInterpolationPart cstate (spart :: result) rest

        let parts = compileInterpolationPart cstate [] (List.rev lstr)
        List.reduce concatSymbol parts

    and private compileLiteral (lit: LiteralWithPos) =
        match removePos lit with
        | Literal.Char c -> CoreTerm.Literal (CoreLiteral.Char c)
        | Literal.Float f -> CoreTerm.Literal (CoreLiteral.Float f)
        | Literal.Integer i -> CoreTerm.Literal (CoreLiteral.Integer (bigint i))
        | Literal.String s -> CoreTerm.Literal (CoreLiteral.String s)
        | Literal.Unit -> simpleSymbol "unit"

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

        let step = Option.defaultValue (simpleSymbol "none") (Option.map (fun s -> symbol "some" [ s ]) step)

        symbol "range" [ start; step; stop ]

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
            (if isDownTo then "minus" else "plus")
            (if isDownTo then "geq" else "leq")

    and private compileForIn (cstate: State) (loop: ForIn) =
        let compiledPattern = compilePattern cstate loop.Pattern
        let compiledList = compileExpression cstate loop.ListExpr
        let compiledBody = compileExpression cstate loop.Body

        let listVar = UniqueName.get "forin_list"
        let lenVar = UniqueName.get "forin_length"
        let indexVar = UniqueName.get "forin_index"

        // Stores the list in a variable
        let bindList =
            CoreLet {
                Pattern = Variable listVar
                Value = compiledList
                IsVariable = false }

        // Binds an item in the list to the body pattern
        let bindElement =
            CoreLet {
                Pattern = compiledPattern
                Value = collectionAccessSymbol (Variable listVar) [ Variable indexVar ]
                IsVariable = false }

        // Stores the list's length in a variable
        let bindLength =
            CoreLet {
                Pattern = Variable lenVar
                Value = symbol "length" [ Variable listVar ]
                IsVariable = false }

        TermSequence [
            bindList
            bindLength
            whileLoop
                (FromString indexVar)
                (CoreTerm.Literal (CoreLiteral.Integer 0I))
                (Variable lenVar)
                (TermSequence [ bindElement; compiledBody ] |> flattenTermSequence)
                "plus"
                "le" ]

    and private compileLamda (cstate: State) (lambda: Lambda) =
        let parameters = 
            lambda.Patterns
            |> List.map (fun patt ->
                match compilePattern cstate patt with
                | Variable v -> v
                | Symbol { Symbol = s; Children = [] } -> s
                | _ -> failwith "Only support variable pattern for now!")

        let body = compileExpression cstate lambda.Body

        // Calculates the free variables in the body of the lambda
        let boundParameters = Set.ofList parameters
        let freeVariables, asDefined = freeVariables boundParameters body

        // Remove 'as-defined' variables from the captured env
        let freeVariables = freeVariables - asDefined

        let capturedEnv =
            freeVariables
            |> Set.fold (fun env var -> Map.add var (Variable var) env) Map.empty

        Closure
            { Env = capturedEnv
              IsEvaluated = false
              Parameters = parameters
              Value = body }

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
        let cases = [ (trueSymbol, thenBranch); (falseSymbol, Option.defaultValue (simpleSymbol "unit") elseBranch) ]

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

    // --- Patterns --- //

    and private compilePattern (cstate: State) (pattern: PatternWithPos) =
        match removePos pattern with
        | VariablePattern v -> Variable v
        | SymbolPattern s -> simpleSymbol (string s)
        | ApplyPattern(lhs, args) -> compileApplyPattern cstate lhs args
        | LiteralPattern lit -> compileLiteral lit
        | TuplePattern xs -> tupleSymbol (List.map (compilePattern cstate) xs)
        | ListPattern xs -> listSymbol (List.map (compilePattern cstate) xs)
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
        let alternatives = listSymbol (List.map compileLiteral alternatives)
        let uv = Variable (UniqueName.get "altp")
        
        WhenClause(uv, containsSymbol alternatives uv)

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
            | other -> failwithf "Todo: %A" other

        AlphaConversion.alphaConversionDefinition UniqueName.get compiled

    and private compileRule (cstate: State) (rule: Rule) =
        let body = compileExpression cstate rule.Body
        let name = removePos rule.Name
        let patterns = List.map (compilePattern cstate) rule.Patterns
        let whenClause = Option.map (compileExpression cstate) rule.WhenClause
        let strategy = Option.defaultValue Innermost rule.Strategy

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
        let strategy = Option.defaultValue Innermost handler.Strategy

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
        |> sortRules
        |> List.map (compileDefinition cstate)

    // TODO: sort handlers, too!

    and private sortRules (definitions: TopLevelWithPos list) =

        let sorter (rules: TopLevelWithPos list) =
            let strategyOrder = function
                | Some Outermost -> 0
                | Some Innermost -> 1
                | Some Invalid -> 2
                | Some Memoize -> 1
                | None -> 1

            let compareRules (i1, { Node = Rule r1 }) (i2, { Node = Rule r2 }) =
                let s1 = strategyOrder r1.Strategy
                let s2 = strategyOrder r2.Strategy
                if s1 <> s2 then compare s1 s2
                else compare i1 i2

            rules
            |> List.mapi (fun i rule -> i, rule)
            |> List.sortWith compareRules
            |> List.map snd

        let rules, others = definitions |> List.partition _.Node.IsRule
        let rules = sorter rules

        others @ rules

    /// Compiles each modules of the list to the LiyhCore intermediate representation.
    /// The compilation is done in parallel.
    and public compileModules (modules: ModuleInfo list) =
        modules
        |> Array.ofList
        |> Array.Parallel.collect (compileModule >> Array.ofList)

