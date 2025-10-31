#nowarn "25"
#nowarn "26"
#nowarn "46"

namespace Liyh.Execution.Core

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

module Helper =
    open Liyh.Syntax.SyntaxTree

    let public symbol (name: string) (args: CoreTerm list) =
        Symbol
            { Symbol = name
              Children = args
              IsVariable = false }

    let public simpleSymbol (name: string) =
        symbol name []

    let public variableSymbol (name: string) (args: CoreTerm list) =
        let (Symbol sym) = symbol name args
        Symbol { sym with IsVariable = true }

    let public tuple (xs: CoreTerm list) =
        symbol "tuple" xs

    let public list (xs: CoreTerm list) =
        let cons h t = symbol "cons" [ h; t ]
        let nil = simpleSymbol "nil"

        let loop lst =
            let rec loopAcc acc =
                function
                | [] -> acc
                | x :: xs -> loopAcc (cons x acc) xs

            loopAcc nil (List.rev lst)

        loop xs

    let public collectionAccess (expr: CoreTerm) (indices: CoreTerm list) =
        symbol "collection_access" [ expr; tuple indices ]

    let public trueSymbol =
        simpleSymbol "true"

    let public falseSymbol =
        simpleSymbol "false"

    let public show (arg: CoreTerm) =
        symbol "printing_show" [ arg ]

    let public concat (a: CoreTerm) (b: CoreTerm) =
        symbol "concat" [ a; b ]

    let public contains (lst: CoreTerm) (arg: CoreTerm) =
        symbol "contains" [ lst; arg ]

    let public ifte (if': CoreTerm) (then': CoreTerm) (else': CoreTerm) =
        CoreTerm.Match
            { ToMatch = if'
              Cases = [ (trueSymbol, then'); (falseSymbol, else') ] }

    type public WhileLoopVariableSource =
        | FromPattern of PatternWithPos
        | FromString of string

    let private tryGetVariable (patt: PatternWithPos) =
        match removePos patt with
        | VariablePattern varName -> Some varName
        | Wildcard -> None
        | other -> failwithf "Expected variable or wildcard, got `%A`." other

    let public whileLoop
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

    let rec public flattenTermSequence (term: CoreTerm) =
        match term with
        | TermSequence terms ->
            let flattenedTerms =
                terms
                |> List.collect (fun t ->
                    match flattenTermSequence t with
                    | TermSequence nestedTerms -> nestedTerms
                    | other -> [ other ])

            TermSequence flattenedTerms
        | Symbol symbol ->
            Symbol
                { symbol with
                    Children = symbol.Children |> List.map flattenTermSequence }
        | Variable _ -> term
        | CoreTerm.Literal _ -> term
        | CoreTerm.RecordExtend { BaseRecord = baseRecord; Extension = fields } ->
            CoreTerm.RecordExtend {
                BaseRecord = Option.map flattenTermSequence baseRecord
                Extension = fields |> List.map (fun (name, value) -> (name, flattenTermSequence value))
            }
        | Closure { Env = env
                    Parameters = params
                    Value = body } ->
            Closure
                { Env = env
                  Parameters = params
                  Value = flattenTermSequence body }
        | FunctionalApplication { Base = func; Arguments = args } ->
            FunctionalApplication { Base = flattenTermSequence func; Arguments = args |> List.map flattenTermSequence }
        | CoreTerm.CoreLet letExpr ->
            CoreTerm.CoreLet
                { letExpr with
                    Pattern = flattenTermSequence letExpr.Pattern
                    Value = flattenTermSequence letExpr.Value }
        | WhileLoop whileExpr ->
            WhileLoop
                { whileExpr with
                    Predicate = flattenTermSequence whileExpr.Predicate
                    Body = flattenTermSequence whileExpr.Body }
        | UpdateVariable(var, value) -> UpdateVariable(var, flattenTermSequence value)
        | WhenClause(condition, consequence) -> WhenClause(flattenTermSequence condition, flattenTermSequence consequence)
        | AsClause(pattern, value) -> AsClause(flattenTermSequence pattern, flattenTermSequence value)
        | CoreTerm.Match { ToMatch = toMatch; Cases = cases } ->
            CoreTerm.Match
                { ToMatch = flattenTermSequence toMatch
                  Cases = List.map (fun (a, b) -> flattenTermSequence a, flattenTermSequence b) cases }
        | Resume { Rewrite = rewrite; State = state } ->
            Resume
                { Rewrite = flattenTermSequence rewrite
                  State = flattenTermSequence state }
        | Handle { Handler = handler
                   State = state
                   ToHandle = toHandle } ->
            Handle
                { Handler = handler
                  State = flattenTermSequence state
                  ToHandle = flattenTermSequence toHandle }
        | CoreTerm.Wildcard -> term

    /// Retrieves variables that are not defined in `term` nor present in `boundVars`.
    let public freeVariables (boundVars: Set<string>) (term: CoreTerm) =
        let mutable internalVars = Set.empty
        let mutable asDefined = Set.empty

        let rec loop =
            function
            | CoreTerm.Variable v ->
                if not (Set.contains v boundVars) && not (Set.contains v internalVars)
                then Set.singleton v
                else Set.empty

            | CoreTerm.CoreLet { Pattern = patt; Value = value } ->
                internalVars <- Set.union internalVars (loop patt)
                loop value

            | CoreTerm.Symbol symbol ->
                if symbol.IsVariable then loop (Variable symbol.Symbol)
                else symbol.Children |> List.map loop |> Set.unionMany

            | CoreTerm.TermSequence terms ->
                terms |> List.map loop |> Set.unionMany

            | CoreTerm.RecordExtend { BaseRecord = baseRecord; Extension = fields } ->
                let a = baseRecord |> Option.map loop |> Option.defaultValue Set.empty
                let b = fields |> List.map (snd >> loop) |> Set.unionMany
                Set.union a b

            | CoreTerm.Closure closure ->
                internalVars <- Set.union internalVars (Set.ofList closure.Parameters)
                loop closure.Value

            | CoreTerm.FunctionalApplication { Base = fn; Arguments = args } ->
                let a = loop fn
                let b = args |> List.map loop |> Set.unionMany
                Set.union a b

            | CoreTerm.WhenClause(patt, pred) ->
                let a = loop patt
                let b = loop pred
                Set.union a b

            | CoreTerm.AsClause(patt, as') ->
                let a = loop patt
                let b = loop as'

                internalVars <- Set.union internalVars a
                internalVars <- Set.union internalVars b

                asDefined <- Set.union asDefined b

                a

            | CoreTerm.Match match' ->
                let a = loop match'.ToMatch
                let casesVars, valuesVars =
                    match'.Cases
                    |> List.map (fun (patt, value) -> loop patt, loop value)
                    |> List.unzip

                let casesVars = Set.unionMany casesVars
                internalVars <- Set.union internalVars casesVars

                let valuesVars = Set.unionMany valuesVars
                let valuesVars = Set.difference valuesVars casesVars

                Set.union a valuesVars

            | CoreTerm.WhileLoop whileLoop ->
                let a = loop whileLoop.Predicate
                let b = loop whileLoop.Body

                Set.union a b
            
            | CoreTerm.UpdateVariable(v, value) ->
                // We can potentially detect here if an external variable (`v`) is updated, do we throw an error?
                // → Normally, this is handled in the previous phases.
                loop value

            | CoreTerm.Resume resume ->
                let a = loop resume.Rewrite
                let b = loop resume.State
                Set.union a b
            
            | CoreTerm.Handle handle ->
                let a = loop handle.State
                let b = loop handle.ToHandle
                Set.union a b

            | CoreTerm.Wildcard | CoreTerm.Literal _ -> Set.empty
            | other -> failwithf "Todo (freeVariables): %A" other

        loop term, asDefined

module CoreTermSubstitution =

    let rec public replaceCoreTerm (substitutions: Map<CoreTerm, CoreTerm>) (term: CoreTerm) =
        match Map.tryFind term substitutions with
        | Some replacement -> replacement
        | None ->
            match term with
            | Symbol sym ->
                let newChildren = List.map (replaceCoreTerm substitutions) sym.Children
                if newChildren = sym.Children then term
                else Symbol { sym with Children = newChildren }

            | Variable _ -> term
            | Literal _ -> term

            | RecordExtend ext ->
                let newBase = Option.map (replaceCoreTerm substitutions) ext.BaseRecord
                let newExtension = List.map (fun (k, v) -> (k, replaceCoreTerm substitutions v)) ext.Extension
                if newBase = ext.BaseRecord && newExtension = ext.Extension then
                    term
                else
                    RecordExtend { ext with BaseRecord = newBase; Extension = newExtension }

            | Match m ->
                let newToMatch = replaceCoreTerm substitutions m.ToMatch
                let newCases = List.map (fun (pat, body) ->
                    let newPat = replaceCoreTerm substitutions pat
                    let newBody = replaceCoreTerm substitutions body
                    (newPat, newBody)) m.Cases
                if newToMatch = m.ToMatch && newCases = m.Cases then
                    term
                else
                    Match { m with ToMatch = newToMatch; Cases = newCases }

            | Closure c ->
                let newEnv = Map.map (fun _ v -> replaceCoreTerm substitutions v) c.Env
                let newValue = replaceCoreTerm substitutions c.Value
                if newEnv = c.Env && newValue = c.Value then
                    term
                else
                    Closure { c with Env = newEnv; Value = newValue }

            | FunctionalApplication fa ->
                let newBase = replaceCoreTerm substitutions fa.Base
                let newArgs = List.map (replaceCoreTerm substitutions) fa.Arguments
                if newBase = fa.Base && newArgs = fa.Arguments then
                    term
                else
                    FunctionalApplication { fa with Base = newBase; Arguments = newArgs }

            | TermSequence terms ->
                let newTerms = List.map (replaceCoreTerm substitutions) terms
                if newTerms = terms then
                    term
                else
                    TermSequence newTerms

            | CoreLet l ->
                let newPattern = replaceCoreTerm substitutions l.Pattern
                let newValue = replaceCoreTerm substitutions l.Value
                if newPattern = l.Pattern && newValue = l.Value then
                    term
                else
                    CoreLet { l with Pattern = newPattern; Value = newValue }

            | WhileLoop w ->
                let newPred = replaceCoreTerm substitutions w.Predicate
                let newBody = replaceCoreTerm substitutions w.Body
                if newPred = w.Predicate && newBody = w.Body then
                    term
                else
                    WhileLoop { w with Predicate = newPred; Body = newBody }

            | UpdateVariable (name, expr) ->
                let newExpr = replaceCoreTerm substitutions expr
                if newExpr = expr then
                    term
                else
                    UpdateVariable (name, newExpr)

            | Resume r ->
                let newRewrite = replaceCoreTerm substitutions r.Rewrite
                let newState = replaceCoreTerm substitutions r.State
                if newRewrite = r.Rewrite && newState = r.State then
                    term
                else
                    Resume { r with Rewrite = newRewrite; State = newState }

            | Handle h ->
                let newHandler = h.Handler // string, inchangé
                let newState = replaceCoreTerm substitutions h.State
                let newToHandle = replaceCoreTerm substitutions h.ToHandle
                if newState = h.State && newToHandle = h.ToHandle then
                    term
                else
                    Handle { h with State = newState; ToHandle = newToHandle }

            | WhenClause (cond, body) ->
                let newCond = replaceCoreTerm substitutions cond
                let newBody = replaceCoreTerm substitutions body
                if newCond = cond && newBody = body then
                    term
                else
                    WhenClause (newCond, newBody)

            | AsClause (pat, body) ->
                let newPat = replaceCoreTerm substitutions pat
                let newBody = replaceCoreTerm substitutions body
                if newPat = pat && newBody = body then
                    term
                else
                    AsClause (newPat, newBody)

            | Wildcard -> term

[<RequireQualifiedAccess>]
module CoreCompiler =
    open Liyh.Module
    open Liyh.Syntax.SyntaxTree
    open Helper

    type private State =
        { Notations: Notation list }

        static member Empty =
            { Notations = List.empty }

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
        | Tuple xs -> tuple (List.map (compileExpression cstate) xs)
        | List xs -> list (List.map (compileExpression cstate) xs)
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
            | Symbol symb -> Symbol { symb with Children = child :: symb.Children }
            | Variable v -> variableSymbol v [ child ]
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
        collectionAccess (compileExpression cstate expr) (List.rev indices)

    and private compileListComprehension (cstate: State) (lc: ListComprehension) =
        let compiledItem = compileExpression cstate lc.ItemValue
        let compiledPattern = Variable lc.Pattern
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
            CoreLet { Pattern = compiledPattern; Value = collectionAccess (Variable listVar) [ Variable indexVar ]; IsVariable = false }

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
            if symb.Children.IsEmpty then Symbol { symb with Children = args }
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
                let spart = show e
                compileInterpolationPart cstate (spart :: result) rest

        let parts = compileInterpolationPart cstate [] (List.rev lstr)
        List.reduce concat parts

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
                Value = collectionAccess (Variable listVar) [ Variable indexVar ]
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

        Resume { Rewrite = value; State = state }

    // --- Patterns --- //

    and private compilePattern (cstate: State) (pattern: PatternWithPos) =
        match removePos pattern with
        | VariablePattern v -> Variable v
        | SymbolPattern s -> simpleSymbol (string s)
        | ApplyPattern(lhs, args) -> compileApplyPattern cstate lhs args
        | LiteralPattern lit -> compileLiteral lit
        | TuplePattern xs -> tuple (List.map (compilePattern cstate) xs)
        | ListPattern xs -> list (List.map (compilePattern cstate) xs)
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
            if symb.Children.IsEmpty then Symbol { symb with Children = args }
            else failwithf "Application on non-applicable symbol"
        | Variable v -> variableSymbol v args
        | _ -> failwith "Application on non-applicable symbol"

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
        let alternatives = list (List.map compileLiteral alternatives)
        let uv = Variable (UniqueName.get "altp")
        
        WhenClause(uv, contains alternatives uv)

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

