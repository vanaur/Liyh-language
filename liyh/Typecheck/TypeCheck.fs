#nowarn "25"
namespace Liyh.TypeCheck

module rec TypeCheck =
    open Liyh.Utils.ErrorReporter
    open Liyh.Syntax.SyntaxTree

    [<RequireQualifiedAccess>]
    module private ErrorCodes =

        // E-XYZ
        // E=ERROR, X=COMPILER-CURRENT-PASS, YZ=ERROR-CODE
        // TypeCheck : pass 3

        type public ErrorCode =

            /// A rule was invoked, but it is explicitly invalid given the arguments provided.
            | MatchedInvalidRuleError = 1

            /// Too many constraints and not enough values: need help from the user with a type annotation.
            | NeedTypeAnnotationError = 2

            /// Invalid type unification.
            | TypeMismatchError = 3

            /// Invalid alternative pattern (unexpected type).
            | BadAlternativeTypeError = 4

            /// Two rules have the same pattern and are indistinguishable.
            | RedundantRuleError = 5

            /// A rule can never be achieved due to the associated previous definitions.
            | UnreachableRuleError = 6

            /// Variable (constant or mutable) does not exist in the current scope.
            | UnfoundVariableError = 7

            /// Variable applied to one or more arguments, but the type of the variable is not a function.
            | NotApplicableVariableError = 8

            /// An intermediate expression in an expression block is not of type Unit.
            | BadIntermediateExpressionSequenceTypeError = 9

            /// A value is reassigned to a variable marked as immutable.
            | ImmutableVariableMutationError = 10

            /// The return type of a while loop is non-Unit.
            | LoopReturnTypeError = 11

            /// A variable in a nonlinear pattern has a different type from its first instance.
            | IncompatibleNonLinearVariablesError = 12

            /// The collection has not the required dimension.
            | InvalidRankCollectionAccess = 13

            /// An external variable is mutated inside a lambda expression.
            | ReadOnlyLambdaError = 14

        let inline public format (code: ErrorCode) =
            sprintf "E3%02d" (int code)


    //                                                        //
    // --- Basic definitions and elements for unification --- //
    //                                                        //


    type public Identifier =
        { Qualifier: string list
          Name: string }

        static member Simple name =
            { Qualifier = []; Name = name }

        override this.ToString() =
            let qualifiers = this.Qualifier
            String.concat "." (qualifiers @ [ this.Name ])

    /// Converts from syntax tree's identifier to typechecker's identifier.
    let private astIdentifierToMonoTypeIdentifier (id: Liyh.Syntax.SyntaxTree.Identifier) =
        { Qualifier = List.map removePos id.Qualifier
          Name = removePos id.Name }

    /// Represents a basic monomorphic type.
    type public MonoType =
        | TName of Identifier
        | TVar of string
        | TFun of MonoType list * MonoType
        | TTuple of MonoType list
        | TRecord of (string * MonoType) list
        | TApp of Identifier * MonoType list
        | TEffect of MonoType * Identifier list
        | TSymbol of TSymbol
        | TAny

        static member tsymbol =
            TSymbol { U = () }

    /// Represents the informations the symbol type would keep. For the moment, there is nothing to keep.
    and public TSymbol =
        { U : unit } // I don't know what to put in there, but if we want to expand later, it will make things easier.

    type private TypeScheme = Scheme of string list * MonoType

    /// Represents important and useful information for a rewrite rule or handler.
    type private SymbolInfo =
        {
            /// The position of the symbol's definition in the code.
            Position: FParsec.Position

            /// Inferred types for parameters of the rule.
            ParametersTypes: MonoType list

            /// Patterns ("parameters") of the rule.
            Patterns: PatternWithPos list

            /// Inferred return type for the rule.
            ReturnType: MonoType

            /// The rewriting part of the rule.
            Body: ExpressionWithPos option

            /// Type scheme for type inference associated to the rule.
            Scheme: TypeScheme

            /// The rewriting strategy of the rule (innermost, outermost, invalid).
            Strategy: RewritingStrategy

            /// Indicates whether the rule is globally conditional.
            HasWhenClause: bool

            /// The number of parameters the rule expect.
            Arity: int

            /// The unique hash for this rule.
            Hash: int }

    /// Represents the typing and symbol environment during type checking and rule validation.
    /// It tracks variable bindings, mutable variables with their scope, lambda nesting depth,
    /// accessible symbols, and file context. This structure is passed around and updated
    /// as the type checker processes expressions and rules.
    type private Env =
        { /// The current binding variables in the environment.
          Bindings: Map<string, TypeScheme>

          /// Lists the mutable variables in the current environment.
          MutableVariables: (string * int) list

          /// Used to detect mutations of external variables in lambdas. The scope is increased each time the
          /// field of a lambda is entered and decreased each time it is exited. This allows comparison with
          /// the contents of `MutableVariables`.
          LambdaScope: int

          /// The list of top-level accessible rules.
          Symbols: Map<Identifier, SymbolInfo list>

          /// The current stream name
          CurrentFile: string

          /// All lines in the text file. It's lazy, so it costs almost nothing even if the file is huge.
          AllLines: string seq }

        static member Empty streamName text =
            { Bindings = Map.empty
              MutableVariables = List.empty
              LambdaScope = 0
              Symbols = Map.empty
              CurrentFile = streamName
              AllLines = NodeInfo.getLines text }

    type private Substitution = Map<string, MonoType>

    /// Represents the state of the type inference process. It holds the current substitution
    /// being built, the active environment, and a counter for generating fresh type variables.
    type private InferenceState =
        { CurrentSubst: Substitution
          CurrentEnv: Env
          NextId: int }

        static member Empty streamName text =
            { CurrentSubst = Map.empty
              CurrentEnv = Env.Empty streamName text
              NextId = 0 }


    //                                                             //
    // --- Helpers needed for type inference and type checking --- //
    //                                                             //


    module private Variable =
        open Liyh.Utils.ColorTerm

        /// The color used for showing variables.
        let public colored =
            colorize (Indexed 48) << sprintf "'%s"

    module private Substitution =

        /// Replaces variable types found in the substitution with the corresponding types.
        let public applySubstitution (subst: Substitution) (t: MonoType) =

            let rec loop =
                function
                | TVar v -> Option.defaultWith (fun _ -> TVar v) (Option.map loop (Map.tryFind v subst))
                | TSymbol _ as t -> t
                | TFun(args, ret) -> TFun(List.map loop args, loop ret)
                | TTuple ts -> TTuple(List.map loop ts)
                | TRecord fs -> TRecord(List.map (fun (f, ty) -> f, loop ty) fs)
                | TApp(id, args) -> TApp(id, List.map loop args)
                | TEffect(ty, ids) -> TEffect(loop ty, ids)
                | TName _ as t -> t
                | TAny -> TAny

            loop t

    module private InferenceState =

        /// Generate a fresh new type variable and return the updated state.
        let public freshVar (state: InferenceState) =
            let varName = sprintf "t%d" state.NextId
            TVar varName, { state with NextId = state.NextId + 1 }

        /// Increment the lambda scope counter.
        let public incrementLambdaScope (state: InferenceState) =
            { state with CurrentEnv = { state.CurrentEnv with LambdaScope = state.CurrentEnv.LambdaScope + 1 } }

        /// Decrement the lambda scope counter.
        let public decrementLambdaScope (state: InferenceState) =
            { state with CurrentEnv = { state.CurrentEnv with LambdaScope = state.CurrentEnv.LambdaScope - 1 } }

        /// Instantiates a polymorphic type scheme into a monotype within the given inference state.
        /// For each quantified variable in the scheme, a fresh type variable is generated and
        /// substituted into the body type. Returns the instantiated type along with the updated state.
        let public instantiate (state: InferenceState) (Scheme(quant, ty)) =
            let mapping, state' =
                quant
                |> List.fold
                    (fun (acc, s) q ->
                        let v, s' = freshVar s

                        match v with
                        | TVar name -> Map.add q (TVar name) acc, s'
                        | _ -> acc, s')

                    (Map.empty, state)

            Substitution.applySubstitution mapping ty, state'

        /// Checks whether the given variable type is present in the given monomorphic type.
        let rec public occurs (state: InferenceState) (v: string) (t: MonoType) =
            match t with
            | TVar x when x = v -> true
            | TVar x ->
                match Map.tryFind x state.CurrentSubst with
                | Some ty -> occurs state v ty
                | None -> false
            | TFun(args, ret) -> List.exists (occurs state v) args || occurs state v ret
            | TTuple ts -> List.exists (occurs state v) ts
            | TRecord fs -> List.exists (snd >> occurs state v) fs
            | TApp(_, args) -> List.exists (occurs state v) args
            | TEffect(ty, _) -> occurs state v ty
            | (TName _ | TAny | TSymbol _) -> false

        /// Searches for the given variable in the state.
        let public lookupVariable (name: string) (state: InferenceState) =
            Map.tryFind name state.CurrentEnv.Bindings
            |> Option.map (instantiate state)

        /// Searches for the given symbol (i.e. rule/handler) in the state.
        let public lookupSymbols (symbol: Identifier) (state: InferenceState) =
            Map.tryFind symbol state.CurrentEnv.Symbols
            |> Option.map sortDefinitions

        /// Same as `lookupSymbols` but filter by arity.
        let public lookupSymbolsByArity (symbol: Identifier) (arity: int) (state: InferenceState) =
            lookupSymbols symbol state
            |> Option.map (List.filter (_.Arity >> ( = ) arity))

        /// Same as `lookupSymbols` but filter by hash to obtain at most one element.
        let public lookupSymbolByHash (symbol: Identifier) (hash: int) (state: InferenceState) =
            InferenceState.lookupSymbols symbol state
            |> Option.bind (List.tryFind (_.Hash >> ( = ) hash))

        /// Sorts definitions by strategy.
        let public sortDefinitions (sinfo: SymbolInfo list) =

            let strategyOrder = function
                | Outermost -> 0
                | Innermost -> 1
                | Invalid -> 2

            List.sortBy (_.Strategy >> strategyOrder) sinfo

        /// Adds a new symbol (rule/handler) into the state.
        let public addSymbolInfo (id: Identifier) (sinfo: SymbolInfo) (state: InferenceState) =
            let env = state.CurrentEnv

            let symbols =
                match Map.tryFind id env.Symbols with
                | Some family -> Map.add id (family @ [ sinfo ]) env.Symbols    // <- keep the definition order
                | None -> Map.add id [ sinfo ] env.Symbols

            let env' = { env with Symbols = symbols }
            { state with CurrentEnv = env' }

        /// Update an existing symbol (rule/handler) of the state.
        let public updateSymbolInfo (id: Identifier) (hash: int) (newSinfo: SymbolInfo) (state: InferenceState) =
            let env = state.CurrentEnv

            let updatedSymbols =
                env.Symbols
                |> Map.change id (function Some s -> Some(List.map (fun a -> if a.Hash = hash then newSinfo else a) s))

            let env' = { env with Symbols = updatedSymbols }
            { state with CurrentEnv = env' }

    module private MonoType =

        /// Checks of the given type is `TVar` or `TAny`.
        let public isAnyOrVar = function
            | (TVar _ | TAny) -> true
            | _ -> false

        /// Returns the set of variable types present in the given monomorphic type.
        let rec public getFreeVariables (t: MonoType) =
            match t with
            | TVar v -> Set.singleton v
            | TFun(args, ret) -> Set.union (args |> List.map getFreeVariables |> Set.unionMany) (getFreeVariables ret)
            | TTuple ts -> ts |> List.map getFreeVariables |> Set.unionMany
            | TRecord fs -> fs |> List.map (snd >> getFreeVariables) |> Set.unionMany
            | TApp(_, args) -> args |> List.map getFreeVariables |> Set.unionMany
            | TEffect(ty, _) -> getFreeVariables ty
            | TName _ -> Set.empty
            | TAny -> Set.empty
            | TSymbol _ -> Set.empty

        /// Checks if the given type contains variable types.
        let public hasVariableTypes =
            getFreeVariables >> Set.isEmpty >> not

        module public PrettyPrint =
            open Liyh.Utils.ColorTerm

            /// The color used to display types.
            let public colored =
                colorize (Indexed 45)

            let private buildTVarMap (ts: MonoType list) =

                let rec collect (accSet, accList) ty =
                    match ty with
                    | (TAny | TSymbol _ | TName _) -> (accSet, accList)
                    | TVar v ->
                        if Set.contains v accSet then (accSet, accList)
                        else (Set.add v accSet, v :: accList)

                    | TFun(args, ret) ->
                        let acc' = List.fold collect (accSet, accList) args
                        collect acc' ret

                    | TTuple ts -> List.fold collect (accSet, accList) ts
                    | TRecord fs -> List.fold collect (accSet, accList) (List.map snd fs)
                    | TApp(_, args) -> List.fold collect (accSet, accList) args
                    | TEffect(t, _) -> collect (accSet, accList) t

                let (_, collectedList) = List.fold collect (Set.empty, []) ts
                let collectedList = List.rev collectedList

                let getName k =
                    let baseChar = int 'α'
                    let c = char (baseChar + (k % 26))
                    let n = k / 26
                    if n = 0 then sprintf "'%c" c
                    else sprintf "'%c%i" c n

                collectedList
                |> List.mapi (fun k var -> (var, getName k))
                |> Map.ofList

            let rec private prettyPrintMonoTypeWithTVarMap (table: Map<string, string>) =
                function
                | TAny -> "Any"
                | TName id ->
                    (String.concat "." id.Qualifier)
                    + (if id.Qualifier.Length > 0 then "." else "")
                    + id.Name

                | TVar v ->
                    match Map.tryFind v table with
                    | Some newName -> newName
                    | None -> sprintf "'%s" v

                | TSymbol _ -> "Σ"

                | TFun(args, ret) ->
                    let sret = prettyPrintMonoTypeWithTVarMap table ret
                    let sret = if ret.IsTFun then sprintf "(%s)" sret else sret

                    sprintf
                        "[%s] -> %s"
                        (String.concat ", " (List.map (prettyPrintMonoTypeWithTVarMap table) args))
                        sret

                | TTuple ts ->  "(" + String.concat ", " (List.map (prettyPrintMonoTypeWithTVarMap table) ts) + ")"
                | TRecord fs ->
                    "{ "
                    + String.concat ", " (List.map (fun (n, t) -> n + ": " + prettyPrintMonoTypeWithTVarMap table t) fs)
                    + " }"

                | TApp(id, args) -> id.Name + "[" + String.concat ", " (List.map (prettyPrintMonoTypeWithTVarMap table) args) + "]"
                | TEffect(t, ids) ->
                    prettyPrintMonoTypeWithTVarMap table t
                    + " % {"
                    + String.concat ", " (List.map (fun i -> i.Name) ids)
                    + "}"

            /// Pretty printer for monomorphic types with pretty replacement for type variables.
            let public prettyPrintMonoType (ty: MonoType) =
                prettyPrintMonoTypeWithTVarMap (buildTVarMap [ ty ]) ty

            /// Pretty printer for monomorphic types without pretty replacement for type variables.
            let public prettyPrintMonoTypeOriginal =
                prettyPrintMonoTypeWithTVarMap Map.empty

            /// Pretty print a list of monomorphic types with pretty replacement for type variables
            /// consistent accross the list's items.
            let public prettyPrintMonoTypeList (ts: MonoType list) =
                let mapping = buildTVarMap ts
                List.map (prettyPrintMonoTypeWithTVarMap mapping) ts

            /// Pretty print a monomorphic type's small description for error display.
            let public mainType (ty: MonoType) =
                match ty with
                | TVar _
                | TAny -> "any type"
                | TSymbol _ -> sprintf "an abstract symbol"
                | TFun _ as t -> sprintf "a function of the type %s" (colored (prettyPrintMonoType t))
                | TRecord _ as t -> sprintf "a record of the type %s" (colored (prettyPrintMonoType t))
                | TTuple _ as t -> sprintf "a tuple of the type %s" (colored (prettyPrintMonoType t))
                | TEffect _ as t -> sprintf "an effect signature %s" (colored (prettyPrintMonoType t))
                | (TApp _ | TName _) as t -> sprintf "a value of the type %s" (colored (prettyPrintMonoType t))

        /// Convert a syntactic type to an actual typechecker's type.
        let rec public monoTypeFromSyntax (twp: TypeWithPos) =
            match removePos twp with
            | VariableType s -> TVar s // Warning: could be the same as in the state!

            | NamedType idwp ->
                let id = astIdentifierToMonoTypeIdentifier (removePos idwp)
                if id = Identifier.Simple "Any" then TAny else TName id

            | RuleType(args, ret) ->
                let a = List.map monoTypeFromSyntax args
                let r = monoTypeFromSyntax ret

                TFun(a, r)

            | TupleType ts -> TTuple(List.map monoTypeFromSyntax ts)
            | RowRecordType fs -> TRecord(List.map (fun (f, tw) -> f, monoTypeFromSyntax tw) fs)

            | ParametrizedType(idwp, args) ->
                let id = astIdentifierToMonoTypeIdentifier (removePos idwp)
                TApp(id, List.map monoTypeFromSyntax args)

            | ModuloEffectType(t, ids) ->
                TEffect(monoTypeFromSyntax t, List.map (removePos >> astIdentifierToMonoTypeIdentifier) ids)

            | WildcardType -> TAny

        /// Type of a literal.
        let public monoTypeFromLiteral (litwp: LiteralWithPos) =
            match removePos litwp with
            | Literal.Unit -> TName(Identifier.Simple "Unit")
            | Literal.Integer _ -> TName(Identifier.Simple "Int")
            | Literal.Float _ -> TName(Identifier.Simple "Float")
            | Literal.String _ -> TName(Identifier.Simple "String")
            | Literal.Char _ -> TName(Identifier.Simple "Char")
            | Literal.InterpolatedString _ -> TName(Identifier.Simple "String")

    module private Env =

        /// Computes the set of free type variables appearing in all bindings of the environment,
        /// excluding those that are explicitly quantified in their type schemes.
        let private freeVarsEnv (env: Env) =
            env.Bindings
            |> Seq.map (function KeyValue(_, Scheme(vars, ty)) -> MonoType.getFreeVariables ty - Set.ofList vars)
            |> Seq.fold Set.union Set.empty

        /// Produces a polymorphic type scheme by quantifying all free type variables of `t`
        /// that are not already bound in the environment.
        let public generalize (env: Env) (t: MonoType) =
            let ftv = MonoType.getFreeVariables t
            let envFtv = freeVarsEnv env
            let quant = Set.toList (ftv - envFtv)

            Scheme(quant, t)

        /// Extend the environment by the given bindings and override the existing ones if already present.
        let public extend (env: Env) (bindings: (string * TypeScheme) list) =
            { env with Bindings = List.fold (fun acc (n, s) -> Map.add n s acc) env.Bindings bindings }

        /// Extend the state's environment by the given bindings and override the existing ones if already present.
        let public extendWithinState (state: InferenceState) (bindings: (string * TypeScheme) list) =
            { state with CurrentEnv = extend state.CurrentEnv bindings }

    module private Unify =

        /// Attempts to unify the two given types, if they are compatible and return the updated
        /// inference state, otherwise returns a contextualized error message.
        let rec public unify
            (what: string)
            (t1: MonoType)
            (t2: MonoType)
            (state: InferenceState)
            : Result<InferenceState, string> =

            let buildContext (contexts: string list) =
                match contexts |> List.filter (not << System.String.IsNullOrEmpty) with
                | [] -> ""
                | [ single ] -> sprintf "during type-checking the %s" single
                | multiple ->
                    let multiple = List.rev multiple
                    let path = String.concat "'s " multiple
                    sprintf "during type-checking the %s" path

            let rec unifyWithTrace contexts (t1: MonoType) (t2: MonoType) (state: InferenceState) =
                let subst = state.CurrentSubst
                let t1 = Substitution.applySubstitution subst t1
                let t2 = Substitution.applySubstitution subst t2

                match t1, t2 with
                | (TVar v, ty | ty, TVar v) ->
                    if ty = TVar v then Ok state
                    elif InferenceState.occurs state v ty then
                        let contextStr = buildContext contexts
                        Error(sprintf "Occurs check failed: %s in %s %s" v (MonoType.PrettyPrint.mainType ty) contextStr)
                    else Ok { state with CurrentSubst = Map.add v ty subst }

                | (TAny, _ | _, TAny) -> Ok state

                // The symbols can be unified with each other, but not with the rest.
                | TSymbol _, TSymbol _ -> Ok state

                | TName a, TName b when a = b -> Ok state // todo: handle subtyping (if we decide to support it)

                | TFun(args1, r1), TFun(args2, r2) when List.length args1 = List.length args2 ->
                    let finalState =
                        (Ok state,
                        List.zip args1 args2
                        |> List.mapi (fun i (a, b) ->
                            let argContext = sprintf "%dnth argument of the function" (i + 1)
                            (a, b, argContext)))
                        ||> List.fold (fun acc (a, b, ctx) ->
                            Result.bind (fun s -> unifyWithTrace (ctx :: contexts) a b s) acc)

                    Result.bind (fun s -> unifyWithTrace ("return type" :: contexts) r1 r2 s) finalState

                | TTuple ts1, TTuple ts2 when List.length ts1 = List.length ts2 ->
                    (Ok state,
                    List.zip ts1 ts2
                    |> List.mapi (fun i (a, b) ->
                        let elemContext = sprintf "%dnth element of the tuple" (i + 1)
                        (a, b, elemContext)))
                    ||> List.fold (fun acc (a, b, ctx) -> Result.bind (fun s -> unifyWithTrace (ctx :: contexts) a b s) acc)

                | TRecord f1, TRecord f2 ->
                    let mutable state' = Ok state
                    let fields2 = Map.ofList f2

                    for (fieldName, fieldType1) in f1 do
                        match Map.tryFind fieldName fields2 with
                        | Some fieldType2 ->
                            let fieldContext = sprintf "record field `%s`" fieldName
                            state' <-
                                Result.bind
                                    (fun s -> unifyWithTrace (fieldContext :: contexts) fieldType1 fieldType2 s)
                                    state'

                        | None ->
                            let contextStr = buildContext contexts
                            state' <-
                                Error(
                                    sprintf "Field `%s` is required but missing in the given record %s" fieldName contextStr
                                )

                    state'

                | TApp(id1, args1), TApp(id2, args2) when id1 = id2 && List.length args1 = List.length args2 ->
                    (Ok state,
                    List.zip args1 args2
                    |> List.mapi (fun i (a, b) ->
                        let typeArgContext = sprintf "%dnth type argument of %s" (i + 1) (MonoType.PrettyPrint.mainType t1)
                        (a, b, typeArgContext)))
                    ||> List.fold (fun acc (a, b, ctx) -> Result.bind (fun s -> unifyWithTrace (ctx :: contexts) a b s) acc)

                | TEffect(ty1, ids1), TEffect(ty2, ids2) when ids1 = ids2 ->
                    unifyWithTrace ("effect type" :: contexts) ty1 ty2 state

                | _ ->
                    let contextStr = buildContext contexts

                    Error(
                        sprintf
                            "Expected %s, but got %s%s"
                            (MonoType.PrettyPrint.mainType t1)
                            (MonoType.PrettyPrint.mainType t2)
                            (if contextStr = "" then "" else sprintf " %s" contextStr)
                    )

            unifyWithTrace (if System.String.IsNullOrEmpty what then [] else [ what ]) t1 t2 state

        /// Attempts to unify a list of pairs of types and share the updated state at each stage.
        let rec public unifyMany (what: string) (pairs: (MonoType * MonoType) list) (state: InferenceState) =
            match pairs with
            | [] -> Ok state
            | (t1, t2) :: rest ->
                match unify what t1 t2 state with
                | Ok newState -> unifyMany what rest newState
                | Error err -> Error err

        /// Checks whether two types are unifiable without reporting any error.
        let inline public doUnify (t1: MonoType) (t2: MonoType) (state: InferenceState) =
            unify null t1 t2 state |> Result.isOk

        /// Checks whether a list of pairs of types are unifiable without reporting any error.
        let inline public doUnifyMany (pairs: (MonoType * MonoType) list) (state: InferenceState) =
            unifyMany null pairs state |> Result.isOk

    /// Executes an inference action within a temporary environment extended by the given bindings,
    /// restoring the outer environment afterwards.
    let private withLocalBindings (bindings: (string * TypeScheme) list) (state: InferenceState) (action: InferenceState -> 'a) =
        let localEnv = Env.extend state.CurrentEnv bindings
        let localState = { state with CurrentEnv = localEnv }
        action localState

    /// Returns a string for the file name of a given position and returns "this file" if the
    /// position indicates the current file.
    let private fileName (state: InferenceState) (pos: FParsec.Position) =
        if state.CurrentEnv.CurrentFile = pos.StreamName then "this file"
        else sprintf "the file '%s'" pos.StreamName


    //                                                       //
    // --- Ad-hoc polymorphism & static pattern checking --- //
    //                                                       //


    module private StaticPattern =

        /// Assuming that the pattern and expression are type-compatible, check statically if they match whenever
        /// possible. This is mainly used for purely symbolic expressions, as they are always constant.
        let public doMatch (state: InferenceState) (pattwp: PatternWithPos) (exprwp: ExpressionWithPos) =

            (*

            // we assume the types are compatibles
            assert
                match PatternInference.inferPattern pattwp state (ErrorQueue()) with
                | None -> false
                | Some r1 ->
                    let state = Env.extendWithinState r1.State r1.Bindings
                    match ExpressionInference.inferExpressionType exprwp state (ErrorQueue()) with
                    | None -> false
                    | Some r2 ->
                        let t1 = r1.Type
                        let t2 = fst r2
                        let state = snd r2

                        Unify.doUnify t1 t2 state

            *)

            let rec loop (pattwp: PatternWithPos) (exprwp: ExpressionWithPos) =
                match removePos pattwp, removePos exprwp with
                | Wildcard, _ -> true
                | VariablePattern _, _ -> true
                | SymbolPattern id1, Identifier id2 ->
                    astIdentifierToMonoTypeIdentifier id1 = astIdentifierToMonoTypeIdentifier (removePos id2)
                | ApplyPattern(h1, args1), Apply apply when args1.Length = apply.Arguments.Length ->
                    loop h1 apply.LHS && List.forall2 loop args1 apply.Arguments
                | LiteralPattern lp, Literal le -> removePos lp = removePos le
                | (ListPattern xs, List ys | TuplePattern xs, Tuple ys) when xs.Length = ys.Length -> List.forall2 loop xs ys
                | Pattern.TypedPattern _, _ -> true // already checked at this stage
                | _ -> false // TODO

            loop pattwp exprwp

        /// Same as `doMatch` but for a list of pairs.
        let public doMatchMany (state: InferenceState) (pairs: (PatternWithPos * ExpressionWithPos) list) =

            let rec loop =
                function
                | (p, e) :: rest -> if doMatch state p e then loop rest else false
                | _ -> true

            loop pairs

    module private AdHocPolymorphism =

        type private ParameterData<'T> =
            { Items: 'T list
              PrettyPrint: 'T -> string }

        let private invalidRuleError 
            (state: InferenceState) 
            (symbol: Identifier)
            (matchedSymbol: SymbolInfo) 
            (parametersTypes: MonoType list) 
            (parameterData: ParameterData<'T>)
            (symbols: SymbolInfo list) 
            (pos, pos')
            (errorQueue: ErrorQueue) =

            let formatRuleMessage () =
                let exprStr = 
                    match matchedSymbol.Body.Value with
                    | { Node = Literal { Node = String str } } -> str
                    | expr -> Liyh.Syntax.PrettyPrint.prettyPrintExpression expr
                sprintf "Specific user error message from this invalid rule: \"%s\"." exprStr

            let formatParametersTypes () =
                matchedSymbol.ParametersTypes
                |> MonoType.PrettyPrint.prettyPrintMonoTypeList
                |> List.map MonoType.PrettyPrint.colored
                |> String.concat ", "
                |> sprintf "[%s]"

            let buildMainMessage () =
                sprintf
                    "Invalid rule for `%s`: arguments of form/type `%s%s` are not supported (defined at line %d of %s). %s"
                    (string symbol)
                    (string symbol)
                    (formatParametersTypes ())
                    matchedSymbol.Position.Line
                    (fileName state matchedSymbol.Position)
                    (formatRuleMessage ())

            let buildTypeInfo () =
                let patternTypes = MonoType.PrettyPrint.prettyPrintMonoTypeList matchedSymbol.ParametersTypes
                let argumentTypes = 
                    parametersTypes
                    |> List.map (Substitution.applySubstitution state.CurrentSubst)
                    |> List.map MonoType.PrettyPrint.prettyPrintMonoType

                let lines =
                    List.zip3 patternTypes argumentTypes parameterData.Items
                    |> List.map (fun (pattTy, argTy, param) ->
                        let paramStr = parameterData.PrettyPrint param
                        sprintf
                            "  %s : %s ≡ %s"
                            paramStr
                            (MonoType.PrettyPrint.colored argTy)
                            (MonoType.PrettyPrint.colored pattTy))

                "In this case,\n\n" + (String.concat "\n" lines) + "\n\nThis combination is invalid by user definition.\n"

            let buildAlternatives () =
                let alts =
                    symbols
                    |> List.filter (fun s -> not s.Strategy.IsInvalid)
                
                if List.isEmpty alts then ""
                else
                    alts
                    |> List.map (fun s -> TFun(s.ParametersTypes, s.ReturnType) |> MonoType.PrettyPrint.prettyPrintMonoType |> fun s -> sprintf "%s%s" (string symbol) s)
                    |> String.concat "\n  "
                    |> sprintf "Form/type of existing valid rules:\n\n  %s"

            let hint = 
                "Rules marked as \"invalid\" produce an unrecoverable error if ever reached; " +
                "you can implement a new rule for the pattern concerned or adapt the expected patterns."

            let report =
                { ErrorType = ErrorType.Type
                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.MatchedInvalidRuleError
                  EnclosingPosition = pos, pos'
                  Description = buildMainMessage ()
                  AllLines = state.CurrentEnv.AllLines
                  Informations = [ buildTypeInfo (); buildAlternatives () ]
                  Hint = hint }

            errorQueue.AddError report
            None

        let private genericLookup
            (symbolId: Identifier)
            (parametersTypes: MonoType list)
            (parameterData: ParameterData<'T>)
            (patternMatcher: InferenceState -> ('T * PatternWithPos) list -> bool)
            (pos, pos')
            (state: InferenceState)
            (errorQueue: ErrorQueue)
            =

            /// Attempts to find the first compatible rule by instantiating its type scheme for each attempt.
            let rec findFirstMatch (candidates: SymbolInfo list) =
                match candidates with
                | [] -> None // No rule match

                | currentSymbol :: rest ->
                    let instantiatedType, state =
                        InferenceState.instantiate state currentSymbol.Scheme

                    let (instantiatedParamTypes, instantiatedReturnType) =
                        match instantiatedType with
                        | TFun (args, ret) -> (args, ret)
                        | other -> ([], other) // it is normally managed elsewhere, but if we arrive here it works too

                    match Unify.unifyMany "rule patterns" (List.zip parametersTypes instantiatedParamTypes) state with
                    | Ok successState when patternMatcher state (List.zip parameterData.Items currentSymbol.Patterns) ->
                        Some (currentSymbol, instantiatedReturnType, successState)
                    | _ -> findFirstMatch rest

            let arity = parametersTypes.Length
            match InferenceState.lookupSymbolsByArity symbolId arity state with
            | None ->
                // Pure symbolic case.
                Some
                    {| Type = MonoType.tsymbol
                       State = state |}

            | Some symbols ->
                match findFirstMatch symbols with
                | None ->
                    // Pure symbolic case.
                    Some
                        {| Type = MonoType.tsymbol
                           State = state |}

                | Some (matchedSymbol, instantiatedReturnType, finalState) ->
                    // If the first matching symbol is invalid, the error is reported.
                    if matchedSymbol.Strategy.IsInvalid then
                        invalidRuleError
                            state symbolId matchedSymbol parametersTypes parameterData symbols (pos, pos') errorQueue
                    else
                        Some
                            {| Type = Substitution.applySubstitution finalState.CurrentSubst instantiatedReturnType
                               State = finalState |}

        /// Find the first rule whose patterns are compatible with the given symbol and its children. In case
        /// of an invalid rule, returns an error in the queue, otherwise if no rule is found then the type is
        /// inferred as that of an abstract symbol, otherwise unifies the types and infers the return type from
        /// the selected rule. The order of definitions is taken into account, as are "innermost" and "outermost"
        /// in order to properly represent semantics.
        let public lookupWithExpressions
            (symbolId: Identifier)
            (parametersTypes: MonoType list)
            (parameters: ExpressionWithPos list)
            (pos, pos')
            (state: InferenceState)
            (errorQueue: ErrorQueue)
            =
            
            let parameterData =
                { Items = parameters
                  PrettyPrint = Liyh.Syntax.PrettyPrint.prettyPrintExpression }

            let patternMatcher state pairs =
                StaticPattern.doMatchMany state (List.map (fun (a, b) -> (b, a)) pairs)

            genericLookup symbolId parametersTypes parameterData patternMatcher (pos, pos') state errorQueue

        /// Find the first rule whose parameter types are compatible with the given symbol, without 
        /// static pattern matching verification. In case of an invalid rule, returns an error in the 
        /// queue, otherwise if no rule is found then the type is inferred as that of an abstract 
        /// symbol, otherwise unifies the types and infers the return type from the selected rule. 
        /// The order of definitions is taken into account.
        let public lookupWithPatterns
            (symbolId: Identifier)
            (parametersTypes: MonoType list)
            (patterns: PatternWithPos list)
            (pos, pos')
            (state: InferenceState)
            (errorQueue: ErrorQueue)
            =

            let parameterData =
                { Items = patterns
                  PrettyPrint = Liyh.Syntax.PrettyPrint.prettyPrintPattern }

            let patternMatcher _ _ = true

            genericLookup symbolId parametersTypes parameterData patternMatcher (pos, pos') state errorQueue


    //                                      //
    // --- Pattern inference & checking --- //
    //                                      //


    module private PatternInference =

        type public PatternInferenceResult =
            { Bindings: (string * TypeScheme) list  // needed for non-linear pattern typechecking
              Type: MonoType
              State: InferenceState }

        /// Attempts to infer the type of a pattern, returning `None` otherwise with the error queue updated.
        let rec public inferPattern 
            (pattwp: PatternWithPos)
            (state: InferenceState)
            (errorQueue: ErrorQueue)
            : PatternInferenceResult option =

            let pos, pos' = pattwp.Pos, pattwp.Pos'

            match inferPatternInternal pattwp state errorQueue with
            | None -> None
            | Some pir ->
                match checkNonLinearPatternConsistency pir.Bindings pir.State (Some pos, Some pos') errorQueue with
                | None -> None
                | Some state' -> Some { pir with State = state' }

        and private inferPatternInternal
            (pattwp: PatternWithPos)
            (state: InferenceState)
            (errorQueue: ErrorQueue)
            : PatternInferenceResult option =

            let pos, pos' = pattwp.Pos, pattwp.Pos'

            match removePos pattwp with
            | Pattern.VariablePattern name ->
                let ftv, state' = InferenceState.freshVar state
                Some
                    { Bindings = [ (name, Scheme([], ftv)) ]
                      Type = ftv
                      State = state' }

            | Pattern.LiteralPattern lit ->
                Some
                    { Bindings = []
                      Type = MonoType.monoTypeFromLiteral lit
                      State = state }

            | Pattern.TuplePattern items ->
                let rec loop (state, bindings, types) =
                    function
                    | [] ->
                        Some
                            { Bindings = List.rev bindings
                              Type = TTuple(List.rev types)
                              State = state }

                    | p :: rest ->
                        match inferPatternInternal p state errorQueue with
                        | Some pir -> loop (pir.State, bindings @ pir.Bindings, pir.Type :: types) rest
                        | None -> None

                loop (state, [], []) items

            | Pattern.Wildcard ->
                let tv, state' = InferenceState.freshVar state

                Some
                    { Bindings = []
                      Type = tv
                      State = state' }

            | Pattern.AsPattern(left, right) ->
                match inferPatternInternal left state errorQueue with
                | Some inferedLeft ->
                    match inferPatternInternal right inferedLeft.State errorQueue with
                    | Some inferedRight ->
                        match Unify.unify "as-pattern" inferedLeft.Type inferedRight.Type inferedRight.State with
                        | Ok result ->
                            Some
                                { Bindings = inferedLeft.Bindings @ inferedRight.Bindings
                                  Type = Substitution.applySubstitution result.CurrentSubst inferedLeft.Type
                                  State = result }

                        | Error msg ->
                            let report =
                                { ErrorType = ErrorType.Type
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                  EnclosingPosition = Some pos, Some pos'
                                  Description = sprintf "Type mismatch in as-pattern: %s." msg
                                  AllLines = state.CurrentEnv.AllLines
                                  Informations = []
                                  Hint = null }

                            errorQueue.AddError report
                            None
                    | None -> None
                | None -> None

            | Pattern.TypedPattern(p, twp) ->
                match inferPatternInternal p state errorQueue with
                | Some inferd ->
                    let ty = MonoType.monoTypeFromSyntax twp

                    match Unify.unify "type-pattern" ty inferd.Type inferd.State with
                    | Ok state' ->
                        Some
                            { Bindings = inferd.Bindings
                              Type = Substitution.applySubstitution state'.CurrentSubst inferd.Type
                              State = state' }

                    | Error msg ->
                        let report =
                            { ErrorType = ErrorType.Type
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                              EnclosingPosition = Some pos, Some pos'
                              Description = sprintf "Type annotation mismatch: %s." msg
                              AllLines = state.CurrentEnv.AllLines
                              Informations = []
                              Hint = null }

                        errorQueue.AddError report
                        None
                | None -> None

            | Pattern.RecordPattern fs ->
                let rec loop state acc =
                    function
                    | [] ->
                        let topBindings = List.collect (fun (_, _, bs) -> bs) acc
                        let recFields = List.map (fun (n, t, _) -> (n, t)) acc

                        Some
                            { Bindings = topBindings
                              Type = TRecord recFields
                              State = state }

                    | (name, pwp) :: rest ->
                        match inferPatternInternal pwp state errorQueue with
                        | Some inferred -> loop inferred.State ((name, inferred.Type, inferred.Bindings) :: acc) rest
                        | None -> None

                loop state [] fs

            | Pattern.SymbolPattern id ->
                let id = astIdentifierToMonoTypeIdentifier id

                match InferenceState.lookupSymbolsByArity id 0 state with
                | None ->
                    Some
                        { Bindings = []
                          Type = MonoType.tsymbol
                          State = state }

                | Some [ s ] ->
                    Some
                        { Bindings = []
                          Type = s.ReturnType
                          State = state }

                | _ -> failwith "Internal error: too many choices!"

            | Pattern.ApplyPattern(left, right) ->

                let rec processArguments (state: InferenceState) (argsTypes: MonoType list) =
                    function
                    | [] -> Some(state, argsTypes)
                    | pwp :: rest ->
                        match inferPatternInternal pwp state errorQueue with
                        | None -> None
                        | Some r ->
                            let state = Env.extendWithinState r.State r.Bindings
                            inferPattern pwp state errorQueue
                            |> Option.bind (fun res -> processArguments res.State (argsTypes @ [ res.Type ]) rest)

                match removePos left with
                | Pattern.SymbolPattern id ->
                    processArguments state List.empty right
                    |> Option.bind (fun (state, argsTypes) ->
                        let id = astIdentifierToMonoTypeIdentifier id
                        AdHocPolymorphism.lookupWithPatterns id argsTypes right (Some pos, Some pos') state errorQueue
                        |> Option.map (fun res -> { Bindings = []; Type = res.Type; State = res.State }))

                | _ ->
                    match inferPatternInternal left state errorQueue with
                    | Some inferedLeft ->
                        let rec loop state accBindings accTys =
                            function
                            | [] ->
                                let tv, state' = InferenceState.freshVar state

                                match Unify.unify "apply-pattern" inferedLeft.Type (TFun(List.rev accTys, tv)) state' with
                                | Ok finalState ->
                                    Some
                                        { Bindings = accBindings @ inferedLeft.Bindings
                                          Type = Substitution.applySubstitution finalState.CurrentSubst tv
                                          State = finalState }

                                | Error msg ->
                                    let report =
                                        { ErrorType = ErrorType.Type
                                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                          EnclosingPosition = Some pos, Some pos'
                                          Description = sprintf "Apply pattern type mismatch: %s." msg
                                          AllLines = state.CurrentEnv.AllLines
                                          Informations = []
                                          Hint = null }

                                    errorQueue.AddError report
                                    None

                            | p :: rest ->
                                match inferPatternInternal p state errorQueue with
                                | Some inferred ->
                                    loop
                                        inferred.State
                                        (accBindings @ inferred.Bindings)
                                        (inferred.Type :: accTys)
                                        rest

                                | None -> None

                        loop inferedLeft.State [] [] right

                    | None -> None

            | Pattern.ListPattern items ->
                let rec loop state bindings tys  =
                    function
                    | [] ->
                        match tys with
                        | [] ->
                            let tv, state' = InferenceState.freshVar state

                            Some
                                { Bindings = bindings
                                  Type = TApp(Identifier.Simple "List", [ tv ])
                                  State = state' }

                        | h :: rest ->
                            let res =
                                List.fold
                                    (fun acc r ->
                                        match acc with
                                        | Ok st -> Unify.unify "list-item" h r st
                                        | Error _ -> acc)
                                    (Ok state)
                                    rest

                            match res with
                            | Ok state' ->
                                Some
                                    { Bindings = bindings
                                      Type = TApp(Identifier.Simple "List", [ h ])
                                      State = state' }

                            | Error msg ->
                                let report =
                                    { ErrorType = ErrorType.Type
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                      EnclosingPosition = Some pos, Some pos'
                                      Description = sprintf "List pattern type mismatch: %s." msg
                                      AllLines = state.CurrentEnv.AllLines
                                      Informations = []
                                      Hint = null }

                                errorQueue.AddError report
                                None

                    | p :: rest ->
                        match inferPatternInternal p state errorQueue with
                        | Some inferred ->
                            loop inferred.State (bindings @ inferred.Bindings) (tys @ [ inferred.Type ]) rest
                        | None -> None

                loop state [] [] items

            | Pattern.AlternativePattern alts ->
                let (originalType :: rest) = List.map MonoType.monoTypeFromLiteral alts

                match List.tryFindIndex ((<>) originalType) rest with // don't need to Unify.unify here
                | None ->
                    Some
                        { Bindings = []
                          Type = originalType
                          State = state }

                | Some i ->
                    let report =
                        { ErrorType = ErrorType.Type
                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.BadAlternativeTypeError
                          EnclosingPosition = Some pos, Some pos'
                          Description =
                            sprintf
                                "This alternative pattern's item was expected to be of the type %s, but it has the type %s (based on the first alternative)."
                                (MonoType.PrettyPrint.mainType originalType)
                                (MonoType.PrettyPrint.mainType rest.[i])
                          AllLines = state.CurrentEnv.AllLines
                          Informations = []
                          Hint = null }

                    errorQueue.AddError report
                    None

            | Pattern.MixfixOperatorPattern(name, holes) ->
                failwith "todo: mixfix pattern type inference"

            | Pattern.WhenPattern(patt, guard) ->
                match inferPatternInternal patt state errorQueue with
                | Some inferred ->
                    let env = Env.extend inferred.State.CurrentEnv inferred.Bindings
                    let state = { inferred.State with CurrentEnv = env }

                    match ExpressionInference.inferExpressionType guard state errorQueue with
                    | None -> None
                    | Some (ty, state) ->
                        match Unify.unify "when-clause" (TName(Identifier.Simple "Bool")) ty state with
                        | Ok state ->
                            Some
                                { inferred with
                                    Type = Substitution.applySubstitution state.CurrentSubst inferred.Type
                                    State = state
                                    Bindings = Map.toList state.CurrentEnv.Bindings }

                        | Error msg ->
                            let report =
                                { ErrorType = ErrorType.Semantic
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnfoundVariableError
                                  EnclosingPosition = Some guard.Pos, Some guard.Pos'
                                  Description = sprintf "%s." msg
                                  AllLines = state.CurrentEnv.AllLines
                                  Informations = []
                                  Hint = null }

                            errorQueue.AddError report
                            None

                | None -> None

        /// Check that the binding variables that appear in non-linear patterns are type-consistent.
        and public checkNonLinearPatternConsistency
            (bindings: (string * TypeScheme) list)
            (state: InferenceState)
            (pos, pos')
            (errorQueue: ErrorQueue)
            =

            let grouped =
                (Map.empty, bindings)
                ||> List.fold (fun acc (id, Scheme(_, ty)) ->
                    let z = Substitution.applySubstitution state.CurrentSubst ty
                    match Map.tryFind id acc with
                    | Some schemes -> Map.add id (z :: schemes) acc
                    | None -> Map.add id [ z ] acc)

            let report msg =
                { ErrorType = ErrorType.Type
                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.IncompatibleNonLinearVariablesError
                  EnclosingPosition = pos, pos'
                  Description = sprintf "%s (according to the first instance of this pattern)." msg
                  AllLines = state.CurrentEnv.AllLines
                  Informations = []
                  Hint = "Each non-linear variable must be of the same type." }

            let rec check state xs =
                match xs with
                | (v, tys) :: rest ->
                    let rec loop state =
                        function
                        | ([] | [ _ ]) -> Some state
                        | t1 :: t2 :: ts ->
                            match Unify.unify (sprintf "non-linear pattern's variable %s" (Variable.colored v)) t1 t2 state with
                            | Ok state' -> loop state' ts
                            | Error msg -> errorQueue.AddError (report msg); None
                    Option.bind (fun s -> check s rest) (loop state tys)
                | _ -> Some state

            check state (Map.toList grouped)

    module private PatternCheck =

        /// Check whether the two patterns are equivalent.
        let rec public arePatternsEquivalent (patt1: PatternWithPos) (patt2: PatternWithPos) (state: InferenceState) (keepAnyTypeUnification: bool) =
            let p1wp, p2wp = patt1, patt2

            match removePos patt1, removePos patt2 with
            | (Pattern.VariablePattern _, Pattern.VariablePattern _)
            | (Pattern.VariablePattern _, Pattern.Wildcard)
            | (Pattern.Wildcard, Pattern.Wildcard)
            | (Pattern.Wildcard, Pattern.VariablePattern _) -> true

            | Pattern.SymbolPattern s1, Pattern.SymbolPattern s2 -> s1 = s2

            | Pattern.ApplyPattern(pattwp1, args1), Pattern.ApplyPattern(pattwp2, args2) ->
                arePatternsEquivalent pattwp1 pattwp2 state keepAnyTypeUnification
                && args1.Length = args2.Length
                && List.forall2 (fun p1 p2 -> arePatternsEquivalent p1 p2 state keepAnyTypeUnification) args1 args2

            | Pattern.LiteralPattern l1, Pattern.LiteralPattern l2 -> l1.Node = l2.Node
            | Pattern.TuplePattern items1, Pattern.TuplePattern items2
            | Pattern.ListPattern items1, Pattern.ListPattern items2 ->
                items1.Length = items2.Length
                && List.forall2 (fun p1 p2 -> arePatternsEquivalent p1 p2 state keepAnyTypeUnification) items1 items2

            | Pattern.RecordPattern fields1, Pattern.RecordPattern fields2 ->
                let fields1 = List.sortBy (fun a -> fst a, (snd a).Node) fields1
                let fields2 = List.sortBy (fun a -> fst a, (snd a).Node) fields2
                List.length fields1 = List.length fields2
                && List.forall2 (fun (name1, patt1) (name2, patt2) ->
                    name1 = name2 && arePatternsEquivalent patt1 patt2 state keepAnyTypeUnification) fields1 fields2

            | Pattern.MixfixOperatorPattern(op1, args1), Pattern.MixfixOperatorPattern(op2, args2) ->
                op1 = op2
                && args1.Length = args2.Length
                && List.forall2 (fun p1 p2 -> arePatternsEquivalent p1 p2 state keepAnyTypeUnification) args1 args2

            | Pattern.AsPattern(inner1, alias1), Pattern.AsPattern(inner2, alias2) ->
                arePatternsEquivalent inner1 inner2 state keepAnyTypeUnification
                && arePatternsEquivalent alias1 alias2 state keepAnyTypeUnification

            | Pattern.WhenPattern(patt1, guard1), Pattern.WhenPattern(patt2, guard2) ->
                // this is impossible to check, but a simple check is doable anyway
                arePatternsEquivalent patt1 patt2 state keepAnyTypeUnification
                && guard1.Node = guard2.Node

            | Pattern.AlternativePattern literals1, Pattern.AlternativePattern literals2 ->
                List.length literals1 = List.length literals2
                && List.forall2 ( = ) (List.sort (List.map _.Node literals1)) (List.sort (List.map _.Node literals2))

            | (Pattern.VariablePattern _ | Pattern.Wildcard), Pattern.TypedPattern(_, ty)
            | Pattern.TypedPattern(_, ty), (Pattern.VariablePattern _ | Pattern.Wildcard) ->
                let ty = MonoType.monoTypeFromSyntax ty
                if MonoType.isAnyOrVar ty then true
                else false

            | Pattern.TypedPattern(patt1, ty1), Pattern.TypedPattern(patt2, ty2) ->
                let t1 = MonoType.monoTypeFromSyntax ty1
                let t2 = MonoType.monoTypeFromSyntax ty2

                // Untyped patterns do not have type constraints to be checked, and for typed pattern with TAny
                // and TVar it matches every time, hence a possible error when comparing type signature and
                // pattern. To correct this, it is worth constraining typed patterns not to be TAny or TVar.

                // TODO: c'est pas terrible
                // Est-ce que le cas précédent ne gère pas ce qu'on avait comme problème ici ?

                let inline checkPatterns patt1 patt2 =
                    arePatternsEquivalent patt1 patt2 state keepAnyTypeUnification

                if not keepAnyTypeUnification then
                    match t1, t2 with
                    | (TAny, TAny) | (TVar _, TVar _) | (TAny, TVar _) | (TVar _, TAny) -> checkPatterns patt1 patt2
                    | (_, TAny) | (_, TVar _) -> checkPatterns p1wp patt2
                    | (TAny, _) | (TVar _, _) -> checkPatterns patt1 p2wp
                    | _ -> checkPatterns patt1 patt2 && Unify.doUnify t1 t2 state

                else
                    checkPatterns patt1 patt2 && Unify.doUnify t1 t2 state

            | _ -> false

        let public arePatternListEquivalent (patts1: PatternWithPos list) (patts2: PatternWithPos list) (state: InferenceState) =
            List.length patts1 = List.length patts2
            && List.forall2 (fun p1 p2 -> arePatternsEquivalent p1 p2 state false) patts1 patts2

        // Check if the given pattern is already covered by a pattern in the list.
        let private isPatternCoveredBy (pattern: PatternWithPos) (coveringPatterns: PatternWithPos list) (state: InferenceState) =
            List.exists
                (fun coveringPattern ->
                    match removePos pattern, removePos coveringPattern with
                    | _, Pattern.Wildcard | _, Pattern.VariablePattern _ -> true
                    | _ -> arePatternsEquivalent pattern coveringPattern state false)
                coveringPatterns

        // Obtain all unreachable patterns.
        let public findAllUnreachablePatterns (patterns: PatternWithPos list) (state: InferenceState) =
            let rec checkAllPatterns coveredPatterns remainingPatterns index unreachableIndices =
                match remainingPatterns with
                | [] -> List.rev unreachableIndices
                | currentPattern :: restPatterns ->
                    if isPatternCoveredBy currentPattern coveredPatterns state
                    then checkAllPatterns coveredPatterns restPatterns (index + 1) (index :: unreachableIndices)
                    else checkAllPatterns (currentPattern :: coveredPatterns) restPatterns (index + 1) unreachableIndices

            checkAllPatterns [] patterns 0 []

        /// Detects unreachable and redundant patterns in a list of patterns.
        let public checkUnreachableAndRedundantPatterns (patterns: PatternWithPos list) (state: InferenceState) (errorQueue: ErrorQueue) =
            let hint = "The highlighted pattern(s) are equivalent to previous ones and will never be matched. Consider removing or reordering them."

            // --- redundant patterns --- //

            let groupEquivalentPatterns (patterns: PatternWithPos list) (state: InferenceState) =
                let rec loop acc remaining =
                    match remaining with
                    | [] -> Map.filter (fun _ v -> not (List.isEmpty v)) acc
                    | p :: rest ->
                        let equivalent, notEquivalent = 
                            List.partition (fun q -> arePatternsEquivalent p q state false) rest

                        let equivalentLines = List.map id equivalent
                        let newAcc = 
                            if List.isEmpty equivalentLines then acc
                            else Map.add p equivalentLines acc

                        loop newAcc notEquivalent

                loop Map.empty patterns

            let formatList =
                let rec joinWithAnd = function
                    | [ x: _ WithPos ] -> string x.Line
                    | [ x; y ] -> sprintf "%d and %d" x.Line y.Line
                    | x :: xs -> sprintf "%d, %s" x.Line (joinWithAnd xs)
                    | [] -> ""
                joinWithAnd

            // Keeps a list of patterns already processed to avoid duplicate errors if necessary.
            let mutable redundantPatternIndices = []

            for KeyValue(patt, equivalents) in groupEquivalentPatterns patterns state do
                let pls = if equivalents.Length > 1 then "s" else ""
                let report =
                    { ErrorType = ErrorType.Semantic
                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.RedundantRuleError
                      EnclosingPosition = Some equivalents.Head.Pos, Some equivalents.Head.Pos'
                      Description = sprintf "Redundant pattern%s detected on line%s %s. The first equivalent pattern was on line %d." pls pls (formatList equivalents) patt.Line
                      AllLines = state.CurrentEnv.AllLines
                      Informations = []
                      Hint = hint }
                errorQueue.AddError report

                for pattern in equivalents do
                    redundantPatternIndices <- pattern.Line :: redundantPatternIndices

            // --- Unreachable patterns --- //

            let unreachableIndices = findAllUnreachablePatterns patterns state

            for index in unreachableIndices do
                let pattern = patterns.[index]

                if not (List.contains pattern.Line redundantPatternIndices) then
                    let report =
                        { ErrorType = ErrorType.Semantic
                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnreachableRuleError
                          EnclosingPosition = Some pattern.Pos, Some pattern.Pos'
                          Description = "This pattern is unreachable because all cases are already covered above it."
                          AllLines = state.CurrentEnv.AllLines
                          Informations = []
                          Hint = hint }
                    errorQueue.AddError report


    //                              //
    // --- Expression inference --- //
    //                              //


    module private ExpressionInference =

        type public ExpressionInferenceResult =
            { Type: MonoType
              State: InferenceState }

        /// Manages type inference of application by combining the very similar cases of `Apply` and `UFCS`.
        let private inferApplication (prefixArgs: (MonoType * ExpressionWithPos) list) (context: string) (callableExpr: ExpressionWithPos) (arguments: ExpressionWithPos list) (initialState: InferenceState) (errorQueue: ErrorQueue) (pos, pos') =

            let rec processArguments state argTypes exprs =
                match exprs with
                | [] -> Some(state, argTypes)
                | e :: rest ->
                    inferExpression e state errorQueue
                    |> Option.bind (fun res -> processArguments res.State (argTypes @ [res.Type]) rest)

            processArguments initialState [] arguments
            |> Option.bind (fun (stateAfterArgs, regularArgsTypes) ->
                let allArgTypes = (prefixArgs |> List.map fst) @ regularArgsTypes
                let allArgExprs = (prefixArgs |> List.map snd) @ arguments

                match removePos callableExpr with
                | Identifier idwp ->
                    let id = astIdentifierToMonoTypeIdentifier (removePos idwp)
                    AdHocPolymorphism.lookupWithExpressions id allArgTypes allArgExprs (pos, pos') stateAfterArgs errorQueue
                    |> Option.map (fun res -> { Type = res.Type; State = res.State })

                | BindingVariable v ->
                    let returnType, state = InferenceState.freshVar stateAfterArgs
                    let expectedFunType = if allArgTypes.IsEmpty then returnType else TFun(allArgTypes, returnType)

                    match InferenceState.lookupVariable v state with
                    | Some (existingType, state) ->
                        match Unify.unify null existingType expectedFunType state with
                        | Ok state -> Some { Type = returnType; State = state }
                        | Error msg ->
                            let report =
                                { ErrorType = ErrorType.Type
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.NotApplicableVariableError
                                  EnclosingPosition = pos, pos'
                                  Description = sprintf "Cannot apply variable %s%s: %s." (Variable.colored v) context msg
                                  AllLines = state.CurrentEnv.AllLines
                                  Informations = []
                                  Hint = null }
                            errorQueue.AddError report
                            None
                    
                    | None ->
                        let suggestion =
                            Liyh.Utils.DamerauLevenshtein.suggest v state.CurrentEnv.Bindings.Keys
                            |> Liyh.Utils.DamerauLevenshtein.formatSuggestions "the variable"

                        let report =
                            { ErrorType = ErrorType.Semantic
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnfoundVariableError
                              EnclosingPosition = pos, pos'
                              Description = sprintf "The variable %s was not found in this scope." (Variable.colored v)
                              AllLines = state.CurrentEnv.AllLines
                              Informations = [ suggestion ]
                              Hint = null }
                        errorQueue.AddError report
                        None

                | _ ->
                    inferExpression callableExpr stateAfterArgs errorQueue
                    |> Option.bind (fun callableResult ->
                        let returnType, state = InferenceState.freshVar callableResult.State
                        let expectedFunType = if allArgTypes.IsEmpty then returnType else TFun(allArgTypes, returnType)

                        match callableResult.Type with
                        | TSymbol _ as t -> Some { Type = t; State = state }
                        | other ->
                            match Unify.unify null other expectedFunType state with
                            | Ok state -> Some { Type = returnType; State = state }
                            | Error msg ->
                                let report =
                                    { ErrorType = ErrorType.Type
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                      EnclosingPosition = pos, pos'
                                      Description = sprintf "%s." msg
                                      AllLines = state.CurrentEnv.AllLines
                                      Informations = []
                                      Hint = null }
                                errorQueue.AddError report
                                None
                    )
            )

        /// Attempts to infer the type of an expression, returning `None` otherwise with the error queue updated.
        let rec private inferExpression
            (exprwp: ExpressionWithPos)
            (state: InferenceState)
            (errorQueue: ErrorQueue)
            : ExpressionInferenceResult option =

            let pos, pos' = Some exprwp.Pos, Some exprwp.Pos'

            match removePos exprwp with
            | Literal lit ->
                Some
                    { Type = MonoType.monoTypeFromLiteral lit
                      State = state }

            | Identifier idwp ->
                let id = astIdentifierToMonoTypeIdentifier (removePos idwp)

                match InferenceState.lookupSymbolsByArity id 0 state with
                | None ->
                    Some
                        { Type = MonoType.tsymbol
                          State = state }

                | Some [ s ] ->
                    Some
                        { Type = s.ReturnType
                          State = state }

                | _ -> failwith "Internal error: too many choices!"

            | BindingVariable v ->
                match InferenceState.lookupVariable v state with
                | Some(ty, state') -> Some { Type = ty; State = state' }
                | None ->
                    let suggestion =
                        Liyh.Utils.DamerauLevenshtein.suggest v state.CurrentEnv.Bindings.Keys
                        |> Liyh.Utils.DamerauLevenshtein.formatSuggestions "the variable"

                    let report =
                        { ErrorType = ErrorType.Semantic
                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnfoundVariableError
                          EnclosingPosition = pos, pos'
                          Description = sprintf "The variable %s was not found in this scope." (Variable.colored v)
                          AllLines = state.CurrentEnv.AllLines
                          Informations = [ suggestion ]
                          Hint = null }

                    errorQueue.AddError report
                    None

            | Apply app ->
                inferApplication [] "" app.LHS app.Arguments state errorQueue (pos, pos')

            | UFCS ufcs ->
                inferExpression ufcs.LHS state errorQueue
                |> Option.bind (fun lhsResult ->
                    let prefixArg = (lhsResult.Type, ufcs.LHS)

                    let inferUfcsApplication expr arguments =
                        inferApplication [prefixArg] " in UFCS" expr arguments lhsResult.State errorQueue (pos, pos')

                    match removePos ufcs.RHS with
                    | Apply app -> inferUfcsApplication app.LHS app.Arguments
                    | _ -> inferUfcsApplication ufcs.RHS []
                )

            | Lambda lambda ->
                let rec loop state paramBindings paramTypes =
                    function
                    | [] ->
                        let envWithParams = Env.extend state.CurrentEnv paramBindings

                        let state' =
                            { state with
                                CurrentEnv = envWithParams }

                        inferExpression lambda.Body state' errorQueue
                        |> Option.map (fun bodyResult ->
                            { Type = TFun(paramTypes, bodyResult.Type)
                              State = bodyResult.State })

                    | pwp :: rest ->
                        PatternInference.inferPattern pwp state errorQueue
                        |> Option.bind (fun inferred ->
                            loop inferred.State (paramBindings @ inferred.Bindings) (paramTypes @ [ inferred.Type ]) rest)

                let state = InferenceState.incrementLambdaScope state
                loop state [] [] lambda.Patterns
                |> Option.map (fun r -> { r with State = InferenceState.decrementLambdaScope r.State })

            | Let(patt, rhs)
            | Var(patt, rhs) ->
                let letVar = (if exprwp.Node.IsLet then "let" else "var") + "-expression"

                match inferExpression rhs state errorQueue with
                | Some inferedRhs ->
                    match PatternInference.inferPattern patt inferedRhs.State errorQueue with
                    | Some inferedPatt ->
                        match Unify.unify letVar inferedPatt.Type inferedRhs.Type inferedPatt.State with
                        | Ok state' ->
                            let generalizedBindings =
                                inferedPatt.Bindings
                                |> List.map (fun (name, Scheme(_, mono)) ->
                                    let appliedMono = Substitution.applySubstitution state'.CurrentSubst mono
                                    let scheme = Env.generalize state'.CurrentEnv appliedMono
                                    (name, scheme))

                            let newEnv =
                                let baseEnv = Env.extend inferedRhs.State.CurrentEnv generalizedBindings

                                let filteredMutables =
                                    baseEnv.MutableVariables
                                    |> List.filter (fun (m, _) ->
                                        not (inferedPatt.Bindings |> List.exists (fun (n, _) -> n = m)))

                                if exprwp.Node.IsVar then
                                    { baseEnv with
                                        MutableVariables = filteredMutables @ (inferedPatt.Bindings |> List.map (fun a -> fst a, state.CurrentEnv.LambdaScope)) }
                                else
                                    { baseEnv with
                                        MutableVariables = filteredMutables }

                            Some
                                { Type = TName(Identifier.Simple "Unit")
                                  State = { state' with CurrentEnv = newEnv } }

                        | Error msg ->
                            let report =
                                { ErrorType = ErrorType.Type
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                  EnclosingPosition = Some rhs.Pos, Some rhs.Pos'
                                  Description =
                                    sprintf "%s (according to the definition of the %s's pattern)." msg letVar
                                  AllLines = state.CurrentEnv.AllLines
                                  Informations = Seq.empty
                                  Hint = null }

                            errorQueue.AddError report
                            None
                    | None -> None
                | None -> None

            | Tuple items ->
                let rec loop state acc =
                    function
                    | [] ->
                        Some
                            { Type = TTuple(List.rev acc)
                              State = state }

                    | e :: rest ->
                        match inferExpression e state errorQueue with
                        | Some result -> loop result.State (result.Type :: acc) rest
                        | None -> None

                loop state [] items

            | List items ->
                let rec loop state accTypes accValues index =
                    function
                    | [] ->
                        match accTypes with
                        | [] ->
                            let elemType, state = InferenceState.freshVar state

                            Some
                                { Type = TApp(Identifier.Simple "List", [ elemType ])
                                  State = state }

                        | firstType :: rest ->
                            let rec checkTypes state idx tList =
                                match tList with
                                | [] -> state, None
                                | t :: ts ->
                                    match Unify.unify null t firstType state with
                                    | Ok state' -> checkTypes state' (idx + 1) ts
                                    | Error _ -> state, Some(idx, t)

                            match checkTypes state 1 rest with
                            | state, None ->
                                Some
                                    { Type = TApp(Identifier.Simple "List", [ firstType ])
                                      State = state }

                            | _, Some(relativeIndex, conflictType) ->
                                let actualIndex = relativeIndex

                                let report =
                                    { ErrorType = ErrorType.Type
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                      EnclosingPosition = Some items.[actualIndex].Pos, Some items.[actualIndex].Pos'
                                      Description =
                                        sprintf
                                            "The %dnth item of the list has the type %s, but it was expected to have the type %s."
                                            actualIndex
                                            (MonoType.PrettyPrint.colored (MonoType.PrettyPrint.prettyPrintMonoType conflictType))
                                            (MonoType.PrettyPrint.colored (MonoType.PrettyPrint.prettyPrintMonoType firstType))
                                      AllLines = state.CurrentEnv.AllLines
                                      Informations = Seq.empty
                                      Hint = "All items in a list should be of the same type (note: we start counting from 0)." }

                                errorQueue.AddError report
                                None

                    | e :: rest ->
                        match inferExpression e state errorQueue with
                        | Some result ->
                            loop
                                result.State
                                (accTypes @ [ result.Type ])
                                (accValues @ [ result.Type ])
                                (index + 1)
                                rest
                        | None -> None

                loop state [] [] 0 items

            | Range range ->
                let unifyOpt a b st =
                    match Unify.unify "range" a b st with
                    | Ok st' -> Some st'
                    | Error msg ->
                        let report =
                            { ErrorType = ErrorType.Type
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                              EnclosingPosition = Some range.RangeStart.Pos, Some range.RangeStop.Pos'
                              Description = sprintf "%s (according to the starting item)." msg
                              AllLines = state.CurrentEnv.AllLines
                              Informations = []
                              Hint =
                                "All items in the range must be of the same type and all elements of the range must be enumerable." }

                        errorQueue.AddError report
                        None

                match inferExpression range.RangeStart state errorQueue with
                | None -> None
                | Some inferedStart ->
                    let stepResult =
                        match range.RangeStep with
                        | Some stepExpr ->
                            match inferExpression stepExpr inferedStart.State errorQueue with
                            | Some stepInfer -> Some(Some stepInfer)
                            | None -> None
                        | None -> Some None

                    match stepResult with
                    | None -> None
                    | Some inferedStep ->
                        let stateForStop =
                            match inferedStep with
                            | Some s -> s.State
                            | None -> inferedStart.State

                        match inferExpression range.RangeStop stateForStop errorQueue with
                        | None -> None
                        | Some inferedStop ->
                            match unifyOpt inferedStart.Type inferedStop.Type inferedStop.State with
                            | None -> None
                            | Some state1 ->
                                let finalStateResult =
                                    match inferedStep with
                                    | Some step -> unifyOpt inferedStart.Type step.Type state1
                                    | None -> Some state1

                                match finalStateResult with
                                | None -> None
                                | Some finalState ->
                                    Some
                                        { Type = TApp(Identifier.Simple "List", [ inferedStart.Type ])
                                          State = finalState }

            | ExpressionSequence exprs ->
                let unitType = TName(Identifier.Simple "Unit")

                let rec loop state lastType =
                    function
                    | [] ->
                        let finalType = Option.defaultValue unitType lastType
                        Some { Type = finalType; State = state }

                    | [ e ] -> // The last expression has the resulting type
                        match inferExpression e state errorQueue with
                        | Some result -> Some result
                        | None -> None

                    | e :: rest -> // Intermediate expression must be Unit-typed
                        match inferExpression e state errorQueue with
                        | None -> None
                        | Some result when result.Type = unitType -> loop result.State (Some result.Type) rest
                        | Some result ->
                            let report =
                                { ErrorType = ErrorType.Type
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.BadIntermediateExpressionSequenceTypeError
                                  EnclosingPosition = Some e.Pos, Some e.Pos'
                                  AllLines = state.CurrentEnv.AllLines
                                  Description =
                                    sprintf
                                        "Expected type %s for intermediate sequential expression, but got %s."
                                        (MonoType.PrettyPrint.colored "Unit")
                                        (MonoType.PrettyPrint.mainType result.Type)
                                  Informations = List.empty
                                  Hint =
                                    "Only the last expression in a sequence of expressions indicates the return type." }

                            errorQueue.AddError report
                            None

                loop state None exprs

            | ReAssign(v, value) ->
                match inferExpression value state errorQueue with
                | None -> None
                | Some valueResult ->
                    match InferenceState.lookupVariable v valueResult.State with
                    | None ->
                        let suggestion =
                            Liyh.Utils.DamerauLevenshtein.suggest v (List.map fst valueResult.State.CurrentEnv.MutableVariables)
                            |> Liyh.Utils.DamerauLevenshtein.formatSuggestions "the variable"

                        let report =
                            { ErrorType = ErrorType.Semantic
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnfoundVariableError
                              EnclosingPosition = Some exprwp.Pos, Some exprwp.Pos'
                              Description = sprintf "The (mutable) variable %s was not found in this scope." (Variable.colored v)
                              AllLines = valueResult.State.CurrentEnv.AllLines
                              Informations = [ suggestion ]
                              Hint = null }

                        errorQueue.AddError report
                        None

                    | Some(ty, _) ->
                        let isMutable = List.contains v (List.map fst valueResult.State.CurrentEnv.MutableVariables)

                        if not isMutable then
                            let report =
                                { ErrorType = ErrorType.Semantic
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.ImmutableVariableMutationError
                                  EnclosingPosition = Some exprwp.Pos, Some value.Pos'
                                  Description =
                                      sprintf "The variable %s was not declared as mutable and cannot be reassigned." (Variable.colored v)
                                  AllLines = valueResult.State.CurrentEnv.AllLines
                                  Informations = []
                                  Hint =
                                      sprintf
                                          "Use `var` to declare mutable variables or overwrite the previous binding with a new definition of %s."
                                          (Variable.colored v) }

                            errorQueue.AddError report
                            None
                        else
                            let variableLambdaScope = List.find (fst >> ( = ) v) state.CurrentEnv.MutableVariables |> snd
                            if state.CurrentEnv.LambdaScope > variableLambdaScope then
                                let report =
                                    { ErrorType = ErrorType.Semantic
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.ReadOnlyLambdaError
                                      EnclosingPosition = Some exprwp.Pos, Some value.Pos'
                                      Description = sprintf "You are trying to modify the external variable %s inside a lambda expression, which is not allowed." (Variable.colored v)
                                      AllLines = valueResult.State.CurrentEnv.AllLines
                                      Informations = [ sprintf "The variable %s was defined outside the lambda." (Variable.colored v) ]
                                      Hint = sprintf "Lambda are read-only: you can read %s inside but not change it." (Variable.colored v) }
                                errorQueue.AddError report
                                None
                            else
                                match Unify.unify null ty valueResult.Type valueResult.State with
                                | Ok state' ->
                                    Some
                                        { Type = TName(Identifier.Simple "Unit")
                                          State = state' }

                                | Error msg ->
                                    let report =
                                        { ErrorType = ErrorType.Type
                                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                          EnclosingPosition = Some value.Pos, Some value.Pos'
                                          Description = sprintf "%s for the mutation of the variable %s." msg (Variable.colored v)
                                          AllLines = valueResult.State.CurrentEnv.AllLines
                                          Informations = []
                                          Hint = "Variables are strongly typed, which means that they cannot change type." }
                                    errorQueue.AddError report
                                    None

            | Record fields ->
                let rec loop state acc =
                    function
                    | [] ->
                        Some
                            { Type = TRecord(List.rev acc)
                              State = state }

                    | (name, ewp) :: rest ->
                        match inferExpression ewp state errorQueue with
                        | Some result -> loop result.State ((name, result.Type) :: acc) rest
                        | None -> None

                loop state [] fields

            | Match m ->
                match inferExpression m.ToMatch state errorQueue with
                | None -> None
                | Some scrResult ->
                    let rec processCases state resTy cases =
                        match cases with
                        | [] ->
                            let finalType = defaultArg resTy (TName(Identifier.Simple "Unit"))

                            Some { Type = finalType; State = state }

                        | (pat, body) :: rest ->
                            match PatternInference.inferPattern pat state errorQueue with
                            | None -> None
                            | Some inferedPattern ->
                                match Unify.unify "match's cases" scrResult.Type inferedPattern.Type inferedPattern.State with
                                | Error msg ->
                                    let report =
                                        { ErrorType = ErrorType.Type
                                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                          EnclosingPosition = Some pat.Pos, Some pat.Pos'
                                          Description = sprintf "%s." msg
                                          AllLines = state.CurrentEnv.AllLines
                                          Informations = []
                                          Hint =
                                            "Each case's pattern of a match-expression must have the same type as the matched expression." }

                                    errorQueue.AddError report
                                    None

                                | Ok state' ->
                                    let envWithBindings = Env.extend state'.CurrentEnv inferedPattern.Bindings

                                    let state' =
                                        { state' with
                                            CurrentEnv = envWithBindings }

                                    match inferExpression body state' errorQueue with
                                    | None -> None
                                    | Some bodyResult ->
                                        match resTy with
                                        | None -> processCases bodyResult.State (Some bodyResult.Type) rest
                                        | Some r ->
                                            match Unify.unify "case's value" r bodyResult.Type bodyResult.State with
                                            | Error msg ->
                                                let report =
                                                    { ErrorType = ErrorType.Type
                                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                                      EnclosingPosition = Some body.Pos, Some body.Pos'
                                                      Description = sprintf "%s." msg
                                                      AllLines = state.CurrentEnv.AllLines
                                                      Informations = []
                                                      Hint =
                                                        "Each case's value of a match-expression must return a value of the same type." }

                                                errorQueue.AddError report
                                                None

                                            | Ok st ->
                                                let newR = Substitution.applySubstitution st.CurrentSubst r
                                                processCases st (Some newR) rest

                    // Check equivalent patterns and update the error queue if needed.

                    let patterns = List.map fst m.Cases
                    PatternCheck.checkUnreachableAndRedundantPatterns patterns state errorQueue

                    // Check each cases of the pattern.

                    processCases scrResult.State None m.Cases

            | While w ->
                match inferExpression w.Predicate state errorQueue with
                | Some predResult ->
                    match Unify.unify "while-loop" (TName(Identifier.Simple "Bool")) predResult.Type predResult.State with
                    | Ok state' ->
                        match inferExpression w.Body state' errorQueue with
                        | None -> None
                        | Some bodyResult ->
                            match
                                Unify.unify
                                    "while-loop's body"
                                    (TName(Identifier.Simple "Unit"))
                                    bodyResult.Type
                                    bodyResult.State
                            with
                            | Ok result ->
                                Some
                                    { Type = TName(Identifier.Simple "Unit")
                                      State = result }

                            | Error msg ->
                                let report =
                                    { ErrorType = ErrorType.Type
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.LoopReturnTypeError
                                      EnclosingPosition = Some w.Body.Pos', None
                                      Description = sprintf "%s." msg
                                      AllLines = state.CurrentEnv.AllLines
                                      Informations = []
                                      Hint =
                                        sprintf
                                            "Loops are not meant to return a result and their content must therefore be of type %s."
                                            (MonoType.PrettyPrint.colored "Unit") }

                                errorQueue.AddError report
                                None

                    | Error msg ->
                        let report =
                            { ErrorType = ErrorType.Type
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                              EnclosingPosition = Some w.Predicate.Pos, Some w.Predicate.Pos'
                              Description = sprintf "%s." msg
                              AllLines = state.CurrentEnv.AllLines
                              Informations = []
                              Hint = "The predicate of a while loop must be a boolean." }

                        errorQueue.AddError report
                        None

                | None -> None

            | RecordUsing(baseRecord, fields) ->
                match inferExpression baseRecord state errorQueue with
                | None -> None
                | Some inferred1 ->

                    let rec loop state acc =
                        function
                        | [] ->
                            Some
                                { Type = TRecord(List.rev acc)
                                  State = state }

                        | (name, ewp) :: rest ->
                            match inferExpression ewp state errorQueue with
                            | Some result -> loop result.State ((name, result.Type) :: acc) rest
                            | None -> None

                    match loop inferred1.State [] fields with
                    | None -> None
                    | Some inferred2 ->
                        let t1 = Substitution.applySubstitution inferred2.State.CurrentSubst inferred1.Type
                        let t2 = Substitution.applySubstitution inferred2.State.CurrentSubst inferred2.Type

                        match t1, t2 with
                        | TRecord baseRecord, TRecord extensionRecord ->

                            // --- Check that each common fields share the same type --- //

                            let intersectLists l1 l2 =
                                let m1 = Map.ofList l1
                                let m2 = Map.ofList l2

                                (Map.empty, m1)
                                ||> Map.fold (fun acc k v1 ->
                                    match Map.tryFind k m2 with
                                    | Some v2 -> Map.add k (v1, v2) acc
                                    | None -> acc)

                            let result =
                                (Some inferred2.State, intersectLists baseRecord extensionRecord)
                                ||> Map.fold (fun accState fieldName (baseFieldType, extensionFieldType) ->
                                    accState |> Option.bind (fun state -> 
                                        match Unify.unify (sprintf "field `%s`" fieldName) baseFieldType extensionFieldType state with
                                        | Ok state -> Some state
                                        | Error msg ->
                                            let report =
                                                { ErrorType = ErrorType.Type
                                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                                  EnclosingPosition = pos, pos'
                                                  Description = sprintf "%s." msg
                                                  AllLines = state.CurrentEnv.AllLines
                                                  Informations = []
                                                  Hint = "To overwrite the value of a record field, the types must match." }
                                            errorQueue.AddError report
                                            None))

                            result |> Option.map (fun state ->
                                let a = Set.ofList baseRecord + Set.ofList extensionRecord
                                let a = Set.map (fun (fieldName, ty) -> fieldName, Substitution.applySubstitution state.CurrentSubst ty) a
                                let a = Set.toList a
                                { Type = TRecord a
                                  State = state })

                        | _, _ ->
                            match Unify.unify "record overwrite" inferred1.Type inferred2.Type inferred2.State with
                            | Ok state ->

                                //
                                // TODO: The type system for records isn't great; we need to think about a better
                                // design, perhaps with true row polymorphism this time.
                                //

                                // This will force the system to associate the same type with the base record
                                // as with its extension. If we don't do this, then there is no constraint:
                                // "are we adding a field or overwriting one?" It's ambiguous, and enforcing
                                // consistency through unification seems more coherent.
                                //
                                // Records are not truly row-polymorphic but structurally constrained.
                                //
                                // Example:
                                //
                                //      foo['r] -> { 'r using x = 42 }
                                //
                                // The unification of 'r with { x: Int } is the minimum constraint necessary
                                // for the operation to be type-safe.

                                Some
                                    { Type = Substitution.applySubstitution state.CurrentSubst inferred1.Type
                                      State = state }

                            | Error msg ->
                                let report =
                                    { ErrorType = ErrorType.Type
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError // plus spécifique ?
                                      EnclosingPosition = pos, pos'
                                      Description = sprintf "%s." msg
                                      AllLines = state.CurrentEnv.AllLines
                                      Informations = []
                                      Hint = null }
                                errorQueue.AddError report
                                None

            | CollectionAccess collectionAccess ->
                match inferExpression collectionAccess.LHS state errorQueue with
                | None -> None
                | Some inferred ->
                    let tv, state = InferenceState.freshVar inferred.State
                    let tl = Identifier.Simple "List"
                    let dim = collectionAccess.Indices.Length

                    // build List(List(...(tv)...)) with `dim` nestings
                    let rec makeNestedList (elem: MonoType) (d: int) =
                        if d <= 0 then elem
                        else TApp(tl, [ makeNestedList elem (d - 1) ])

                    let intType = TName(Identifier.Simple "Int")

                    let rec checkIndices (st: InferenceState) indices =
                        match indices with
                        | [] -> Some st
                        | idx :: rest ->
                            match inferExpression idx st errorQueue with
                            | None -> None
                            | Some idxInferred ->
                                match Unify.unify "index expression" intType idxInferred.Type idxInferred.State with
                                | Ok st' -> checkIndices st' rest
                                | Error msg ->
                                    let p, p' = idx.Pos, idx.Pos'
                                    let report =
                                        { ErrorType = ErrorType.Type
                                          ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                          EnclosingPosition = Some p, Some p'
                                          Description = sprintf "%s." msg
                                          AllLines = state.CurrentEnv.AllLines
                                          Informations = []
                                          Hint = "Index expressions must evaluate to integers." }
                                    errorQueue.AddError report
                                    None

                    match checkIndices state collectionAccess.Indices with
                    | None -> None
                    | Some stateAfterIndices ->
                        if dim = 0 then failwith "Internal error: zero index"

                        let appliedLhsType = Substitution.applySubstitution stateAfterIndices.CurrentSubst inferred.Type

                        let rec countNestedLists = function
                            | TApp(t, [ inner ]) when t = tl -> 1 + countNestedLists inner
                            | _ -> 0

                        let actualDim = countNestedLists appliedLhsType

                        if actualDim >= 0 && actualDim < dim then
                            let p = (List.head collectionAccess.Indices).Pos
                            let p' = (List.last collectionAccess.Indices).Pos'
                            let report =
                                { ErrorType = ErrorType.Type
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.InvalidRankCollectionAccess
                                  EnclosingPosition = Some p, Some p'
                                  Description = sprintf "Access outside the rank of the collection: you are trying to access a collection of rank %d but the collection is %s, so of rank %d." dim (MonoType.PrettyPrint.mainType inferred.Type) actualDim
                                  AllLines = stateAfterIndices.CurrentEnv.AllLines
                                  Informations = []
                                  Hint = "Provide a number of access indices that is less than or equal to the number of nested collections." }
                            errorQueue.AddError report
                            None
                        else
                            let expected = makeNestedList tv dim

                            match Unify.unify null expected inferred.Type stateAfterIndices with
                            | Error msg ->
                                let report =
                                    { ErrorType = ErrorType.Type
                                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                      EnclosingPosition = Some collectionAccess.LHS.Pos, Some collectionAccess.LHS.Pos'
                                      Description = sprintf "%s." msg
                                      AllLines = stateAfterIndices.CurrentEnv.AllLines
                                      Informations = []
                                      Hint = "Indexing allows you to access an item in a collection, so you must provide a collection." }
                                errorQueue.AddError report
                                None

                            | Ok finalState ->
                                let elemType = Substitution.applySubstitution finalState.CurrentSubst tv
                                Some { Type = elemType; State = finalState }

            | other -> failwithf "todo: infer expression for %A" other

        /// Attempts to infer the type of an expression, returning `None` otherwise with the error queue updated.
        let public inferExpressionType (expr: ExpressionWithPos) (state: InferenceState) (errorQueue: ErrorQueue) =
            inferExpression expr state errorQueue
            |> Option.map (fun result ->
                let finalType = Substitution.applySubstitution result.State.CurrentSubst result.Type
                finalType, result.State)


    //                              //
    // --- Signature processing --- //
    //                              //


    module private ModuleDefinitions =

        /// Check whether the signature given for the symbol is duplicated (in terms of types and patterns).
        /// TODO: TODO
        let private hasEquivalentDefinitions (id: Identifier) (name: string WithPos) (sinfo: SymbolInfo) (state: InferenceState) (errorQueue: ErrorQueue) =
            if sinfo.HasWhenClause then false
            else
                match Map.tryFind id state.CurrentEnv.Symbols with
                | None -> false
                | Some symbols ->
                    match List.tryFind (fun s -> PatternCheck.arePatternListEquivalent sinfo.Patterns s.Patterns state) symbols with
                    | None -> false
                    | Some original ->
                        let report =
                            { ErrorType = ErrorType.Semantic
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.RedundantRuleError
                              EnclosingPosition = Some name.Pos, Some name.Pos'
                              Description =
                                  sprintf
                                      "A pattern-equivalent definition for `%s` has already been given at line %d of %s." name.Node original.Position.Line (fileName state name.Pos)
                              AllLines = state.CurrentEnv.AllLines
                              Informations = []
                              Hint = "Top-level definitions cannot be overridden. You can apply a type annotation to one or more of the arguments to explicitly specify the definition for the expected patterns of this definition or you can specify your definition with a `when-clause` (but the equivalence of definitions by `when-clause` is generally undecidable and, therefore, will not be verified statically)." }
                        errorQueue.AddError report
                        true

        let private getParametersBindings (Rule rule) (state: InferenceState) (errorQueue: ErrorQueue) =
            (([], [], state), rule.Patterns)
            ||> List.fold (fun (bindings, types, state) patt ->
                match PatternInference.inferPattern patt state errorQueue with
                | Some result -> result.Bindings @ bindings, types @ [ result.Type ], result.State
                | None -> bindings, types, state)

        let private updateDefinition id h paramsTypes retType state =
            let refinedParamsTypes = List.map (Substitution.applySubstitution state.CurrentSubst) paramsTypes
            let refinedReturnType = Substitution.applySubstitution state.CurrentSubst retType

            let refinedSignature =
                match refinedParamsTypes with
                | [] -> refinedReturnType
                | pts -> TFun(pts, refinedReturnType)

            let refinedScheme = Scheme(Set.toList (MonoType.getFreeVariables refinedSignature), refinedSignature)

            let refinedSymbolInfo =
                { Option.get (InferenceState.lookupSymbolByHash id h state) with
                    ParametersTypes = refinedParamsTypes
                    ReturnType = refinedReturnType
                    Scheme = refinedScheme }

            InferenceState.updateSymbolInfo id h refinedSymbolInfo state

        let private ruleSignature (Rule rule) (state: InferenceState) (errorQueue: ErrorQueue) =
            let bindings, paramTypes, state' = getParametersBindings (Rule rule) state errorQueue

            let startPosOpt, endPosOpt =
                match rule.Patterns with
                | [] -> None, None
                | h :: t ->
                    let last = List.fold (fun _ x -> x) h t
                    Some h.Pos, Some last.Pos'

            let mutable paramTypes = paramTypes

            match PatternInference.checkNonLinearPatternConsistency bindings state' (startPosOpt, endPosOpt) errorQueue with
            | None -> None
            | Some state' ->

                let returnTypeAnnotation =
                    match rule.Type with
                    | None -> InferenceState.freshVar state'
                    | Some ty -> MonoType.monoTypeFromSyntax ty, state'

                let signatureInfo () =
                    withLocalBindings bindings state' (fun stateWithLocalEnv ->

                        // Check the when-clause

                        let stateWithLocalEnv' =
                            rule.WhenClause
                            |> Option.bind (fun wc ->
                                match ExpressionInference.inferExpressionType wc stateWithLocalEnv errorQueue with
                                | None -> None
                                | Some(ty, stateWithLocalEnv) ->
                                    match Unify.unify "when-clause" (TName (Identifier.Simple "Bool")) ty stateWithLocalEnv with
                                    | Ok st -> Some st
                                    | Error msg ->
                                        let report =
                                            { ErrorType = ErrorType.Type
                                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                                              EnclosingPosition = Some wc.Pos, Some wc.Pos'
                                              AllLines = stateWithLocalEnv.CurrentEnv.AllLines
                                              Description = sprintf "%s." msg
                                              Informations = []
                                              Hint = "when-clause are Boolean predicates." }
                                        errorQueue.AddError report
                                        None)
                            |> Option.defaultValue stateWithLocalEnv

                        let ps = List.map (Substitution.applySubstitution stateWithLocalEnv'.CurrentSubst) paramTypes
                        paramTypes <- ps

                        // Return type (variable type or annotation)

                        Some returnTypeAnnotation
                    )

                match signatureInfo () with
                | None -> None
                | Some(returnType, finalState) ->

                    let signature =
                        match paramTypes with
                        | [] -> returnType
                        | paramTypes -> TFun(paramTypes, returnType)

                    let strategy = Option.defaultValue Innermost rule.Strategy
                    let arity = paramTypes.Length

                    let sinfo =
                        { Position = rule.Name.Pos
                          ParametersTypes = paramTypes
                          Patterns = rule.Patterns
                          ReturnType = returnType
                          Body = Some rule.Body
                          Scheme = Scheme(Set.toList (MonoType.getFreeVariables signature), signature)
                          Strategy = strategy
                          HasWhenClause = rule.WhenClause.IsSome
                          Arity = arity
                          Hash = hash rule }

                    Some (rule.Name, sinfo, finalState)

        let private inferRuleBody (Rule rule) (state: InferenceState) (errorQueue: ErrorQueue) =
            let name = rule.Name.Node
            let id = Identifier.Simple name
            let h = hash rule

            let bindings, paramsTypes, localState = getParametersBindings (Rule rule) state errorQueue
            let mutable pass = false

            // Since each signature is unique, we can retrieve the return type inferred during the first pass
            // and instantiate it here if necessary.

            let paramsTypes, previousReturnType, localState =
                match InferenceState.lookupSymbolByHash id h localState with
                | None ->
                    pass <- true
                    [], TAny, localState // for typechecking
                    //failwithf "The symbol should be accessible at this point: `%s`." name

                | Some prev ->
                    let rt = prev.ReturnType
                    match Unify.unifyMany null (List.zip prev.ParametersTypes paramsTypes) localState with
                    | Error _ -> failwithf "Unification should succeed at this point."
                    | Ok st ->
                        let paramsTypes = List.map (Substitution.applySubstitution st.CurrentSubst) prev.ParametersTypes
                        paramsTypes, rt, st

            if pass then
                printfn "Passed '%s'" name
                None
            else

            withLocalBindings bindings localState (fun stateWithLocalEnv ->
                match ExpressionInference.inferExpressionType rule.Body stateWithLocalEnv errorQueue with
                | None -> None
                | Some(ty, inferredState) ->
                    let cleanState = { inferredState with NextId = inferredState.NextId }

                    match Unify.unify null previousReturnType ty cleanState with
                    | Ok finalState ->
                        // Update the previous types from the first pass with the new informations
                        Some (updateDefinition id h paramsTypes previousReturnType finalState)

                    | Error msg ->
                        let (description, pos, pos') =
                            match rule.Type with
                            | Some n ->
                                let p, p' = Some n.Pos, Some n.Pos'
                                let desc = sprintf "%s by comparing the deduced type for `%s` (according to its value) and the given type annotation." msg name
                                (desc, p, p')

                            | None ->
                                let p, p' = Some rule.Body.Pos', None
                                let desc = sprintf "%s by comparing the deduced type for `%s` and its previous usage." msg name
                                (desc, p, p')

                        let report =
                            { ErrorType = ErrorType.Type
                              ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.TypeMismatchError
                              EnclosingPosition = pos, pos'
                              Description = description
                              AllLines = state.CurrentEnv.AllLines
                              Informations = []
                              Hint = "The return value must have a type that matches the type annotation and/or the definition's value." }

                        errorQueue.AddError report
                        None
            )

        let public typeCheckModule (modl: Liyh.Module.ModuleInfo) (errorQueue: ErrorQueue) =
            let rules = Liyh.Module.Definitions.tryGetByType Liyh.Module.Definitions.Rule modl |> List.map _.Node
            let mutable state = InferenceState.Empty (string modl.Identifier + ".liyh") modl.Text
            let mutable success = true

            // 1. Collect all the signatures
            for (Rule rule) in rules do
                match ruleSignature (Rule rule) state errorQueue with
                | None -> success <- false
                | Some (name, sinfo, state') ->
                    let id = Identifier.Simple name.Node

                    //if hasEquivalentDefinitions id name sinfo state errorQueue then ()
                    //else
                    state <- InferenceState.addSymbolInfo id sinfo state'

            // 2. Solve the remaining constraints
            // (it's done using brute force at the moment, this absolutely must be changed).

            let mutable iteration = 0
            let maxIterations = 5

            while success && iteration < maxIterations do
                for rule in rules do
                    match inferRuleBody rule state errorQueue with
                    | None -> success <- false
                    | Some state' ->
                        state <- state'

                iteration <- iteration + 1

            if success then
                for KeyValue(k, v) in state.CurrentEnv.Symbols do
                    let name = string k
                    for a in InferenceState.sortDefinitions v do
                        let ft = TFun(a.ParametersTypes, a.ReturnType)
                        let inv = if a.Strategy.IsInvalid then Liyh.Utils.ColorTerm.colorize (Liyh.Utils.ColorTerm.Basic "red") " (invalid)" else ""
                        printfn "%s%s%s" name (MonoType.PrettyPrint.prettyPrintMonoType ft) inv

            success, state


    //                                            //
    // --- Entry point of the static analyser --- //
    //                                            //


    let public run (modules: Liyh.Module.ModuleInfo list) (errorQueue: ErrorQueue) =

        for modl in modules do
            let state = ModuleDefinitions.typeCheckModule modl errorQueue
            ()


