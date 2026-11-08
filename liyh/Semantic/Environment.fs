#nowarn "40"
namespace rec Liyh.Semantic

open Liyh.FFI
open Liyh.FFI.GeneralFFI
open Liyh.Syntax.SyntaxTree
open Liyh.Semantic.TypedSyntaxTree

[<RequireQualifiedAccess>]
module private TypeSubstitution =

    /// Recursively substitutes type variables in a `LiyhType` using the given map.
    let rec public apply (subst: Map<TypeVar ref, LiyhType>) (ty: LiyhType) : LiyhType =
        if Map.isEmpty subst then ty
        else
            match ty.Prune() with
            | TVar r ->
                match Map.tryFind r subst with
                | Some repl -> repl
                | None -> TVar r

            | TArrow(args, ret, effs) ->
                TArrow(List.map (apply subst) args, apply subst ret, effs)

            | TTuple ts ->
                TTuple(List.map (apply subst) ts)

            | TRecord(fields, rest) ->
                TRecord(Map.map (fun _ -> apply subst) fields, apply subst rest)

            | TApp(name, args) ->
                TApp(name, List.map (apply subst) args)

            | TMeasure(baseT, dim) ->
                TMeasure(apply subst baseT, dim)

            | other -> other

/// A type scheme: `body` with the listed type and dimension variables universally quantified.
/// Other free variables in `body` remain monomorphic.
type private Scheme =
    | Scheme of
        typeVars:       (TypeVar ref) list *    // scheme for the classical type variables
        dimVars:        (DimVar ref) list *     // scheme for the dimensional type variables
        body:           LiyhType *              // the actual type
        mangledName:    string                  // the associated mangled name

/// A sum type constructor definition.
type private ConstructorDef =
    { Name: string
      TypeName: string
      TypeParams: (TypeVar ref) list
      ArgTypes: LiyhType list
      ResultType: LiyhType }

    /// Instantiates the constructor and returns its arguments and return type.
    member public this.Instantiate(tsCtx: TypecheckContext) : LiyhType list * LiyhType =
        if List.isEmpty this.TypeParams then
            (this.ArgTypes, this.ResultType)
        else
            let subst =
                this.TypeParams
                |> List.map (fun r -> (r, tsCtx.FreshVar "a"))
                |> Map.ofList

            (List.map (TypeSubstitution.apply subst) this.ArgTypes, TypeSubstitution.apply subst this.ResultType)

    /// Instantiates the constructor as a single type (arrow or simple type).
    member public this.ToType(tsCtx: TypecheckContext) : LiyhType =
        let args, ret = this.Instantiate(tsCtx)
        if List.isEmpty args then ret else TArrow(args, ret, Set.empty)

type private UnitDef = unit // TODO
type private HandlerDef = unit // TODO
type private EffectDef = unit // TODO

/// A sum type signature definition.
type private SumTypeDef =
    { Name: string
      TypeParams: string list }

/// A type alias definition.
type private TypeAliasDef =
    { Name: string
      TypeParams: (TypeVar ref) list
      TargetType: LiyhType
      NamePos: NameWithPos }

    /// Expands the alias by substituting its formal parameters with the given concrete argument types.
    member public this.Expand(args: LiyhType list) : LiyhType =
        if List.isEmpty this.TypeParams then
            this.TargetType
        else
            let subst = List.zip this.TypeParams args |> Map.ofList
            TypeSubstitution.apply subst this.TargetType

/// A foreign function interface (FFI) definition.
type private ExternDef =
    { Library: string
      FunctionName: string
      Scheme: Scheme }

/// Track mutable variables mutations.
type private MutableValue =
    { LexicalDepth: int
      Mutated: bool ref
      PattDecl: PatternWithPos }

/// Track local variables usage.
type private LocalVar =
    { LexicalDepth: int
      Ident: ResolvedIdent
      Type: LiyhType
      Used: bool ref }

/// The signatures for the built-in functions.
module private BuiltinSignatures =

    let private binInt = TArrow([ TInt; TInt ], TInt, Set.empty)
    let private binFloat = TArrow([ TFloat; TFloat ], TFloat, Set.empty)
    let private cmpInt = TArrow([ TInt; TInt ], TBool, Set.empty)
    let private cmpFloat = TArrow([ TFloat; TFloat ], TBool, Set.empty)
    let private binBool = TArrow([ TBool; TBool ], TBool, Set.empty)
    let private uniBool = TArrow([ TBool ], TBool, Set.empty)

    /// Polymorphic equality predicate: `∀ 'α, ['α; 'α] → Bool`.
    let private polyEq () =
        let a = ref (UnboundVar "a")
        Scheme([ a ], [], TArrow([ TVar a; TVar a ], TBool, Set.empty), "")

    /// Polymorphic display: `∀ 'α, ['α] → String`.
    let private polyShow () =
        let a = ref (UnboundVar "a")
        Scheme([ a ], [], TArrow([ TVar a ], TString, Set.empty), "")

    /// Intrinsic type test predicates: `∀ 'α, ['α] → Bool`.
    let private polyTypeCheck () =
        let a = ref (UnboundVar "a")
        Scheme([ a ], [], TArrow([ TVar a ], TBool, Set.empty), "")

    /// Built-in and natives functions.
    let public all : Map<string, Scheme list> =
        [
            Internals.Add, [ Scheme.empty binInt; Scheme.empty binFloat ]
            Internals.Sub, [ Scheme.empty binInt; Scheme.empty binFloat ]
            Internals.Mul, [ Scheme.empty binInt; Scheme.empty binFloat ]
            Internals.Div, [ Scheme.empty binInt; Scheme.empty binFloat ]
            Internals.Mod, [ Scheme.empty binInt ]

            Internals.Eq,  [ polyEq () ]
            Internals.Neq, [ polyEq () ]
            Internals.Le,  [ Scheme.empty cmpInt; Scheme.empty cmpFloat ]
            Internals.Leq, [ Scheme.empty cmpInt; Scheme.empty cmpFloat ]
            Internals.Ge,  [ Scheme.empty cmpInt; Scheme.empty cmpFloat ]
            Internals.Geq, [ Scheme.empty cmpInt; Scheme.empty cmpFloat ]
            Internals.Nt,  [ Scheme.empty uniBool ]
            Internals.And, [ Scheme.empty binBool ]
            Internals.Or,  [ Scheme.empty binBool ]

            Internals.Strcat, [ Scheme.empty (TArrow([ TString; TString ], TString, Set.empty)) ]
            Internals.Print,  [ Scheme.empty (TArrow([ TString ], TUnit, Set.empty)) ]
            Internals.Ppshow, [ polyShow () ]

            Internals.IsInt,     [ polyTypeCheck () ]
            Internals.IsFloat,   [ polyTypeCheck () ]
            Internals.IsChar,    [ polyTypeCheck () ]
            Internals.IsString,  [ polyTypeCheck () ]
            Internals.IsBool,    [ polyTypeCheck () ]
            Internals.IsNumeric, [ polyTypeCheck () ]

            Internals.CastItf, [ Scheme.empty (TArrow([ TInt ], TFloat, Set.empty)) ]
            Internals.CastItc, [ Scheme.empty (TArrow([ TInt ], TChar, Set.empty)) ]
            Internals.CastIts, [ Scheme.empty (TArrow([ TInt ], TString, Set.empty)) ]

            Internals.CastFti, [ Scheme.empty (TArrow([ TFloat ], TInt, Set.empty)) ]
            Internals.CastFtc, [ Scheme.empty (TArrow([ TFloat ], TChar, Set.empty)) ]
            Internals.CastFts, [ Scheme.empty (TArrow([ TFloat ], TString, Set.empty)) ]

            Internals.CastCti, [ Scheme.empty (TArrow([ TChar ], TInt, Set.empty)) ]
            Internals.CastCtf, [ Scheme.empty (TArrow([ TChar ], TFloat, Set.empty)) ]
            Internals.CastCts, [ Scheme.empty (TArrow([ TChar ], TString, Set.empty)) ]

            Internals.CastSti, [ Scheme.empty (TArrow([ TString ], TInt, Set.empty)) ]
            Internals.CastStf, [ Scheme.empty (TArrow([ TString ], TFloat, Set.empty)) ]
            Internals.CastStc, [ Scheme.empty (TArrow([ TString ], TChar, Set.empty)) ]

            Internals.BufferAlloc,     [ Scheme.empty (TArrow([ TInt ], TCType (CType.Pointer CType.Void), Set.empty)) ]
            Internals.BufferGet,       [ Scheme.empty (TArrow([ TCType (CType.Pointer CType.Void); TInt ], TInt, Set.empty)) ]
            Internals.BufferSet,       [ Scheme.empty (TArrow([ TCType (CType.Pointer CType.Void); TInt; TInt ], TUnit, Set.empty)) ]
            Internals.BufferRealloc,   [ Scheme.empty (TArrow([ TCType (CType.Pointer CType.Void); TInt ], TCType (CType.Pointer CType.Void), Set.empty)) ]
            Internals.BufferLength,    [ Scheme.empty (TArrow([ TCType (CType.Pointer CType.Void) ], TInt, Set.empty)) ]
            Internals.BufferToString,  [ Scheme.empty (TArrow([ TCType (CType.Pointer CType.Void) ], TString, Set.empty)) ]
            Internals.StringToBuffer,  [ Scheme.empty (TArrow([ TString ], TCType (CType.Pointer CType.Void), Set.empty)) ]
        ]
        |> Map.ofList

/// The environment for type checking and type inference.
type private Env =
    { Signatures: Map<string, Scheme list>              // the list of possible signatures
      Constructors: Map<string, ConstructorDef list>    // the list of defined ADT's constructors (list of overloads)
      Units: Map<string, UnitDef>                       // the list of defined units
      Externs: Map<string * string, ExternDef list>     // the list of external functions

      Notations: Map<string, Notation>                  // the list of defined notations

      DeclaredSymbols: Set<string>                      // the list of declared symbols in a symbolic scope
      InSymbolicScope: bool                             // check whether we are in a symbolic scope or not

      LambdaDepth: int                                  // current lexical depth
      Mutables: Map<string, MutableValue>               // the list of current mutable varible by lexical depth and mutation done or not
      Locals: Map<string, LocalVar>                     // the list of local variables

      Adts: Map<string, SumTypeDef>                     // the list of sum types
      TypeAlias: Map<string, TypeAliasDef>              // the list of type alias

      Handlers: Map<string, HandlerDef>                 // the list of defined handlers
      Effects: Map<string, EffectDef> }                 // the list of defined effects

    static member Empty =
        { Signatures = BuiltinSignatures.all
          Constructors = Map.empty
          Units = Map.empty
          Externs = Map.empty

          Notations = Map.empty

          DeclaredSymbols = Set.empty
          InSymbolicScope = false

          LambdaDepth = 0
          Mutables = Map.empty
          Locals = Map.empty

          Adts = Map.empty
          TypeAlias = Map.empty

          Handlers = Map.empty
          Effects = Map.empty }

/// A dictionary `type variable name : actual type variable` for both variables and dimensions.
/// This type allows to keep the same type variables across a given scope.
type private TypeScope =
    { mutable TypeVars: Map<string, TypeVar ref>
      mutable DimVars: Map<string, DimVar ref> }

module private TypeScope =

    /// Creates a new type scope.
    let public create() =
        { TypeVars = Map.empty; DimVars = Map.empty }

    /// Gets of adds a type variable to the given type scope.
    let public getOrAddTypeVar (scope: TypeScope) (name: string) : LiyhType =
        match Map.tryFind name scope.TypeVars with
        | Some r -> TVar r
        | None ->
            let r = ref (UnboundVar name)
            scope.TypeVars <- Map.add name r scope.TypeVars
            TVar r

    /// Gets of adds a dim variable to the given type scope.
    let public getOrAddDimVar (scope: TypeScope) (name: string) : Dimension =
        let r =
            match Map.tryFind name scope.DimVars with
            | Some r -> r
            | None ->
                let r = ref (UnboundDim name)
                scope.DimVars <- Map.add name r scope.DimVars
                r

        Map.ofList [ (DimVar r, Rational.One) ]

module private Scheme =
    let public empty (t: LiyhType) = Scheme([], [], t, "")
    let public emptyWithMangled (m: string) (t: LiyhType) = Scheme([], [], t, m)
    let public getMangledName (Scheme(_, _, _, m)) = m

    /// Returns the set of free dim variables of the given type.
    let rec private freeDimVars (t: LiyhType) : Set<DimVar ref> =
        match t.Prune() with
        | TArrow(args, ret, _) ->
            let fda = args |> List.map freeDimVars |> Set.unionMany
            let fdb = freeDimVars ret

            fda + fdb

        | TTuple ts ->
            ts |> List.map freeDimVars |> Set.unionMany

        | TRecord(fields, rest) ->
            let fda = fields |> Map.values |> Seq.map freeDimVars |> Set.unionMany
            let fdb = freeDimVars rest

            fda + fdb

        | TApp(_, args) ->
            args |> List.map freeDimVars |> Set.unionMany

        | TMeasure(baseT, dim) ->
            let inDim =
                Dimension.prune dim
                |> Map.keys
                |> Seq.choose (function DimVar r -> Some r | _ -> None)
                |> Set.ofSeq

            freeDimVars baseT + inDim

        | _ -> Set.empty

    /// Returns the set of free type variables of the given type.
    let rec private freeVars (t: LiyhType) : Set<TypeVar ref> =
        match t.Prune() with
        | TVar r ->
            Set.singleton r

        | TArrow(args, ret, _) ->
            let fv = args |> List.map freeVars |> Set.unionMany
            fv + freeVars ret

        | TTuple ts ->
            ts |> List.map freeVars |> Set.unionMany

        | TRecord(fields, rest) ->
            let fv = fields |> Map.values |> Seq.map freeVars |> Set.unionMany
            fv + freeVars rest

        | TApp(_, args) ->
            args |> List.map freeVars |> Set.unionMany

        | TMeasure(baseT, _) ->
            freeVars baseT

        | _ -> Set.empty

    /// Returns the set of free type variables of the env signatures.
    let private freeVarsEnv (env: Env) : Set<TypeVar ref> =
        env.Signatures
        |> Map.values
        |> Seq.concat
        |> Seq.map (function Scheme (quantified, _, body, _) -> (freeVars body) - (Set.ofList quantified))
        |> Set.unionMany

    /// Fixes the free variables of the given type that are unbound in the given env.
    ///
    /// Converts a type `t` into a polymorphic type scheme by quantifying the free variables
    /// of `t` that are not already constrained by the environment.
    let public generalizeWithMangled (mangled: string) (env: Env) (t: LiyhType) : Scheme =
        let inTypeTV = freeVars t
        let inEnvTV = freeVarsEnv env
        let forallTV = Set.toList (inTypeTV - inEnvTV)

        let inTypeDV = freeDimVars t
        let inEnvDV =
            env.Signatures
            |> Map.values
            |> Seq.concat
            |> Seq.map (function Scheme(_, dvs, b, _) -> (freeDimVars b - Set.ofList dvs))
            |> Set.unionMany

        let forallDV = Set.toList (inTypeDV - inEnvDV)
        Scheme(forallTV, forallDV, t.Prune(), mangled)

    /// Fixes the free variables of the given type that are unbound in the given env.
    ///
    /// Converts a type `t` into a polymorphic type scheme by quantifying the free variables
    /// of `t` that are not already constrained by the environment.
    let public generalize (env: Env) (t: LiyhType) : Scheme =
        generalizeWithMangled "" env t

    /// Substituates each quantified variables by a fresh new type variable.
    let public instantiate (tsCtx: TypecheckContext) (Scheme(typeVars, dimVars, body, _)) : LiyhType =
        let substType =
            typeVars
            |> List.map (fun r -> (r, tsCtx.FreshVar "a"))
            |> Map.ofList

        let substDim =
            dimVars
            |> List.map (fun r -> (r, Map.ofList [ (DimVar (tsCtx.FreshDim "d"), Rational.One) ]))
            |> Map.ofList

        let rec substituateDimension (d: Dimension) : Dimension =
            Dimension.prune d
            |> Map.fold (fun acc atom coeff ->
                match atom with
                | DimVar r ->
                    match Map.tryFind r substDim with
                    | Some repl -> Dimension.mul acc (Dimension.scale coeff repl)
                    | None -> Dimension.mul acc (Map.ofList [ (atom, coeff) ])
                | _ -> Dimension.mul acc (Map.ofList [ (atom, coeff) ])
            ) Dimension.empty

        let rec loop (t: LiyhType) =
            match t.Prune() with
            | TVar r -> Map.tryFind r substType |> Option.defaultValue (TVar r)
            | TArrow(args, ret, effs) -> TArrow(List.map loop args, loop ret, effs)
            | TTuple ts -> TTuple(List.map loop ts)
            | TRecord(f, r) -> TRecord(Map.map (fun _ -> loop) f, loop r)
            | TMeasure(baseT, dim) -> TMeasure(loop baseT, substituateDimension dim)
            | TApp(name, args) -> TApp(name, List.map loop args)
            | other -> other

        loop body

