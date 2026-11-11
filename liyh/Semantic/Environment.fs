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
type public Scheme =
    | Scheme of
        typeVars:       (TypeVar ref) list *    // scheme for the classical type variables
        dimVars:        (DimVar ref) list *     // scheme for the dimensional type variables
        body:           LiyhType *              // the actual type
        mangledName:    string                  // the associated mangled name

/// A sum type constructor definition.
type public ConstructorDef =
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
type public SumTypeDef =
    { Name: string
      TypeParams: string list }

/// A type alias definition.
type public TypeAliasDef =
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
type public ExternDef =
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

/// All the static symbol tables in a module (which may be exportable).
type public ModuleScope =
    { Signatures: Map<string, Scheme list>
      Constructors: Map<string, ConstructorDef list>
      Adts: Map<string, SumTypeDef>
      TypeAlias: Map<string, TypeAliasDef>
      Notations: Map<string, Notation>
      Externs: Map<string * string, ExternDef list>
      Units: Map<string, UnitDef>
      Handlers: Map<string, HandlerDef>
      Effects: Map<string, EffectDef> }

    static member Empty =
        { Signatures = BuiltinSignatures.all
          Constructors = Map.empty
          Adts = Map.empty
          TypeAlias = Map.empty
          Notations = Map.empty
          Externs = Map.empty
          Units = Map.empty
          Handlers = Map.empty
          Effects = Map.empty }

/// The environment for type checking and type inference.
type private Env =
    {

      // --- Locally defined and imported symbol tables --- //

      LocalScope: ModuleScope
      ImportedScope: ModuleScope

      // --- What is local to an expression or the body of a rule --- //

      Locals: Map<string, LocalVar>
      Mutables: Map<string, MutableValue>
      LambdaDepth: int

      // --- What is local to an expression or the body of a rule within a symbolic scope --- //

      DeclaredSymbols: Set<string>
      InSymbolicScope: bool }

    static member Empty =
        { LocalScope = ModuleScope.Empty
          ImportedScope = { ModuleScope.Empty with Signatures = Map.empty } // no duplicates with the builtins
          Locals = Map.empty
          Mutables = Map.empty
          LambdaDepth = 0
          DeclaredSymbols = Set.empty
          InSymbolicScope = false }

    member public this.TryFindSignature(name: string) : Scheme list option =
        match Map.tryFind name this.LocalScope.Signatures with
        | Some s -> Some s
        | None -> Map.tryFind name this.ImportedScope.Signatures

    member public this.ContainsSignature(name: string) : bool =
        Map.containsKey name this.LocalScope.Signatures
        || Map.containsKey name this.ImportedScope.Signatures

    member this.TryFindConstructor(name: string) : ConstructorDef list option =
        match Map.tryFind name this.LocalScope.Constructors with
        | Some c -> Some c
        | None -> Map.tryFind name this.ImportedScope.Constructors

    member this.ContainsConstructor(name: string) : bool =
        Map.containsKey name this.LocalScope.Constructors
        || Map.containsKey name this.ImportedScope.Constructors

    member this.TryFindAdt(name: string) : SumTypeDef option =
        match Map.tryFind name this.LocalScope.Adts with
        | Some a -> Some a
        | None -> Map.tryFind name this.ImportedScope.Adts

    member this.ContainsAdt(name: string) : bool =
        Map.containsKey name this.LocalScope.Adts
        || Map.containsKey name this.ImportedScope.Adts

    member this.TryFindTypeAlias(name: string) : TypeAliasDef option =
        match Map.tryFind name this.LocalScope.TypeAlias with
        | Some t -> Some t
        | None -> Map.tryFind name this.ImportedScope.TypeAlias

    member this.ContainsTypeAlias(name: string) : bool =
        Map.containsKey name this.LocalScope.TypeAlias
        || Map.containsKey name this.ImportedScope.TypeAlias

    member this.TryFindNotation(name: string) : Notation option =
        match Map.tryFind name this.LocalScope.Notations with
        | Some n -> Some n
        | None -> Map.tryFind name this.ImportedScope.Notations

    member this.ContainsNotation(name: string) : bool =
        Map.containsKey name this.LocalScope.Notations
        || Map.containsKey name this.ImportedScope.Notations

    member this.TryFindExtern(lib: string, fn: string) : ExternDef list option =
        match Map.tryFind (lib, fn) this.LocalScope.Externs with
        | Some e -> Some e
        | None -> Map.tryFind (lib, fn) this.ImportedScope.Externs

    member this.ContainsExtern(lib: string, fn: string) : bool =
        Map.containsKey (lib, fn) this.LocalScope.Externs
        || Map.containsKey (lib, fn) this.ImportedScope.Externs

    member this.TryFindEffect(name: string) : EffectDef option =
        match Map.tryFind name this.LocalScope.Effects with
        | Some eff -> Some eff
        | None -> Map.tryFind name this.ImportedScope.Effects

    member this.ContainsEffect(name: string) : bool =
        Map.containsKey name this.LocalScope.Effects
        || Map.containsKey name this.ImportedScope.Effects

    member this.WithLocalSignatures(sigs: Map<string, Scheme list>) =
        { this with LocalScope = { this.LocalScope with Signatures = sigs } }

    member this.WithLocalConstructors(ctors: Map<string, ConstructorDef list>) =
        { this with LocalScope = { this.LocalScope with Constructors = ctors } }

    member this.WithLocalAdts(adts: Map<string, SumTypeDef>) =
        { this with LocalScope = { this.LocalScope with Adts = adts } }

    member this.WithLocalTypeAliases(aliases: Map<string, TypeAliasDef>) =
        { this with LocalScope = { this.LocalScope with TypeAlias = aliases } }

    member this.WithLocalNotations(notations: Map<string, Notation>) =
        { this with LocalScope = { this.LocalScope with Notations = notations } }

    member this.WithLocalExterns(externs: Map<string * string, ExternDef list>) =
        { this with LocalScope = { this.LocalScope with Externs = externs } }

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
        env.LocalScope.Signatures
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
            env.LocalScope.Signatures
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


// --- Module handling --- //


/// Represents the public interface exported by a compiled module.
type public ModuleInterface =
    { Identifier: Identifier
      Scope: ModuleScope }

module private Env =

    /// Collect all the named types of the given type.
    let rec private collectNamedTypes (t: LiyhType) : Set<string> =
        match t.Prune() with
        | TApp(name, args) ->
            let sub = args |> List.map collectNamedTypes |> Set.unionMany
            Set.add name sub

        | TArrow(args, ret, _) ->
            (args |> List.map collectNamedTypes |> Set.unionMany) + collectNamedTypes ret

        | TTuple ts ->
            ts |> List.map collectNamedTypes |> Set.unionMany

        | TRecord(fields, rest) ->
            (fields |> Map.values |> Seq.map collectNamedTypes |> Set.unionMany) + collectNamedTypes rest

        | TMeasure(baseT, _) ->
            collectNamedTypes baseT

        | _ -> Set.empty

    /// Checks that no locally defined types marked as private are leaked into exported signatures.
    let public checkInterfaceLeaks (tsCtx: TypecheckContext) (env: Env) (modl: Liyh.Module.ModuleInfo) =
        let exportsSet = Set.ofList (List.map removePos modl.Exports)
        let localAdts = Set.ofSeq env.LocalScope.Adts.Keys
        let localAliases = Set.ofSeq env.LocalScope.TypeAlias.Keys
        let privateLocalTypes = (localAdts + localAliases) - exportsSet

        for expNameWp in modl.Exports do
            let expName = removePos expNameWp

            // Leaks in rules.
            match Map.tryFind expName env.LocalScope.Signatures with
            | None -> ()
            | Some schemes ->
                for Scheme(_, _, body, _) in schemes do
                    let leaked = Set.intersect (collectNamedTypes body) privateLocalTypes
                    if not (Set.isEmpty leaked) then
                        let leakedStr = String.concat ", " leaked
                        let desc = sprintf "Exported symbol '%s' exposes private type(s): %s." expName leakedStr
                        let hint = "Add the private type(s) to the module's export list or make this declaration private."
                        tsCtx.ReportError ErrorCode.PublicExposedSymbolLeak desc [] hint expNameWp

            // Leaks in type constructors
            match Map.tryFind expName env.LocalScope.Adts with
            | None -> ()
            | Some _ ->
                let ctors =
                    env.LocalScope.Constructors
                    |> Map.values
                    |> Seq.concat
                    |> Seq.filter (fun ctor -> ctor.TypeName = expName)

                for cdef in ctors do
                    for argTy in cdef.ArgTypes do
                        let leaked = Set.intersect (collectNamedTypes argTy) privateLocalTypes
                        if not (Set.isEmpty leaked) then
                            let leakedStr = String.concat ", " leaked
                            let desc = sprintf "Exported constructor '%s.%s' exposes private type(s): %s." expName cdef.Name leakedStr
                            let hint = "Export the private type(s) or adjust the constructor signature."
                            tsCtx.ReportError ErrorCode.PublicExposedSymbolLeak desc [] hint expNameWp

            match Map.tryFind expName env.LocalScope.TypeAlias with
            | None -> ()
            | Some aliasDef ->
                let leaked = Set.intersect (collectNamedTypes aliasDef.TargetType) privateLocalTypes
                if not (Set.isEmpty leaked) then
                    let leakedStr = String.concat ", " leaked
                    let desc = sprintf "Exported type alias '%s' expands to private type(s): %s." expName leakedStr
                    let hint = "Export the target type(s) or make this type alias private."
                    tsCtx.ReportError ErrorCode.PublicExposedSymbolLeak desc [] hint expNameWp

    /// Injects a module interface into `ImportedScope`.
    let public extractInterface (modl: Liyh.Module.ModuleInfo) (env: Env) : ModuleInterface =
        let exportsSet = Set.ofList (List.map removePos modl.Exports)

        let exportedConstructors =
            env.LocalScope.Constructors
            |> Map.filter (fun key cdefs ->
                exportsSet.Contains key
                || cdefs |> List.exists (fun ctor -> exportsSet.Contains ctor.TypeName))

        let exportedScope =
            { Signatures = env.LocalScope.Signatures |> Map.filter (fun k _ -> exportsSet.Contains k)
              Constructors = exportedConstructors
              Adts = env.LocalScope.Adts |> Map.filter (fun k _ -> exportsSet.Contains k)
              TypeAlias = env.LocalScope.TypeAlias |> Map.filter (fun k _ -> exportsSet.Contains k)
              Notations = env.LocalScope.Notations |> Map.filter (fun k _ -> exportsSet.Contains k)
              Externs = env.LocalScope.Externs |> Map.filter (fun (_, fn) _ -> exportsSet.Contains fn)
              Units = env.LocalScope.Units |> Map.filter (fun k _ -> exportsSet.Contains k)
              Handlers = env.LocalScope.Handlers |> Map.filter (fun k _ -> exportsSet.Contains k)
              Effects = env.LocalScope.Effects |> Map.filter (fun k _ -> exportsSet.Contains k) }

        { Identifier = modl.Identifier; Scope = exportedScope }

    let public importInterface (depId: Identifier) (aliasOpt: string option) (iface: ModuleInterface) (env: Env) : Env =
        let fullPath = string depId
        let terminalName = removePos depId.Name

        let prefixes =
            match aliasOpt with
            | Some alias ->
                if alias = terminalName then [ terminalName; fullPath ]
                else [ alias ]
            | None ->
                let baseList = [ ""; terminalName ]
                if fullPath <> terminalName then fullPath :: baseList else baseList

        let inline qualify prefix name =
            if System.String.IsNullOrEmpty prefix then name
            else sprintf "%s.%s" prefix name

        let mutable importedSigs = env.ImportedScope.Signatures
        let mutable importedCtors = env.ImportedScope.Constructors
        let mutable importedAdts = env.ImportedScope.Adts
        let mutable importedAliases = env.ImportedScope.TypeAlias
        let mutable importedNotations = env.ImportedScope.Notations
        let mutable importedEffects = env.ImportedScope.Effects

        for prefix in prefixes do
            // Signatures
            for KeyValue(name, schemes) in iface.Scope.Signatures do
                let qualName = qualify prefix name
                let fixedSchemes =
                    schemes
                    |> List.map (fun (Scheme(tvs, dvs, body, mangled)) ->
                        let target = if System.String.IsNullOrEmpty mangled then name else mangled
                        Scheme(tvs, dvs, body, target))

                let existing = Map.tryFind qualName importedSigs |> Option.defaultValue []
                importedSigs <- Map.add qualName (existing @ fixedSchemes) importedSigs

            // ADT constructors
            for KeyValue(name, cdefs) in iface.Scope.Constructors do
                let qualName = qualify prefix name
                let existing = Map.tryFind qualName importedCtors |> Option.defaultValue []
                importedCtors <- Map.add qualName (existing @ cdefs) importedCtors

            // Sum types
            for KeyValue(name, adt) in iface.Scope.Adts do
                importedAdts <- Map.add (qualify prefix name) adt importedAdts

            // Type aliases
            for KeyValue(name, alias) in iface.Scope.TypeAlias do
                importedAliases <- Map.add (qualify prefix name) alias importedAliases

            // Notations
            for KeyValue(name, nt) in iface.Scope.Notations do
                importedNotations <- Map.add name nt importedNotations

            // Effects
            for KeyValue(name, eff) in iface.Scope.Effects do
                importedEffects <- Map.add name eff importedEffects

        let newImportedScope =
            { env.ImportedScope with
                Signatures = importedSigs
                Constructors = importedCtors
                Adts = importedAdts
                TypeAlias = importedAliases
                Notations = importedNotations
                Effects = importedEffects }

        { env with ImportedScope = newImportedScope }
