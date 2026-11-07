namespace Liyh.Semantic

[<AutoOpen>]
module private Helpers =
    open System.Linq
    open Liyh.Utils
    open Liyh.Syntax.SyntaxTree
    open Liyh.Semantic.TypedSyntaxTree

    /// Active pattern for AST identifier without qualifiers.
    let inline public (|UnqualifiedIdentifier|_|) (id: Identifier) =
        if List.isEmpty id.Qualifier then Some (removePos id.Name)
        else None

    /// Active pattern for AST identifier with qualifiers
    let inline public (|QualifiedIdentifier|) (id: Identifier) =
        (List.map removePos id.Qualifier, removePos id.Name)

    /// Using the Damerau-Levenshtein method, suggest alternatives based on the lexical env
    /// for an unbound identifier values.
    let private suggestAlternatives (label: string) (original: string) (keys: string seq) =
        keys
        |> DamerauLevenshtein.suggest original
        |> DamerauLevenshtein.formatSuggestions label

    /// Using the Damerau-Levenshtein method, suggest alternatives based on the lexical env
    /// for an unbound identifier values (variable, rule, constructor or symbols).
    let public suggestAlternativesIdentifiers (env: Env) (original: string) =
        let externKeys = env.Externs.Keys |> Seq.map (fun (lib, fn) -> sprintf "%s.%s" lib fn) |> _.ToList()

        Seq.concat [ env.Signatures.Keys; env.Constructors.Keys; env.DeclaredSymbols; env.Notations.Keys; externKeys ]
        |> suggestAlternatives "the known identifier" original

    /// Using the Damerau-Levenshtein method, suggest alternatives based on the lexical env
    /// for an unbound type name.
    let public suggestAlternativesNamedTypes (env: Env) (original: string) =
        let nativeTypeNames = [ "Unit"; "Int"; "Float"; "String"; "Char"; "Bool" ].ToList()
        Seq.concat [ env.Adts.Keys; env.TypeAlias.Keys; nativeTypeNames ]
        |> suggestAlternatives "the known type name" original

    /// Using the Damerau-Levenshtein method, suggest alternatives based on the lexical env
    /// for an unbound effect name.
    let public suggestAlternativesEffects (env: Env) (original: string) =
        env.Effects.Keys
        |> suggestAlternatives "the known effect" original

    let public showInlinePosition (wp: WithPos<_>) =
        sprintf "at ln %d of '%s'" wp.Line wp.File

    /// Merges the variable bindings in a pattern and unify duplicate variables (non-linear patterns).
    let public mergeBindings
        (tsCtx: TypecheckContext)
        (parentPosition: WithPos<_>)
        (maps: Map<string, ResolvedIdent * LiyhType> list)
        : Map<string, ResolvedIdent * LiyhType>
        =

        List.fold (fun acc m ->
            Map.fold (fun acc' varName (varIdent, varType) ->
                match Map.tryFind varName acc' with
                | Some (existingIdent, existingType) ->
                    // Non-linear pattern constraint the equality of the type.
                    try
                        Unification.unify tsCtx existingType varType
                    with
                    | UnifyException d ->
                        let desc = sprintf "Non-linear pattern variable '%s' has conflicting types: %s." varName d.Message
                        let hint = "Variables with the same name in a single pattern must share the exact same type."

                        tsCtx.ReportError ErrorCode.IncompatibleNonLinearVariablesError desc [] hint parentPosition
                    acc'
                | None ->
                    Map.add varName (varIdent, varType) acc'
            ) acc m
        ) Map.empty maps

    /// Returns the specified environment, updated with new bindings.
    let public envWithBindings (env: Env) (bindings: Map<string, ResolvedIdent * LiyhType>) : Env =
        let newSignatures =
            Map.fold (fun acc k (_, ty) -> Map.add k [ Scheme.empty ty ] acc) env.Signatures bindings

        let newLocals =
            Map.fold (fun acc k (ident, ty) ->
                let local =
                    { LexicalDepth = env.LambdaDepth
                      Ident = ident
                      Type = ty
                      Used = ref false }
                Map.add k local acc) env.Locals bindings

        { env with Signatures = newSignatures; Locals = newLocals }

    /// Adds a signature' scheme to the environment.
    let public addOverload (name: string) (scheme: Scheme) (env: Env) =
        let current = Map.tryFind name env.Signatures |> Option.defaultValue []
        { env with Signatures = Map.add name (current @ [ scheme ]) env.Signatures }
