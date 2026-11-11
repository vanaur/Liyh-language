namespace Liyh.Semantic

[<AutoOpen>]
module private Helpers =
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

        let relevantIdentifiers = seq {
            env.LocalScope.Externs.Keys |> Seq.map (fun (lib, fn) -> sprintf "%s.%s" lib fn)
            env.ImportedScope.Externs.Keys |> Seq.map (fun (lib, fn) -> sprintf "%s.%s" lib fn)

            env.LocalScope.Signatures.Keys
            env.ImportedScope.Signatures.Keys

            env.LocalScope.Constructors.Keys
            env.ImportedScope.Constructors.Keys

            env.DeclaredSymbols
        }

        relevantIdentifiers
        |> Seq.concat
        |> Seq.distinct
        |> suggestAlternatives "the known identifier" original

    /// Using the Damerau-Levenshtein method, suggest alternatives based on the lexical env
    /// for an unbound type name.
    let public suggestAlternativesNamedTypes (env: Env) (original: string) =
        let nativeTypeNames = seq { "Unit"; "Int"; "Float"; "String"; "Char"; "Bool" }

        let relevantIdentifiers = seq {
            nativeTypeNames

            env.LocalScope.Adts.Keys
            env.ImportedScope.Adts.Keys

            env.LocalScope.TypeAlias.Keys
            env.ImportedScope.TypeAlias.Keys
        }

        Seq.concat relevantIdentifiers
        |> suggestAlternatives "the known type name" original

    /// Using the Damerau-Levenshtein method, suggest alternatives based on the lexical env
    /// for an unbound effect name.
    let public suggestAlternativesEffects (env: Env) (original: string) =
        seq { env.LocalScope.Effects.Keys; env.ImportedScope.Effects.Keys }
        |> Seq.concat
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
            Map.fold (fun acc k (_, ty) -> Map.add k [ Scheme.empty ty ] acc) env.LocalScope.Signatures bindings

        let newLocals =
            Map.fold (fun acc k (ident, ty) ->
                let local =
                    { LexicalDepth = env.LambdaDepth
                      Ident = ident
                      Type = ty
                      Used = ref false }
                Map.add k local acc) env.Locals bindings

        { env.WithLocalSignatures(newSignatures) with Locals = newLocals }

    /// Adds a signature' scheme to the environment.
    let public addOverload (name: string) (scheme: Scheme) (env: Env) =
        let current = Map.tryFind name env.LocalScope.Signatures |> Option.defaultValue []
        env.WithLocalSignatures (Map.add name (current @ [ scheme ]) env.LocalScope.Signatures)
