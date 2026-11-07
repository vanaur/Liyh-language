namespace Liyh.Semantic

[<AutoOpen>]
module private TypeResolve =
    open Liyh.Syntax.SyntaxTree
    open Liyh.FFI.GeneralFFI

    /// Converts the AST representation of effects to a set of effect's names, and reports errors
    /// if any effect does not exists in the given environment.
    let rec public resolveEffects (tsCtx: TypecheckContext) (env: Env) (effects: IdentifierWithPos list) : Set<string> =
        effects
        |> List.map (fun idWithPos ->
            let effectName = string (removePos idWithPos)

            if not (Map.containsKey effectName env.Effects) then
                let desc = sprintf "No effect named '%s' was found in the current environment." effectName
                let infos = [ suggestAlternativesEffects env effectName ]

                tsCtx.ReportError ErrorCode.UnknownEffectError desc infos null idWithPos
            effectName)
        |> Set.ofList

    and public resolveCType
        (tsCtx: TypecheckContext)
        (env: Env)
        (ctype: string)
        (decl: WithPos<_>)
        : LiyhType
        =
        match ctype with
        | "UInt8" -> TCType CType.UInt8
        | "Int8" -> TCType CType.Int8
        | "UInt16" -> TCType CType.UInt16
        | "Int16" -> TCType CType.Int16
        | "UInt32" -> TCType CType.UInt32
        | "Int32" -> TCType CType.Int32
        | "UInt64" -> TCType CType.UInt64
        | "Int64" -> TCType CType.Int64
        | "Float32" -> TCType CType.Float32
        | "Float64" -> TCType CType.Float64
        | "LongDouble" -> TCType CType.LongDouble
        | "Char" -> TCType CType.Char
        | "String" -> TCType CType.String
        | "Ptr" -> TCType (CType.Pointer CType.Void)
        | "Void" -> TCType CType.Void
        | _ ->
            let desc = sprintf "Unknown type identifier: `%s`." ctype
            let infos = [ suggestAlternativesNamedTypes env ctype ]
            tsCtx.ReportError ErrorCode.UnknownTypeError desc infos ctype decl
            tsCtx.FreshError ()

    /// Converts an AST type to a LiyhType, reports errors if any AST type does not exists
    /// in the given environment.
    and public resolveType
        (tsCtx: TypecheckContext)
        (scope: TypeScope)
        (env: Env)
        (decl: TypeWithPos)
        : LiyhType
        =

        let inline fail errorCode (desc: string) (infos: string list) (hint: string) =
            tsCtx.ReportError errorCode desc infos hint decl
            tsCtx.FreshError ()

        match removePos decl with

        // Standard Liyh types

        | NamedType(UnqualifiedIdentifier "Int") -> TInt
        | NamedType(UnqualifiedIdentifier "Float") -> TFloat
        | NamedType(UnqualifiedIdentifier "Bool") -> TBool
        | NamedType(UnqualifiedIdentifier "Char") -> TChar
        | NamedType(UnqualifiedIdentifier "String") -> TString
        | NamedType(UnqualifiedIdentifier "Unit") -> TUnit

        // FFI types

        | NamedType(QualifiedIdentifier([ "C" ], ctype)) -> resolveCType tsCtx env ctype decl
        | ParametrizedType({ Node = QualifiedIdentifier([ "C" ], "Ptr") }, [ pointee ]) ->
            let depth, leaf = ForeignTypes.peelCPtr 1 pointee
            let resolved = resolveType tsCtx scope env leaf

            match ForeignTypes.check tsCtx leaf depth resolved with
            | Some cty -> TCType cty
            | None -> ForeignTypes.errorExpectedCType tsCtx leaf resolved

        // Other types

        | NamedType ident ->
            let fullName = string ident

            match Map.tryFind fullName env.TypeAlias with
            | Some aliasDef ->
                let n = List.length aliasDef.TypeParams
                if n > 0 then
                    fail ErrorCode.TypeArityMismatchError
                        (sprintf "Type alias `%s` expects %d type argument(s), but got none." fullName n)
                        [ sprintf "`%s` expects %d parameter(s)." fullName n ]
                        null
                else
                    aliasDef.Expand([])

            | None ->
                match Map.tryFind fullName env.Adts with
                | Some typeDef ->
                    let n = List.length typeDef.TypeParams
                    if n > 0 then
                        fail ErrorCode.TypeArityMismatchError (sprintf "Type `%s` expects %d type argument(s), but got none." fullName n) [] null
                    else
                        TApp(fullName, [])

                | None ->
                    let infos = [ suggestAlternativesNamedTypes env fullName ]
                    fail ErrorCode.UnknownTypeError (sprintf "Unknown type identifier: `%s`." fullName) infos null

        | VariableType name ->
            TypeScope.getOrAddTypeVar scope name

        | RuleType(paramTypes, retType) ->
            let pTypes = paramTypes |> List.map (resolveType tsCtx scope env)

            match removePos retType with
            | ModuloEffectType(innerRet, effects) ->
                let rType = resolveType tsCtx scope env innerRet
                let effNames = resolveEffects tsCtx env effects
                TArrow(pTypes, rType, effNames)

            | _ ->
                let rType = resolveType tsCtx scope env retType
                TArrow(pTypes, rType, Set.empty)

        | TupleType ts ->
            TTuple(ts |> List.map (resolveType tsCtx scope env))

        | RowRecordType fields ->
            let fieldMap =
                fields
                |> List.map (fun (nameWithPos, typeWithPos) ->
                    (removePos nameWithPos, resolveType tsCtx scope env typeWithPos))
                |> Map.ofList

            TRecord(fieldMap, TEmptyRow)

        | ParametrizedType(identWithPos, argTypes) ->
            let ident = removePos identWithPos
            let fullName = string ident
            let resolvedArgs = argTypes |> List.map (resolveType tsCtx scope env)

            match Map.tryFind fullName env.TypeAlias with
            | Some aliasDef ->
                let expectedArity = List.length aliasDef.TypeParams
                let actualArity = List.length resolvedArgs

                if actualArity <> expectedArity then
                    fail ErrorCode.TypeArityMismatchError
                        (sprintf "Type alias `%s` expects %d argument(s), but got %d." fullName expectedArity actualArity)
                        [ sprintf "`%s` expects %d argument(s)." fullName expectedArity ]
                        null
                else
                    aliasDef.Expand(resolvedArgs)

            | None ->
                match Map.tryFind fullName env.Adts with
                | Some typeDef ->
                    let expectedArity = List.length typeDef.TypeParams
                    let actualArity = List.length resolvedArgs

                    if actualArity <> expectedArity then
                        fail ErrorCode.TypeArityMismatchError
                            (sprintf "Type `%s` expects %d argument(s), but got %d." fullName expectedArity actualArity)
                            [ sprintf "`%s` expects parameters: [%s]." fullName (String.concat ", " typeDef.TypeParams) ]
                            null
                    else
                        TApp(fullName, resolvedArgs)

                | None ->
                    let infos = [ suggestAlternativesNamedTypes env fullName ]
                    fail ErrorCode.UnknownTypeError (sprintf "Unknown generic type: '%s'." fullName) infos null

        | ModuloEffectType(baseTypeWithPos, effects) ->
            let baseType = resolveType tsCtx scope env baseTypeWithPos
            let effectNames = resolveEffects tsCtx env effects

            match baseType with
            | TArrow(args, ret, existingEffs) -> TArrow(args, ret, existingEffs + effectNames)
            | other ->
                fail ErrorCode.InvalidEffectAnnotationError
                    "Effects annotations can only be applied to rule or function types."
                    [ sprintf "Type `%s` is not a function." (string other) ]
                    null

        | WildcardType ->
            tsCtx.FreshVar "w"

    /// Resolves and instantiates a constructor within a pattern, using `expectedOpt` to resolve any ambiguity
    /// if several constructors have the same name and arity.
    and public resolveConstructorPattern
        (tsCtx: TypecheckContext)
        (lookupKey: string)
        (arity: int)
        (expectedOpt: LiyhType option)
        (node: WithPos<_>)
        (env: Env)
        : (LiyhType list * LiyhType) option
        =
        Map.tryFind lookupKey env.Constructors
        |> Option.map (fun cdefs ->
            let probe (cdef: ConstructorDef) =
                match expectedOpt with
                | Some exp ->
                    tsCtx.Probe (fun _ ->
                        let _, resType = cdef.Instantiate(tsCtx)
                        Unification.unify tsCtx resType exp)
                | None -> true

            let commit (cdef: ConstructorDef) =
                let argTypes, resType = cdef.Instantiate(tsCtx)
                Option.iter (fun exp -> Unification.unifyOrReport tsCtx resType exp node) expectedOpt
                (argTypes, resType)

            let fallback = (List.init arity (fun _ -> tsCtx.FreshError()), tsCtx.FreshError())

            OverloadResolver.resolve
                tsCtx
                lookupKey
                node
                arity
                cdefs
                (fun c -> List.length c.ArgTypes)
                (fun c -> sprintf "%s.%s" c.TypeName c.Name)
                None
                probe
                commit
                fallback)

