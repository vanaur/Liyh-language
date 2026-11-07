namespace Liyh.Semantic

/// Algebraic Data Type & Type Alias elaboration.
module private TypeDefs =
    open Liyh.Syntax.SyntaxTree
    open Liyh.Semantic.TypedSyntaxTree

    /// Registers ADT headers so that the names are known before using them.
    let rec public registerSumTypeHeaders (tsCtx: TypecheckContext) (env: Env) (sumTypes: SumType list) : Env =
        let mutable adtsMap = env.Adts

        for st in sumTypes do
            let typeName = removePos st.Name
            if Map.containsKey typeName adtsMap || Map.containsKey typeName env.TypeAlias then
                let desc = sprintf "Duplicate type declaration: type '%s' is already defined." typeName
                tsCtx.ReportError ErrorCode.DuplicateTypeDeclarationError desc [] null st.Name
            else
                let paramNames = List.map removePos st.VarTypes
                let distinctParams = List.distinct paramNames

                if List.length distinctParams <> List.length paramNames then
                    let desc = sprintf "Duplicate type parameter in declaration of type '%s'." typeName
                    tsCtx.ReportError ErrorCode.DuplicateTypeParameterError desc [] null st.Name

                let adtDef = { Name = typeName; TypeParams = paramNames }
                adtsMap <- Map.add typeName adtDef adtsMap

        { env with Adts = adtsMap }

    /// Resolves ADT constructors and elaborates them into TTypeDef top-level declarations.
    and public registerSumTypeConstructors
        (tsCtx: TypecheckContext)
        (env: Env)
        (sumTypes: SumType list)
        : Env * TTopLevel list
        =
        let mutable ctorsMap = env.Constructors
        let mutable elaboratedSumTypes = []

        for st in sumTypes do
            let typeName = removePos st.Name
            let typeParamNames = List.map removePos st.VarTypes
            let scope = TypeScope.create()

            let typeParamRefs =
                List.map (fun paramName ->
                    match TypeScope.getOrAddTypeVar scope paramName with
                    | TVar r -> r
                    | _ -> failwith "unreachable") typeParamNames

            let resultType =
                if List.isEmpty typeParamRefs then TApp(typeName, [])
                else TApp(typeName, List.map TVar typeParamRefs)

            let mutable elaboratedCtors = []

            for ctorWp in st.Constructors do
                let ctor = removePos ctorWp
                let ctorName = removePos ctor.Name
                let resolvedArgs = List.map (resolveType tsCtx scope env) ctor.ArgumentsType

                let cdef =
                    { Name = ctorName
                      TypeName = typeName
                      TypeParams = typeParamRefs
                      ArgTypes = resolvedArgs
                      ResultType = resultType }

                let qualifiedKey = sprintf "%s.%s" typeName ctorName
                ctorsMap <- Map.add qualifiedKey [ cdef ] ctorsMap

                let currentList = Map.tryFind ctorName ctorsMap |> Option.defaultValue []
                ctorsMap <- Map.add ctorName (currentList @ [ cdef ]) ctorsMap

                let ctorIdent = tsCtx.CreateIdent { Qualifier = []; Name = ctor.Name } (SymbolKind.Constructor typeName) (Some (spanOf ctor.Name))
                let tsig : TSignature =
                    { SigSymbol = ctorIdent
                      SigArguments = resolvedArgs
                      SigReturn = Some resultType }

                let tsigWp : TSignatureWithPos = { Node = tsig; StartPos = ctorWp.StartPos; EndPos = ctorWp.EndPos }
                elaboratedCtors <- tsigWp :: elaboratedCtors

            let sumIdent = tsCtx.CreateIdent { Qualifier = []; Name = st.Name } SymbolKind.PureSymbol (Some (spanOf st.Name))
            let tsum : TSumType =
                { SumSymbol = sumIdent
                  SumTypeVars = st.VarTypes
                  SumConstructors = List.rev elaboratedCtors }

            let endPos =
                match st.Constructors with
                | [] -> st.Name.EndPos
                | ctors -> (List.last ctors).EndPos

            let tTop : TTopLevel =
                { Node = TTopLevelNode.TTypeDef tsum
                  StartPos = st.Name.StartPos
                  EndPos = endPos }

            elaboratedSumTypes <- tTop :: elaboratedSumTypes

        ({ env with Constructors = ctorsMap }, List.rev elaboratedSumTypes)

    /// Registers new type aliases to the environment and elaborates them into TTypeAliasDef declarations.
    and public registerTypeAliases
        (tsCtx: TypecheckContext)
        (env: Env)
        (aliases: (NameWithPos * NameWithPos list * TypeWithPos) list)
        : Env * TTopLevel list
        =
        let mutable validAliases = []
        let mutable knownNames = Set.union (Map.keys env.TypeAlias |> Set.ofSeq) (Map.keys env.Adts |> Set.ofSeq)

        for (nameWp, varTypesWp, targetTypeWp) in aliases do
            let aliasName = removePos nameWp

            if Set.contains aliasName knownNames then
                let desc = sprintf "Duplicate type declaration: type '%s' is already defined." aliasName
                tsCtx.ReportError ErrorCode.DuplicateTypeDeclarationError desc [] null nameWp
            else
                knownNames <- Set.add aliasName knownNames
                let paramNames = List.map removePos varTypesWp
                let distinctParams = List.distinct paramNames

                if List.length distinctParams <> List.length paramNames then
                    let desc = sprintf "Duplicate type parameter in declaration of type alias '%s'." aliasName
                    tsCtx.ReportError ErrorCode.DuplicateTypeParameterError desc [] null nameWp

                /// Checks that the free variables in the target type are correctly declared in the parameters.
                let rec checkUnboundTypeVars (t: TypeWithPos) =
                    match removePos t with
                    | VariableType name ->
                        if not (List.contains name paramNames) then
                            let desc = sprintf "Type variable `%s` is unbound in definition of type alias '%s'." name aliasName
                            tsCtx.ReportError ErrorCode.UnboundTypeVariableError desc [] null t

                    | RuleType(args, ret) ->
                        List.iter checkUnboundTypeVars args
                        checkUnboundTypeVars ret

                    | TupleType ts ->
                        List.iter checkUnboundTypeVars ts

                    | RowRecordType fields ->
                        List.iter (snd >> checkUnboundTypeVars) fields

                    | ParametrizedType(_, args) ->
                        List.iter checkUnboundTypeVars args

                    | ModuloEffectType(baseT, _) ->
                        checkUnboundTypeVars baseT

                    | (NamedType _ | WildcardType) -> ()

                checkUnboundTypeVars targetTypeWp
                validAliases <- (aliasName, nameWp, varTypesWp, targetTypeWp) :: validAliases

        let aliasMap =
            validAliases
            |> List.map (fun (name, nameWp, varTypesWp, target) -> name, (nameWp, varTypesWp, target))
            |> Map.ofList

        /// Returns the set of named type dependencies of the given type `t`.
        let rec collectAliasDeps (t: TypeWithPos) : Set<string> =
            match removePos t with
            | NamedType id when List.isEmpty id.Qualifier ->
                Set.singleton (removePos id.Name)

            | ParametrizedType(idWp, args) when List.isEmpty (removePos idWp).Qualifier ->
                let head = Set.singleton (removePos (removePos idWp).Name)
                let sub = args |> List.map collectAliasDeps |> Set.unionMany
                head + sub

            | RuleType(args, ret) ->
                (args |> List.map collectAliasDeps |> Set.unionMany) + collectAliasDeps ret

            | TupleType ts ->
                ts |> List.map collectAliasDeps |> Set.unionMany

            | RowRecordType fields ->
                fields |> List.map (snd >> collectAliasDeps) |> Set.unionMany

            | ModuloEffectType(baseT, _) ->
                collectAliasDeps baseT

            | _ -> Set.empty

        // Topological sorting with cycle detection to ensure that aliases do not create any cycles.
        let mutable visited = Set.empty
        let mutable visiting = Set.empty
        let mutable sortedNames = []

        let rec dfs name =
            if Set.contains name visiting then
                let (nameWp, _, _) = aliasMap.[name]
                let desc = sprintf "Cyclic type alias: '%s' expands to itself." name
                let hint = "Break the cycle by using an algebraic data type instead of a type alias."
                tsCtx.ReportError ErrorCode.CyclicTypeAliasError desc [] hint nameWp

            elif not (Set.contains name visited) then
                visiting <- Set.add name visiting

                if Map.containsKey name aliasMap then
                    let (_, _, targetWp) = aliasMap.[name]
                    let deps = collectAliasDeps targetWp |> Set.filter (fun d -> Map.containsKey d aliasMap)
                    Set.iter dfs deps

                visiting <- Set.remove name visiting
                visited <- Set.add name visited
                sortedNames <- name :: sortedNames

        for KeyValue(name, _) in aliasMap do
            dfs name

        let mutable currentEnv = env
        let mutable elaboratedAliases = []

        for name in List.rev sortedNames do
            match Map.tryFind name aliasMap with
            | Some (nameWp, varTypesWp, targetTypeWp) ->
                let scope = TypeScope.create()
                let paramNames = List.map removePos varTypesWp
                let typeParamRefs =
                    paramNames
                    |> List.map (fun p ->
                        match TypeScope.getOrAddTypeVar scope p with
                        | TVar r -> r
                        | _ -> failwith "unreachable")

                let targetType = resolveType tsCtx scope currentEnv targetTypeWp

                let aliasDef =
                    { Name = name
                      TypeParams = typeParamRefs
                      TargetType = targetType
                      NamePos = nameWp }

                currentEnv <- { currentEnv with TypeAlias = Map.add name aliasDef currentEnv.TypeAlias }

                let aliasIdent = tsCtx.CreateIdent { Qualifier = []; Name = nameWp } SymbolKind.PureSymbol (Some (spanOf nameWp))
                let tAlias : TTypeAlias =
                    { AliasSymbol = aliasIdent
                      AliasTypeVars = varTypesWp
                      AliasTarget = targetType }

                let tTop : TTopLevel =
                    { Node = TTopLevelNode.TTypeAliasDef tAlias
                      StartPos = nameWp.StartPos
                      EndPos = targetTypeWp.EndPos }

                elaboratedAliases <- tTop :: elaboratedAliases

            | None -> ()

        (currentEnv, List.rev elaboratedAliases)

