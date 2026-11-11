#nowarn "3370"
namespace Liyh.Semantic

module public TypeChecker =
    open Liyh.Module
    open Liyh.Utils
    open Liyh.Utils.ErrorReporter
    open Liyh.Syntax.SyntaxTree
    open Liyh.Semantic.TypedSyntaxTree

    let private typecheckModule
        (sourceManager: SourceManager)
        (errorQueue: ErrorQueue)
        (importedInterfaces: Map<string, ModuleInterface>)
        (modl: ModuleInfo)
        : TModule * ModuleInterface
        =


        // --- Setup the administrative context --- //


        let modulePath = LiyhPackage.identifierToPath modl.Identifier

        let lines =
            sourceManager.TryGetLines modulePath
            |> Option.orElseWith (fun () -> sourceManager.TryGetLines (System.IO.Path.GetFullPath modulePath))
            |> Option.defaultWith (fun _ -> failwithf "unknown source: '%s'." modulePath)

        let tsCtx = TypecheckContext(lines)
        let mutable env = Env.Empty

        // Injection of direct (non-transitive) dependency interfaces.
        for KeyValue(depId, aliasOpt) in modl.Uses do
            let fullKey = string depId
            let nameKey = removePos depId.Name

            let ifaceOpt =
                match Map.tryFind fullKey importedInterfaces with
                | Some iface -> Some iface
                | None -> Map.tryFind nameKey importedInterfaces

            match ifaceOpt with
            | Some iface -> env <- Env.importInterface depId aliasOpt iface env
            | None -> ()

        // Build the typed AST's definitions.
        let elaboratedDeclarations = ResizeArray<TTopLevel>()


        // --- Retrieves all the definitions --- //


        let notations =
            Definitions.tryGetByType Definitions.Notation modl
            |> List.choose (removePos >> function
                | Notation nt -> Some nt
                | _ -> None)

        let sumTypes =
            Definitions.tryGetByType Definitions.Type modl
            |> List.choose (removePos >> function
                | Type st -> Some st
                | _ -> None)

        let typeAliases =
            Definitions.tryGetByType Definitions.TypeAlias modl
            |> List.choose (removePos >> function
                | TypeAlias(name, vars, target) -> Some(name, vars, target)
                | _ -> None)

        let rules =
            Definitions.tryGetByType Definitions.Rule modl
            |> List.choose (removePos >> function
                | Rule rule -> Some (rule, false)
                | LetRule rule -> Some (rule, true)
                | _ -> None)

        let externs =
            Definitions.tryGetByType Definitions.Extern modl
            |> List.choose (removePos >> function
                | Extern extrn -> Some extrn
                | _ -> None)


        // --- Register them in the environment --- //


        env <- Mixfix.registerNotations tsCtx env notations
        for nt in notations do
            let tTop =
                { Node = TTopLevelNode.TNotationDef nt
                  StartPos = nt.NotationName.StartPos
                  EndPos = nt.NotationName.EndPos }
            elaboratedDeclarations.Add(tTop)

        let (envAfterExterns, externDecls) = Rules.registerExternDefinitions tsCtx env externs
        env <- envAfterExterns
        elaboratedDeclarations.AddRange(externDecls)

        env <- TypeDefs.registerSumTypeHeaders tsCtx env sumTypes

        let (envAfterAlias, aliasDecls) = TypeDefs.registerTypeAliases tsCtx env typeAliases
        env <- envAfterAlias
        elaboratedDeclarations.AddRange(aliasDecls)

        let (envAfterCtors, sumTypeDecls) = TypeDefs.registerSumTypeConstructors tsCtx env sumTypes
        env <- envAfterCtors
        elaboratedDeclarations.AddRange(sumTypeDecls)


        // --- Type check rules and handlers by analysing their dependencies --- //


        let rulesByName =
            rules
            |> List.groupBy (fst >> _.Name >> removePos)
            |> Map.ofList

        for scc in DependencyAnalysis.computeRuleSCCs (List.map fst rules) do
            match scc with
            | [ singleName ] ->
                let (newEnv, ruleDecls) = Rules.typecheckPartitionedRules tsCtx env rulesByName.[singleName]
                env <- newEnv
                elaboratedDeclarations.AddRange(ruleDecls)

            | mutualNames ->
                let (newEnv, ruleDecls) = Rules.typecheckMutuallyRecursiveGroup tsCtx env rulesByName mutualNames
                env <- newEnv
                elaboratedDeclarations.AddRange(ruleDecls)

        // Checking for leaks of private types and extracting the public interface.
        Env.checkInterfaceLeaks tsCtx env modl
        let iface = Env.extractInterface modl env

        tsCtx.EmitDiagnosticsTo(errorQueue)

        { Description = None
          Declarations = Seq.toList elaboratedDeclarations }, iface

    /// Runs the type checker on the given (supposed) independent list of modules.
    let public run
        (modules: ModuleInfo list)
        (importedInterfaces: Map<string, ModuleInterface>)
        (sourceManager: SourceManager)
        (errorQueue: ErrorQueue)
        : TModule list * Map<string, ModuleInterface>
        =

        let results =
            modules
            |> Array.ofList
            |> Array.Parallel.map (typecheckModule sourceManager errorQueue importedInterfaces)
            |> Array.toList

        let tmodules = List.map fst results
        let newIfaces =
            results
            |> List.collect (fun (_, iface) ->
                [ string iface.Identifier, iface
                  removePos iface.Identifier.Name, iface ])
            |> Map.ofList

        let mergedIfaces = Map.fold (fun acc k v -> Map.add k v acc) importedInterfaces newIfaces
        (tmodules, mergedIfaces)
