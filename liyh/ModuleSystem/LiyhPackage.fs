#nowarn "25"
namespace Liyh.Module

module LiyhPackage =
    open System
    open System.IO
    open Liyh.Syntax.SyntaxTree
    open Liyh.Syntax.Parser
    open Liyh.Utils.ErrorReporter
    open Liyh.Module

    [<RequireQualifiedAccess>]
    module private ErrorCodes =

        // E-XYZ
        // E=ERROR, X=COMPILER-CURRENT-PASS, YZ=ERROR-CODE
        // Packages : pass 1

        type public ErrorCode =

            /// The module was not found.
            | UnfoundModuleError = 1

            /// The root path was not found.
            | UnfoundRootPathError = 2

            /// Cyclic importations.
            | CircularDependenciesError = 3

            /// An undefined symbol is marked as exported.
            | ExportedUndefinedSymbolError = 4

        let inline public format (code: ErrorCode) =
            sprintf "E1%02d" (int code)

    type private Set<'T when 'T : comparison> with
        static member TryFind (predicate: 'T -> bool) (set: Set<'T>) : 'T option =
            set
            |> Set.filter predicate
            |> Set.toSeq
            |> Seq.tryHead
        
        member public this.TryFind (predicate: 'T -> bool) : 'T option =
            Set.TryFind predicate this

    /// Convert a file path to a Liyh identifier.
    let private pathToIdentifier (projectRoot: string) (fullPath: string) =
        let fullPath = Path.GetFullPath fullPath
        let relative = Path.GetRelativePath(projectRoot, fullPath)
        let withoutExtension = relative.Replace(".liyh", "")
        let parts = withoutExtension.Split(Path.DirectorySeparatorChar) |> Array.toList

        match List.rev parts with
        | name :: qualifier -> { Qualifier = List.rev (List.map (fun q -> { Node = q; Pos = null; Pos' = null }) qualifier); Name = { Node = name; Pos = null; Pos' = null } }
        | [] -> failwithf "invalid path: %s" fullPath

    /// Convert a Liyh identifier to a file path.
    let private identifierToPath (identifier: Identifier) =
        Path.Combine(Path.Combine(identifier.Qualifier |> List.map _.Node |> Array.ofList), identifier.Name.Node + ".liyh")

    let private resolveRelativePath (currentFilePath: string) (identifier: Identifier) =
        Path.Combine(Path.GetDirectoryName(currentFilePath), identifierToPath identifier)
        |> Path.GetFullPath

    let private resolveFromProjectRoot (projectRootPath: string) (identifier: Identifier) =
        Path.Combine(projectRootPath, identifierToPath identifier)
        |> Path.GetFullPath

    let private resolveHybridPath (projectRootPath: string) (projectName: string) (currentFilePath: string) (identifier: Identifier) =
        let pathFromRoot = resolveFromProjectRoot projectRootPath identifier
        if File.Exists(pathFromRoot) then pathFromRoot
        else resolveRelativePath currentFilePath identifier // `pathFromRoot` returns the correct message,
                                                            // but we must keep this for relative paths,
                                                            // for example `use Internal.C` from B.

    /// Represents a dependency graph useful for organizing dependencies between modules, detecting
    /// cycles, and detecting independent modules so that they can be sorted topologically.
    type public ProjectGraph = ProjectGraph of Map<ModuleInfo, Set<ModuleInfo>>

    module public ProjectGraph =
        open System.Text

        let public Empty = ProjectGraph Map.empty

        let public addModule (node: ModuleInfo) (deps: Set<ModuleInfo>) (ProjectGraph g) =
            ProjectGraph (Map.add node deps g)

        /// Detects cyclic imports.
        let public tryGetCycles (ProjectGraph g) =
            let rec dfs visited visiting path node =
                if Set.contains node visiting then
                    let idx = List.findIndex ((=) node) path
                    Some (List.skip idx path)
                elif Set.contains node visited then
                    None
                else
                    match Map.tryFind node g with
                    | None -> None
                    | Some deps ->
                        deps |> Seq.toList |> List.tryPick (dfs visited (Set.add node visiting) (path @ [node]))
            g |> Map.tryPick (fun node _ -> dfs Set.empty Set.empty [] node)

        let public updateModule (oldMI: ModuleInfo) (newMI: ModuleInfo) (ProjectGraph pgraph) =
            assert (oldMI.Identifier = newMI.Identifier)

            let pgraph1 =
                pgraph |> Map.map (fun _ deps ->
                    if deps.Contains oldMI
                    then deps.Remove oldMI |> Set.add newMI
                    else deps)

            let oldDeps = defaultArg (pgraph1.TryFind oldMI) Set.empty

            let pgraph2 =
                pgraph1
                |> Map.remove oldMI
                |> Map.add newMI oldDeps

            ProjectGraph pgraph2

        let public getModules (ProjectGraph pgraph) =
            pgraph.Keys

        let public getDependencies (mi: ModuleInfo) (ProjectGraph pgraph) =
            assert Map.containsKey mi pgraph
            pgraph.[mi] |> Set.toList

        let public tryGetModule (id: Identifier) (ProjectGraph pgraph) =
            pgraph |> Map.tryPick (fun mi _ -> if mi.Identifier = id then Some mi else None)

        let public graphToString (ProjectGraph g: ProjectGraph) : string =
            let sb = StringBuilder()
            for KeyValue(node, deps) in g do
                let name = string node.Identifier
                if Set.isEmpty deps then
                    sb.AppendLine(sprintf "%s" name) |> ignore
                else
                    for dep in deps do
                        let depName = string dep.Identifier
                        sb.AppendLine(sprintf "%s -> %s" name depName) |> ignore
            sb.ToString()

        /// Groups modules into independent layers based on their dependencies. Each layer contains modules
        /// that can be processed in parallel, and layers are ordered topologically (dependencies always
        /// appear in earlier layers).
        let public topologicalLayers (ProjectGraph pgraph) =
            let rec loop (m: Map<ModuleInfo, Set<ModuleInfo>>) (acc: ModuleInfo list list) =
                if Map.isEmpty m then List.rev acc
                else
                    let zeros =
                        m
                        |> Map.toList
                        |> List.choose (fun (k, deps) -> if Set.isEmpty deps then Some k else None)

                    let zeroSet = Set.ofList zeros

                    let m' =
                        m
                        |> Map.fold (fun acc k deps ->
                            if Set.contains k zeroSet then acc
                            else Map.add k (deps - zeroSet) acc) Map.empty

                    loop m' (zeros :: acc)

            loop pgraph []

    /// Builds the initial module graph for the project: retrieves all files/modules used, checks that they exist,
    /// checks for circular dependencies, and returns the initial graph if no errors are found. The ‘initial graph’
    /// means that no concrete, usable information is available (this is done immediately after this first phase).
    let public buildProjectGraph (rootFilePath: string) (errorQueue: ErrorQueue) =
        let useWPToIdentifier { Node = { Lib = lib; Qualifier = qualifier } } = removePos lib, qualifier

        let projectRoot =
            if Path.IsPathRooted rootFilePath
            then Path.GetDirectoryName rootFilePath
            else Directory.GetCurrentDirectory()

        let projectName = Path.GetFileName projectRoot

        let candidateFiles (qualifier: string list) (path: string) =
            let dir =
                let d = Path.GetDirectoryName path
                if String.IsNullOrEmpty d then "." else d

            let targetName = Path.GetFileNameWithoutExtension path

            if Directory.Exists dir then
                Directory.GetFiles(dir, "*", SearchOption.TopDirectoryOnly)
                |> Seq.filter (fun name -> name.EndsWith ".liyh")
                |> Seq.map Path.GetFileNameWithoutExtension
                |> Liyh.Utils.DamerauLevenshtein.suggest targetName
                |> Seq.map
                    (fun suggest ->
                        if List.isEmpty qualifier then suggest else
                        sprintf "%s.%s" (System.String.Join(".", List.map id qualifier)) suggest)
            else
                Seq.empty

        let rec build filePath visited pgraph =
            if not (File.Exists filePath) then failwithf "Internal error: file not found: '%s'" filePath
            elif Set.contains filePath visited then pgraph
            else
                let visited' = Set.add filePath visited
                let text = File.ReadAllText(filePath)
                let moduleId = pathToIdentifier projectRoot filePath

                match parseUses text filePath errorQueue with
                | None -> ProjectGraph.addModule { ModuleInfo.empty moduleId with Text = text } Set.empty pgraph
                | Some uses ->
                    let mutable deps = Set.empty
                    let mutable pgraph' = pgraph

                    for use' in uses do
                        let depId = fst (useWPToIdentifier use')
                        let depPath = resolveHybridPath projectRoot projectName filePath depId

                        // handle the standard library as a separate case

                        let isLiyhRoot =
                            match depId.Qualifier with
                            | [] -> depId.Name.Node = "Liyh"
                            | x :: _ -> x.Node = "Liyh"

                        if isLiyhRoot then
                            let depModId = pathToIdentifier projectRoot depPath
                            let depModule =
                                Option.defaultWith
                                    (fun _ -> { ModuleInfo.empty depModId with Done = true })
                                    (ProjectGraph.tryGetModule depId pgraph')

                            deps <- Set.add depModule deps

                        elif File.Exists depPath then
                            pgraph' <- build depPath visited' pgraph'

                            let depModId = pathToIdentifier projectRoot depPath
                            let depModule =
                                Option.defaultWith
                                    (fun _ -> { ModuleInfo.empty depModId with Text = File.ReadAllText depPath })
                                    (ProjectGraph.tryGetModule depId pgraph')

                            deps <- Set.add depModule deps

                        else
                            let informations =
                                let candidates = candidateFiles (use'.Node.Lib.Node.Qualifier |> List.map _.Node) depPath
                                if Seq.isEmpty candidates then []
                                else [ Liyh.Utils.DamerauLevenshtein.formatSuggestions "the module" candidates ]

                            let report =
                                { ErrorType = Package
                                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnfoundModuleError
                                  EnclosingPosition = Some use'.Node.Lib.Pos, Some use'.Node.Lib.Pos'
                                  Description = sprintf "Module '%s' not found." (string use'.Node)
                                  AllLines = NodeInfo.getLines text
                                  Informations = informations
                                  Hint = "Imports are case-sensitive and only files with extension `.liyh` are considered." }
                            errorQueue.AddError report

                    let uses = uses
                               |> List.map (fun { Node = node } -> removePos node.Lib, node.Qualifier)
                               |> Map.ofList

                    ProjectGraph.addModule { ModuleInfo.empty moduleId with Uses = uses; Text = text } deps pgraph'

        if not (File.Exists rootFilePath) then
            let informations =
                let candidates = candidateFiles [] rootFilePath
                if Seq.isEmpty candidates then []
                else [ Liyh.Utils.DamerauLevenshtein.formatSuggestions "the module" candidates ]

            let report =
                { ErrorType = Package
                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.UnfoundRootPathError
                  EnclosingPosition = None, None
                  Description = sprintf "Root path '%s' not found." rootFilePath
                  AllLines = []
                  Informations = informations
                  Hint = "Imports are case-sensitive and only files with extension `.liyh` are considered." }

            errorQueue.AddError report

            None
        else
            let pgraph = build rootFilePath Set.empty ProjectGraph.Empty
            match ProjectGraph.tryGetCycles pgraph with
            | None ->
                let rootModule =
                    ProjectGraph.getModules pgraph
                    |> Seq.find (fun mi -> identifierToPath mi.Identifier = rootFilePath)

                Some (pgraph, rootModule)
            | Some cycle ->
                let showCycle =
                    let allNames =
                        cycle @ [ cycle.Head ]
                        |> List.map (_.Identifier >> string)

                    match allNames with
                    | [] -> "Empty cycle detected."
                    | [ a ] -> sprintf "'%s' is using itself." a
                    | first :: second :: rest ->
                        let firstPart =
                            if first = second && rest = [] then sprintf "'%s' is using itself" first
                            else sprintf "'%s' is using '%s'" first second

                        let restParts =
                            rest
                            |> List.map (sprintf " that uses '%s'")
                            |> String.concat ""

                        firstPart + restParts

                let report =
                    { ErrorType = Package
                      ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.CircularDependenciesError
                      EnclosingPosition = None, None
                      Description = sprintf "Circular dependencies detected in the project: %s ! This is not allowed with Liyh." showCycle
                      AllLines = []
                      Informations = []
                      Hint = "Extract a common module or review the architecture of the modules." }

                errorQueue.AddError report
                None

    /// Retrieves sytactically exported elements (whether they actually exist or not).
    let private exported (moduleContent: TopLevelWithPos list) =
        moduleContent
        |> List.filter (_.Node >> _.IsModuleExport)
        |> List.collect (function { Node = ModuleExport exports } -> exports)

    let private checkExports (moduleInfo: ModuleInfo) (errorQueue: ErrorQueue) =
        match List.filter (not << Definitions.containsDefinitionName moduleInfo) moduleInfo.Exports with
        | [] -> true
        | undefinedExportedSymbols ->
            let msg =
                sprintf
                    (if undefinedExportedSymbols.Length = 1
                     then "An undefined symbol is marked as \"exported\" in the module %s: %s"
                     else "Undefined symbols are marked as \"exported\" in module %s: %s.")
                    (string moduleInfo.Identifier)
                    (String.concat ", " (List.map (sprintf "'%s'") undefinedExportedSymbols))

            let suggestions =
                Definitions.listAllDefinitionNames moduleInfo
                |> Map.fold (fun acc defType definedSymbols ->
                    undefinedExportedSymbols
                    |> List.choose (fun undefExport ->
                        let suggs = Liyh.Utils.DamerauLevenshtein.suggest undefExport definedSymbols
                        if Seq.isEmpty suggs then None
                        else Some (defType, suggs))
                    |> List.append acc
                ) []
                |> List.map (fun (defType, suggs) ->
                    let label = sprintf "the %s" (string defType)
                    Liyh.Utils.DamerauLevenshtein.formatSuggestions label suggs)

            let hint =
                "Only defined symbols can be exported. The language allows referencing undefined symbols symbolically, but exporting them requires a definition. This ensures consistency across packages."

            let report =
                { ErrorType = Package
                  ErrorCode = ErrorCodes.format ErrorCodes.ErrorCode.ExportedUndefinedSymbolError
                  EnclosingPosition = None, None
                  Description = msg
                  AllLines = NodeInfo.getLines moduleInfo.Text
                  Informations = suggestions
                  Hint = hint }

            errorQueue.AddError report
            false

    /// Fill in the dependency graph from the source file/module.
    let public fillProjectGraph (rootModule: ModuleInfo) (pgraph: ProjectGraph) (errorQueue: ErrorQueue) =
        let rec processModule (pgraph: ProjectGraph) (module': ModuleInfo) =
            if module'.Done then pgraph, module'.MixfixOperators
            else
                let currentPath = identifierToPath module'.Identifier

                // Treat dependencies first.
                let pgraph' =
                    ProjectGraph.getDependencies module' pgraph
                    |> List.fold (fun acc dep ->
                        let g, _ = processModule acc dep
                        g) pgraph

                // Retrieve the parsing user states from the direct dependencies.
                let directNotations =
                    ProjectGraph.getDependencies module' pgraph'
                    |> List.collect (fun dep ->
                        ProjectGraph.getModules pgraph'
                        |> Seq.tryFind (fun m -> m.Identifier = dep.Identifier)
                        |> Option.map (fun m -> m.MixfixOperators)
                        |> Option.defaultValue [])

                match parse module'.Text currentPath directNotations errorQueue with
                | None ->
                    let updated = { module' with Done = true; MixfixOperators = [] }
                    ProjectGraph.updateModule module' updated pgraph', []

                | Some result ->
                    let newNotations =
                        result.MixfixOperators
                        |> List.filter (fun n -> not (List.contains n directNotations))
                    
                    let updated =
                        { module' with
                            ModuleDescription = result.Module.ModuleDescription
                            ModuleContent = result.Module.ModuleContent
                            Exports = exported result.Module.ModuleContent
                            Done = true
                            MixfixOperators = newNotations }

                    if checkExports updated errorQueue = true then
                        let finalGraph = ProjectGraph.updateModule module' updated pgraph'
                        finalGraph, newNotations
                    else
                        pgraph, []

        let finalGraph, _ = processModule pgraph rootModule
        finalGraph, ProjectGraph.tryGetModule rootModule.Identifier finalGraph

    /// Attempts to retrieve the program entry point ("main function").
    let public tryGetEntryPoint (ProjectGraph pgraph) =
        let mutable result = None

        for modl in pgraph.Keys do
            if result.IsSome then ()
            else
                Definitions.classifyDefinitions modl
                |> Map.tryFind Definitions.DefinitionType.Rule
                |> Option.map (List.tryFind (removePos >> function Rule { Name = name } -> name.Node = "main"))
                |> Option.map (fun r -> result <- r)
                |> ignore

        result
        |> Option.map (removePos >> function Rule r -> r.Body)

    // For debug purpose.
    let public getAllNotations (ProjectGraph pgraph) =
        let mutable result = []

        for modl in pgraph.Keys do
            Definitions.classifyDefinitions modl
            |> Map.tryFind Definitions.DefinitionType.Notation
            |> Option.map (List.map (removePos >> function Notation notation -> notation))
            |> Option.map (fun newNotations -> result <- result @ newNotations)
            |> ignore

        result
