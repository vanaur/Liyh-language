namespace Liyh.Module

[<RequireQualifiedAccess>]
module Definitions =
    open System.Collections.Concurrent
    open Liyh.Syntax.SyntaxTree
    open Liyh.Module

    /// List the different possibilities for top-level definitions.
    type public DefinitionType =
        | Rule
        | Handler
        | Extern
        | Effect
        | Type
        | TypeAlias
        | Notation
        | Context

        override this.ToString () =
            match this with
            | Rule -> "rule"
            | Handler -> "handler"
            | Extern -> "extern"
            | Effect -> "effect"
            | Type -> "type"
            | TypeAlias -> "type alias"
            | Notation -> "notation"
            | Context -> "context"

    /// Returns the definition type from the given top level definition.
    let private getDefinitionType { Node = node } =
        match node with
        | TopLevel.Rule _ -> Some Rule
        | TopLevel.LetRule _ -> Some Rule
        | TopLevel.Handler _ -> Some Handler
        | TopLevel.Extern _ -> Some Extern
        | TopLevel.Effect _ -> Some Effect
        | TopLevel.Type _ -> Some Type
        | TopLevel.TypeAlias _ -> Some TypeAlias
        | TopLevel.Notation _ -> Some Notation
        | TopLevel.Context _ -> Some Context
        | _ -> None

    /// Classify the definitions in a Map.
    let public classifyDefinitions =
        let cache = ConcurrentDictionary<_, Map<DefinitionType, TopLevelWithPos list>>()

        fun (modl: ModuleInfo) ->
            cache.GetOrAdd(modl, fun { ModuleContent = content } ->
                let rec loop (result: Map<DefinitionType, TopLevelWithPos list>) =
                    function
                    | [] -> result
                    | tlwp :: xs ->
                        match getDefinitionType tlwp with
                        | None -> loop result xs
                        | Some kind ->
                            let updated =
                                match Map.tryFind kind result with
                                | Some lst -> Map.add kind (lst @ [ tlwp ]) result
                                | None -> Map.add kind [tlwp] result
                            loop updated xs

                loop Map.empty content
            )

    /// Retrieves definitions of the same type given.
    let public tryGetByType (kind: DefinitionType) (modl: ModuleInfo) =
        classifyDefinitions modl
        |> Map.tryFind kind
        |> Option.defaultValue []

    /// Retrieves the name of the given definition.
    let private getNames (tlwp: TopLevelWithPos) =
        match tlwp.Node with
        | TopLevel.Rule { Name = name } -> [ name.Node ]
        | TopLevel.LetRule { Name = name } -> [ name.Node ]
        | TopLevel.Handler { Name = name } -> [ name.Node ]
        | TopLevel.Effect (name', _, _) -> [ name'.Node ]
        | TopLevel.Type { Name = name } -> [ name.Node ]
        | TopLevel.TypeAlias (name', _, _) -> [ name'.Node ]
        | TopLevel.Notation notation -> [ notation.NotationName.Node ]
        | TopLevel.Context ctx -> [ ctx.Name.Node ]
        | TopLevel.Extern extrn -> extrn.Content |> List.map (removePos >> _.Name >> removePos)
        | _ -> []

    /// Try to return the definition according to its type and its name, if found.
    let public tryGet (kind: DefinitionType) (name: string) (modl: ModuleInfo) =
        tryGetByType kind modl
        |> List.tryFind (fun tlwp -> List.contains name (getNames tlwp))

    /// Return the list of the whole definition's name in the given module.
    let public listAllDefinitionNames (modl: ModuleInfo) =
        classifyDefinitions modl
        |> Map.map (fun _ defs -> List.collect getNames defs)

    /// Check if the given module contains a definition by it's name.
    let public containsDefinitionName (modl: ModuleInfo) (name: string) =
        listAllDefinitionNames modl
        |> Map.toList
        |> List.tryFind (fun (_, names) -> List.contains name names)
        |> Option.isSome

    /// Check for name conflicts in the module.
    let public clashingNames (modl: ModuleInfo) =
        let defsByType = classifyDefinitions modl

        let filteredTypes =
            defsByType
            |> Map.filter (fun k _ -> k <> Rule && k <> Handler)

        let nameTypePosList =
            filteredTypes
            |> Map.toList
            |> List.collect (fun (typ, lst) ->
                lst |> List.collect (fun tlwp ->
                    getNames tlwp |> List.map (fun name -> (name, typ, tlwp.StartPos))
                )
            )

        let rules =
            defsByType |> Map.tryFind Rule |> Option.defaultValue []
            |> List.collect (fun tlwp ->
                getNames tlwp |> List.map (fun name -> (name, Rule, tlwp.StartPos))
            )

        let handlers =
            defsByType |> Map.tryFind Handler |> Option.defaultValue []
            |> List.collect (fun tlwp ->
                getNames tlwp |> List.map (fun name -> (name, Handler, tlwp.StartPos))
            )

        let allDefs = nameTypePosList @ rules @ handlers

        allDefs
        |> List.groupBy (fun (name, _, _) -> name)
        |> List.choose (fun (name, items) ->
            let types = items |> List.map (fun (_, typ, _) -> typ) |> List.distinct
            let positions = items |> List.map (fun (_, _, pos) -> pos)
            match types with
            | _ when List.length items > 1 ->
                if types = [Rule] || types = [Handler] then None
                else Some (name, positions, types)
            | _ -> None
        )
