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
    let private getName (tlwp: TopLevelWithPos) =
        match tlwp.Node with
        | TopLevel.Rule { Name = name } -> name.Node
        | TopLevel.Handler { Name = name } -> name
        | TopLevel.Effect (name', _, _) -> name'
        | TopLevel.Type { Name = name } -> name
        | TopLevel.TypeAlias (name', _, _) -> name'
        | TopLevel.Notation notation -> notation.NotationName.Node
        | TopLevel.Context ctx -> ctx.Name.Node
        | _ -> failwith "??"

    /// Try to return the definition according to its type and its name, if found.
    let public tryGet (kind: DefinitionType) (name: string) (modl: ModuleInfo) =
        tryGetByType kind modl
        |> List.tryFind (fun tlwp -> getName tlwp = name)

    /// Return the list of the whole definition's name in the given module.
    let public listAllDefinitionNames (modl: ModuleInfo) =
        classifyDefinitions modl
        |> Map.map (fun _ v -> List.map getName v)

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
                lst |> List.map (fun tlwp -> (getName tlwp, typ, tlwp.Pos))
            )

        let rules =
            defsByType |> Map.tryFind Rule |> Option.defaultValue []
            |> List.map (fun tlwp -> (getName tlwp, Rule, tlwp.Pos))

        let handlers =
            defsByType |> Map.tryFind Handler |> Option.defaultValue []
            |> List.map (fun tlwp -> (getName tlwp, Handler, tlwp.Pos))

        let allDefs = nameTypePosList @ rules @ handlers

        allDefs
        |> List.groupBy (fun (name, _, _) -> name)
        |> List.choose (fun (name, items) ->
            // On sépare les types présents pour ce nom
            let types = items |> List.map (fun (_, typ, _) -> typ) |> List.distinct
            let positions = items |> List.map (fun (_, _, pos) -> pos)
            match types with
            | _ when List.length items > 1 ->
                if types = [Rule] || types = [Handler] then None
                else Some (name, positions, types)
            | _ -> None
        )

    // Unfinished:

    /// Retrieves all symbols from a definition.
    let public getSymbolsOfExpression (expr: ExpressionWithPos) =

        let rec loop result { Node = node } =
            let listOfExpr1 xs = List.map (snd >> loop result) xs |> List.concat
            let listOfExpr2 xs = List.map (loop result) xs |> List.concat

            match node with
            | Expression.Identifier id -> id :: result
            | Expression.Apply { LHS = a; Arguments = b } -> loop result a @ listOfExpr2 b
            | Expression.CollectionAccess { LHS = a; Indices = b } -> loop result a @ listOfExpr2 b
            | Expression.ExpressionSequence xs -> listOfExpr2 xs
            | Expression.ForDownTo { InitialValue = a; EndValue = b; Body = c } -> loop result a @ loop result b @ loop result c
            | Expression.ForIn { ListExpr = a; Body = b } -> loop result a @ loop result b
            | Expression.ForTo { InitialValue = a; EndValue = b; Body = c } -> loop result a @ loop result b @ loop result c
            | Expression.HandleEffect { InitialState = a; Body = b } -> loop result a @ loop result b
            | Expression.Lambda { Body = a } -> loop result a
            | Expression.Let(_, a) -> loop result a
            | Expression.Var(_, a) -> loop result a
            | Expression.List xs -> listOfExpr2 xs
            | Expression.ListComprehension { ItemValue = a; ListExpr = c; IfPred = d } -> loop result a @ loop result c @ Option.defaultValue result (Option.map (loop result) d)
            | Expression.Match { ToMatch = a; Cases = b } -> loop result a @ listOfExpr1 b
            | Expression.MixfixOperator { Arguments = a } -> listOfExpr2 a
            | Expression.Range { RangeStart = a; RangeStep = b; RangeStop = c } -> loop result a @ loop result c @ Option.defaultValue result (Option.map (loop result) b)
            | Expression.ReAssign(_, a) -> loop result a
            | Expression.Record xs -> listOfExpr1 xs
            | Expression.RecordUsing(_, a) -> listOfExpr1 a
            | Expression.ResumeWith { Node = r } -> loop result r.HandlerState @ loop result r.Value
            | Expression.Tuple xs -> listOfExpr2 xs
            | Expression.UFCS { LHS = a; RHS = b } -> loop result a @ loop result b
            | Expression.While { Predicate = a; Body = b } -> loop result a @ loop result b
            | _ -> result

        loop [] expr
        |> List.distinct

    /// List all symbols used in the module.
    let public getAllSymbolsUsed (modl: ModuleInfo) =

        let rec loop result =
            function
            | [] -> result
            | { Node = TopLevel.Rule { WhenClause = whenClause; Body = expr } } :: xs ->
                loop (result @ getSymbolsOfExpression expr) xs
                @ Option.defaultValue result (Option.map getSymbolsOfExpression whenClause)

            | _ :: xs -> loop result xs

        loop [] modl.ModuleContent

