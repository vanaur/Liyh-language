namespace Liyh.Utils

module Utils =

    module Map =
        let inline public findOrDefault defaultValue key map =
            Option.defaultValue defaultValue (Map.tryFind key map)

    module List =
        let inline public last (lst: _ list) =
            if List.isEmpty lst then invalidArg "lst" "The list is empty"
            else (List.rev >> List.head) lst

        let inline public containsBy (pred: 't -> bool) (lst: 't list) =
            List.tryFind pred lst |> Option.isSome

