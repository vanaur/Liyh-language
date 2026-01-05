namespace Liyh.Utils


module public UnionFind =
    open System.Collections.Generic
    open System.Linq

    /// Generic [union-find](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) data structure
    /// using the path compression find amelioration, making `Find` and `Connect` O(log n) in the worst case.
    type public UnionFind<'t when 't: equality>(defaultElements: 't seq) =
        let mutable parents = Dictionary<'t, 't>()
        let mutable ranks = Dictionary<'t, int>()

        do
            Seq.iter
                (fun element ->
                    parents.Add(element, element)
                    ranks.Add(element, 1))
                defaultElements

        let treeSize (element: 't) = ranks.[element]

        member public __.Find (element: 't) =
            let rec inner (element: 't) =
                match parents.TryGetValue element with
                | true, parent when parent <> element ->
                    let grandParent = parents.[parent]
                    parents.[element] <- grandParent
                    inner grandParent
                | _ -> element

            inner element

        member internal __.GetParents
            with get () = parents
            and set value = parents <- value

        member internal __.GetRanks
            with get () = ranks
            and set value = ranks <- value

        /// Adds an element to the original set.
        member public __.AddElement(element: 't) =
            match parents.TryGetValue element with
            | false, _ ->
                parents.Add(element, element)
                ranks.Add(element, 1)
            | _ -> ()

        /// Adds the list of elements given in the original set.
        member public this.AddRange(elements: 't seq) = Seq.iter this.AddElement elements

        /// Combines the two equivalence classes to which the two given representatives belong into a single class.
        member public this.Connect (left: 't) (right: 't) =
            assert (parents.ContainsKey left)
            assert (parents.ContainsKey right)

            let leftTree = this.Find left
            let rightTree = this.Find right

            if leftTree = rightTree then
                ()

            let leftTreeSize = treeSize leftTree
            let rightTreeSize = treeSize rightTree

            if leftTreeSize < rightTreeSize then
                parents.[leftTree] <- rightTree
                ranks.[rightTree] <- leftTreeSize + rightTreeSize
            else
                parents.[rightTree] <- leftTree
                ranks.[leftTree] <- leftTreeSize + rightTreeSize

        /// Combines all the equivalence classes to which the list of given representatives belong into a single class.
        member public this.ConnectRange(xs: 't seq) =
            if Seq.length xs < 2 then
                ()

            let head = Seq.head xs
            let tail = Seq.tail xs

            Seq.iter (this.Connect head) tail

        /// Retrieves the equivalence class to which the given element belongs.
        member public this.GetConnections(item: 't) =
            if not (parents.ContainsKey item) then
                Array.empty
            else
                let representative = this.Find item

                parents
                    .GroupBy(fun kvp -> kvp.Value)
                    .Where(fun x -> x.Key = representative)
                    .Select(fun gp -> gp.Select(fun kvp -> kvp.Key) |> Seq.toArray)
                |> Seq.toArray

        /// Gets the set of equivalence classes.
        member public __.GetAllConnections() =
            parents
                .GroupBy(fun kvp -> kvp.Value)
                .Select(fun gp -> gp.Select(fun kvp -> kvp.Key) |> Seq.toArray)
            |> Seq.toArray

        /// Check whether two elements belong to the same equivalence class.
        member public this.AreConnected (left: 't) (right: 't) =
            this.Find left = this.Find right

    /// Adds an element to the original set.
    let inline public addElement (uf: 't UnionFind) = uf.AddElement

    /// Adds the list of elements given in the original set.
    let inline public addRange (uf: 't UnionFind) = uf.AddRange

    /// Combines the two equivalence classes to which the two given representatives belong into a single class.
    let inline public connect (uf: 't UnionFind) = uf.Connect

    /// Combines all the equivalence classes to which the list of given representatives belong into a single class.
    let inline public connectRange (uf: 't UnionFind) = uf.ConnectRange

    /// Retrieves the equivalence class to which the given element belongs.
    let inline public getConnections (uf: 't UnionFind) = uf.GetConnections

    /// Gets the set of equivalence classes.
    let inline public getAllConnections (uf: 't UnionFind) = uf.GetAllConnections()

    /// Check whether two elements belong to the same equivalence class.
    let inline public areConnected (uf: 't UnionFind) = uf.AreConnected

    let inline public find (uf: 't UnionFind) = uf.Find

