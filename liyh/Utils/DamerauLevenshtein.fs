namespace Liyh.Utils

module DamerauLevenshtein =
    open System

    let private damerauLevenshtein (s1: string) (s2: string) =
        let m = s1.Length
        let n = s2.Length
        let matrix = Array2D.init (m + 1) (n + 1) (fun i j -> if i = 0 then j elif j = 0 then i else 0)

        for i in 1 .. m do
            for j in 1 .. n do
                let cost = if s1.[i - 1] = s2.[j - 1] then 0 else 1

                let deletion = matrix.[i - 1, j] + 1
                let insertion = matrix.[i, j - 1] + 1
                let substitution = matrix.[i - 1, j - 1] + cost

                let mutable currentMin = min deletion (min insertion substitution)

                if i > 1 && j > 1 && s1.[i - 1] = s2.[j - 2] && s1.[i - 2] = s2.[j - 1] then
                    let transposition = matrix.[i - 2, j - 2] + 1
                    currentMin <- min currentMin transposition
                
                matrix.[i, j] <- currentMin

        matrix.[m, n]

    /// Uses the Damerau-Levenshtein distance to suggest a list of candidate words for the given word.
    let public suggest (originalString: string) (candidates: string seq) =
        let evaluateCandidate (candidate: string) =
            if Char.ToLower originalString.[0] <> Char.ToLower candidate.[0] then None
            else
                let distance = damerauLevenshtein originalString candidate
                let maxDistance = min 4 (int (originalString.Length / 3) + 1)
                if distance <= maxDistance then Some (candidate, distance)
                else None

        candidates
        |> Seq.choose evaluateCandidate
        |> Seq.sortBy snd
        |> Seq.map fst

    let public formatSuggestions (what: string) (suggestions: string seq) =
        let suggestions = Seq.distinct suggestions

        if Seq.isEmpty suggestions then ""
        else
            sprintf
                "Perhaps you were referring to %s %s ?"
                what
                (String.concat " or " (Seq.map (sprintf "`%s`") suggestions))

