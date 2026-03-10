namespace Liyh.Utils

module public LiyhCloc =
    open FParsec
    open System
    open System.Text
    open System.IO
    open ErrorReporter

    type public ClocState =
        { CodeLines: int
          CommentLines: int
          BlankLines: int
          HasCode: bool
          HasComment: bool }

        static member Default =
            { CodeLines = 0
              CommentLines = 0
              BlankLines = 0
              HasCode = false
              HasComment = false }

    let private commitLine st =
        let newSt =
            if st.HasCode then { st with CodeLines = st.CodeLines + 1 }
            elif st.HasComment then { st with CommentLines = st.CommentLines + 1 }
            else { st with BlankLines = st.BlankLines + 1 }

        { newSt with HasCode = false; HasComment = false }

    let private pNewline =
        newline >>. updateUserState commitLine

    let private pInline =
        pstring "--" 
        >>. updateUserState (fun st -> { st with HasComment = true }) 
        >>. skipRestOfLine false

    let private pBlock =
        pstring "{-" >>. manyCharsTill anyChar (pstring "-}") >>= fun content ->
            updateUserState (fun st ->
                let newlines = content |> Seq.filter ((=) '\n') |> Seq.length
                if newlines = 0 then
                    { st with HasComment = true }
                else
                    let stAfterStart = commitLine { st with HasComment = true }
                    let midLines = if newlines > 1 then newlines - 1 else 0
                    let stAfterMid = { stAfterStart with CommentLines = stAfterStart.CommentLines + midLines }

                    { stAfterMid with HasComment = true; HasCode = false }
            )

    let private pCodeOrSpace =
        choice [
            satisfy (fun c -> c = ' ' || c = '\t') >>% ()
            anyChar >>= fun _ -> updateUserState (fun st -> { st with HasCode = true })
        ]

    let private simpleClocReport =
        simpleReport (Warning (Tooling "cloc"))

    /// Returns the number of line of code, spaces and comments in the given file.
    let public countSource (fileName: string) =
        let parser = 
            skipMany (choice [pNewline; pInline; pBlock; pCodeOrSpace]) 
            >>. getUserState 
            >>= fun st -> eof >>. preturn (commitLine st)

        match runParserOnFile parser ClocState.Default fileName Encoding.Default with
        | Success(finalState, _, _) ->
            Result.Ok
                {| Code = finalState.CodeLines
                   Comment = finalState.CommentLines
                   Blank = finalState.BlankLines |}

        | Failure(_, _, _) ->
            let desc = $"Some parsing error in {fileName} prevents line counting."
            Result.Error (simpleClocReport desc null)

    /// Returns an array of statistics for the given directory.
    /// Returns the number of line of code, spaces and comments in each `*.liyh` file.
    let public countDir (srcDir: string) =
        try
            Directory.GetFiles(srcDir, "*.liyh", SearchOption.AllDirectories)
            |> Array.map (fun fileName -> (fileName, countSource fileName))
            |> Result.Ok
        with
        | :? UnauthorizedAccessException ->
            let desc = $"Liyh does not have the necessary access permissions to read in '{srcDir}'."
            Result.Error (simpleClocReport desc "Try using running the command as an administrator.")

        | :? DirectoryNotFoundException ->
            let desc = $"Location '{srcDir}' could not be found."
            Result.Error (simpleClocReport desc null)

        | _ ->
            let desc = $"Liyh is having trouble reading from location '{srcDir}'."
            Result.Error (simpleClocReport desc null)

    /// Displays the file statistics.
    let public displayStats (statsRes: Result<(string * Result<{| Blank: int; Code: int; Comment: int |}, ErrorReport>) array, ErrorReport>) =
        let errorQueue = new ErrorQueue()

        match statsRes with
        | Result.Error errorReport ->
            errorQueue.AddError(errorReport)
            errorQueue.ReportAll Console.Error true

        | Result.Ok stats ->
            if Array.isEmpty stats then
                printfn "0 files."
            else
                let successes = stats |> Array.choose (fun (name, r) -> match r with Result.Ok s -> Some (name, s) | _ -> None)
                let failures  = stats |> Array.choose (fun (_, r) -> match r with Result.Error e -> Some e | _ -> None)

                let totalBlank   = successes |> Array.sumBy (snd >> _.Blank)
                let totalComment = successes |> Array.sumBy (snd >> _.Comment)
                let totalCode    = successes |> Array.sumBy (snd >> _.Code)
                let fileTotal    = successes |> Array.sumBy (snd >> fun stats -> stats.Blank + stats.Comment + stats.Code)

                let hBlank, hComment, hCode, hTotal = "blank", "comment", "code", "total"

                let largestName =
                    stats |> Array.map (fst >> _.Length) |> Array.max

                let widthBlank   = max hBlank.Length   (string totalBlank).Length
                let widthComment = max hComment.Length (string totalComment).Length
                let widthCode    = max hCode.Length    (string totalCode).Length
                let widthTotal   = max hTotal.Length   (string fileTotal).Length

                let separatorLength = largestName + widthBlank + widthComment + widthCode + widthTotal + 8

                if not (Array.isEmpty failures) then
                    errorQueue.AddErrors failures

                printfn "%d liyh file%s found.\n" stats.Length (if stats.Length > 1 then "s" else "")
                printfn "%s" (String.replicate separatorLength "-")

                printfn "%-*s  %*s  %*s  %*s  %*s"
                    largestName "file"
                    widthBlank   hBlank
                    widthComment hComment
                    widthCode    hCode
                    widthTotal   hTotal

                printfn "%s" (String.replicate separatorLength "-")

                for (fileName, stat) in successes do
                    printfn "%-*s  %*d  %*d  %*d  %*d"
                        largestName fileName
                        widthBlank   stat.Blank
                        widthComment stat.Comment
                        widthCode    stat.Code
                        widthTotal   (stat.Blank + stat.Comment + stat.Code)

                printfn "%s" (String.replicate separatorLength "-")
                printfn "%-*s  %*d  %*d  %*d  %*d"
                    largestName  "sum"
                    widthBlank   totalBlank
                    widthComment totalComment
                    widthCode    totalCode
                    widthTotal   fileTotal
                printfn "%s" (String.replicate separatorLength "-")
