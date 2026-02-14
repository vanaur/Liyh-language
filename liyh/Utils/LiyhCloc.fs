namespace Liyh.Utils

module public LiyhCloc =
    open FParsec
    open System.Text
    open System.IO

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

    /// Returns the number of line of code, spaces and comments in the given file.
    let public countSource (fileName: string) =
        let parser = 
            skipMany (choice [pNewline; pInline; pBlock; pCodeOrSpace]) 
            >>. getUserState 
            >>= fun st -> eof >>. preturn (commitLine st)

        match runParserOnFile parser ClocState.Default fileName Encoding.Default with
        | Success(finalState, _, _) -> 
            {| Code = finalState.CodeLines
               Comment = finalState.CommentLines
               Blank = finalState.BlankLines |}

        | Failure(msg, _, _) ->
            failwithf "Erreur de parsing : %s" msg

    /// Returns an array of statistics for the given directory.
    /// Returns the number of line of code, spaces and comments in each `*.liyh` file.
    let public countDir (srcDir: string) =
        Directory.GetFiles(srcDir, "*.liyh", SearchOption.AllDirectories)
        |> Array.map (fun fileName -> (fileName, countSource fileName))

    /// Displays the file statistics.
    let public displayStats (stats: (string * {| Blank: int; Code: int; Comment: int |}) array) =
        if Array.isEmpty stats then
            printfn "0 files."
        else
            let totalBlank = stats |> Array.sumBy (snd >> _.Blank)
            let totalComment = stats |> Array.sumBy (snd >> _.Comment)
            let totalCode = stats |> Array.sumBy (snd >> _.Code)

            let hBlank, hComment, hCode = "blank", "comment", "code"

            let largestName = stats |> Array.map (fst >> _.Length) |> Array.max
            let widthBlank = max hBlank.Length (string totalBlank).Length
            let widthComment = max hComment.Length (string totalComment).Length
            let widthCode = max hCode.Length (string totalCode).Length

            let separatorLength = largestName + widthBlank + widthComment + widthCode + 6

            printfn "%d liyh file%s found.\n" stats.Length (if stats.Length > 1 then "s" else "")
            printfn "%s" (String.replicate separatorLength "-")

            printfn "%-*s  %*s  %*s  %*s" 
                largestName "file" 
                widthBlank hBlank 
                widthComment hComment 
                widthCode hCode

            printfn "%s" (String.replicate separatorLength "-")

            for (fileName, stat) in stats do
                printfn "%-*s  %*d  %*d  %*d" 
                    largestName fileName 
                    widthBlank stat.Blank 
                    widthComment stat.Comment 
                    widthCode stat.Code

            printfn "%s" (String.replicate separatorLength "-")
            printfn "%-*s  %*d  %*d  %*d" 
                largestName "total" 
                widthBlank totalBlank 
                widthComment totalComment 
                widthCode totalCode
            printfn "%s" (String.replicate separatorLength "-")

