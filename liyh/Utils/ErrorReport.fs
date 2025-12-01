namespace Liyh.Utils

module ErrorReporter =
    open System
    open System.Text
    open System.Collections.Concurrent
    open System.IO
    open FParsec

    type public ErrorType =
        | Syntax
        | Type
        | Semantic
        | Package // file and import system
        | RuntimeInternal // bugs that should not occur
        | Runtime // invalid rules during runtime, can be raised by the user

        override this.ToString() =
            match this with
            | Syntax -> "Syntax"
            | Type -> "Type checking"
            | Semantic -> "Semantic"
            | Package -> "Package"
            | RuntimeInternal -> "Runtime internal"
            | Runtime -> "User triggered runtime"

    type public ErrorReport =
        { ErrorType: ErrorType
          ErrorCode: string
          EnclosingPosition: Position option * Position option
          Description: string
          AllLines: string seq
          Informations: string seq
          Hint: string }

    let private indent (n: int) (s: string) =
        let prefix = String.replicate n " "

        s.Split('\n')
        |> Array.map (fun line -> if String.IsNullOrEmpty(line) then line else prefix + line)
        |> String.concat "\n"

    let private formatCodeSnippet
        (lines: string[])
        (errorLine: int64)
        (errorCol: int64)
        (enclosingEnd: Position option)
        =

        let getLine l =
            if l >= 0 && l < lines.Length then lines[l] else ""

        let caretLine =
            let start = int (errorCol - 1L)

            let endCol =
                match enclosingEnd with
                | Some pos when pos.Line = errorLine -> int (pos.Column - 1L)
                | _ -> start + 1

            let len = max 1 (endCol - start)

            let cursor =
                ColorTerm.colorize (ColorTerm.Indexed 131) (if len <= 1 then "^" else "𜰉")

            String.replicate 9 " "
            + "𜰊"
            + " "
            + String.replicate (12 - (9 + 2) + start) " "
            + String.replicate len cursor

        let startLine = max 1L (errorLine - 2L)
        let endLine = min (int64 lines.Length) (errorLine + 2L)

        let collected =
            [ for lineNum in startLine..endLine ->
                  let content = getLine (int (lineNum - 1L))
                  lineNum, content ]

        let trimmed =
            collected
            |> List.skipWhile (fun (_, line) -> String.IsNullOrWhiteSpace line)
            |> List.rev
            |> List.skipWhile (fun (_, line) -> String.IsNullOrWhiteSpace line)
            |> List.rev

        let rec compress acc =
            function
            | [] -> List.rev acc
            | [ x ] -> List.rev (x :: acc)
            | (ln1, l1) :: (ln2, l2) :: xs when String.IsNullOrWhiteSpace l1 && String.IsNullOrWhiteSpace l2 ->
                compress acc ((ln2, l2) :: xs)
            | x :: xs -> compress (x :: acc) xs

        let cleaned = compress [] trimmed

        let sb = StringBuilder()
        sb.Append(indent 9 "⋮") |> ignore
        sb.AppendLine() |> ignore

        for (lineNum, line) in cleaned do
            let lineNumStr = sprintf "%4d" lineNum
            sb.AppendFormat("    {0} {1}  {2}\n", lineNumStr, "│", line) |> ignore

            if lineNum = errorLine then
                sb.Append(caretLine + "\n") |> ignore

        sb.Append(indent 9 "⋮") |> ignore
        sb.ToString()

    let private formatListItems (items: string seq) =
        items
        |> Seq.map (fun s ->
            let indentedContent = s.Replace("\n", "\n      ")
            "    𜲂 " + indentedContent)
        |> String.concat "\n"

    let private simpleWrap (text: string) (max: int) (indent: int) : string =
        let indentStr = String.replicate indent " "

        let wrapLine (s: string) =
            let rec wrap (s: string) =
                if ColorTerm.visibleLength s <= max then
                    [ s ]
                else
                    let findPhysicalPosition (text: string) (maxVisible: int) =
                        let mutable visibleCount = 0
                        let mutable physicalPos = 0
                        let mutable inEscape = false

                        while physicalPos < text.Length && visibleCount < maxVisible do
                            if text.[physicalPos] = '\027' then inEscape <- true
                            elif inEscape && text.[physicalPos] = 'm' then inEscape <- false
                            elif not inEscape then visibleCount <- visibleCount + 1
                            physicalPos <- physicalPos + 1

                        if visibleCount = maxVisible then physicalPos else text.Length
                    
                    let physicalMax = findPhysicalPosition s max
                    let chunk = s.Substring(0, physicalMax)

                    let rec findLastSpace (text: string) (pos: int) =
                        if pos <= 0 then -1
                        elif text.[pos] = ' ' then
                            let mutable inEscape = false
                            let mutable i = 0
                            while i <= pos do
                                if text.[i] = '\027' then inEscape <- true
                                elif inEscape && text.[i] = 'm' then inEscape <- false
                                i <- i + 1
                            if not inEscape then pos else findLastSpace text (pos - 1)
                        else
                            findLastSpace text (pos - 1)

                    let splitPos = findLastSpace chunk (chunk.Length - 1)

                    if splitPos > 0 then
                        let line = s.Substring(0, splitPos)
                        let rest = s.Substring(splitPos + 1)
                        line :: wrap rest
                    else
                        let line = chunk
                        let rest = s.Substring physicalMax
                        line :: wrap rest

            wrap s

        text.Split('\n')
        |> Seq.collect wrapLine
        |> Seq.map (fun line -> indentStr + line)
        |> String.concat "\n"

    let public formatError (error: ErrorReport) =
        let (startPos, endPosOpt) = error.EnclosingPosition
        let linesArray = Seq.toArray error.AllLines

        let codeSnippet =
            if startPos.IsNone then
                None
            else
                Some(formatCodeSnippet linesArray startPos.Value.Line startPos.Value.Column endPosOpt)

        let infoText =
            let informations = Seq.filter (not << String.IsNullOrEmpty) error.Informations

            if Seq.isEmpty informations then
                None
            else
                Some(formatListItems informations)

        let hintText =
            if String.IsNullOrEmpty error.Hint then
                None
            else
                let wrapped = simpleWrap error.Hint (Console.WindowWidth - 4 * 5) 4
                Some wrapped

        let description = simpleWrap error.Description (Console.WindowWidth - 4 * 5) 4

        let positionHeader =
            let errorTypeText =
                ColorTerm.colorize
                    (ColorTerm.Indexed 203)
                    (string error.ErrorType + " error")
                    + if String.IsNullOrEmpty error.ErrorCode then ""
                      else ColorTerm.colorize (ColorTerm.Indexed 102) (sprintf " [%s]" error.ErrorCode)

            match startPos with
            | None -> errorTypeText
            | Some pos ->
                let clr = ColorTerm.colorize (ColorTerm.Indexed 131)

                let filePart =
                    if String.IsNullOrWhiteSpace pos.StreamName then
                        ""
                    else
                        sprintf "file %s, " (clr pos.StreamName)

                sprintf "%s (%sln %d):" errorTypeText filePart pos.Line

        let firstLine = positionHeader + "\n" + description

        [ yield firstLine
          yield! Option.toList codeSnippet
          yield! Option.toList infoText
          yield! Option.toList hintText ]
        |> List.map (fun s -> s.TrimEnd())
        |> String.concat "\n\n"
        |> fun s -> s + "\n"

    /// A thread-safe error report queue.
    type public ErrorQueue() =
        let queue = ConcurrentQueue<ErrorReport>()

        /// Appends an error reports to the queue.
        member public __.AddError(error: ErrorReport) = queue.Enqueue error

        /// Retrieves the current number of error reports in the queue.
        member public __.Count() = queue.Count

        /// Writes all errors from the queue to the write destination. If `cleanAfter` is `true`, clears the error cache.
        member public __.ReportAll(writer: TextWriter) (cleanAfter: bool) =
            let errors = ResizeArray<ErrorReport>()
            let enumerator = queue.GetEnumerator()

            while enumerator.MoveNext() do
                if not (errors.Contains enumerator.Current) then
                    errors.Add enumerator.Current

            let count = errors.Count
            if count = 0 then ()
            else
                match count with
                | 1 -> writer.WriteLine("Compilation failed with an error. Please fix it to proceed.\n")
                | n -> writer.WriteLine(sprintf "Compilation failed with %d errors. Please fix them to proceed.\n" n)

                for error in errors do
                    writer.WriteLine("└ " + formatError error)

            if cleanAfter then
                queue.Clear()

    let inline public immediateError (report: ErrorReport) = printfn "%s" (formatError report)

    let inline public immediateRuntimeError (errorType: ErrorType) (msg: string) =
        { ErrorType = errorType
          ErrorCode = null
          EnclosingPosition = None, None
          Description = msg
          AllLines = Seq.empty
          Informations = Seq.empty
          Hint = null }

        |> formatError
        |> printfn "%s"

        exit -1
