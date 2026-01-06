namespace Liyh.Utils

module ErrorReporter =
    open System
    open System.Text
    open System.Collections.Concurrent
    open System.IO
    open FParsec

    type private SeverityPalette =
        { Primary   : ColorTerm.Color
          Accent    : ColorTerm.Color
          Secondary : ColorTerm.Color
          Muted     : ColorTerm.Color
          Code      : ColorTerm.Color
          Location  : ColorTerm.Color }

    let private errorPalette =
        { Primary   = ColorTerm.Indexed 203
          Accent    = ColorTerm.Indexed 203
          Secondary = ColorTerm.Indexed 167
          Muted     = ColorTerm.Indexed 131
          Code      = ColorTerm.Indexed 102
          Location  = ColorTerm.Indexed 131 }

    let private warningPalette =
        { Primary   = ColorTerm.Indexed 214
          Accent    = ColorTerm.Indexed 214
          Secondary = ColorTerm.Indexed 179
          Muted     = ColorTerm.Indexed 136
          Code      = ColorTerm.Indexed 102
          Location  = ColorTerm.Indexed 136 }

    type public ErrorType =
        | Syntax
        | Type
        | Semantic
        | Package
        | RuntimeInternal
        | Runtime
        | Warning of ErrorType

        override this.ToString() =
            match this with
            | Syntax -> "Syntax"
            | Type -> "Type checking"
            | Semantic -> "Semantic"
            | Package -> "Package"
            | RuntimeInternal -> "Runtime internal"
            | Runtime -> "User triggered runtime"
            | Warning kind -> string kind

    let inline private paletteOfErrorType errorType =
        match errorType with
        | Warning _ -> warningPalette
        | _         -> errorPalette

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
        (mutedColor: ColorTerm.Color)
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
                ColorTerm.colorize mutedColor (if len <= 1 then "^" else "𜰉")

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
        let palette = paletteOfErrorType error.ErrorType

        let (startPos, endPosOpt) = error.EnclosingPosition
        let linesArray = Seq.toArray error.AllLines

        let codeSnippet =
            startPos
            |> Option.map (fun pos ->
                formatCodeSnippet
                    linesArray
                    pos.Line
                    pos.Column
                    endPosOpt
                    palette.Muted)

        let infoText =
            error.Informations
            |> Seq.filter (not << String.IsNullOrEmpty)
            |> Seq.tryHead
            |> Option.map (fun _ ->
                formatListItems error.Informations)

        let hintText =
            if String.IsNullOrEmpty error.Hint then None
            else
                Some (simpleWrap error.Hint (Console.WindowWidth - 4 * 5) 4)

        let description =
            simpleWrap error.Description (Console.WindowWidth - 4 * 5) 4

        let errorTypeText =
            let label =
                match error.ErrorType with
                | Warning _ -> " warning"
                | _         -> " error"

            let main =
                ColorTerm.colorize palette.Primary (string error.ErrorType + label)

            if String.IsNullOrEmpty error.ErrorCode then
                main
            else
                main
                + " "
                + ColorTerm.colorize palette.Code (sprintf "[%s]" error.ErrorCode)

        let positionHeader =
            match startPos with
            | None -> errorTypeText
            | Some pos ->
                let filePart =
                    if String.IsNullOrWhiteSpace pos.StreamName then ""
                    else sprintf "file %s, " (ColorTerm.colorize palette.Location pos.StreamName)

                sprintf "%s (%sln %d):" errorTypeText filePart pos.Line

        let firstLine = positionHeader + "\n" + description

        [ yield firstLine
          yield! Option.toList codeSnippet
          yield! Option.toList infoText
          yield! Option.toList hintText ]
          |> List.map (fun s -> s.TrimEnd())
          |> String.concat "\n\n"
          |> fun s -> s + "\n"


    type public ErrorQueue() =
        let queue = ConcurrentQueue<ErrorReport>()

        member public __.AddError(error: ErrorReport) = queue.Enqueue error

        /// Returns the number of errors and warnings.
        member public __.Count() =
            queue
            |> Seq.countBy _.ErrorType.IsWarning
            |> Seq.fold (fun acc (isWarn, count) ->
                if isWarn then (fst acc, snd acc + count)
                else (fst acc + count, snd acc)) (0, 0)

        member public this.HasErrors() =
            fst (this.Count()) <> 0

        member public this.HasWarnings() =
            snd (this.Count()) <> 0

        member public this.ReportAll(writer: TextWriter) (cleanAfter: bool) =
            let errors = ResizeArray<ErrorReport>()
            let enumerator = queue.GetEnumerator()

            while enumerator.MoveNext() do
                if not (errors.Contains enumerator.Current) then
                    errors.Add enumerator.Current

            let (nError, nWarning) = this.Count()
            if nError = 0 && nWarning = 0 then ()
            else
                let parts = [
                    if nError > 0 then
                        match nError with
                        | 1 -> "an error"
                        | n -> sprintf "%d errors" n
                    if nWarning > 0 then
                        match nWarning with
                        | 1 -> "a warning"
                        | n -> sprintf "%d warnings" n
                ]
                
                let message = String.concat " and " parts
                writer.WriteLine(sprintf "Compilation failed with %s. Please fix %s to proceed.\n" 
                    message 
                    (if nError > 0 then "them" else "it"))

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
