namespace Liyh.Utils

open System.IO
open System.Collections.Concurrent

type SourceFile =
    { Content: string
      Lines: string[] }

type SourceManager() =
    let sources = ConcurrentDictionary<string, SourceFile>()

    let splitLines (text: string) =
        let reader = new StringReader(text)
        let lines = ResizeArray()
        let mutable line = reader.ReadLine()

        while not (isNull line) do
            lines.Add line
            line <- reader.ReadLine()

        lines.ToArray()

    /// Registers a new file source (and computes line indexes).
    member public __.RegisterSource(fileKey: string, content: string) =
        sources.[fileKey] <- { Content = content; Lines = splitLines content }

    /// Obtains the raw content of the given file source if it exists.
    member public __.TryGetFullSource(fileKey: string) =
        if isNull fileKey then None
        else
            match sources.TryGetValue fileKey with
            | true, file -> Some file.Content
            | _ -> None

    /// Obtains all lines of the given file source if it exists.
    member public __.TryGetLines(fileKey: string) =
        if isNull fileKey then None
        else
            match sources.TryGetValue fileKey with
            | true, file -> Some file.Lines
            | _ -> None

    /// Obtains a specific 1-based line from the file source.
    member public __.TryGetLine(fileKey: string, lineNumber: int64) : string option =
        if isNull fileKey then None
        else
            match sources.TryGetValue fileKey with
            | true, file when lineNumber >= 1L && lineNumber <= int64 file.Lines.Length -> Some file.Lines.[int lineNumber - 1]
            | true, file when lineNumber = int64 file.Lines.Length + 1L && file.Content.EndsWith("\n") -> Some ""
            | _ -> None

