namespace Liyh.Repl

module Repl =
    open Liyh.Utils.ColorTerm
    open Liyh.Utils.ErrorReporter
    open Liyh.Module.LiyhPackage
    open Liyh.TypeCheck
    open Liyh.Execution.Core
    open System
    open System.Text
    open System.Linq
    open System.Collections.Generic

    let private header = """
     __    _       __  
    / /   (_)_  __/ /_      Liyh (dev)
   / /   / / / / / __ \     Copyright (c) 2024 by vanaur
  / /___/ / /_/ / / / /     (Type `:help` for help)
 /_____/_/\__, /_/ /_/      
         /____/             https://github.com/vanaur/Liyh-language/

 Type ENTER to execute and ALT+ENTER to add lines. Use arrows to navigate
 within a block of Liyh code.

    """

    type private BlockType =
        | CodeBlock of ResizeArray<ResizeArray<char>>
        | ResultBlock of string

    let private codeBlockToString (codeBlock: ResizeArray<ResizeArray<char>>) =
        let sb = StringBuilder()

        for i in 0 .. codeBlock.Count - 1 do
            let line = codeBlock.[i]

            for char in line do
                sb.Append char |> ignore

            if i < codeBlock.Count - 1 then
                sb.AppendLine() |> ignore

        string sb

    module private ReplParser =
        open FParsec
        open Liyh.Syntax.Parser

        let public parseBlock (text: string) =
            // TODO
            text

    type public Repl() =
        let mutable currentBlockLines = ResizeArray([ResizeArray<char>()])
        let mutable currentLine = 0
        let mutable cursorX = 0

        // Block history.
        let finishedBlocks = ResizeArray<BlockType>()

        let mutable running = true
        let mutable lineCountWidth = 1

        let headerLines = header.Split('\n').Length

        let redraw () =
            Console.Clear()
            printfn "%s" header

            for block in finishedBlocks do
                match block with
                | CodeBlock lines ->
                    for i = 0 to lines.Count - 1 do
                        let content = System.String(lines[i].ToArray())
                        printfn " %*d ┃  %s" lineCountWidth (i + 1) content
                    printfn ""
                    
                | ResultBlock result ->
                    let resultLines = result.Split('\n')
                    for line in resultLines do
                        printfn " %s %s" (colorize (Indexed 115) "  🮥") line
                    printfn ""

            lineCountWidth <- (currentBlockLines.Count).ToString().Length

            for i = 0 to currentBlockLines.Count - 1 do
                let prefix =
                    if i = currentLine then colorize (Indexed 120) "┣"
                    else colorize (Indexed 240) "┃"
                let content = System.String(currentBlockLines[i].ToArray())
                printfn " %*d %s  %s" lineCountWidth (i + 1) prefix content

            let prefixLen = 5 + lineCountWidth  // " n ┣  "

            let mutable finishedLinesCount = 0
            for block in finishedBlocks do
                match block with
                | CodeBlock lines -> finishedLinesCount <- finishedLinesCount + lines.Count + 1
                | ResultBlock result -> finishedLinesCount <- finishedLinesCount + result.Split('\n').Length + 1
            
            let cursorY = headerLines + finishedLinesCount + currentLine
            Console.SetCursorPosition(prefixLen + cursorX, cursorY)

        member __.Run() =
            Console.Clear()
            printfn "%s" header
            redraw()

            while running do
                let key = Console.ReadKey(true)

                match key.Key with
                | ConsoleKey.LeftArrow ->
                    if cursorX > 0 then cursorX <- cursorX - 1

                | ConsoleKey.RightArrow ->
                    if cursorX < currentBlockLines[currentLine].Count then cursorX <- cursorX + 1

                | ConsoleKey.UpArrow ->
                    if currentLine > 0 then
                        currentLine <- currentLine - 1
                        cursorX <- min cursorX currentBlockLines[currentLine].Count

                | ConsoleKey.DownArrow ->
                    if currentLine < currentBlockLines.Count - 1 then
                        currentLine <- currentLine + 1
                        cursorX <- min cursorX currentBlockLines[currentLine].Count

                | ConsoleKey.Enter when key.Modifiers.HasFlag(ConsoleModifiers.Alt) ->
                    currentBlockLines.Insert(currentLine + 1, ResizeArray<char>())
                    currentLine <- currentLine + 1
                    cursorX <- 0

                | ConsoleKey.Enter ->
                    finishedBlocks.Add(CodeBlock currentBlockLines)

                    let result = ReplParser.parseBlock (codeBlockToString currentBlockLines)
                    finishedBlocks.Add(ResultBlock (string result))

                    currentBlockLines <- ResizeArray([ResizeArray<char>()])
                    currentLine <- 0
                    cursorX <- 0

                | ConsoleKey.Backspace ->
                    if cursorX > 0 then
                        currentBlockLines[currentLine].RemoveAt(cursorX - 1)
                        cursorX <- cursorX - 1
                    elif currentLine > 0 then
                        let prevLen = currentBlockLines[currentLine - 1].Count
                        currentBlockLines[currentLine - 1].AddRange(currentBlockLines[currentLine])
                        currentBlockLines.RemoveAt(currentLine)
                        currentLine <- currentLine - 1
                        cursorX <- prevLen

                | ConsoleKey.Escape ->
                    running <- false

                | _ ->
                    if key.KeyChar <> char 0 then
                        currentBlockLines[currentLine].Insert(cursorX, key.KeyChar)
                        cursorX <- cursorX + 1

                redraw()
