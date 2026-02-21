#nowarn "25"
namespace Liyh

module Program =
    open System
    open Liyh.Core
    open Liyh.Utils.ErrorReporter
    open Liyh.Module.LiyhPackage

    let private version = "0.1.1"

    [<AutoOpen>]
    module private Cli =
        open Argu

        type CompileArgs =
            | [<MainCommand; ExactlyOnce>] File of string
            | [<AltCommandLine("-o")>] Output of path: string
            | [<AltCommandLine("-O")>] Optimize
            | Emit of file: string

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | File _ -> "the root file of your project to compile."
                    | Output _ -> "the path for the compiled executable (default: same as input)."
                    | Optimize -> "activate the optimizations."
                    | Emit _ -> "write the compiled bytecode in the given file for textual visualization."

        type ExecuteArgs =
            | [<MainCommand; ExactlyOnce>] File of string
            | [<AltCommandLine("-o")>] Optimize

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | File _ -> "the root file of the program to run."
                    | Optimize -> "activate the optimizations before running."

        type ExplainArgs =
            | [<MainCommand; ExactlyOnce>] Code of string
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Code _ -> "explain the cause of the given error code."
                    | Dummy -> ""

        type ClocArgs =
            | [<MainCommand; ExactlyOnce>] Path of string
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Path _ -> "display the number of lines of code of Liyh files for the given location."
                    | Dummy -> ""

        type ReplArgs =
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Dummy -> ""

        type ServerArgs =
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Dummy -> ""

        [<CliPrefix(CliPrefix.None)>]
        type CliArguments =
            | Compile of ParseResults<CompileArgs>
            | Run of ParseResults<ExecuteArgs>
            | Explain of ParseResults<ExplainArgs>
            | Cloc of ParseResults<ClocArgs>
            | Repl of ParseResults<ReplArgs>
            | Server of ParseResults<ServerArgs>
            | [<AltCommandLine("-v")>] Version

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Compile _ -> "compile a project into an executable."
                    | Run _ -> "directly run the given program."
                    | Explain _ -> "explain the cause of a specific error code."
                    | Cloc _ -> "count lines of Liyh code in a specific path."
                    | Repl _ -> "open the interactive environment."
                    | Server _ -> "activate the LSP server."
                    | Version -> "display the version of the compiler."

        let cliParser = ArgumentParser.Create<CliArguments>(programName = "liyh")

    let private runOrCompile
        (rootFile: string)
        (doOptimize: bool)
        (run: bool)
        (output: string option)
        (emitBytecode: string option)

        =

        let errorQueue = new ErrorQueue()

        match buildProjectGraph rootFile errorQueue with
        | None ->
            errorQueue.ReportAll Console.Error true
            exit 1

        | Some(pgraph, rootModule) ->
            let pgraph, rootModule = fillProjectGraph rootModule pgraph errorQueue
            errorQueue.ReportIfNeeded Console.Error

            let coreDefinitions =
                pgraph
                |> ProjectGraph.topologicalLayers
                |> Array.ofList
                |> Array.Parallel.collect (fun layer ->
                    // let typechecked = TypeCheck.run layer errorQueue
                    CoreCompiler.compileModules layer)
                |> Array.toList

            errorQueue.ReportIfNeeded Console.Error

            if not (containsEntryPoint pgraph) then
                let report =
                    { ErrorType = Package
                      ErrorCode = null
                      EnclosingPosition = (None, None)
                      Description = "No entry point was found in the project."
                      AllLines = Seq.empty
                      Informations =
                        [ "The content has still been analysed, but no compilation output will be produced."
                          "Use `main[] -> ...` to define an entry point" ]
                      Hint = "If you want to compile the project as a library, then use the appropriate compilation option."
                    }

                errorQueue.AddError report
                errorQueue.ReportAll Console.Error true
                exit 1

            let cp = LyVM.BytecodeCompiler.compile coreDefinitions

            Option.iter
                (LyVM.PrettyPrinter.saveToFile cp)
                emitBytecode

            let vm = new LyVM.VM()
            vm.EmitFromCompiledProgram cp

            let compileTo (destFile: string) =
                LyVM.AOT.compile cp destFile
                printfn "Compiled %s to %s." rootFile destFile

            match output with
            | None when not run ->
                let output = System.IO.Path.GetFileNameWithoutExtension rootFile
                compileTo output

            | None when run ->
                let ms = vm.Run()
                printfn "\nTime taken: %d ms." ms

            | Some output when not run ->
                compileTo output
            
            | _ ->
                failwith "??"

            ()

    [<EntryPoint>]
    let main args =
        try
            let cli = cliParser.Parse(args)

            Option.iter
                (fun _ -> printfn "Liyh version: %s" version)
                (cli.TryGetResult Version)

            // Option.iter
            //     (fun _ -> Liyh.LspServer.runServer() |> ignore)
            //     (cli.TryGetResult Server)

            Option.iter
                (fun _ -> Repl.Repl.Repl().Run())
                (cli.TryGetResult Repl)

            match cli.TryGetResult Cloc with
            | None -> ()
            | Some clocArgs ->
                let path = clocArgs.GetResult(Path)
                let result = Utils.LiyhCloc.countDir path
                Utils.LiyhCloc.displayStats result

            match cli.TryGetResult Run with
            | None -> ()
            | Some runArgs ->
                let rootFile = runArgs.GetResult(File)
                let doOptimize = runArgs.Contains(Optimize)

                runOrCompile rootFile doOptimize true None None

            match cli.TryGetResult Compile with
            | None -> ()
            | Some compileArgs ->
                let rootFile = compileArgs.GetResult(CompileArgs.File)
                let doOptimize = compileArgs.Contains(CompileArgs.Optimize)
                let emit = compileArgs.TryGetResult(Emit)
                let output = compileArgs.TryGetResult(Output)

                runOrCompile rootFile doOptimize false output emit

            exit 0

        with
        | :? Argu.ArguParseException as exn ->
            printfn "%s" exn.Message
            exit 1

