#nowarn "25"
namespace Liyh

module public LiyhVersion =
    open System.Reflection

    let public liyhVersion =
        let asm = Assembly.GetExecutingAssembly()
        let assemblyName = asm.GetName().Name

        let resourceName = $"{assemblyName}.VERSION"
        use stream = asm.GetManifestResourceStream(resourceName)

        if stream <> null then
            use reader = new System.IO.StreamReader(stream)
            reader.ReadToEnd()
        else
            // this may not happen
            failwithf "Unfound ressource: 'VERSION'."

module Program =
    open System
    open Liyh.Core
    open Liyh.Utils.ErrorReporter
    open Liyh.Module.LiyhPackage

    /// The Command Line Interface, using Argu.
    [<AutoOpen>]
    module private Cli =
        open Argu

        type CompileArgs =
            | [<MainCommand; ExactlyOnce>] File of string
            | [<AltCommandLine("-o")>] Output of path: string
            | [<AltCommandLine("-O")>] Optimize
            | [<AltCommandLine("-s")>] Stfu
            | [<AltCommandLine("-cc")>] CCompiler of cc: string
            | Emit of file: string

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | File _ -> "The root file of your project to compile."
                    | Output _ -> "The path for the compiled executable (default: same as input)."
                    | Optimize -> "Activate the optimizations."
                    | Emit _ -> "Write the compiled bytecode in the given file for textual visualization."
                    | Stfu -> "Displays only the necessary information."
                    | CCompiler _ -> "The C compiler to use (default is `cc` on Unix)"

        type ExecuteArgs =
            | [<MainCommand; ExactlyOnce>] File of string
            | [<AltCommandLine("-o")>] Optimize
            | [<CustomCommandLine("--args")>] ProgramArgs of string list
            | [<AltCommandLine("-s")>] Stfu

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | File _ -> "The root file of the program to run."
                    | Optimize -> "Activate the optimizations before running."
                    | ProgramArgs _ -> "Arguments to pass to the Liyh program's main function."
                    | Stfu -> "Displays only the necessary information."

        type ExplainArgs =
            | [<MainCommand; ExactlyOnce>] Code of string
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Code _ -> "Explain the cause of the given error code."
                    | Dummy -> ""

        type ClocArgs =
            | [<MainCommand; ExactlyOnce>] Path of string
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Path _ -> "Display the number of lines of code of Liyh files for the given location."
                    | Dummy -> ""

        type ReplArgs =
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Dummy -> ""

        type ServerArgs =
            | Stdio
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Stdio -> "Use standard input/output for LSP communication (used by VS Code)."
                    | Dummy -> ""

        type Init =
            | [<Hidden>] Dummy

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Dummy -> ""

        type VersionArgs =
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
            | Init of ParseResults<Init>
            | [<AltCommandLine("-v")>] Version of ParseResults<VersionArgs>

            interface IArgParserTemplate with
                member this.Usage =
                    match this with
                    | Compile _ -> "Compile a project into an executable."
                    | Run _ -> "Directly run the given program."
                    | Explain _ -> "Explain the cause of a specific error code."
                    | Cloc _ -> "Count lines of Liyh code in a specific path."
                    | Repl _ -> "Open the interactive environment."
                    | Server _ -> "Activate the LSP server."
                    | Init _ -> "Generates a new project."
                    | Version _ -> "Display the version of the compiler."

        let cliParser = ArgumentParser.Create<CliArguments>(programName = "liyh")

    module private CompilationProcess =

        let private showTimeTaken (ms: int64) =
            if ms < 1000 then sprintf "\nTime taken: %dms." ms
            else sprintf "\nTime taken: %gs." (double ms / 1000.0)

        let public runOrCompile
            (rootFile: string)
            (cc: string option)
            (doOptimize: bool)
            (run: bool)
            (output: string option)
            (emitBytecode: string option)
            (programArgs: string list)
            (stfu: bool)

            =

            let sw = Diagnostics.Stopwatch.StartNew()

            let errorQueue = new ErrorQueue()

            match buildProjectGraph rootFile errorQueue with
            | None ->
                errorQueue.ReportAll Console.Error true
                exit 1

            | Some(pgraph, rootModule) ->
                let pgraph, rootModule = fillProjectGraph rootModule pgraph errorQueue
                errorQueue.ReportIfNeeded Console.Error

                let compiledLayers =
                    pgraph
                    |> ProjectGraph.topologicalLayers
                    |> Array.ofList
                    |> Array.Parallel.map (fun layer ->
                        // let typechecked = TypeCheck.run layer errorQueue
                        CoreCompiler.compileModules layer)

                errorQueue.ReportIfNeeded Console.Error

                (*

                /// Check the expressions semantically. If no problems are found, group the expressions by
                /// their rewritten form and the information related to commutativity and associativity.
                let notationsInfo = TypeCheck.CheckNotations.check pgraph errorQueue

                errorQueue.ReportIfNeeded Console.Error

                *)

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
                          Hint = "If you want to compile the project as a library, then use the appropriate compilation option." }

                    errorQueue.AddError report
                    errorQueue.ReportAll Console.Error true
                    exit 1

                // Building the global compilation environment.

                let ffiBindings = getFFIBindings pgraph
                let globalCompilationEnv = CoreCompiler.getGlobalCompilationEnv ffiBindings compiledLayers

                checkGlobalFFIBindings ffiBindings [] errorQueue |> ignore
                errorQueue.ReportIfNeeded Console.Error

                // The compiled program (bytecode).
                let cp = LyVM.BytecodeCompiler.compile globalCompilationEnv

                // Saves the compiled bytecode to a file if requested by the user.
                Option.iter (LyVM.PrettyPrinter.saveToFile cp) emitBytecode

                let vm = new LyVM.VM()
                vm.EmitFromCompiledProgram cp

                let compileTo (destFile: string) =
                    if LyVM.AOT.compile cp destFile cc doOptimize then
                        printfn "Compiled %s to %s." rootFile destFile

                match output with
                | None when not run ->
                    let output = System.IO.Path.GetFileNameWithoutExtension rootFile
                    compileTo output

                | None when run ->
                    let ms = vm.Run(programArgs)

                    if not stfu then
                        printfn "%s" (showTimeTaken ms)

                | Some output when not run ->
                    compileTo output
                
                | _ ->
                    failwith "??"

                if not run then
                    printfn "%s" (showTimeTaken sw.ElapsedMilliseconds)

    module private ProjectInitialization =
        open System.IO
        open System.Reflection
        open System.Diagnostics

        type private PromptKind =
            | FreeText
            | Choices of string list

        let private askChoices (message: string) (kind: PromptKind) (defaultValue: string option) =
            let defaultStr =
                match defaultValue with
                | None -> ""
                | Some def -> sprintf " (default: %s)" def

            match kind with
            | (FreeText | Choices []) ->
                let rec ask (count: int) =
                    printf "%s%s%s: " (if count = 0 then " + " else "   ") message defaultStr

                    match Console.ReadLine(), defaultValue with
                    | input, Some default' when String.IsNullOrWhiteSpace input -> default'
                    | input, _ when not (String.IsNullOrWhiteSpace input) -> input
                    | input, _ -> ask (count + 1)

                ask 0

            | Choices choices ->
                let rec ask (count: int) =
                    let choicesStr = String.Join('/', choices)
                    printf "%s%s [%s]%s: " (if count = 0 then " + " else "   ") message choicesStr defaultStr

                    match Console.ReadLine(), defaultValue with
                    | input, Some default' when System.String.IsNullOrWhiteSpace input -> default'
                    | input, _ ->
                        let matchOpt =
                            choices
                            |> List.tryFind (fun x -> String.Equals(x, input, StringComparison.OrdinalIgnoreCase))

                        match matchOpt with
                        | Some matchedValue -> matchedValue
                        | None -> ask (count + 1)

                ask 0

        let private initGitRepo (folderPath: string) =
            let startInfo = ProcessStartInfo(
                FileName = "git",
                Arguments = "init",
                WorkingDirectory = folderPath,
                CreateNoWindow = true,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true
            )

            try
                use proc = Process.Start(startInfo)
                proc.WaitForExit()

                if proc.ExitCode = 0 then
                    // let output = proc.StandardOutput.ReadToEnd().Trim()
                    // printfn "Git: %s" output
                    ()
                else
                    let error = proc.StandardError.ReadToEnd().Trim()
                    printfn "Error when initializing Git: %s" error
                    printfn "Continue without Git..."
            with
            | ex ->
                printfn "Unable to launch Git: %s" ex.Message
                printfn "Continue without Git..."

        let public init () =
            printfn "Building a new project in the current directory..."
            printfn "(you can change these settings later)\n"

            let projectName = askChoices "Project name" FreeText None
            let projectAuthor = askChoices "Author" FreeText (Some Environment.UserName)
            let projectDescription = askChoices "Description" FreeText None
            let projectLicense = askChoices "License" (Choices [ "MIT"; "Apache 2.0"; "GPL"; "None" ]) (Some "MIT")
            let projectGit = askChoices "Initialize a git repository?" (Choices [ "Y"; "n" ]) (Some "Y")
            let projectTemplate = askChoices "Choose a template" (Choices [ "Example"; "Basic"; "Library"; "None" ]) (Some "Basic")

            // ---

            let invalidChars = Path.GetInvalidFileNameChars()
            let folderName =
                projectName.Replace(' ', '-')
                |> String.filter (fun c -> not (Array.contains c invalidChars))

            let folderPath = Path.Combine(".", folderName)
            Directory.CreateDirectory(folderPath) |> ignore

            let licenseFile, licenseName =
                match projectLicense.ToLower() with
                | "mit" ->          Some "MIT",     Some "MIT"
                | "apache 2.0" ->   Some "Apache",  Some "Apache 2.0"
                | "gpl" ->          Some "GPL",     Some "GPL v3"
                | _ ->              None, None

            let assembly = Assembly.GetExecutingAssembly()
            let assemblyName = assembly.GetName().Name

            let resources =
                [ "README.md"
                  "main.liyh"
                  yield! Option.toList licenseFile ]

            let licenseReplacement =
                match licenseName with
                | Some l -> $"# License\nThis project is licensed under {l}."
                | None -> ""

            let replacements =
                Map.ofList
                    [ ("<year>", string DateTime.Now.Year)
                      ("<author>", projectAuthor)
                      ("<project-name>", projectName)
                      ("<project-description>", projectDescription)
                      ("<project-license>", licenseReplacement) ]

            for fileName in resources do
                let resourceName = $"{assemblyName}.InitProjectRessources.{fileName}"
                use stream = assembly.GetManifestResourceStream(resourceName)
                
                if stream <> null then
                    use reader = new System.IO.StreamReader(stream)
                    let mutable content = reader.ReadToEnd()

                    content <-
                        replacements
                        |> Map.fold (fun acc placeholder value -> acc.Replace(placeholder, value)) content

                    let destFileName =
                        match licenseFile with
                        | Some lf when lf = fileName -> "LICENSE"
                        | _ -> fileName

                    let destPath = Path.Combine(folderPath, destFileName)
                    File.WriteAllText(destPath, content)

                else
                    // this may not happen
                    failwithf "Unfound ressource: '%s'." fileName

            if projectGit.ToLower() = "y" then
                initGitRepo folderPath

            printfn "\nDone! Go to %s and run the project using `liyh run main.liyh`." folderPath

    let private version = LiyhVersion.liyhVersion

    // It's a bit pretentious, I think... but one can always dream. 🥹
    [<Literal>]
    let private poem = """
  In Liyh, rules are queen and patterns are king,
  Match your way through most anything.
  Effects flow free, types keep you right,
  Symbols and functions shine bright.

  Loops and mutables? Still around,
  But rules and patterns are the crown.
  The syntax is fresh, a little new —
  Just enough structure to see you through.
                """

    [<EntryPoint>]
    let main (args: string[]) =
        try

            if Array.isEmpty args then
                let url = "https://github.com/vanaur/Liyh-language"
                printfn "%s" (Utils.ColorTerm.colorize (Utils.ColorTerm.Basic "blue") $"Welcome to Liyh (v{version})!\n")
                printfn "Liyh is a functional, rule-based programming language."
                printfn "Please see: \u001b[4m%s\u001b[0m for more information!" url
                printfn "%s" poem
                printfn "If you are new here, maybe start with `liyh init` to generate a sample."
                printfn "You can also launch the help using `liyh help`.\n"
                0

            else
                let cli = cliParser.Parse(args)

                match cli.GetSubCommand() with
                | Version _ ->
                    printfn "Liyh version: v%s" version

                | Repl _ ->
                    Repl.Repl.Repl().Run()

                | Init _ ->
                    ProjectInitialization.init ()

                | Server _ ->
                    // Liyh.LspServer.runServer() |> ignore
                    printfn "LSP Server not yet implemented."

                | Cloc clocArgs ->
                    let path = clocArgs.GetResult(ClocArgs.Path)
                    let result = Utils.LiyhCloc.countDir path
                    Utils.LiyhCloc.displayStats result

                | Run runArgs ->
                    let rootFile = runArgs.GetResult(ExecuteArgs.File)
                    let doOptimize = runArgs.Contains(ExecuteArgs.Optimize)
                    let programArgs = runArgs.GetResult(ExecuteArgs.ProgramArgs, [])
                    let stfu = runArgs.Contains(ExecuteArgs.Stfu)

                    CompilationProcess.runOrCompile rootFile None doOptimize true None None programArgs stfu

                | Compile compileArgs ->
                    let rootFile = compileArgs.GetResult(CompileArgs.File)
                    let doOptimize = compileArgs.Contains(CompileArgs.Optimize)
                    let emit = compileArgs.TryGetResult(CompileArgs.Emit)
                    let output = compileArgs.TryGetResult(CompileArgs.Output)
                    let stfu = compileArgs.Contains(CompileArgs.Stfu)
                    let cc = compileArgs.TryGetResult(CompileArgs.CCompiler)

                    CompilationProcess.runOrCompile rootFile cc doOptimize false output emit [] stfu

                | Explain explainArgs ->
                    let code = explainArgs.GetResult(ExplainArgs.Code)
                    printfn "Code Error Explain not yet implemented."

                0

        with
        | :? Argu.ArguParseException as exn ->
            printfn "%s" exn.Message
            1
