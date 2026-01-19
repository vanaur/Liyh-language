namespace Liyh.Utils

module ProgressBar =
    open System

    let private frames =
        [| "⠋"; "⠙"; "⠹"; "⠸"; "⠼"; "⠴"; "⠦"; "⠧"; "⠇"; "⠏" |]

    type private MultiProgressDisplay() =
        let mutable tasks = Map.empty<int, string * bool>
        let mutable frameIndex = 0
        let mutable isRunning = true

        let startLine = Console.CursorTop
        let lockObj = obj()

        member private __.UpdateDisplay() =
            lock lockObj (fun _ ->
                if startLine < Console.BufferHeight then
                    try
                        Console.SetCursorPosition(0, startLine)

                        tasks
                        |> Map.toSeq
                        |> Seq.iter (fun (_, (msg, completed)) ->
                            let status = if completed then "✓" else frames.[frameIndex]
                            let line = $"{status} {msg}"
                            Console.Write(line.PadRight(Console.BufferWidth - 1))
                            Console.WriteLine()
                        )

                        frameIndex <- (frameIndex + 1) % frames.Length
                    with :? ArgumentOutOfRangeException -> ()
            )

        member this.Start() =
            async {
                while isRunning do
                    this.UpdateDisplay()
                    do! Async.Sleep 80
            }

        member __.AddTask(id, message) =
            lock lockObj (fun _ ->
                tasks <- Map.add id (message, false) tasks
            )

        member __.CompleteTask(id) =
            lock lockObj (fun _ ->
                tasks <- tasks
                         |> Map.change id (Option.map (fun (msg, _) -> (msg, true)))
            )

        member this.Stop() =
            isRunning <- false
            this.UpdateDisplay()

    /// Performs multiple tasks in parallel with a progress bar for each one.
    let runParallelWithProgress (namedTasks: (string * Async<'T>) list) =
        async {
            let display = MultiProgressDisplay()

            List.iteri (fun i (name, _) -> display.AddTask(i, name)) namedTasks
            Async.Start(display.Start())

            try
                let! results =
                    namedTasks
                    |> List.mapi (fun i (_, task) ->
                        async {
                            let! result = task
                            display.CompleteTask(i)
                            return result
                        })
                    |> Async.Parallel

                do! Async.Sleep 200
                display.Stop()
                return Array.toList results

            with ex ->
                display.Stop()
                return raise ex
        }
