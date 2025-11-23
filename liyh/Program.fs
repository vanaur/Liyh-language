#nowarn "25"
namespace Liyh

module Program =
    open System
    open Liyh.Utils.ErrorReporter
    open Liyh.Module.LiyhPackage
    open Liyh.TypeCheck
    open Liyh.Execution
    open Liyh.Execution.Core

    open Binarysharp.Benchmark

    /// A small utility for benchmarking a function given the number of iterations to be performed.
    /// This function does not replace a real benchmark tool, but is a first approach.
    let inline bench ([<InlineIfLambda>] fn: unit -> 'a) (iterations: int) =
        let shark = BenchShark()
        let res = shark.EvaluateTask(Action(fn >> ignore), uint iterations)

        printfn "[%d runs] %gms." iterations res.AverageExecutionTime.TotalMilliseconds

    [<EntryPoint>]
    let main _ =
        //Execution.Disctree.example()
        //exit 0

        let errorQueue = new ErrorQueue()

        match buildProjectGraph "Test.liyh" errorQueue with
        | None ->
            errorQueue.ReportAll Console.Error true
            exit -1

        | Some(pgraph, rootModule) ->
            let pgraph, rootModule = fillProjectGraph rootModule pgraph errorQueue

            if errorQueue.Count() > 0 then
                errorQueue.ReportAll Console.Error true
                exit -1

            for layer in ProjectGraph.topologicalLayers pgraph do
                let typechecked = TypeCheck.run layer errorQueue
                ()

            errorQueue.ReportAll Console.Error true

        0
