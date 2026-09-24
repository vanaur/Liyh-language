namespace Liyh.Utils

module Utils =

    module Benchmark =
        open System
        open Binarysharp.Benchmark

        /// A small utility for benchmarking a function given the number of iterations to be performed.
        /// This function does not replace a real benchmark tool, but is a first approach.
        let inline bench ([<InlineIfLambda>] fn: unit -> 'a) (iterations: int) =
            let shark = BenchShark()
            let res = shark.EvaluateTask(Action(fn >> ignore), uint iterations)

            printfn "[%d runs] %gms." iterations res.AverageExecutionTime.TotalMilliseconds

