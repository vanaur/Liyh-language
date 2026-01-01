#nowarn "25"
namespace Liyh

module Program =
    open System
    open Liyh.Utils.ErrorReporter
    open Liyh.Module.LiyhPackage
    open Liyh.TypeCheck
    open Liyh.Core.Execution
    open Liyh.Core.Execution.Core
    open System.Runtime.InteropServices
    open Liyh.Core

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
