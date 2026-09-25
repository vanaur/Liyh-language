namespace Liyh.Module
open System
open Liyh.Syntax.SyntaxTree

type public UseMap = Map<Identifier, string option>

[<CustomEquality; CustomComparison>]
type public ModuleInfo =
    {
        /// path of the module as an identifier format, e.g. 'MyProject.Utils.Data'
        Identifier: Identifier

        /// list of imported modules associated with their qualifiers if any
        Uses: UseMap

        /// list of exported symbols
        Exports: string list

        /// the optional description of the module (in the very top of the file)
        ModuleDescription: string option

        /// the top-level definitions of the module
        ModuleContent: TopLevelWithPos list

        /// the user-state to be used for the parsing
        MixfixOperators: MixfixOperator list

        /// the list of all external functions (FFI)
        FFIBinings: Liyh.FFI.GeneralFFI.FFIBinding list

        /// check if this data has been processed, all fields are filled
        Done: bool }

    override this.Equals (obj: obj) =
        match obj with
        | :? ModuleInfo as { Identifier = identifier } -> this.Identifier = identifier
        | _ -> false

    override this.GetHashCode() = hash this.Identifier

    interface IComparable with
        member this.CompareTo (obj: obj) =
            match obj with
            | :? ModuleInfo as { Identifier = identifier } -> compare this.Identifier identifier
            | _ -> -1

    static member empty (identifier: Identifier) =
        { Identifier = identifier
          Uses = Map.empty
          Exports = []
          ModuleDescription = None
          ModuleContent = []
          MixfixOperators = []
          FFIBinings = []
          Done = false }
