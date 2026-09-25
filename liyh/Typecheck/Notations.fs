namespace Liyh.TypeCheck

module CheckNotations =
    open Liyh.Utils.ErrorReporter
    open Liyh.Module.LiyhPackage
    open Liyh.Syntax.SyntaxTree

    type private CanonicalPart =
        | CHole
        | CFixed of string

    let private getCanonicalSignature patternNodes =
        patternNodes |> List.map (function
            | HolePart _ -> CHole
            | FixedPart f -> CFixed f.Node
        )

    /// Performs a semantic analysis over the notations. Returns a map with the rewriting of the notation as keys
    /// and their associativity and commutativity as value.
    let public check (pgraph: ProjectGraph) (errorQueue: ErrorQueue) =
        let allNotations = getAllNotations pgraph

        let mutable notationACInfo = Map.empty
        let mutable seenSignatures = Map.empty
        let mutable validPrecedences = []

        for (modInfo, notation) in allNotations do
            let allLines = NodeInfo.getLines modInfo.Text

            // Check variable correspondance

            let patternVariables =
                notation.NotationPattern.Node
                |> List.choose (function HolePart var -> Some var | _ -> None)

            // Il faut récupérer toutes les variables de l'expression... Chiant => On ferra ça plus tard
            // dans le typechecker.


            // Check if the notations has operands

            if List.isEmpty patternVariables then
                let report =
                    { ErrorType = Warning Semantic
                      ErrorCode = null
                      EnclosingPosition = (Some notation.NotationPattern.StartPos, Some notation.NotationPattern.EndPos)
                      Description = "A notation should contain one or more operands rather than zero."
                      AllLines = allLines
                      Informations = [ "Notations are not used to define constants." ]
                      Hint = null }

                errorQueue.AddError report

            // Check non-linear variables in the pattern

            let distinctVariables = List.countBy id patternVariables
            for (var, count) in distinctVariables do
                if count > 1 then
                    let report =
                        { ErrorType = Semantic
                          ErrorCode = null
                          EnclosingPosition = (Some notation.NotationPattern.StartPos, Some notation.NotationPattern.EndPos)
                          Description = "Non-linear patterns are not allowed in the definition of notations."
                          AllLines = allLines
                          Informations = [ "At this stage, equality is generally undecidable." ]
                          Hint = null }

                    errorQueue.AddError report

            // Check consistency with fields

            let isInfix =
                match notation.NotationPattern.Node with
                | [ HolePart _; FixedPart _; HolePart _ ] -> true
                | _ -> false

            match notation.NotationAssociativity.Node with
            | (Associativity.Left | Associativity.Right) when not isInfix ->
                let report =
                    { ErrorType = Semantic
                      ErrorCode = null
                      EnclosingPosition = (Some notation.NotationAssociativity.StartPos, Some notation.NotationAssociativity.EndPos)
                      Description = "Only infix operators can be associative."
                      AllLines = allLines
                      Informations = [ ]
                      Hint = "Just write `associativity: none` instead." }

                errorQueue.AddError report

            | _ -> ()

            if notation.NotationCommutative.Node = true && not isInfix then
                let report =
                    { ErrorType = Semantic
                      ErrorCode = null
                      EnclosingPosition = (Some notation.NotationCommutative.StartPos, Some notation.NotationCommutative.EndPos)
                      Description = "Only infix operators can be commutative."
                      AllLines = allLines
                      Informations = [ ]
                      Hint = "Just write `commutativity: false` or ignore this field instead." }

                errorQueue.AddError report

            // Check if the pattern already exists

            let canonicalSignature = getCanonicalSignature notation.NotationPattern.Node

            match Map.tryFind canonicalSignature seenSignatures with
            | Some (originalPos: _ WithPos) ->
                let ln = originalPos.Line
                let file = originalPos.File

                let report =
                    { ErrorType = Semantic
                      ErrorCode = null
                      EnclosingPosition = (Some notation.NotationPattern.StartPos, Some notation.NotationPattern.EndPos)
                      Description = sprintf "This notation pattern is structurally identical to an already defined notation at ln %d of file %s." ln file
                      AllLines = allLines
                      Informations = [ ]
                      Hint = "Remove the duplicate or change the fixed parts of the pattern." }

                errorQueue.AddError report

            | _ ->
                seenSignatures <- Map.add canonicalSignature notation.NotationPattern seenSignatures

                notationACInfo <-
                    Map.add
                        notation.NotationIs
                        (notation.NotationAssociativity.Node, notation.NotationCommutative.Node)
                        notationACInfo

                validPrecedences <- (notation.NotationPrecedence.Node, notation.NotationIs) :: validPrecedences

        notationACInfo
