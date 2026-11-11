namespace Liyh.Semantic

open Liyh.Semantic.TypedSyntaxTree
open Liyh.Syntax.SyntaxTree
open Liyh.Utils.ErrorReporter

/// Internal diagnostic information to be used in error messages.
type internal InternalDiagnostic =
    { Message: string
      Informations: string list
      Hint: string }

/// Internal exception raised when unification does not work, so that
/// the internal diagnostic information can be used in the error messages.
exception private UnifyException of InternalDiagnostic

/// Checkpoint covering both variable bindings (types and dimensions) and the
/// reported diagnostics for backtracking.
[<Struct>]
type public Checkpoint =
    { UndoCount: int
      DiagnosticCount: int }

[<Struct>]
type private UndoAction =
    | UndoTypeVar of targetTV: TypeVar ref * previousValueTV: TypeVar
    | UndoDimVar of targetDV: DimVar ref * previousValueDV: DimVar

/// Type checker context: generates new variables, logs variable bindings, collects diagnostics,
/// and allows to roll back the entire process using checkpoints.
type public TypecheckContext(lines: string seq) =
    let diagnostics = ResizeArray<ErrorReport>()
    let undoStack = ResizeArray<UndoAction>()

    let mutable varCounter = 0
    let mutable dimCounter = 0

    let mutable symbolCounter = 0

    let rollbackBindingsTo (targetCount: int) =
        for i in undoStack.Count - 1 .. -1 .. targetCount do
            match undoStack.[i] with
            | UndoTypeVar(r, prev) -> r.Value <- prev
            | UndoDimVar(r, prev) -> r.Value <- prev

        undoStack.RemoveRange(targetCount, undoStack.Count - targetCount)

    /// Creates a new type variable.
    member public __.FreshVar (prefix: string) =
        varCounter <- varCounter + 1
        TVar(ref (UnboundVar (sprintf "%s%d" prefix varCounter)))

    /// Creates a new dimension variable.
    member public __.FreshDim (prefix: string) =
        dimCounter <- dimCounter + 1
        ref (UnboundDim (sprintf "%s%d" prefix dimCounter))

    /// Creates a `ResolvedIdent` for the typed AST.
    member public this.CreateIdent
        (written: Identifier)
        (kind: SymbolKind)
        (definedAt: Span option)
        : ResolvedIdent
        =
        { Symbol = this.FreshSymbolId()
          Kind = kind
          Written = written
          DefinedAt = definedAt }

    /// Allocates a new symbol ID for the typed AST.
    member public __.FreshSymbolId () : SymbolId =
        symbolCounter <- symbolCounter + 1
        SymbolId symbolCounter

    /// Returns a fresh type variable to continue the type checking in case of error.
    /// This is simply an unbound type variable prefixed by `"err"`.
    member public this.FreshError () =
        this.FreshVar "err"

    /// Modifies a TypeVar by logging the restore operation.
    member public __.BindTypeVar (r: TypeVar ref) (newVal: TypeVar) =
        undoStack.Add(UndoTypeVar(r, r.Value))
        r.Value <- newVal

    /// Modifies a DimVar by logging the restore operation.
    member public __.BindDimVar (r: DimVar ref) (newVal: DimVar) =
        undoStack.Add(UndoDimVar(r, r.Value))
        r.Value <- newVal

    /// Adds an error to the queue.
    member public __.ReportError
        (errorCode: ErrorCode)
        (description: string)
        (informations: string list)
        (hint: string)
        (wp: WithPos<_>)
        =

        let report =
            { ErrorType = ErrorType.Type
              ErrorCode = format errorCode
              EnclosingPosition = (Some wp.StartPos, Some wp.EndPos)
              Description = description
              Informations = informations
              Hint = hint
              AllLines = lines }

        diagnostics.Add(report)

    /// Adds a warning to the queue.
    member public __.ReportWarning
        (warningCode: WarningCode)
        (description: string)
        (informations: string list)
        (hint: string)
        (wp: WithPos<_>)
        =

        let report =
            { ErrorType = Warning ErrorType.Type
              ErrorCode = formatWarning warningCode
              EnclosingPosition = (Some wp.StartPos, Some wp.EndPos)
              Description = description
              Informations = informations
              Hint = hint
              AllLines = lines }

        diagnostics.Add(report)

    /// Emits all diagnostic messages to the given error queue.
    member public __.EmitDiagnosticsTo (errorQueue: ErrorQueue) =
        errorQueue.AddErrors(diagnostics)

    /// Returns whether any new diagnostics were recorded since the specified checkpoint.
    member public __.HasDiagnosticsSince (cp: Checkpoint) =
        diagnostics.Count > cp.DiagnosticCount

    /// Adds an informational note to all diagnostics recorded since the given checkpoint.
    member public __.AddInfoToDiagnosticsSince (cp: Checkpoint) (info: string) =
        for i = cp.DiagnosticCount to diagnostics.Count - 1 do
            let r = diagnostics.[i]
            if not (Seq.contains info r.Informations) then
                diagnostics.[i] <- { r with Informations = Seq.append (Seq.singleton info) r.Informations }

    /// Saves the current state (connections and diagnostics) as a checkpoint.
    member public __.Checkpoint () : Checkpoint =
        { UndoCount = undoStack.Count
          DiagnosticCount = diagnostics.Count }

    /// Returns to the given checkpoint: undoes variable bindings and clears any diagnostics reported.
    member public __.BacktrackTo (cp: Checkpoint) =
        if cp.UndoCount > undoStack.Count || cp.DiagnosticCount > diagnostics.Count then
            invalidArg (nameof cp) "Invalid checkpoint"

        rollbackBindingsTo cp.UndoCount
        diagnostics.RemoveRange(cp.DiagnosticCount, diagnostics.Count - cp.DiagnosticCount)

    /// Returns to the given checkpoint: undoes variable bindings BUT keep the reported diagnostics.
    member public __.BacktrackBindingsTo (cp: Checkpoint) =
        if cp.UndoCount > undoStack.Count then
            invalidArg (nameof cp) "Invalid checkpoint"

        rollbackBindingsTo cp.UndoCount

    /// Executes `f` speculatively: if it throws a `UnifyException` or produces any diagnostic,
    /// then the type checker's state is restored and the result is `None`.
    member public this.Attempt (f: unit -> 'a) : 'a option =
        let cp = this.Checkpoint()
        let rollback () =
            this.BacktrackTo cp
            None
        try
            let result = f ()
            if this.HasDiagnosticsSince cp then rollback ()
            else Some result
        with
        | UnifyException _ -> rollback ()

    /// Executes `f` speculatively but always restores the states: if it throws a `UnifyException` or
    /// produces any diagnostic, then return `false`, otherwise returns `true`. This is a lookahead function.
    member public this.Probe (f: unit -> unit) : bool =
        let cp = this.Checkpoint()
        try
            f ()
            let ok = not (this.HasDiagnosticsSince cp)
            this.BacktrackTo cp
            ok
        with
        | UnifyException _ ->
            this.BacktrackTo cp
            false
