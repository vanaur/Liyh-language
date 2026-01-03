namespace Liyh.Core.DecisionTree

open Liyh.Core

type public Path =
    | Child of Path * int
    | Field of Path * string    // for record fields
    | Root

    member this.Extend(index: int) = Child(this, index)
    member this.Access(field: string) = Field(this, field)

    override this.ToString() =
        let rec build path acc =
            match path with
            | Root -> if List.isEmpty acc then "." else String.concat "" acc
            | Child(parent, idx) -> build parent (sprintf "[%d]" idx :: acc)
            | Field(parent, name) -> build parent (sprintf ".%s" name :: acc)
        build this []

type public DecisionTree =
    | Switch of
        _path: Path *
        _cases: Map<string * int, DecisionTree> *
        _default: DecisionTree option

    | SwitchLiteral of
        _path: Path *
        _cases: Map<CoreLiteral, DecisionTree> *
        _default: DecisionTree option

    | ArityCheck of
        _path: Path *
        _arity: int *
        _success: DecisionTree *
        _failure: DecisionTree option

    | TypeCheck of
        _path: Path *
        _cases: Map<TermType, DecisionTree> *
        _default: DecisionTree option

    | Bind of
        _varName: string *
        _path: Path *
        _continuation: DecisionTree
    
    | WhenGuard of
        _guard: CoreTerm *
        _bindings: Map<string, Path> *
        _success: DecisionTree *
        _failure: DecisionTree option

    | Leaf of
        _ruleIndex: int *
        _bindings: Map<string, Path>
    
    | Fail

and public TermType =
    | TSymbol
    | TVariable
    | TLiteral of LiteralType
    | TClosure
    | TRecord
    | TWildcard

and public LiteralType =
    | TInteger
    | TFloat
    | TString
    | TChar

module public PathAccess =

    let rec public access (path: Path) (term: CoreTerm) =
        match path with
        | Root -> term
        | Child(parent, idx) ->
            let parentTerm = access parent term
            match parentTerm with
            | Symbol { Children = children } when idx >= 0 && idx < children.Length ->
                children.[idx]
            | Symbol { Children = children } ->
                failwithf "Path %O out of bounds: index %d, but term %s has only %d children"
                    path idx (PrettyPrinter.prettyPrintExpr parentTerm) children.Length
            | _ ->
                failwithf "Path %O cannot descend into non-symbol term: %s"
                    path (PrettyPrinter.prettyPrintExpr parentTerm)

        | Field(parent, name) ->
            let parentTerm = access parent term
            match parentTerm with
            | RecordExtend { Extension = fields } ->
                match List.tryFind (fun (k, _) -> k = name) fields with
                | Some (_, v) -> v
                | None -> failwithf "Field '%s' not found in record." name
            | _ ->
                failwithf "Path %O expects a record, but got '%s'"
                    path (PrettyPrinter.prettyPrintExpr parentTerm)

