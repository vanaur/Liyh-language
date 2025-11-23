namespace Liyh.Execution.Core

module Builtin =
    open Liyh.Execution

    // --- Lists --- //

    let rec public (|Nil|_|) =
        function
        | Symbol { Symbol = "nil"; Children = [] } -> true
        | _ -> false

    and public (|Cons|_|) =
        function
        | Symbol { Symbol = "cons"; Children = [ x; xs ] } -> Some(x, xs)
        | _ -> None

    and public (|Range|_|) =
        function
        | Symbol { Symbol = "range"; Children = [ start; step; stop ] } -> Some(start, step, stop)
        | _ -> None

    and public (|Concat|_|) =
        function
        | Symbol { Symbol = "concat"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Contains|_|) =
        function
        | Symbol { Symbol = "contains"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // -- Tuples --

    and public (|TupleN|_|) (n: int) =
        function
        | Symbol { Symbol = s; Children = xs } ->
            if xs.Length = n && s.StartsWith "tuple" && s.EndsWith(string n)
            then Some xs else None
        | _ -> None

    and public (|Tuple|_|) =
        function
        | Symbol { Symbol = s; Children = xs } ->
            if s.StartsWith "tuple" then
                match s.Remove("tuple".Length - 1) |> System.Int32.TryParse with
                | true, n when xs.Length = n -> Some(n, xs)
                | _ -> None
            else None
        | _ -> None

    // -- Options --

    and public (|Some'|_|) =
        function
        | Symbol { Symbol = "some"; Children = [ some ] } -> Some some
        | _ -> None

    and public (|None'|_|) =
        function
        | Symbol { Symbol = "none"; Children = [] } -> true
        | _ -> false

    // -- Arithmetic --

    and public (|Plus|_|) =
        function
        | Symbol { Symbol = "plus"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Minus|_|) =
        function
        | Symbol { Symbol = "minus"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Asterisk|_|) =
        function
        | Symbol { Symbol = "asterisk"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Slash|_|) =
        function
        | Symbol { Symbol = "slash"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Percent|_|) =
        function
        | Symbol { Symbol = "percent"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|DoubleAsterisk|_|) =
        function
        | Symbol { Symbol = "double_asterisk"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // -- Comparison --

    and public (|Ge|_|) =
        function
        | Symbol { Symbol = "ge"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Geq|_|) =
        function
        | Symbol { Symbol = "geq"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Le|_|) =
        function
        | Symbol { Symbol = "le"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Leq|_|) =
        function
        | Symbol { Symbol = "leq"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Eq|_|) =
        function
        | Symbol { Symbol = "eq"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Neq|_|) =
        function
        | Symbol { Symbol = "neq"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // -- Boolean --

    and public (|And|_|) =
        function
        | Symbol { Symbol = "and"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Or|_|) =
        function
        | Symbol { Symbol = "or"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Not|_|) =
        function
        | Symbol { Symbol = "not"; Children = [ a ] } -> Some(a)
        | _ -> None

    and public (|SymbolTrue|_|) =
        function
        | Symbol { Symbol = "true"; Children = [] } -> true
        | _ -> false

    and public (|SymbolFalse|_|) =
        function
        | Symbol { Symbol = "false"; Children = [] } -> true
        | _ -> false

    // -- Types --

    and public (|IsType|_|) =
        function
        | Symbol { Symbol = "is_type"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    and public (|Cast|_|) =
        function
        | Symbol { Symbol = "cast"; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // -- Misc --

    and public (|Show|_|) =
        function
        | Symbol { Symbol = "show"; Children = [ a ] } -> Some a
        | _ -> None

    and public (|PrintingShow|_|) =
        function
        | Symbol { Symbol = "printing_show"; Children = [ a ] } -> Some a
        | _ -> None

    and public (|DebugBench|_|) =
        function
        | Symbol { Symbol = "debug_bench"; Children = [ a; b ] } -> Some (a, b)
        | _ -> None

    and public (|DebugPrint|_|) =
        function
        | Symbol { Symbol = "debug_print"; Children = [ value ] } -> Some value
        | _ -> None
