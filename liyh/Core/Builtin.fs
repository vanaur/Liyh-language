namespace Liyh.Core

/// The "internals" are native instructions in the runtime.
[<RequireQualifiedAccess>]
module Internals =
    open Liyh.FFI
    open Liyh.Core

    // --- Arithmetic internals --- //

    let public (|Internal_add|_|) = function
        | Symbol { Symbol = Internals.Add; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_sub|_|) = function
        | Symbol { Symbol = Internals.Sub; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_mul|_|) = function
        | Symbol { Symbol = Internals.Mul; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_div|_|) = function
        | Symbol { Symbol = Internals.Div; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_mod|_|) = function
        | Symbol { Symbol = Internals.Mod; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // --- Boolean internals --- //

    let public (|Internal_eq|_|) = function
        | Symbol { Symbol = Internals.Eq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_nt|_|) = function
        | Symbol { Symbol = Internals.Nt; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_neq|_|) = function
        | Symbol { Symbol = Internals.Neq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_le|_|) = function
        | Symbol { Symbol = Internals.Le; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_leq|_|) = function
        | Symbol { Symbol = Internals.Leq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_ge|_|) = function
        | Symbol { Symbol = Internals.Ge; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_geq|_|) = function
        | Symbol { Symbol = Internals.Geq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_or|_|) = function
        | Symbol { Symbol = Internals.Or; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_and|_|) = function
        | Symbol { Symbol = Internals.And; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // --- Primitive types checking internals --- //

    let public (|Internal_is_int|) = function
        | Symbol { Symbol = Internals.IsInt; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_float|) = function
        | Symbol { Symbol = Internals.IsFloat; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_char|) = function
        | Symbol { Symbol = Internals.IsChar; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_string|) = function
        | Symbol { Symbol = Internals.IsString; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_bool|) = function
        | Symbol { Symbol = Internals.IsBool; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_numeric|) = function
        | Symbol { Symbol = Internals.IsNumeric; Children = [ a ] } -> Some(a)
        | _ -> None

    // --- Pretty printing --- //

    let public (|Internal_print|_|) = function
        | Symbol { Symbol = Internals.Print; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_strcat|_|) = function
        | Symbol { Symbol = Internals.Strcat; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_ppshow|_|) = function
        | Symbol { Symbol = Internals.Ppshow; Children = [ a ] } -> Some(a)
        | _ -> None

    // --- Primitive types casting internals --- //

    let public (|Internal_cast_sti|_|) = function
        | Symbol { Symbol = Internals.CastSti; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_stf|_|) = function
        | Symbol { Symbol = Internals.CastStf; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_stc|_|) = function
        | Symbol { Symbol = Internals.CastStc; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_its|_|) = function
        | Symbol { Symbol = Internals.CastIts; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_itf|_|) = function
        | Symbol { Symbol = Internals.CastItf; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_itc|_|) = function
        | Symbol { Symbol = Internals.CastItc; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_fts|_|) = function
        | Symbol { Symbol = Internals.CastFts; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_fti|_|) = function
        | Symbol { Symbol = Internals.CastFti; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_ftc|_|) = function
        | Symbol { Symbol = Internals.CastFtc; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_cts|_|) = function
        | Symbol { Symbol = Internals.CastCts; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_cti|_|) = function
        | Symbol { Symbol = Internals.CastCti; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Internal_cast_ctf|_|) = function
        | Symbol { Symbol = Internals.CastCtf; Children = [ a ] } -> Some a
        | _ -> None

    // --- Buffer internals --- //

    let public (|Buffer_alloc|_|) = function
        | Symbol { Symbol = Internals.BufferAlloc; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Buffer_set|_|) = function
        | Symbol { Symbol = Internals.BufferSet; Children = [ a; b; c ] } -> Some(a, b, c)
        | _ -> None

    let public (|Buffer_get|_|) = function
        | Symbol { Symbol = Internals.BufferGet; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Buffer_realloc|_|) = function
        | Symbol { Symbol = Internals.BufferRealloc; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Buffer_length|_|) = function
        | Symbol { Symbol = Internals.BufferLength; Children = [ a ] } -> Some a
        | _ -> None

    let public (|Buffer_to_string|_|) = function
        | Symbol { Symbol = Internals.BufferToString; Children = [ a ] } -> Some a
        | _ -> None

    let public (|String_to_buffer|_|) = function
        | Symbol { Symbol = Internals.StringToBuffer; Children = [ a ] } -> Some a
        | _ -> None

/// The "builtins" are built-in functions of symbols for the runtime.
[<RequireQualifiedAccess>]
module rec Builtin =
    open Liyh.Core

    //
    // The runtime needs some builtin functional constructs to work properly. By nature,
    // the "builtin symbols" are more a matter of code design, since simple symbols without
    // arguments always exist due to the symbolic nature of the language.
    //

    // --- Lists --- //

    let [<Literal>] public Cons = "Cons"
    let [<Literal>] public Nil = "Nil"
    let [<Literal>] public Reverse = "reverse"
    let [<Literal>] public Range = "range"
    let [<Literal>] public Contains = "contains"
    let [<Literal>] public Access = "collection_access"

    let public symbolCons a b = symbol Cons [ a; b ]
    let public symbolNil = simpleSymbol Nil
    let public symbolReverse x = symbol Reverse [ x ]
    let public symbolRange a b c = symbol Range [ a; b; c ]
    let public symbolContains a b = symbol Contains [ a; b ]

    let public symbolList (xs: CoreTerm list) =
        let loop lst =
            let rec loopAcc acc =
                function
                | [] -> acc
                | x :: xs -> loopAcc (symbolCons x acc) xs

            loopAcc symbolNil (List.rev lst)

        loop xs

    let public symbolCollectionAccess (expr: CoreTerm) (indices: CoreTerm list) =
        symbol Access [ expr; symbolTuple indices ]

    let public (|Nil|_|) =
        function
        | Symbol { Symbol = Nil; Children = [] } -> Some()
        | _ -> None

    let public (|Cons|_|) =
        function
        | Symbol { Symbol = Cons; Children = [ x; xs ] } -> Some(x, xs)
        | _ -> None

    let public (|Reverse|_|) =
        function
        | Symbol { Symbol = Reverse; Children = [ x ] } -> Some x
        | _ -> None

    let public (|Range|_|) =
        function
        | Symbol { Symbol = Range; Children = [ a; b; c ] } -> Some(a, b, c)
        | _ -> None

    let public (|Contains|_|) =
        function
        | Symbol { Symbol = Contains; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Access|_|) =
        function
        | Symbol { Symbol = Access; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // --- Boolean --- //

    let [<Literal>] public True = "true"
    let [<Literal>] public False = "false"
    let [<Literal>] public And = "and"
    let [<Literal>] public Or = "or"
    let [<Literal>] public Not = "not"

    let public symbolTrue = simpleSymbol True
    let public symbolFalse = simpleSymbol False
    let public symbolAnd a b = symbol And [ a; b ]
    let public symbolOr a b = symbol Or [ a; b ]
    let public symbolNot a = symbol Not [ a ]

    let public (|True|_|) =
        function
        | Symbol { Symbol = True; Children = [] } -> Some()
        | _ -> None

    let public (|False|_|) =
        function
        | Symbol { Symbol = False; Children = [] } -> Some()
        | _ -> None

    let public (|And|_|) =
        function
        | Symbol { Symbol = And; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Or|_|) =
        function
        | Symbol { Symbol = Or; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Not|_|) =
        function
        | Symbol { Symbol = Not; Children = [ a ] } -> Some a
        | _ -> None

    // --- Option --- //

    let [<Literal>] public Some' = "Some"
    let [<Literal>] public None' = "None"

    let public symbolSome x = symbol Some' [ x ]
    let public symbolNone = simpleSymbol None'

    let public (|None'|_|) =
        function
        | Symbol { Symbol = None'; Children = [] } -> Some()
        | _ -> None

    let public (|Some'|_|) =
        function
        | Symbol { Symbol = Some'; Children = [ x ] } -> Some x
        | _ -> None

    // --- Misc --- //

    let [<Literal>] public Unit = "unit"
    let [<Literal>] public Tuple = "tuple"
    let [<Literal>] public Ptr = "ptr"
    let [<Literal>] public Cast = "cast"
    let [<Literal>] public Show = "show"

    let public symbolUnit = simpleSymbol Unit
    let public symbolTuple xs = symbol Tuple xs
    let public symbolPtr ptr = symbol Ptr [ Literal (Integer ptr) ]
    let public symbolCast a b = symbol Cast [ a; b ]
    let public symbolShow x = symbol Show [ x ]

    let public (|Unit|_|) =
        function
        | Symbol { Symbol = Unit; Children = [] } -> Some()
        | _ -> None

    let public (|Tuple|_|) =
        function
        | Symbol { Symbol = Tuple; Children = xs } -> Some xs
        | _ -> None

    let public (|Ptr|_|) =
        function
        | Symbol { Symbol = Ptr; Children = [ Literal (Integer ptr) ] } -> Some (nativeint ptr)
        | _ -> None

    let public (|Cast|_|) =
        function
        | Symbol { Symbol = Cast; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Show|_|) =
        function
        | Symbol { Symbol = Show; Children = [ x ] } -> Some x
        | _ -> None

    // --- Arithmetic symbolics --- //

    let [<Literal>] public Plus = "plus"
    let [<Literal>] public Minus = "minus"
    let [<Literal>] public Asterisk = "asterisk"
    let [<Literal>] public Slash = "slash"
    let [<Literal>] public Percent = "percent"
    let [<Literal>] public DoubleAsterisk = "double_asterisk"

    let public symbolPlus a b = symbol Plus [ a; b ]
    let public symbolMinus a b = symbol Minus [ a; b ]
    let public symbolAsterisk a b = symbol Asterisk [ a; b ]
    let public symbolSlash a b = symbol Slash [ a; b ]
    let public symbolPercent a b = symbol Percent [ a; b ]
    let public symbolDoubleAsterisk a b = symbol DoubleAsterisk [ a; b ]

    let public (|Plus|_|) =
        function
        | Symbol { Symbol = Plus; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Minus|_|) =
        function
        | Symbol { Symbol = Minus; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Asterisk|_|) =
        function
        | Symbol { Symbol = Asterisk; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Slash|_|) =
        function
        | Symbol { Symbol = Slash; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Percent|_|) =
        function
        | Symbol { Symbol = Percent; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|DoubleAsterisk|_|) =
        function
        | Symbol { Symbol = DoubleAsterisk; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // --- Boolean symbolics --- //

    let [<Literal>] public Ge = "ge"
    let [<Literal>] public Geq = "geq"
    let [<Literal>] public Le = "le"
    let [<Literal>] public Leq = "leq"
    let [<Literal>] public Eq = "eq"
    let [<Literal>] public Neq = "neq"

    let public symbolGe a b = symbol Ge [ a; b ]
    let public symbolGeq a b = symbol Geq [ a; b ]
    let public symbolLe a b = symbol Le [ a; b ]
    let public symbolLeq a b = symbol Leq [ a; b ]
    let public symbolEq a b = symbol Eq [ a; b ]
    let public symbolNeq a b = symbol Neq [ a; b ]

    let public (|Ge|_|) =
        function
        | Symbol { Symbol = Ge; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Geq|_|) =
        function
        | Symbol { Symbol = Geq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Le|_|) =
        function
        | Symbol { Symbol = Le; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Leq|_|) =
        function
        | Symbol { Symbol = Leq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Eq|_|) =
        function
        | Symbol { Symbol = Eq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Neq|_|) =
        function
        | Symbol { Symbol = Neq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

