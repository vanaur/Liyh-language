namespace Liyh.Core

/// The "internals" are native instructions in the runtime.
[<RequireQualifiedAccess>]
module Internals =
    open Liyh.Core

    // --- Arithmetic internals --- //

    let [<Literal>] public Add = "__internal_add"
    let [<Literal>] public Sub = "__internal_sub"
    let [<Literal>] public Mul = "__internal_mul"
    let [<Literal>] public Div = "__internal_div"
    let [<Literal>] public Mod = "__internal_mod"

    /// Internal arithmetic operation (+, -, *, /, %).
    let public arithmeticInternals =
        [| Add
           Sub
           Mul
           Div
           Mod |]

    let public (|Internal_add|_|) = function
        | Symbol { Symbol = Add; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_sub|_|) = function
        | Symbol { Symbol = Sub; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_mul|_|) = function
        | Symbol { Symbol = Mul; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_div|_|) = function
        | Symbol { Symbol = Div; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_mod|_|) = function
        | Symbol { Symbol = Mod; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // --- Boolean internals --- //

    let [<Literal>] public Eq = "__internal_eq"
    let [<Literal>] public Neq = "__internal_neq"
    let [<Literal>] public Le = "__internal_le"
    let [<Literal>] public Leq = "__internal_leq"
    let [<Literal>] public Ge = "__internal_ge"
    let [<Literal>] public Geq = "__internal_geq"

    /// Internal boolean operations for comparison (eq, neq, le, leq, ge, geq).
    let public booleanInternals =
        [| Eq
           Neq
           Le
           Leq
           Ge
           Geq |]

    let public (|Internal_eq|_|) = function
        | Symbol { Symbol = Eq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_neq|_|) = function
        | Symbol { Symbol = Neq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_le|_|) = function
        | Symbol { Symbol = Le; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_leq|_|) = function
        | Symbol { Symbol = Leq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_ge|_|) = function
        | Symbol { Symbol = Ge; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_geq|_|) = function
        | Symbol { Symbol = Geq; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    // --- Primitive types checking internals --- //

    let [<Literal>] public IsInt = "__internal_is_int"
    let [<Literal>] public IsFloat = "__internal_is_float"
    let [<Literal>] public IsChar = "__internal_is_char"
    let [<Literal>] public IsString = "__internal_is_string"

    /// Internal primitive type checking (is_int, is_float, is_char, is_string).
    let public primitiveTypeCheckingInternals =
        [| IsInt
           IsFloat
           IsChar
           IsString |]

    let public (|Internal_is_int|) = function
        | Symbol { Symbol = IsInt; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_float|) = function
        | Symbol { Symbol = IsFloat; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_char|) = function
        | Symbol { Symbol = IsChar; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_is_string|) = function
        | Symbol { Symbol = IsString; Children = [ a ] } -> Some(a)
        | _ -> None

    // --- Pretty printing --- //

    let [<Literal>] public Print = "__internal_print"
    let [<Literal>] public Strcat = "__internal_strcat"
    let [<Literal>] public Ppshow = "__internal_ppshow"

    let public (|Internal_print|_|) = function
        | Symbol { Symbol = Print; Children = [ a ] } -> Some(a)
        | _ -> None

    let public (|Internal_strcat|_|) = function
        | Symbol { Symbol = Strcat; Children = [ a; b ] } -> Some(a, b)
        | _ -> None

    let public (|Internal_ppshow|_|) = function
        | Symbol { Symbol = Ppshow; Children = [ a ] } -> Some(a)
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

    let [<Literal>] public Cons = "cons"
    let [<Literal>] public Nil = "nil"
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
        symbol "collection_access" [ expr; symbolTuple indices ]

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

    let [<Literal>] public Some' = "some"
    let [<Literal>] public None' = "none"

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

    // --- Debug --- //

    let [<Literal>] public BuiltinDebugBench = "debugbench"

    let public symbolDebugBench a b = symbol BuiltinDebugBench [ a; b ]

    let public (|DebugBench|_|) =
        function
        | Symbol { Symbol = BuiltinDebugBench; Children = [ a; b ] } -> Some(a, b)
        | _ -> None
