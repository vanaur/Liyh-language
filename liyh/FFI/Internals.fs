namespace Liyh.FFI

/// The "internals" are native instructions in the runtime.
[<RequireQualifiedAccess>]
module public Internals =

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

    // --- Boolean internals --- //

    let [<Literal>] public Eq = "__internal_eq"
    let [<Literal>] public Nt = "__internal_nt"
    let [<Literal>] public Neq = "__internal_neq"
    let [<Literal>] public Le = "__internal_le"
    let [<Literal>] public Leq = "__internal_leq"
    let [<Literal>] public Ge = "__internal_ge"
    let [<Literal>] public Geq = "__internal_geq"
    let [<Literal>] public Or = "__internal_or"
    let [<Literal>] public And = "__internal_and"

    /// Internal boolean operations for comparison (eq, neq, le, leq, ge, geq, or, and).
    let public booleanInternals =
        [| Eq
           Nt
           Neq
           Le
           Leq
           Ge
           Geq
           Or
           And |]

    // --- Primitive types checking internals --- //

    let [<Literal>] public IsInt = "__internal_is_int"
    let [<Literal>] public IsFloat = "__internal_is_float"
    let [<Literal>] public IsChar = "__internal_is_char"
    let [<Literal>] public IsString = "__internal_is_string"
    let [<Literal>] public IsBool = "__internal_is_bool"
    let [<Literal>] public IsNumeric = "__internal_is_numeric"

    /// Internal primitive type checking (is_int, is_float, is_char, is_string).
    let public primitiveTypeCheckingInternals =
        [| IsInt
           IsFloat
           IsChar
           IsString
           IsBool
           IsNumeric |]

    // --- Pretty printing --- //

    let [<Literal>] public Print = "__internal_print"
    let [<Literal>] public Strcat = "__internal_strcat"
    let [<Literal>] public Ppshow = "__internal_ppshow"

    // --- Primitive types casting internals --- //

    let [<Literal>] public CastSti = "__internal_cast_sti"  // String to Int
    let [<Literal>] public CastStf = "__internal_cast_stf"  // String to Float
    let [<Literal>] public CastStc = "__internal_cast_stc"  // String to Char

    let [<Literal>] public CastIts = "__internal_cast_its"  // Int to String
    let [<Literal>] public CastItf = "__internal_cast_itf"  // Int to Float
    let [<Literal>] public CastItc = "__internal_cast_itc"  // Int to Char

    let [<Literal>] public CastFts = "__internal_cast_fts"  // Float to String
    let [<Literal>] public CastFti = "__internal_cast_fti"  // Float to Int
    let [<Literal>] public CastFtc = "__internal_cast_ftc"  // Float to Char

    let [<Literal>] public CastCts = "__internal_cast_cts"  // Char to String
    let [<Literal>] public CastCti = "__internal_cast_cti"  // Char to Int
    let [<Literal>] public CastCtf = "__internal_cast_ctf"  // Char to Float

    /// Casting primitives.
    let public primitiveTypeCastingInternals =
        [| CastSti
           CastStf
           CastStc
           CastIts
           CastItf
           CastItc
           CastFts
           CastFti
           CastFtc
           CastCts
           CastCti
           CastCtf |]

    // --- Buffer internals --- //

    let [<Literal>] BufferAlloc = "__buffer_alloc"
    let [<Literal>] BufferGet = "__buffer_get"
    let [<Literal>] BufferSet = "__buffer_set"
    let [<Literal>] BufferRealloc = "__buffer_realloc"
    let [<Literal>] BufferLength = "__buffer_length"
    let [<Literal>] BufferToString = "__buffer_to_string"
    let [<Literal>] StringToBuffer = "__string_to_buffer"

    /// Buffer primitives (alloc, get, set, realloc, length, string_to_buffer, buffer_to_string).
    let public bufferInternals =
        [| BufferAlloc
           BufferGet
           BufferSet
           BufferRealloc
           BufferLength
           BufferToString
           StringToBuffer |]

