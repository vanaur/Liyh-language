/**
 * @file rcl.c
 * @author vanaur (https://github.com/vanaur)
 * @brief Runtime Core Library (RCL) for the Liyh language.
 * @version 0.1
 * @date 2025-12-25
 *
 * @copyright Copyright (c) 2025
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <float.h>
#include <time.h>

#if __has_include(<ffi.h>)
#   include <ffi.h>
#else
#   error "LibFFI (ffi.h) not found: please install"
#endif

#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
typedef HMODULE rcl_lib_handle;
#define RCL_LOAD_LIB(path) LoadLibraryA(path)
#define RCL_FIND_SYM(lib, name) GetProcAddress(lib, name)
#define RCL_CLOSE_LIB(lib) FreeLibrary(lib)
#else
#include <dlfcn.h>
typedef void* rcl_lib_handle;
#define RCL_LOAD_LIB(path) dlopen(path, RTLD_LAZY | RTLD_GLOBAL)
#define RCL_FIND_SYM(lib, name) dlsym(lib, name)
#define RCL_CLOSE_LIB(lib) dlclose(lib)
#endif



// --------------------------------------- //
// ------------ HELPFUL MACRO ------------ //
// --------------------------------------- //



/// Tells the compiler that the condition is likely to be true.
#define likely(x) __builtin_expect(!!(x), 1)

/// Tells the compiler that the condition is unlikely to be true.
#define unlikely(x) __builtin_expect(!!(x), 0)

typedef uintptr_t term_t;
typedef uint32_t sym_id_t;

#define TAG_PTR         0x0 // tagged pointer (ptr)
#define TAG_INT         0x1 // tagged pointer (int)
#define TAG_CHAR        0x2 // tagged pointer (char)
#define TAG_BOOL        0x3 // tagged pointer (bool)
#define TAG_MASK        0x3 // extract the 2 least significant bits

#define IS_PTR(x)       ((x) != 0 && (((x) & TAG_MASK) == TAG_PTR))

#define IS_INT(x)       (((x) & TAG_MASK) == TAG_INT)
#define MAKE_INT(val)   ((((int64_t)(val)) << 2) | TAG_INT)
#define GET_INT(val)    (((int64_t)(val)) >> 2)

#define MAKE_CHAR(val)  ((((uintptr_t)(val)) << 2) | TAG_CHAR)
#define GET_CHAR(val)   ((uint32_t)(((uintptr_t)(val)) >> 2))
#define IS_CHAR(x)      (((x) & TAG_MASK) == TAG_CHAR)

#define IS_BOOL(x)      (((x) & TAG_MASK) == TAG_BOOL)
#define MAKE_BOOL(val)  ((((uintptr_t)(val ? 1 : 0)) << 2) | TAG_BOOL)
#define GET_BOOL(val)   ((uint32_t)(((uintptr_t)(val)) >> 2))

#define IS_NUMERIC(t)   (IS_INT(t) || (IS_PTR(t) && AS_HEADER(t)->id == SYM_FLOAT_NATIVE))

#define SYM_BUFFER_NATIVE   0xFFFFFFEE  // Mutable & resizeable buffer (bytes).
#define SYM_PTR_NATIVE      0xFFFFFFEF  // opaque pointer (for FFI)
#define SYM_CHAR_NATIVE     0xFFFFFFF0  // characters
#define SYM_NUM_NATIVE      0xFFFFFFF4  // numerical value (int or float)
#define SYM_BOOL_NATIVE     0xFFFFFFF5  // booleans
#define SYM_SUSPENDED_CALL  0xFFFFFFF6  // Indicates a function application that has been created dynamically.
#define SYM_BLACK_HOLE      0xFFFFFFF7  // Indicates that a thunk is currently being evaluated.
#define SYM_THUNK           0xFFFFFFF8  // Thunk for lazy evaluation (delays)
#define SYM_INDIRECT        0xFFFFFFF9  // Indirections in lazy evaluation
#define SYM_CONTINUATION    0xFFFFFFFA  // continuation for symbolic computations and substitutions
#define SYM_STRING_NATIVE   0xFFFFFFFB  // strings
#define SYM_RECORD_NATIVE   0xFFFFFFFC  // records
#define SYM_FLOAT_NATIVE    0xFFFFFFFD  // floats
#define SYM_CLOSURE         0xFFFFFFFE  // closures
#define SYM_INT_NATIVE      0xFFFFFFFF  // integers

#define IS_SYSTEM_TAG(id)   ((id) >= SYM_CHAR_NATIVE)   // identify internal tags
#define IS_USER_DATA(id)    ((id) < SYM_CHAR_NATIVE)    // identify user defined data

#define INITIAL_CAPACITY 1024 // initial capacity for growing vectors



// --------------------------------- //
// ------------ HEADERS ------------ //
// --------------------------------- //



// While `term_t` is an "universal type", `term_header_t` is a "specialized term" (we convert from
// `term_t` to `term_header_t` using the `AS_HEADER` macro). This specialised type allows tree-like
// structures to be represented in a relatively simple manner (without the need to define unions of
// algebraic data types). It forms the basis of constructions in Liyh.


// This type represents the "header" for "structured terms", it serves as a basis for
// each high level composed types (symbolic expressions, closures, records, ...)
typedef struct
{
    size_t rc;              // ref count

    sym_id_t id;            // Identify the symbol id
    uint32_t arity;         // Number of children
    term_t children[];      // Children array

} term_header_t;

#define AS_HEADER(val)  ((term_header_t *)(val))



// --------------------------------------------------------- //
// ------------ AUTOMATIC REFERENCE COUNTING GC ------------ //
// --------------------------------------------------------- //



// We use automatic reference counting (ARC) for the memory management of the VM.
// The memory allocations through this system are done using an arena allocator, and we also use
// a "free memory list" that store recycled memory from the previous allocations by arity to
// limitate the memory fragmentation and new allocations, reducing memory usage and improving
// the overall performances. This is useful for small objects that are created and destroyed in
// loops, for example when traversing recursive structures, as the memory of the older objects is
// then used by the new ones, and so on.
//
// When a new reference is added, the reference count field in the header (`rc` in `header_term_t`)
// is incremented, and when a reference is dropped, the count is decremented. When a reference count
// reaches zero, the object (and its children) is not immediately released, but is added to a "pending queue"
// to prevent cascading releases and release latencies. The queue is flushed (`drain_queue`), in a non-recursive
// manner, at the end of each function (during `ret` and `tailcall` instructions)



#define ARENA_CHUNK_SIZE (1024 * 1024) // 1 Mo

/// Objects with an arity of 0 to 15 are recycled; the others will be recycled when the chunks are released.
// In practice, it should be rare to encounter such a high arity, which ensures fairly good memory recycling.
#define MAX_RECYCLED_ARITY 16

/// Chunk of arena memory allocator.
typedef struct arena_chunk_s
{
    struct arena_chunk_s *next;
    size_t used;
    size_t capacity;
    uint8_t data[];     // points to the memory immediately after the header (the actual memory of the chunk)
} arena_chunk_t;

/// The free node list, used to contain list of unused memory after reference counter reaching 0.
typedef struct free_node_s
{
    struct free_node_s *next;
} free_node_t;

/// Arena memory allocator. It contains the chunks of allocations as well as a fixed array of recycled memory
/// for each arity, allowing to use the old memory back without new allocation.
typedef struct
{
    arena_chunk_t *current_chunk;
    free_node_t *free_lists[MAX_RECYCLED_ARITY];    // An array of free lists, one for each arity.
} arena_t;

static inline void init_arena(arena_t *arena)
{
    memset(arena, 0, sizeof(arena_t));
}

/// Create a new arena zone.
static void arena_grow(arena_t *arena, const size_t min_size)
{
    const size_t capacity = (min_size > ARENA_CHUNK_SIZE ? min_size : ARENA_CHUNK_SIZE);
    arena_chunk_t *new_chunk = malloc(sizeof(arena_chunk_t) + capacity);

    new_chunk->next = arena->current_chunk;
    new_chunk->capacity = capacity;
    new_chunk->used = 0;

    arena->current_chunk = new_chunk;
}

/// Using the given arena allocator, allocate memory for an object of given arity.
static void *arena_alloc_term(arena_t *arena, const size_t arity)
{
    // We are looking for recycled blocks fist.

    if (arity < MAX_RECYCLED_ARITY && arena->free_lists[arity])
    {
        void *ptr = arena->free_lists[arity];
        arena->free_lists[arity] = arena->free_lists[arity]->next;
        return ptr;
    }

    // Otherwise, we just use the bump arena allocator.

    size_t size = (sizeof(term_header_t) + (arity * sizeof(term_t)));
    if (size < sizeof(free_node_t)) size = sizeof(free_node_t); // ensure enough memory for at least one node

    size = (size + 7) & ~7; // align on 64 bits (better on 64 bits systems)

    if (!arena->current_chunk || arena->current_chunk->used + size > arena->current_chunk->capacity)
        arena_grow(arena, size);

    if (!arena->current_chunk)
        return NULL;

    void *ptr = arena->current_chunk->data + arena->current_chunk->used;
    arena->current_chunk->used += size;

    return ptr;
}

/// Releases all the memory of the arena.
static void arena_free(arena_t *arena)
{
    arena_chunk_t *chunk = arena->current_chunk;
    while (chunk)
    {
        arena_chunk_t *next = chunk->next;
        free(chunk);
        chunk = next;
    }
    arena->current_chunk = NULL;
}

typedef struct
{
    term_t *pending;    // objects for whose rc is 0
    size_t size;
    size_t capacity;
} dec_queue_t;

static void init_queue(dec_queue_t *queue)
{
    queue->capacity = INITIAL_CAPACITY;
    queue->size = 0;
    queue->pending = malloc(queue->capacity * sizeof(term_t));
}

static void grow_queue(dec_queue_t *queue)
{
    size_t new_capacity = queue->capacity * 2;
    term_t *new_pending = realloc(queue->pending, new_capacity * sizeof(term_t));

    queue->pending = new_pending;
    queue->capacity = new_capacity;
}

static void free_queue(dec_queue_t *queue)
{
    free(queue->pending);
    queue->pending = NULL;
    queue->capacity = 0;
    queue->size = 0;
}

/// Increments the reference count of the given term. If it is not a heap allocated
/// object, then do nothing (for example, a simple integer is not boxed).
static __always_inline void rc_increment(term_t obj)
{
    if (unlikely(!obj || !IS_PTR(obj)))
        return; // not an object on the heap

    term_header_t *h = AS_HEADER(obj);
    h->rc++;
}

/// Decrements the reference count of the given term. If it is not a heap allocated
/// object, then do nothing (for example, a simple integer is not boxed). If the reference
/// count reaches zero, add the object to the pending queue for freeing or recycling.
static __always_inline void rc_decrement(dec_queue_t *queue, term_t obj)
{
    if (!obj || !IS_PTR(obj))
        return; // not an object on the heap

    term_header_t *h = AS_HEADER(obj);

    if (likely(h->rc > 0))
    {
        h->rc--;

        if (h->rc == 0)
        {
            if (unlikely(queue->size >= queue->capacity))
                grow_queue(queue);

            queue->pending[queue->size++] = obj;
        }
    }
}

/// Assigns a refcounted value to a target refcounted value, and handle the reference count of each one.
/// If one or each of the objects are boxed, then no refcount will occur since it is not necessary.
static __always_inline void rc_assign(dec_queue_t *queue, term_t *target, term_t new_val)
{
    term_t old_val = *target;

    if (old_val == new_val)
        return;

    rc_increment(new_val);
    *target = new_val;
    rc_decrement(queue, old_val);
}

/// Releases each objects on the pending queue and decrement the refcount of each linked objects.
/// Note that decreased counters may add to the pending queue, and will be drained for a next cycle.
static void drain_queue(dec_queue_t *queue, arena_t *arena)
{
    while (queue->size > 0)
    {
        term_t obj = queue->pending[--queue->size];
        term_header_t *h = AS_HEADER(obj);
        uint32_t arity = h->arity;

        // Relase native ressources.
        if (h->id == SYM_STRING_NATIVE || h->id == SYM_BUFFER_NATIVE)
        {
            void *native_ptr = (void *)h->children[0];
            if (native_ptr) free(native_ptr);
        }

        // Propagate the refcount to the children.
        for (uint32_t i = 0; i < h->arity; i++)
        {
            term_t child = h->children[i];
            if (child && IS_PTR(h->children[i]))
                rc_decrement(queue, h->children[i]);
        }

        size_t alloc_words = arity;

        if (h->id == SYM_PTR_NATIVE || h->id == SYM_FLOAT_NATIVE)
            alloc_words = (sizeof(void *) + sizeof(term_t) - 1) / sizeof(term_t);

        else if (h->id == SYM_BUFFER_NATIVE || h->id == SYM_STRING_NATIVE)
            alloc_words = 2;

        // If the arity is in the bounds, recycle the memory of the dead object for a next use.
        if (alloc_words < MAX_RECYCLED_ARITY)
        {
            free_node_t *dead_node = (free_node_t *)h;
            dead_node->next = arena->free_lists[alloc_words];
            arena->free_lists[alloc_words] = dead_node;
        }
    }
}



// ---------------------------------------------------------------- //
// ------------ FOREIGN FUNCTION INTERFACE DEFINITIONS ------------ //
// ---------------------------------------------------------------- //



/// C types for the FFI.
enum rcl_type
{
    RCL_TYPE_UINT8,         // uint8
    RCL_TYPE_INT8,          // int8
    RCL_TYPE_UINT16,        // uint16
    RCL_TYPE_INT16,         // int16
    RCL_TYPE_UINT32,        // uint32
    RCL_TYPE_INT32,         // int32
    RCL_TYPE_UINT64,        // uint64
    RCL_TYPE_INT64,         // int64
    RCL_TYPE_FLOAT32,       // float32
    RCL_TYPE_FLOAT64,       // float64
    RCL_TYPE_LONGDOUBLE,    // long double (precision depends on architecture)
    RCL_TYPE_CHAR,          // char (32 bits unicode in Liyh)
    RCL_TYPE_STRING,        // string (ptr)
    RCL_TYPE_PTR,           // void* (opaque pointer / buffer)
    RCL_TYPE_VOID,          // void
};

/// Given a RCL type, return the associated FFI type representation for LibFFI.
static ffi_type *rcl_type_to_ffi_type(const enum rcl_type rcl_ty)
{
    switch (rcl_ty)
    {
        case RCL_TYPE_UINT8: return &ffi_type_uint8;
        case RCL_TYPE_INT8: return &ffi_type_sint8;
        case RCL_TYPE_UINT16: return &ffi_type_uint16;
        case RCL_TYPE_INT16: return &ffi_type_sint16;
        case RCL_TYPE_UINT32: return &ffi_type_uint32;
        case RCL_TYPE_INT32: return &ffi_type_sint32;
        case RCL_TYPE_UINT64: return &ffi_type_uint64;
        case RCL_TYPE_INT64: return &ffi_type_sint64;
        case RCL_TYPE_FLOAT32: return &ffi_type_float;
        case RCL_TYPE_FLOAT64: return &ffi_type_double;
        case RCL_TYPE_LONGDOUBLE: return &ffi_type_longdouble;
        case RCL_TYPE_CHAR: return &ffi_type_uint32;
        case RCL_TYPE_STRING: return &ffi_type_pointer;
        case RCL_TYPE_PTR: return &ffi_type_pointer;
        case RCL_TYPE_VOID: return &ffi_type_void;
    }
}

/// Returns the string version of the given RCL type.
static const char *rcl_type_name(enum rcl_type type)
{
    switch (type)
    {
        case RCL_TYPE_UINT8: return "uint8";
        case RCL_TYPE_INT8: return "int8";
        case RCL_TYPE_UINT16: return "uint16";
        case RCL_TYPE_INT16: return "int16";
        case RCL_TYPE_UINT32: return "uint32";
        case RCL_TYPE_INT32: return "int32";
        case RCL_TYPE_UINT64: return "uint64";
        case RCL_TYPE_INT64: return "int64";
        case RCL_TYPE_FLOAT32: return "float32";
        case RCL_TYPE_FLOAT64: return "float64";
        case RCL_TYPE_LONGDOUBLE: return "longdouble";
        case RCL_TYPE_CHAR: return "char";
        case RCL_TYPE_STRING: return "string";
        case RCL_TYPE_PTR: return "ptr";
        case RCL_TYPE_VOID: return "void";
    }
}

/// Structured information for calling an external function.
struct ffi_info
{
    ffi_cif *cif;                       // call interface
    void (*function_pointer)(void);     // external function pointer

    size_t arity;                       // number of arguments taken by the external function

    enum rcl_type *arguments_types;     // RCL ffi C types for the arguments
    enum rcl_type return_type;          // RCL ffi C type for the return value
    
    ffi_type **ffi_arguments_types;     // libffi ffi C types for the arguments

    sym_id_t sym_id;                    // symol ID
};

static void free_ffi_info(struct ffi_info *ffi_info)
{
    if (ffi_info == NULL)
        return;

    free(ffi_info->cif);
    free(ffi_info->ffi_arguments_types);
    free(ffi_info);
}

static struct ffi_info *new_ffi_info(
    void (*function_pointer)(void),
    size_t arity,
    enum rcl_type *arguments_types,
    enum rcl_type return_type)
{
    if (function_pointer == NULL)
    {
        fprintf(stderr, "Fatal error: NULL function pointer.\n");
        exit(1);
    }

    struct ffi_info *result = malloc(sizeof(struct ffi_info));

    ffi_type **ffi_arguments_types = malloc(arity * sizeof(ffi_type *));
    ffi_type *ffi_return_type = rcl_type_to_ffi_type(return_type);

    for (size_t i = 0; i < arity; i++)
        ffi_arguments_types[i] = rcl_type_to_ffi_type(arguments_types[i]);

    ffi_cif *cif_ptr = malloc(sizeof(ffi_cif));

    if (ffi_prep_cif(cif_ptr, FFI_DEFAULT_ABI, arity, ffi_return_type, ffi_arguments_types) == FFI_OK)
    {
        *result = (struct ffi_info){ 
            cif_ptr, 
            function_pointer, 
            arity, 
            arguments_types, 
            return_type, 
            ffi_arguments_types
        };
        return result;
    }

    fprintf(stderr, "Fatal error: FFI CIF is not OK.\n");
    exit(1);
}

/// Call the external function given its information and the actual arguments.
/// The returned memory is handled by the caller.
static void *rcl_ffi_call(const struct ffi_info *ffi_info, void **arguments)
{
    size_t ret_size = sizeof(ffi_arg);

    if (ffi_info->cif->rtype->size > ret_size)
        ret_size = ffi_info->cif->rtype->size;

    void *return_value = malloc(ret_size);
    ffi_call(ffi_info->cif, ffi_info->function_pointer, return_value, arguments);

    return return_value;
}



// ----------------------------------------- //
// ------------ VM INSTRUCTIONS ------------ //
// ----------------------------------------- //



typedef enum
{
    // jump instructions

    INSTR_HALT,                                         // HALT exit_code, _, _, _
    INSTR_JUMP,                                         // JUMP label, _, _, _
    INSTR_JUMP_FALSE,                                   // JUMP_FALSE src_reg, label, _, _
    INSTR_JUMP_TRUE,                                    // JUMP_TRUE src_reg, label, _, _

    // function calling instructions

    INSTR_RESERVE,                                      // RESERVE count, _, _, _
    INSTR_CALL,                                         // CALL label, arg_offset, arg_count, dst_reg
    INSTR_TAILCALL,                                     // TAILCALL label, arg_offset, arg_count, _
    INSTR_RET,                                          // RET src_reg, _, _, _
    INSTR_APPLY,                                        // APPLY fn_reg, arg_offset, arg_count, dst_reg
    INSTR_MOV,                                          // MOV dst_reg, src_reg, _, _

    // literal and atom loading instructions

    INSTR_LOAD_INT,                                     // LOAD_INT dst_reg, value, _, _
    INSTR_LOAD_ATOM,                                    // LOAD_ATOM dst_reg, sym_id, _, _
    INSTR_LOAD_FLOAT,                                   // LOAD_FLOAT dst_reg, hi_bits, lo_bits, _
    INSTR_LOAD_CHAR,                                    // LOAD_CHAR dst_reg, value, _, _
    INSTR_LOAD_STRING,                                  // LOAD_STRING dst_reg, str_index, _, _
    INSTR_LOAD_BOOL,                                    // LOAD_BOOL dst_reg, bool (0|1)

    // native arithmetic instructions

    INSTR_ADD,                                          // ADD dst_reg, lhs_reg, rhs_reg, _
    INSTR_SUB,                                          // SUB dst_reg, lhs_reg, rhs_reg, _
    INSTR_MUL,                                          // MUL dst_reg, lhs_reg, rhs_reg, _
    INSTR_DIV,                                          // DIV dst_reg, lhs_reg, rhs_reg, _
    INSTR_MOD,                                          // MOD dst_reg, lhs_reg, rhs_reg, _
    INSTR_NEG,                                          // NEG dst_reg, src_reg, _, _

    // native boolean instructions

    INSTR_EQUAL,                                        // EQUAL dst_reg, lhs_reg, rhs_reg, _
    INSTR_NOT_EQUAL,                                    // NOT_EQUAL dst_reg, lhs_reg, rhs_reg, _
    INSTR_NOT,                                          // NOT dst_reg, src_reg, _, _
    INSTR_LEQ,                                          // LEQ dst_reg, lhs_reg, rhs_reg, _
    INSTR_LE,                                           // LE dst_reg, lhs_reg, rhs_reg, _
    INSTR_GE,                                           // GE dst_reg, lhs_reg, rhs_reg, _
    INSTR_GEQ,                                          // GEQ dst_reg, lhs_reg, rhs_reg, _

    // native string concatenation instruction

    INSTR_STR_CAT,                                      // STR_CAT dst_reg, lhs_reg, rhs_reg, _

    // record specific instructions

    INSTR_MK_RECORD,                                    // MK_RECORD dst_reg, pair_count, start_reg, _
    INSTR_EXTEND_RECORD,                                // EXTEND_RECORD dst_reg, base_reg, ext_count, ext_start
    INSTR_GET_FIELD,                                    // GET_FIELD dst_reg, record_reg, field_id, fail_label

    // symbolic data allocation instruction

    INSTR_ALLOC,                                        // ALLOC dst_reg, sym_id, arity, src_offset
    INSTR_SUBST,                                        // SUBST dst_reg, src_reg, atom_reg, repl_reg

    // closure specific instructions

    INSTR_CLOSURE,                                      // CLOSURE dst_reg, label, upval_count, upval_start
    INSTR_CALL_CLOSURE,                                 // CALL_CLOSURE cl_reg, arg_offset, arg_count, dst_reg
    INSTR_GET_UPVALUE,                                  // GET_UPVALUE dst_reg, upval_index, _, _

    // pattern matching specific instructions

    INSTR_TEST_TAG,                                     // TEST_TAG src_reg, tag_id, fail_label, _
    INSTR_DECONSTRUCT,                                  // DECONSTRUCT dst_reg, src_reg, index, _

    // lazy evaluation instructions

    INSTR_DELAY,                                        // DELAY dst_reg, label, capture_count, capture_start
    INSTR_FORCE,                                        // FORCE dst_reg, src_reg, _, _

    // type conversion instruction

    INSTR_CAST,                                         // CAST dst_reg, src_reg, target_type_id, source_type_id

    // FFI

    INSTR_CALL_FFI,                                     // CALL_FFI dst_reg, ffi_index, args_start_reg, _

    // buffers and arrays

    INSTR_BUFFER_ALLOC,                                 // BUFFER_ALLOC dst_reg, size_reg, _, _
    INSTR_BUFFER_GET,                                   // BUFFER_GET dst_reg, buf_reg, index_reg, _
    INSTR_BUFFER_SET,                                   // BUFFER_SET buf_reg, index_reg, val_reg, _
    INSTR_BUFFER_REALLOC,                               // BUFFER_REALLOC buf_reg, new_size_reg, _, _

    INSTR_BUFFER_LENGTH,                                // BUFFER_LENGTH dst_reg, buf_reg, _, _

    INSTR_BUFFER_TO_STRING,                             // BUFFER_TO_STRING dst_reg, buf_reg, _, _
    INSTR_STRING_TO_BUFFER,                             // STRING_TO_BUFFER dst_reg, str_reg, _, _

    // debugging instruction

    INSTR_PPSHOW,                                       // PPSHOW dst_reg, src_reg, _, _
    INSTR_PRINT,                                        // PRINT str_reg, _, _, _
} opcode_t;

/// The number of opcdes.
#define OPCODE_NUMBER ((int)INSTR_PRINT)  // (`INSTR_PRINT` must be the last opcode)

/// String representation of the opcodes for debugging purpose.
static const char* opcode_names[] = {
    [INSTR_HALT] =          "HALT",
    [INSTR_JUMP] =          "JUMP",
    [INSTR_JUMP_FALSE] =    "JUMP_FALSE",
    [INSTR_JUMP_TRUE] =     "JUMP_TRUE",
    [INSTR_RESERVE] =       "RESERVE",
    [INSTR_CALL] =          "CALL",
    [INSTR_TAILCALL] =      "TAILCALL",
    [INSTR_RET] =           "RET",
    [INSTR_APPLY] =         "APPLY",
    [INSTR_MOV] =           "MOV",
    [INSTR_LOAD_INT] =      "LOAD_INT",
    [INSTR_LOAD_ATOM] =     "LOAD_ATOM",
    [INSTR_LOAD_FLOAT] =    "LOAD_FLOAT",
    [INSTR_LOAD_CHAR] =     "LOAD_CHAR",
    [INSTR_LOAD_STRING] =   "LOAD_STRING",
    [INSTR_LOAD_BOOL] =     "LOAD_BOOL",
    [INSTR_ADD] =           "ADD",
    [INSTR_SUB] =           "SUB",
    [INSTR_MUL] =           "MUL",
    [INSTR_DIV] =           "DIV",
    [INSTR_MOD] =           "MOD",
    [INSTR_NEG] =           "NEG",
    [INSTR_EQUAL] =         "EQUAL",
    [INSTR_NOT_EQUAL] =     "NOT_EQUAL",
    [INSTR_NOT] =           "NOT",
    [INSTR_LEQ] =           "LEQ",
    [INSTR_LE] =            "LE",
    [INSTR_GE] =            "GE",
    [INSTR_GEQ] =           "GEQ",
    [INSTR_STR_CAT] =       "STR_CAT",
    [INSTR_MK_RECORD] =     "MK_RECORD",
    [INSTR_EXTEND_RECORD] = "EXTEND_RECORD",
    [INSTR_GET_FIELD] =     "GET_FIELD",
    [INSTR_ALLOC] =         "ALLOC",
    [INSTR_SUBST] =         "SUSBT",
    [INSTR_CLOSURE] =       "CLOSURE",
    [INSTR_CALL_CLOSURE] =  "CALL_CLOSURE",
    [INSTR_GET_UPVALUE] =   "GET_UPVALUE",
    [INSTR_TEST_TAG] =      "TEST_TAG",
    [INSTR_DECONSTRUCT] =   "DECONSTRUCT",
    [INSTR_DELAY] =         "DELAY",
    [INSTR_FORCE] =         "FORCE",
    [INSTR_CAST] =          "CAST",
    [INSTR_CALL_FFI] =      "CALL_FFI",
    [INSTR_BUFFER_ALLOC] =  "BUFFER_ALLOC",
    [INSTR_BUFFER_GET] =    "BUFFER_GET",
    [INSTR_BUFFER_SET] =    "BUFFER_SET",
    [INSTR_BUFFER_REALLOC] ="BUFFER_REALLOC",
    [INSTR_BUFFER_LENGTH] = "BUFFER_LENGTH",
    [INSTR_BUFFER_TO_STRING] ="BUFFER_TO_STRING",
    [INSTR_STRING_TO_BUFFER] ="STRING_TO_BUFFER",
    [INSTR_PPSHOW] =        "PPSHOW",
    [INSTR_PRINT] =         "PRINT",
};

/// Four-operands instruction.
typedef struct
{
    opcode_t op;        // instruction opcode
    int a, b, c, d;     // arguments (some may be unset / unused (usualy set to 0 if so))
                        // and some informations might also be encoded in the unused arguments (as for floats)
} instr_t;



// ------------------------------------------ //
// ------------ VM ENVIRONNEMENT ------------ //
// ------------------------------------------ //



/// Table of atoms/symbols.
typedef struct atom
{
    char *name;             // name of the atom/symbol
    sym_id_t id;            // associated ID of the atom/symbol
    struct atom *next;      // the next atom/symbol (linked-list)
} atom_t;

/// Dispatch table of functions by symbol/arity
typedef struct dispatch_entry
{
    int arity;                      // arity of the entry
    int label;                      // associated label of the entry
    struct dispatch_entry *next;    // the next entry (linked-list)
} dispatch_entry_t;

typedef struct
{
    instr_t *program;                           // array of bytecode instructions
    size_t program_size;                        // actual size of the program
    size_t program_capacity;                    // allocated size for the program

    int *labels;                                // label table
    size_t labels_capacity;                     // allocated size for the labels

    // Strings are constant and cached.

    char **string_pool;                         // pool for constant strings
    size_t string_pool_count;                   // actual size of the string pool
    size_t string_pool_capacity;                // allocated size for the string pool

    // Symbols are constants and cached.

    atom_t **symbol_pool;                       // pool for constant symbols
    size_t symbol_pool_count;                   // actual size of the symbol pool
    size_t symbol_counter;                      // allocated size for the symbol pool

    dispatch_entry_t **dispatch_table;          // dispatch table of functions by symbol/arity
    size_t dispatch_table_capacity;             // allocated size for the dispatch table

    // Foreign Function Interface.

    rcl_lib_handle *loaded_libs;                // the loaded external dynamic libraries
    size_t loaded_libs_count;                   // actual size of the loaded dynamic libraries
    size_t loaded_libs_capacity;                // allocated size for the loaded dynamic libraries

    struct ffi_info **ffi_table;                // table of external foreign functions 
    size_t ffi_count;                           // actual size of the table of external functions
    size_t ffi_capacity;                        // allocated size of the table of external functions

} vm_env_t;

/// Initializes a new VM environment and returns a pointer to it.
vm_env_t *create_env()
{
    vm_env_t *env = (vm_env_t *)calloc(1, sizeof(vm_env_t));

    env->program_capacity = INITIAL_CAPACITY;
    env->program = malloc(env->program_capacity * sizeof(instr_t));
    env->program_size = 0;

    env->labels_capacity = INITIAL_CAPACITY;
    env->labels = malloc(env->labels_capacity * sizeof(int));
    memset(env->labels, -1, env->labels_capacity * sizeof(int));

    env->string_pool_capacity = 256;
    env->string_pool = calloc(env->string_pool_capacity, sizeof(char *));
    env->string_pool_count = 0;

    env->symbol_pool_count = INITIAL_CAPACITY;
    env->symbol_pool = calloc(env->symbol_pool_count, sizeof(atom_t *));
    env->symbol_counter = 0;

    env->dispatch_table_capacity = INITIAL_CAPACITY;
    env->dispatch_table = calloc(env->dispatch_table_capacity, sizeof(dispatch_entry_t *));

    env->loaded_libs_capacity = 8;
    env->loaded_libs = calloc(env->loaded_libs_capacity, sizeof(rcl_lib_handle));
    env->loaded_libs_count = 0;

    env->ffi_capacity = INITIAL_CAPACITY;
    env->ffi_table = calloc(env->ffi_capacity, sizeof(struct ffi_info *));
    env->ffi_count = 0;

    return env;
}

/// Releases the given environment.
void destroy_env(vm_env_t *env_ptr)
{
    if (env_ptr == NULL)
        return;

    // Libération du code
    free(env_ptr->program);
    free(env_ptr->labels);

    // Libération des chaînes
    for (size_t i = 0; i < env_ptr->string_pool_count; i++)
        free(env_ptr->string_pool[i]);
    free(env_ptr->string_pool);

    // Libération des symboles (liste chaînée)
    for (size_t i = 0; i < env_ptr->symbol_pool_count; i++) {
        atom_t *curr = env_ptr->symbol_pool[i];
        while (curr) {
            atom_t *next = curr->next;
            free(curr->name);
            free(curr);
            curr = next;
        }
    }
    free(env_ptr->symbol_pool);

    // Libération de la dispatch table (liste chaînée)
    for (size_t i = 0; i < env_ptr->dispatch_table_capacity; i++) {
        dispatch_entry_t *curr = env_ptr->dispatch_table[i];
        while (curr) {
            dispatch_entry_t *next = curr->next;
            free(curr);
            curr = next;
        }
    }
    free(env_ptr->dispatch_table);

    // Libération du FFI
    for (size_t i = 0; i < env_ptr->loaded_libs_count; i++) {
        if (env_ptr->loaded_libs[i])
            RCL_CLOSE_LIB(env_ptr->loaded_libs[i]);
    }
    free(env_ptr->loaded_libs);

    for (size_t i = 0; i < env_ptr->ffi_count; i++) {
        if (env_ptr->ffi_table[i])
            free_ffi_info(env_ptr->ffi_table[i]);
    }
    free(env_ptr->ffi_table);

    free(env_ptr);
}

/// Initializes the garbage collector.
void gc_init()
{
    // well, nothing to do! The ARC is autonomous, for now.
    // but in the future, this function might be useful.
}



// ------------------------------------------- //
// ------------ SYMBOLS & STRINGS ------------ //
// ------------------------------------------- //



/// FNV-1a hashing for strings.
static uint32_t hash_string(const char *str)
{
    uint32_t hash = 2166136261u;
    while (*str)
    {
        hash ^= (unsigned char)(*str++);
        hash *= 16777619u;
    }
    return hash;
}

/// Adds a symbol in the symbol table and returns the associated id (uint32).
sym_id_t intern_symbol(vm_env_t *env_ptr, const char *name)
{
    const uint32_t h = hash_string(name);
    const uint32_t index = h & (env_ptr->symbol_pool_count - 1);

    for (atom_t *a = env_ptr->symbol_pool[index]; a != NULL; a = a->next)
    {
        if (strcmp(a->name, name) == 0)
            return a->id;
    }

    atom_t *new_atom = malloc(sizeof(atom_t));

    new_atom->name = malloc(strlen(name) + 1);
    strcpy(new_atom->name, name);

    new_atom->id = env_ptr->symbol_counter++;
    new_atom->next = env_ptr->symbol_pool[index];

    env_ptr->symbol_pool[index] = new_atom;
    return new_atom->id;
}

/// Returns the string's name associated to the given id (uint32) from the environment.
static const char *symbol_name(vm_env_t *env_ptr, const sym_id_t symbol_id)
{
    for (size_t i = 0; i < env_ptr->symbol_pool_count; i++)
    {
        for (atom_t *a = env_ptr->symbol_pool[i]; a != NULL; a = a->next)
        {
            if (a->id == symbol_id)
                return a->name;
        }
    }

    return "<?>";  // this may not happen.
}

/// Adds a string to the string pool. This has to be called by the VM's caller before running the VM.
int intern_string(vm_env_t *env_ptr, const char *s)
{
    if (env_ptr->string_pool_count >= env_ptr->string_pool_capacity)
    {
        const size_t new_capacity = env_ptr->string_pool_capacity * 2;
        char **new_pool = malloc(new_capacity * sizeof(char *));
        memcpy(new_pool, env_ptr->string_pool, env_ptr->string_pool_count * sizeof(char *));
        free(env_ptr->string_pool);
        env_ptr->string_pool = new_pool;
        env_ptr->string_pool_capacity = new_capacity;
    }

    char *copy = malloc(strlen(s) + 1);
    strcpy(copy, s);

    env_ptr->string_pool[env_ptr->string_pool_count] = copy;
    return env_ptr->string_pool_count++;
}



// ------------------------------------------------------------------ //
// ------------ (FOREIGN) FUNCTION (INTERFACE) INTERNING ------------ //
// ------------------------------------------------------------------ //



/// Emits a function's label for the given symbol id.
void intern_function(vm_env_t *env_ptr, const sym_id_t symbol_id, const int arity, const int label)
{
    if (symbol_id >= (sym_id_t)env_ptr->dispatch_table_capacity)
    {
        const size_t old_cap = env_ptr->dispatch_table_capacity;
        const size_t new_cap = (symbol_id + 1) * 2;
        dispatch_entry_t **new_tbl = calloc(new_cap, sizeof(dispatch_entry_t *));

        if (env_ptr->dispatch_table != NULL) {
            memcpy(new_tbl, env_ptr->dispatch_table, old_cap * sizeof(dispatch_entry_t *));
            free(env_ptr->dispatch_table);
        }

        env_ptr->dispatch_table = new_tbl;
        env_ptr->dispatch_table_capacity = new_cap;
    }

    dispatch_entry_t *entry = malloc(sizeof(dispatch_entry_t));
    entry->arity = arity;
    entry->label = label;

    entry->next = env_ptr->dispatch_table[symbol_id];
    env_ptr->dispatch_table[symbol_id] = entry;
}

/// Loads a dynamic library. Returns `true` if the loading was successful.
bool rcl_env_load_library(vm_env_t *env_ptr, const char *path)
{
    rcl_lib_handle lib = RCL_LOAD_LIB(path);

    if (lib == NULL)
    {
        fprintf(stderr, "Fatal error: cannot load the dynamic library '%s'.\n", path);
        return false;
    }

    if (env_ptr->loaded_libs_count >= env_ptr->loaded_libs_capacity)
    {
        const size_t new_cap = env_ptr->loaded_libs_capacity * 2;
        rcl_lib_handle *new_libs = malloc(new_cap * sizeof(rcl_lib_handle));
        memcpy(new_libs, env_ptr->loaded_libs, env_ptr->loaded_libs_count * sizeof(rcl_lib_handle));
        free(env_ptr->loaded_libs);
        env_ptr->loaded_libs = new_libs;
        env_ptr->loaded_libs_capacity = new_cap;
    }

    env_ptr->loaded_libs[env_ptr->loaded_libs_count++] = lib;

    return true;
}

/// Registers a new foreign function.
int rcl_env_register_ffi(
    vm_env_t *env_ptr,
    const char *qual_name,
    const char *func_name,
    size_t arity,
    enum rcl_type *arg_types,
    enum rcl_type ret_type)
{
    void (*func_ptr)(void) = NULL;

    for (size_t i = 0; i < env_ptr->loaded_libs_count; i++)
    {
        func_ptr = (void(*)(void))RCL_FIND_SYM(env_ptr->loaded_libs[i], func_name);

        if (func_ptr != NULL)
            break;
    }

    #if !defined(_WIN32) && !defined(_WIN64)
    if (func_ptr == NULL)
        func_ptr = (void(*)(void))dlsym(RTLD_DEFAULT, func_name);
    #endif

    if (func_ptr == NULL)
    {
        fprintf(stderr, "Fatal error: cannot find the function '%s' in any dynamic library.\n", func_name);
        exit(1);
    }

    struct ffi_info *info = new_ffi_info(func_ptr, arity, arg_types, ret_type);
    if (info == NULL)
        return -1;

    info->sym_id = intern_symbol(env_ptr, qual_name);

    if (env_ptr->ffi_count >= env_ptr->ffi_capacity)
    {
        const size_t new_cap = (env_ptr->ffi_capacity == 0) ? INITIAL_CAPACITY: env_ptr->ffi_capacity * 2;
        struct ffi_info **new_table = malloc(new_cap * sizeof(struct ffi_info*));

        if (env_ptr->ffi_table)
        {
            memcpy(new_table, env_ptr->ffi_table, env_ptr->ffi_count * sizeof(struct ffi_info*));
            free(env_ptr->ffi_table);
        }

        env_ptr->ffi_table = new_table;
        env_ptr->ffi_capacity = new_cap;
    }

    const int ffi_index = (int)env_ptr->ffi_count;
    env_ptr->ffi_table[env_ptr->ffi_count++] = info;
    
    return ffi_index;
}



// ------------------------------------------------------------ //
// ------------ BYTECODE EMIT & CONSTANT INTERNING ------------ //
// ------------------------------------------------------------ //



/// Emits a bytecode instruction as a four address-code instruction.
void emit(vm_env_t *env_ptr, opcode_t op, const int a, const int b, const int c, const int d)
{
    if (env_ptr->program_size >= env_ptr->program_capacity)
    {
        const size_t new_capacity = env_ptr->program_capacity * 2;
        instr_t *new_program = malloc(new_capacity * sizeof(instr_t));
        memcpy(new_program, env_ptr->program, env_ptr->program_size * sizeof(instr_t));
        free(env_ptr->program);
        env_ptr->program = new_program;
        env_ptr->program_capacity = new_capacity;
    }

    env_ptr->program[env_ptr->program_size++] = (instr_t){ op, a, b, c, d };
}

/// Emits a bytecode label.
void set_label(vm_env_t *env_ptr, const int label)
{
    if (label >= (int)env_ptr->labels_capacity)
    {
        const size_t new_cap = (label < 1024) ? 2048 : (label + 1) * 2; // Since the labels are dispersed, this avoids allocating too much into the void.
        int *new_labels = (int *)malloc(new_cap * sizeof(int));
        memset(new_labels, -1, new_cap * sizeof(int));
        if (env_ptr->labels != NULL && env_ptr->labels_capacity > 0)
            memcpy(new_labels, env_ptr->labels, env_ptr->labels_capacity * sizeof(int));

        if (env_ptr->labels != NULL)
            free(env_ptr->labels);

        env_ptr->labels = new_labels;
        env_ptr->labels_capacity = new_cap;
    }

    env_ptr->labels[label] = (int)env_ptr->program_size;
}

/// Emits a "load float" instruction.
void emit_load_float(vm_env_t *env_ptr, const int dst_reg, const double value)
{
    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));

    // We store the double as two uint32.

    uint32_t hi = (uint32_t)(bits >> 32);
    uint32_t lo = (uint32_t) bits;

    emit(env_ptr, INSTR_LOAD_FLOAT, dst_reg, (int32_t)hi, (int32_t)lo, 0);
}

/// Emits a "load string" instruction and intern the given string.
void emit_load_string(vm_env_t *env_ptr, const int dst_reg, const char *s)
{
    const int index = intern_string(env_ptr, s);
    emit(env_ptr, INSTR_LOAD_STRING, dst_reg, index, 0, 0);
}



// ------------------------------------------ //
// ------------ VIRTUAL MACHINE  ------------ //
// ------------------------------------------ //



#define INITIAL_STACK_CAPACITY  8192
#define INITIAL_FRAMES_CAPACITY 2048
#define STACK_FRAME_PADDING     16

/*
The VM is a stack-based virtual machine with register windows.

Temporary virtual registers reside in a single linear stack (`stack[]`), 
but the architecture mainly uses two distinct memory areas at runtime:

 - `stack[]`: window of active virtual registers (offsets relative to bp)
 - `frames[]`: stack of call frames containing metadata (ret_pc, prev_bp, etc.)

The execution stack (`stack[]`) and the frame stack (`frames[]`) follow 
a LIFO discipline for managing function calls.

Virtual registers are aliases over the stack:
they are implemented as offsets relative to a base pointer (bp).
The stack is not directly accessible to the user or compiler.
The stack is the memory model, while the registers are the access model.

Conceptually:
  regs = &stack[bp]
  regs[i] = stack[bp + i]

Registers are not fixed locations and their count is not predefined.
The size of the current register window is determined dynamically
by INSTR_RESERVE, which advances sp.

Each CALL pushes a frame recording the previous bp.
On RET, bp is restored from the frame.
sp always marks the upper bound of the current register window.
*/

// Calling frame.
typedef struct
{
    int ret_pc;                 // the return program counter (pc of return)
    int prev_bp;                // previous base pointer
    int dst_reg;                // destination register for the result

    term_t closure_env;         // closure environment (can be set to 0)
    term_t thunk;               // thunk for lazy evaluation (can be set to 0)
} frame_t;

// Execution state (VM).
typedef struct
{
    term_t *stack;              // evaluation stack
    size_t stack_capacity;      // allocated size for the stack

    frame_t *frames;            // call stack frames
    size_t frames_capacity;     // allocated size for the call stack frames

    int sp, bp, fp, pc;         // Stack Pointer, Base Pointer, Frame Pointer, Program Counter
    vm_env_t *env_ptr;          // Environment pointer

    arena_t arena;              // arena allocator
    dec_queue_t dec_queue;      // queue of ARC decrementation
} vm_t;

/// Creates a new VM and returns a pointer to it.
vm_t *create_vm(vm_env_t *env_ptr)
{
    vm_t *vm = calloc(1, sizeof(vm_t));

    vm->stack_capacity = INITIAL_STACK_CAPACITY;
    vm->stack = calloc(vm->stack_capacity, sizeof(term_t));

    vm->frames_capacity = INITIAL_FRAMES_CAPACITY;
    vm->frames = calloc(vm->frames_capacity, sizeof(frame_t));

    vm->sp = 0;
    vm->bp = 0;
    vm->fp = 0;
    vm->pc = 0;
    vm->env_ptr = env_ptr;

    init_arena(&vm->arena);
    init_queue(&vm->dec_queue);

    return vm;
}

/// Destroys the VM.
void destroy_vm(vm_t *vm_ptr)
{
    if (vm_ptr == NULL)
        return;

    for (int i = 0; i < vm_ptr->stack_capacity; i++)
    {
        if (vm_ptr->stack[i] && IS_PTR(vm_ptr->stack[i]))
            rc_decrement(&vm_ptr->dec_queue, vm_ptr->stack[i]);
    }

    drain_queue(&vm_ptr->dec_queue, &vm_ptr->arena);

    free_queue(&vm_ptr->dec_queue);
    arena_free(&vm_ptr->arena);

    free(vm_ptr->stack);
    free(vm_ptr->frames);
    free(vm_ptr);
}



// ----------------------------------------------- //
// ------------ INDIRECTIONS & THUNKS ------------ //
// ----------------------------------------------- //



/// Follows a chain of indirection pointers until it reaches a concrete value or a term that is no
/// longer an indirection, and returns that final term. The chain is usually very short, if any!
static inline term_t resolve_indirection(term_t term)
{
    while (IS_PTR(term) && AS_HEADER(term)->id == SYM_INDIRECT)
        term = AS_HEADER(term)->children[0];

    return term;
}

/// Transforms a thunk (or any other object) into an indirection to a target value.
/// This allows for memoization to take place.
static void overwrite_with_indirection(vm_t *vm_ptr, const term_t thunk_ptr, const term_t value)
{
    term_header_t *h = AS_HEADER(thunk_ptr);

    if (value && IS_PTR(value))
        rc_increment(value);

    // All previously captured variables by the thunk are released.
    for (uint32_t i = 0; i < h->arity; i++)
    {
        if (h->children[i] && IS_PTR(h->children[i]))
            rc_decrement(&vm_ptr->dec_queue, h->children[i]);
    }

    h->id = SYM_INDIRECT;
    h->arity = 1;
    h->children[0] = value;
}

/// Locks a thunk by marking it as evaluated ("black hole") and detects lazy evaluation loops.
/// This should be fairly rare in practice (for Liyh).
static void lock_and_check_thunk(term_t term)
{
    term = resolve_indirection(term);
    term_header_t *h = AS_HEADER(term);

    if (h->id == SYM_BLACK_HOLE)
    {
        // If the thunk is already marked as `SYM_BLACK_HOLE`, then it means that a cyclic loop
        // is present: we fall into the black hole... and we cannot exit. This is a fatal error.

        fprintf(stderr, "Fatal error: cycle detected during lazy evaluation (black hole).\n");
        exit(1);
    }

    if (h->id == SYM_THUNK)
        h->id = SYM_BLACK_HOLE;
}



// ------------------------------------- //
// ------------ ARC HELPERS ------------ //
// ------------------------------------- //



/// Allocates a n-arity term via ARC.
static term_t arc_alloc_term(vm_t *vm_ptr, sym_id_t id, uint32_t arity)
{
    term_header_t *h = (term_header_t *)arena_alloc_term(&vm_ptr->arena, arity);

    h->rc = 0;
    h->id = id;
    h->arity = arity;

    if (arity > 0)
        memset(h->children, 0, arity * sizeof(term_t));

    return (term_t)h;
}

/// Allocates a 0-arity term via ARC.
static term_t arc_alloc_leaf(vm_t *vm_ptr, sym_id_t id, size_t playload_bytes)
{
    size_t words = (playload_bytes + sizeof(term_t) - 1) / sizeof(term_t);
    term_header_t *h = (term_header_t *)arena_alloc_term(&vm_ptr->arena, words);
    
    h->rc = 0;
    h->id = id;
    h->arity = 0;

    return (term_t)h;
}

static inline void arc_clean_stack_window(vm_t *vm_ptr, int old_sp, int new_sp)
{
    if (old_sp >= new_sp)
        return; // the stack has grown, so nothing is to be released

    for (int i = old_sp; i < new_sp; i++)
    {
        term_t obj = vm_ptr->stack[i];
        if (obj && IS_PTR(obj))
            rc_decrement(&vm_ptr->dec_queue, obj);
        
        vm_ptr->stack[i] = 0;
    }

    drain_queue(&vm_ptr->dec_queue, &vm_ptr->arena);
}

static inline void vm_arc_assign(vm_t *vm_ptr, int reg_index, term_t new_val)
{
    rc_assign(&vm_ptr->dec_queue, &vm_ptr->stack[vm_ptr->bp + reg_index], new_val);
}

/// Assigns a new value to a register whilst properly managing reference counting.
static inline void arc_assign_reg(vm_t *vm_ptr, term_t *regs, const int reg_index, term_t new_val)
{
    //    const term_t old = regs[reg_index];
    //
    //    if (unlikely(old == new_val))
    //        return;
    //    
    //    regs[reg_index] = new_val;
    //
    //    if (unlikely(IS_PTR(old) || IS_PTR(new_val)))
    //    {
    //        rc_increment(new_val);
    //        rc_decrement(&vm_ptr->dec_queue, old);
    //    }

    rc_assign(&vm_ptr->dec_queue, &regs[reg_index], new_val);
}



// ---------------------------------------------------------- //
// ------------ BOXED LITERALS & RECORDS HELPERS ------------ //
// ---------------------------------------------------------- //



/// Creates a boxed value for a float (64 bits).
static term_t make_float(vm_t *vm_ptr, const double value)
{
    term_t term = arc_alloc_leaf(vm_ptr, SYM_FLOAT_NATIVE, sizeof(double));
    term_header_t *h = AS_HEADER(term);

    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    memcpy(&h->children[0], &bits, sizeof(bits));

    return term;
}

/// Gets a float (64 bits) from the given term.
static double get_float(term_t term)
{
    term = resolve_indirection(term);

    if (IS_INT(term))
        return (double)GET_INT(term);

    if (IS_PTR(term))
    {
        const term_header_t *h = AS_HEADER(term);
        if (h->id == SYM_FLOAT_NATIVE)
        {
            double value;
            memcpy(&value, &h->children[0], sizeof value);
            return value;
        }
    }

    fprintf(stderr, "Runtime Error: Expected number (int/float), got type ID %u (or raw %lu)\n",
            IS_PTR(term) ? AS_HEADER(term)->id : 0, (unsigned long)term);
    exit(1);
}

/// Create a new string as a term (copy the given string).
static term_t make_string_with_len(vm_t *vm_ptr, const char *s, const size_t len)
{
    // Allocate 2 words: pointer (children[0]) + size (children[1])
    const term_t term = arc_alloc_leaf(vm_ptr, SYM_STRING_NATIVE, 2 * sizeof(term_t));
    term_header_t *h = AS_HEADER(term);

    char *buff = malloc(len + 1);
    memcpy(buff, s, len);
    buff[len] = '\0';

    h->children[0] = (term_t)buff;
    h->children[1] = MAKE_INT(len);
    return term;
}

/// Create a new string as a term (copy the given string).
static term_t make_string(vm_t *vm_ptr, const char *s)
{
    return make_string_with_len(vm_ptr, s, strlen(s));
}

/// If the term is a string, then gets the string length, else returns 0.
static size_t get_string_len(term_t term)
{
    term = resolve_indirection(term);

    if (IS_PTR(term) && AS_HEADER(term)->id == SYM_STRING_NATIVE)
        return (size_t)GET_INT(AS_HEADER(term)->children[1]);

    return 0;
}

/// Gets a string from the given term.
static const char *get_string_ptr(term_t term)
{
    term = resolve_indirection(term);
    return (const char *)AS_HEADER(term)->children[0];
}

/// A key/value struct for record fields.
typedef struct
{
    sym_id_t key;
    term_t value;
} record_field_t;

static int compare_fields(const void *a, const void *b)
{
    const record_field_t *fa = (const record_field_t *)a;
    const record_field_t *fb = (const record_field_t *)b;

    return (int)fa->key - (int)fb->key;
}

static term_t make_record_from_pairs(vm_t *vm_ptr, record_field_t *pairs, const int count)
{
    qsort(pairs, count, sizeof(record_field_t), compare_fields);
    int unique_count = 0;

    if (count > 0)
    {
        int write_idx = 0;
        for (int read_idx = 0; read_idx < count; read_idx++)
        {
            if (read_idx < count - 1 && pairs[read_idx].key == pairs[read_idx + 1].key)
                continue;

            pairs[write_idx++] = pairs[read_idx];
        }
        unique_count = write_idx;
    }

    const uint32_t arity = 2 * unique_count;
    term_t term = arc_alloc_term(vm_ptr, SYM_RECORD_NATIVE, arity);
    term_header_t *header = AS_HEADER(term);

    for (int i = 0; i < unique_count; i++)
    {
        header->children[i * 2] = MAKE_INT(pairs[i].key);

        term_t val = pairs[i].value;
        if (val && IS_PTR(val))
            rc_increment(val);
        
        header->children[i * 2 + 1] = val;
    }

    return (term_t)header;
}

/// Creates an 'opaque pointer' from a given pointer, converting it into a term with a term id `SYM_PTR_NATIVE`.
static term_t make_opaque_ptr(vm_t *vm_ptr, void *ptr)
{
    term_t term = arc_alloc_leaf(vm_ptr, SYM_PTR_NATIVE, sizeof(void *));
    memcpy(&AS_HEADER(term)->children[0], &ptr, sizeof(void *));
    return term;
}

/// Given a term assuming its term id is `SYM_PTR_NATIVE`, returns a copy of its adress.
static void *get_opaque_ptr(term_t term)
{
    term = resolve_indirection(term);
    if (IS_PTR(term) && AS_HEADER(term)->id == SYM_PTR_NATIVE)
    {
        void *opaque_ptr;
        memcpy(&opaque_ptr, &AS_HEADER(term)->children[0], sizeof(void *));
        return opaque_ptr;
    }

    fprintf(stderr, "Fatal error: expected native pointer.\n");
    exit(1);
}



// -------------------------------------------------------- //
// ------------ TERM COMPARISON & SUBSTITUTION ------------ //
// -------------------------------------------------------- //



typedef struct
{
    term_t a;
    term_t b;
} eq_pair_t;

/// Performs a structural recursive equality test. No overflow will occurs.
static bool term_equals(term_t root_a, term_t root_b)
{
    root_a = resolve_indirection(root_a);
    root_b = resolve_indirection(root_b);

    if (root_a == root_b)
        return true;

    if ((root_a & TAG_MASK) != (root_b & TAG_MASK))
        return false;

    if (IS_INT(root_a) || IS_CHAR(root_a))
        return false;

    // We use an internal stack to avoid recursion and to allows for deep equality
    // test without overflow (this is important for this kind of language).

    size_t capacity = INITIAL_CAPACITY;
    size_t sp = 0;

    eq_pair_t *stack = malloc(capacity * sizeof(eq_pair_t));
    stack[sp++] = (eq_pair_t){ root_a, root_b };

    while (sp > 0)
    {
        eq_pair_t p = stack[--sp];
        p.a = resolve_indirection(p.a);
        p.b = resolve_indirection(p.b);

        if (p.a == p.b)
            continue;

        if ((p.a & TAG_MASK) != (p.b & TAG_MASK) || !IS_PTR(p.a))
        {
            free(stack);
            return false;
        }

        const term_header_t *ha = AS_HEADER(p.a);
        const term_header_t *hb = AS_HEADER(p.b);

        if (ha->id != hb->id)
        {
            free(stack);
            return false;
        }

        if (ha->id == SYM_FLOAT_NATIVE)
        {
            if (get_float(p.a) != get_float(p.b))
            {
                free(stack);
                return false;
            }
            continue;
        }

        if (ha->id == SYM_STRING_NATIVE)
        {
            if (GET_INT(ha->children[1]) != GET_INT(hb->children[1]))
            {
                free(stack);
                return false;
            }

            if (strcmp((const char *)ha->children[0], (const char *)hb->children[0]) != 0)
            {
                free(stack);
                return false;
            }
            continue;
        }

        if (ha->arity != hb->arity)
        {
            free(stack);
            return false;
        }

        if (sp + ha->arity >= capacity)
        {
            capacity *= 2;
            stack = realloc(stack, capacity * sizeof(eq_pair_t));
        }

        for (uint32_t i = 0; i < ha->arity; i++)
            stack[sp++] = (eq_pair_t){ ha->children[i], hb->children[i] };
    }

    free(stack);
    return true;
}

// Work frame structure for the iterative substitution algorithm
typedef struct {
    term_t term;            // the original term being processed
    term_header_t *header;  // pre-resolved header
    uint32_t next_child;    // index of the next child to visit
} subst_frame_t;

/// Performs a structural and recursive substitution: replaces occurrences of `toRepId` with
/// `repl` in `root`. Returns a new term (or the original if no changes were made).
/// No overflow will occurs.
static term_t perform_substitution(vm_t *vm_ptr, term_t root, sym_id_t toRepId, term_t repl)
{
    root = resolve_indirection(root);

    if (!IS_PTR(root)) return root;

    size_t work_capacity = INITIAL_CAPACITY;
    size_t work_sp = 0;

    size_t result_capacity = INITIAL_CAPACITY;
    size_t result_sp = 0;

    subst_frame_t *work_stack = malloc(work_capacity * sizeof(subst_frame_t));
    term_t *result_stack = malloc(result_capacity * sizeof(term_t));

    // Push the root frame onto the work stack
    work_stack[work_sp++] = (subst_frame_t){ root, AS_HEADER(root), 0 };

    while (work_sp > 0)
    {
        // Get pointer to the current frame (top of work stack)
        // Note: We keep this as a pointer because the frame is modified in-place
        subst_frame_t *frame = &work_stack[work_sp - 1];

        // While there are still children to visit, we keep descending into the tree
        if (frame->next_child < frame->header->arity)
        {
            // Get the next child to process
            term_t child = frame->header->children[frame->next_child];
            frame->next_child++;

            child = resolve_indirection(child);

            if (!IS_PTR(child)) {
                if (result_sp == result_capacity)
                {
                    result_capacity *= 2;
                    result_stack = realloc(result_stack, result_capacity * sizeof(term_t));
                }
                result_stack[result_sp++] = child;
            } 
            else
            {
                if (work_sp == work_capacity)
                {
                    work_capacity *= 2;
                    work_stack = realloc(work_stack, work_capacity * sizeof(subst_frame_t));
                    frame = &work_stack[work_sp - 1];
                }
                work_stack[work_sp++] = (subst_frame_t){ child, AS_HEADER(child), 0 };
            }
            continue;
        }

        // At this stage, all children have been processed and their results
        // are on the result stack. Now we reconstruct the parent term.

        work_sp--; // Pop the current frame from work stack.
        const uint32_t arity = frame->header->arity;

        // The results of all children are at the top of the result stack.
        term_t *child_results = &result_stack[result_sp - arity];

        bool children_changed = false;
        for (uint32_t i = 0; i < arity; i++)
        {
            if (child_results[i] != frame->header->children[i])
            {
                children_changed = true;
                break;
            }
        }

        bool self_changed = (frame->header->id == toRepId);
        term_t final_res = (term_t)NULL;

        if (!children_changed && !self_changed)
            final_res = frame->term;

        else if (self_changed && arity == 0)
            final_res = repl;

        else if (self_changed && IS_PTR(repl) && AS_HEADER(repl)->id == SYM_CLOSURE)
        {
            // Replacing a closure: creating a SUSPENDED_CALL
            uint32_t new_arity = arity + 1;
            term_t susp = arc_alloc_term(vm_ptr, SYM_SUSPENDED_CALL, new_arity);
            term_header_t *h = AS_HEADER(susp);

            // The `repl` closure becomes the first child (use rc_increment)
            if (repl && IS_PTR(repl)) rc_increment(repl);
            h->children[0] = repl;

            // rc_increment on the evaluated arguments
            for (uint32_t i = 0; i < arity; i++)
            {
                term_t child = child_results[i];
                if (child && IS_PTR(child)) rc_increment(child);
                h->children[i + 1] = child;
            }
            final_res = susp;
        }
        else
        {
            // General case (change of children or standard replacement)
            sym_id_t new_id = (self_changed && IS_PTR(repl)) ? AS_HEADER(repl)->id : frame->header->id;

            term_t new_term = arc_alloc_term(vm_ptr, new_id, arity);
            term_header_t *h = AS_HEADER(new_term);

            // rc_increment on the evaluated arguments
            for (uint32_t i = 0; i < arity; i++)
            {
                term_t child = child_results[i];
                if (child && IS_PTR(child)) rc_increment(child);
                h->children[i] = child;
            }
            final_res = new_term;
        }

        result_sp -= arity;

        if (result_sp == result_capacity)
        {
            result_capacity *= 2;
            result_stack = realloc(result_stack, result_capacity * sizeof(term_t));
        }
        result_stack[result_sp++] = final_res;
    }

    const term_t final = result_stack[0]; // should be the only item left onto the stack

    free(work_stack);
    free(result_stack);
    
    return final;
}



// ------------------------------------------ //
// ------------ PRETTY PRINTTING ------------ //
// ------------------------------------------ //



// We will not pretty print structures that are too deep; we will stop at an arbitrary limit.
// If the user wishes to pretty print deep structures, it is preferable that they provide their own solution.
#define MAX_PRETTY_PRINT_DEPTH  50

/// Return a pointer to a string associated to a pretty print of the term.
static char *term_to_string(vm_env_t *env_ptr, term_t term, const int depth, size_t *out_len)
{
    term = resolve_indirection(term);

    size_t capacity = 256;
    size_t length = 0;
    char *buffer = malloc(capacity);
    if (!buffer) return NULL;

    #define APPEND(fmt, ...) do { \
        int needed = snprintf(buffer + length, capacity - length, fmt, ##__VA_ARGS__); \
        if (needed >= (int)(capacity - length)) { \
            capacity = length + needed + 256; \
            char *new_buf = realloc(buffer, capacity); \
            if (!new_buf) { free(buffer); return NULL; } \
            buffer = new_buf; \
            snprintf(buffer + length, capacity - length, fmt, ##__VA_ARGS__); \
        } \
        length += needed; \
    } while(0)

    if (IS_INT(term))
        APPEND("%lld", (long long)GET_INT(term));

    else if (IS_CHAR(term))
        APPEND("'%c'", (char)GET_CHAR(term));

    else if (IS_BOOL(term))
        APPEND("%s", GET_BOOL(term) ? "true" : "false");

    else if (IS_PTR(term))
    {
        const term_header_t *header = AS_HEADER(term);

        if (header->id == SYM_STRING_NATIVE)
            //APPEND("\"%s\"", (char *)header->children[0]);
            APPEND("%s", (char *)header->children[0]);

        else if (header->id == SYM_FLOAT_NATIVE)
        {
            const double value = get_float(term);

            if (value == floor(value) && fabs(value) < 1e15)
                APPEND("%.1f", value);
            else
                APPEND("%.*g", DBL_DIG, value);
        }

        else if (header->id == SYM_RECORD_NATIVE)
        {
            APPEND("{ ");
            const int field_count = header->arity / 2;

            for (int i = 0; i < field_count; i++)
            {
                if (i > 0) APPEND(", ");

                const sym_id_t field_id = (sym_id_t)GET_INT(header->children[i * 2]);
                APPEND("%s = ", symbol_name(env_ptr, field_id));

                char *child_str = term_to_string(env_ptr, header->children[i * 2 + 1], depth + 1, NULL);
                if (child_str)
                {
                    APPEND("%s", child_str);
                    free(child_str);
                }
            }
            APPEND(" }");
        }

        else if (header->id == SYM_CLOSURE)
            APPEND("<closure@%lld>", (long long)GET_INT(header->children[0]));

        else if (header->id == SYM_PTR_NATIVE)
            APPEND("<ptr%p>", get_opaque_ptr(term));

        else if (header->id == SYM_BUFFER_NATIVE)
            APPEND("<buff%p>", (void *) AS_HEADER(term)->children[0]);

        else if (header->id == SYM_THUNK)
            APPEND("<thunk@%lld>", (long long)GET_INT(header->children[0]));

        else if (header->id == SYM_BLACK_HOLE)
            APPEND("<cycle>");

        else
        {
            APPEND("%s", symbol_name(env_ptr, header->id));

            if (header->arity > 0) {
                if (depth >= MAX_PRETTY_PRINT_DEPTH)
                    APPEND("[...]");

                else
                {
                    APPEND("[");
                    for (uint32_t i = 0; i < header->arity; i++)
                    {
                        if (i > 0) APPEND(", ");

                        char *child_str = term_to_string(env_ptr, header->children[i], depth + 1, NULL);
                        if (child_str)
                        {
                            APPEND("%s", child_str);
                            free(child_str);
                        }
                    }
                    APPEND("]");
                }
            }
        }
    }

    else
        APPEND("<?>");

    #undef APPEND

    if (out_len) *out_len = length;
    return buffer;
}

/// Displays a term to the terminal, for debugging purposes.
static void io_print_term(vm_env_t *env_ptr, const term_t term)
{
    char *s = term_to_string(env_ptr, term, 0, NULL);
    printf("%s", s);
    free(s);
}



// ------------------------------------------------- //
// ------------ VIRTUAL MACHINE HELPERS ------------ //
// ------------------------------------------------- //



// Sets a recursion limit by limmiting the number of frames.

#define LIMIT               (256)               // arbitrary ~256MB (not small but not too big),
#define DIVISOR             (1024 * 1024)       // allowing very deep recursion
#define MAX_STACK_BYTES     (LIMIT * DIVISOR)
#define MAX_FRAMES_BYTES    (LIMIT * DIVISOR)

/// Grows the stack and check for recursion limit.
static void grow_stack(vm_t *vm_ptr, const int needed)
{
    size_t new_capacity = vm_ptr->stack_capacity * 2;

    // If x2 growth is too low for immediate needs.
    if (new_capacity < vm_ptr->stack_capacity + needed)
        new_capacity = vm_ptr->stack_capacity + needed + 1024;

    const size_t new_size_bytes = new_capacity * sizeof(term_t);

    if (new_size_bytes > MAX_STACK_BYTES)
    {
        fprintf(stderr, "Fatal Error: Stack Overflow.\n");
        fprintf(stderr, "Memory limit reached (%d MB). Likely infinite recursion.\n", LIMIT);

        exit(1);
    }

    term_t *new_stack = realloc(vm_ptr->stack, new_capacity * sizeof(term_t));

    const size_t old_size = vm_ptr->stack_capacity * sizeof(term_t);
    const size_t new_size = new_capacity * sizeof(term_t);

    memset((char *)new_stack + old_size, 0, new_size - old_size);

    vm_ptr->stack = new_stack;
    vm_ptr->stack_capacity = new_capacity;
}

/// Grows the frames and check for recursion limit.
static void grow_frames(vm_t *vm_ptr)
{
    const size_t new_capacity = vm_ptr->frames_capacity * 2;
    const size_t new_size_bytes = new_capacity * sizeof(frame_t);

    if (new_size_bytes > MAX_FRAMES_BYTES)
    {
        fprintf(stderr, "Fatal Error: Stack Overflow.\n");
        fprintf(stderr, "Memory limit reached (%d MB). Likely infinite recursion.\n", LIMIT);

        exit(1);
    }

    frame_t *new_frames = realloc(vm_ptr->frames, new_capacity * sizeof(frame_t));

    const size_t old_size_bytes = vm_ptr->frames_capacity * sizeof(frame_t);
    memset((char*)new_frames + old_size_bytes, 0, new_size_bytes - old_size_bytes);

    vm_ptr->frames = new_frames;
    vm_ptr->frames_capacity = new_capacity;
}

/// Grows the stack and check for recursion limit.
static inline void grow_stack_impl(vm_t *vm, term_t **stack, size_t *cap, int needed)
{
    vm->stack = *stack; // Sync
    grow_stack(vm, needed);
    *stack = vm->stack; // Reload
    *cap = vm->stack_capacity;
}

/// Grows the frames and check for recursion limit.
static inline void grow_frames_impl(vm_t *vm, frame_t **frames, size_t *cap)
{
    vm->frames = *frames; // Sync
    grow_frames(vm);
    *frames = vm->frames; // Reload
    *cap = vm->frames_capacity;
}

/// Helper function to perform a call.
static inline void perform_call(
    vm_t *vm,
    int *pc, int *sp, int *fp, int *bp,
    term_t **stack, size_t *stack_cap,
    frame_t **frames, size_t *frames_cap,
    int target_label, int arg_count, int args_src_offset, int dst_reg, term_t closure_env
)
{
    // Check frame capacity.
    if (unlikely(*fp + 1 >= (int)*frames_cap)) {
        grow_frames_impl(vm, frames, frames_cap);
    }

    // Check stack capacity.
    int needed = arg_count + STACK_FRAME_PADDING;
    if (unlikely(*sp + needed >= (int)*stack_cap)) {
        grow_stack_impl(vm, stack, stack_cap, needed);
    }

    // Save the current frame.
    (*frames)[(*fp)++] = (frame_t){ *pc, *bp, dst_reg, closure_env, 0 };

    // Copy the arguments.
    term_t *src_args = (*stack) + (*bp) + args_src_offset;
    term_t *dst_args = (*stack) + (*sp);

    if (arg_count > 0)
    {
        for (int i = 0; i < arg_count; i++)
        {
            term_t arg = src_args[i];
            dst_args[i] = arg;

            if (arg && IS_PTR(arg))
                rc_increment(arg);
        }
    }

    // Zero-init of padding (it's safier with the GC).
    memset(dst_args + arg_count, 0, STACK_FRAME_PADDING * sizeof(term_t));

    // Update the state registers.
    *bp = *sp;
    *sp = *sp + needed;
    *pc = target_label;
}

/// Helper function to perform a call where arguments are stored in a heap-allocated array.
/// This avoids code duplication in INSTR_FORCE for both symbolic data and suspended calls.
static inline void perform_call_heap_args(
    vm_t *vm,
    int *pc, int *sp, int *fp, int *bp,
    term_t **stack, size_t *stack_cap,
    frame_t **frames, size_t *frames_cap,
    int target_label, int arg_count,
    term_t *args_array, // Array of arguments from the heap (e.g. h->children)
    int dst_reg, term_t closure_env, term_t thunk_ptr
)
{
    if (unlikely(*fp + 1 >= (int)*frames_cap))
        grow_frames_impl(vm, frames, frames_cap);

    const int needed = arg_count + STACK_FRAME_PADDING;
    if (unlikely(*sp + needed >= (int)*stack_cap))
        grow_stack_impl(vm, stack, stack_cap, needed);

    (*frames)[(*fp)++] = (frame_t){ *pc, *bp, dst_reg, closure_env, thunk_ptr };

    term_t *dst_args = (*stack) + (*sp);
    if (arg_count > 0)
    {
        for (int i = 0; i < arg_count; i++)
        {
            term_t arg = args_array[i];
            dst_args[i] = arg;

            if (arg && IS_PTR(arg))
                rc_increment(arg);
        }
    }

    memset(dst_args + arg_count, 0, STACK_FRAME_PADDING * sizeof(term_t));

    *bp = *sp;
    *sp = *sp + needed;
    *pc = target_label;
}

/// Helper to create a { Success, Value } record for cast operations.
static term_t make_cast_result(vm_t *vm_ptr, const bool success, const term_t value)
{
    record_field_t pairs[2];

    pairs[0].key = intern_symbol(vm_ptr->env_ptr, "success"); 
    pairs[0].value = MAKE_INT(success ? 1 : 0);

    pairs[1].key = intern_symbol(vm_ptr->env_ptr, "value");
    pairs[1].value = value;

    return make_record_from_pairs(vm_ptr, pairs, 2);
}

/// We can collect statistics for the VM. This collect the number of times each opcode is called
/// and the average time each opcode took to execute.
typedef struct
{
    opcode_t op;
    int used;
    double *times;
    int times_cap;
    int times_size;
} stats_t;

static int compare_stats_desc(const void *a, const void *b)
{
    const stats_t *stat_a = (const stats_t *)a;
    const stats_t *stat_b = (const stats_t *)b;

    if (stat_a->used > stat_b->used) return -1;
    if (stat_a->used < stat_b->used) return 1;

    return 0;
}

/// Displays the statistics of the VM. We would normally expect an average of ~0.200µs per opcode.
static void display_vm_stats(const stats_t stats[], const char* opcode_names[])
{
    const int NAME_WIDTH = 20;
    const int COUNT_WIDTH = 10;
    const int TIME_WIDTH = 15;

    stats_t sorted[OPCODE_NUMBER];

    for (int i = 0; i < OPCODE_NUMBER; i++)
        sorted[i] = stats[i];

    qsort(sorted, OPCODE_NUMBER, sizeof(stats_t), compare_stats_desc);

    const int total_width = NAME_WIDTH + COUNT_WIDTH + TIME_WIDTH + 2;

    printf("\n%*s\n", total_width, "Virtual Machine Statistics");
    printf("%-*s %*s %*s\n", NAME_WIDTH, "Instruction", COUNT_WIDTH, "Count", TIME_WIDTH, "Mean Time (µs)");
    printf("%-*s %*s %*s\n",
           NAME_WIDTH, "────────────────────",
           COUNT_WIDTH, "──────────",
           TIME_WIDTH, "───────────────");

    for (int i = 0; i < OPCODE_NUMBER; i++)
    {
        if (sorted[i].used <= 0)
            break;

        double mean_time = 0.0;

        for (int j = 0; j < sorted[i].times_size; j++)
            mean_time += sorted[i].times[j];

        mean_time /= (double)sorted[i].times_size;

        printf("%-*s %*d %*.3f\n",
               NAME_WIDTH, opcode_names[sorted[i].op],
               COUNT_WIDTH, sorted[i].used,
               TIME_WIDTH, mean_time);
    }

    printf("%-*s\n", total_width, "──────────────────────────────────────────────────");
}

static inline int instruction_call_ffi(
    vm_t *vm_ptr,
    term_t *regs,
    const int dst_reg,
    const int ffi_index,
    term_t *args_array
)
{
    if (ffi_index < 0 || ffi_index >= (int)vm_ptr->env_ptr->ffi_count)
    {
        fprintf(stderr, "Fatal error: Invalid FFI index: %d.\n", ffi_index);
        return EXIT_FAILURE;
    }

    struct ffi_info *info = vm_ptr->env_ptr->ffi_table[ffi_index];
    const size_t arity = info->arity;

    union ffi_data {
        uint64_t u64;
        int64_t i64;
        uint32_t u32;
        int32_t i32;
        uint16_t u16;
        int16_t i16;
        uint8_t u8;
        int8_t i8;
        long double ld;
        double f64;
        float f32;
        uint32_t c;
        const char *s;
        void *p;
    };

    union ffi_data arg_values[arity];
    void *ffi_args[arity];

    bool has_arg_error = false;
    bool has_bad_arity_error = false;
    size_t arg_error_index = 0;
    enum rcl_type arg_error_expected;

    // Marshalling each arguments from `term_t` into a valid C type.

    for (size_t arg_index = 0; arg_index < arity; arg_index++)
    {
        term_t arg_term = args_array[arg_index];

        if (arg_term == (term_t)NULL)
        {
            has_bad_arity_error = true;
            break;
        }

        arg_term = resolve_indirection(args_array[arg_index]);
        ffi_args[arg_index] = &arg_values[arg_index];

        switch (info->arguments_types[arg_index])
        {
            case RCL_TYPE_UINT8:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].u8 = (uint8_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_INT8:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].i8 = (int8_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_UINT16:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].u16 = (uint16_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_INT16:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].i16 = (int16_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_UINT32:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].u32 = (uint32_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_INT32:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].i32 = (int32_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_UINT64:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].u64 = (uint64_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_INT64:
            {
                if (!IS_INT(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].i64 = (int64_t)GET_INT(arg_term);
                break;
            }

            case RCL_TYPE_LONGDOUBLE:
            {
                if (AS_HEADER(arg_term)->id!= SYM_FLOAT_NATIVE)
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].ld = (long double)get_float(arg_term);
                break;
            }

            case RCL_TYPE_FLOAT64:
            {
                if (AS_HEADER(arg_term)->id!= SYM_FLOAT_NATIVE)
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].f64 = (double)get_float(arg_term);
                break;
            }

            case RCL_TYPE_FLOAT32:
            {
                if (AS_HEADER(arg_term)->id != SYM_FLOAT_NATIVE)
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].f32 = (float)get_float(arg_term);
                break;
            }

            case RCL_TYPE_CHAR:
            {
                if (!IS_CHAR(arg_term))
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].c = (uint32_t)GET_CHAR(arg_term);
                break;
            }

            case RCL_TYPE_STRING:
            {
                if (!IS_PTR(arg_term) || AS_HEADER(arg_term)->id != SYM_STRING_NATIVE)
                {
                    has_arg_error = true;
                    break;
                }
                arg_values[arg_index].s = get_string_ptr(arg_term);
                break;
            }

            case RCL_TYPE_PTR:
            {
                if (IS_PTR(arg_term))
                {
                    const sym_id_t id = AS_HEADER(arg_term)->id;

                    if (id == SYM_BUFFER_NATIVE)
                    {
                        arg_values[arg_index].p = (void *)AS_HEADER(arg_term)->children[0];
                        break;
                    }
                    else if (id == SYM_PTR_NATIVE)
                    {
                        arg_values[arg_index].p = get_opaque_ptr(arg_term);
                        break;
                    }
                    else if (id == SYM_STRING_NATIVE)
                    {
                        arg_values[arg_index].p = (void*)get_string_ptr(arg_term);
                        break;
                    }
                }
                has_arg_error = true;
                break;
            }

            case RCL_TYPE_VOID:
                // Not sure how this should be handled.
                // In practice, nobody does that anyway.
                break;
        }

        if (has_arg_error)
        {
            arg_error_index = arg_index;
            arg_error_expected = info->arguments_types[arg_index];
            break;
        }

        if (has_bad_arity_error)
        {
            arg_error_index = arg_index;
            break;
        }
    }

    if (has_arg_error)
    {
        const term_t bas_term = resolve_indirection(args_array[arg_error_index]);
        size_t data_str_len = 0;
        char *data_str = term_to_string(vm_ptr->env_ptr, bas_term, 3, &data_str_len);

        fprintf(stderr,
            "Fatal error: FFI argument type mismatch "
            "(function '?', argument %zu): expected %s, got value `%s`.\n",
            arg_error_index,
            rcl_type_name(arg_error_expected),
            data_str
        );

        return EXIT_FAILURE;
    }

    if (has_bad_arity_error)
    {
        fprintf(stderr,
            "Fatal error: FFI function arity mismatch "
            "(function '?'): expected %zu arguments, got `%zu` arguments.\n",
            arity,
            (arg_error_index + 1)
        );

        return EXIT_FAILURE;
    }

    // The result of the call of the function is boxed, we have to unbox it and
    // to cast back the value from the heap to a `term_t` value.
    void *raw_result = rcl_ffi_call(info, ffi_args);

    switch (info->return_type)
    {
        case RCL_TYPE_UINT8:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(uint8_t*)raw_result));
            break;
        }

        case RCL_TYPE_INT8:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(int8_t*)raw_result));
            break;
        }
        case RCL_TYPE_UINT16:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(uint16_t*)raw_result));
            break;
        }

        case RCL_TYPE_INT16:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(int16_t*)raw_result));
            break;
        }

        case RCL_TYPE_UINT32:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(uint32_t*)raw_result));
            break;
        }

        case RCL_TYPE_INT32:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(int32_t*)raw_result));
            break;
        }

        case RCL_TYPE_UINT64:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(uint64_t*)raw_result));
            break;
        }

        case RCL_TYPE_INT64:
        {
            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(*(int64_t*)raw_result));
            break;
        }

        case RCL_TYPE_LONGDOUBLE:
        {
            const term_t value = make_float(vm_ptr, (double)*(long double*)raw_result);
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        case RCL_TYPE_FLOAT64:
        {
            const term_t value = make_float(vm_ptr, *(double*)raw_result);
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        case RCL_TYPE_FLOAT32:
        {
            const term_t value = make_float(vm_ptr, (double)*(float*)raw_result);
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        case RCL_TYPE_CHAR:
        {
            const term_t value =  MAKE_CHAR(*(uint32_t*)raw_result);
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        case RCL_TYPE_STRING:
        {
            const char *c_str = *(const char **)raw_result;
            const term_t value = c_str ? make_string(vm_ptr, c_str) : MAKE_INT(0);
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        case RCL_TYPE_PTR:
        {
            const term_t value = make_opaque_ptr(vm_ptr, *(void **)raw_result);
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        case RCL_TYPE_VOID:
        {
            break;
        }
    }

    free(raw_result);
    return EXIT_SUCCESS;
}

static inline int instruction_test_tag(
    vm_t *vm_ptr,
    term_t *regs,
    int *pc,
    int *labels,
    const int src_reg,
    const int tag_id,
    const int fail_label
)
{
    const term_t val = resolve_indirection(regs[src_reg]);
    const sym_id_t toTest = (sym_id_t)tag_id;

    bool matches = false;

    if (toTest == SYM_NUM_NATIVE)
    {
        if (IS_INT(val))
            matches = true;

        else if (IS_PTR(val))
            matches = (AS_HEADER(val)->id == SYM_FLOAT_NATIVE);
    }

    else if (IS_INT(val))
        matches = (toTest == SYM_INT_NATIVE);

    else if (IS_CHAR(val))
        matches = (toTest == SYM_CHAR_NATIVE);

    else if (IS_BOOL(val))
        matches = (toTest == SYM_BOOL_NATIVE);

    else if (IS_PTR(val))
        matches = (AS_HEADER(val)->id == toTest);

    // If it's a float (PTR with SYM_FLOAT), it matches here because toTest == SYM_FLOAT
    // If it's a string (PTR with SYM_STRING), it matches here because toTest == SYM_STRING

    if (!matches)
        *pc = labels[fail_label];

    return EXIT_SUCCESS;
}

static inline int instruction_apply(
    vm_t *vm_ptr,
    term_t *regs,
    int *pc, int *sp, int *fp, int *bp,
    int *labels,
    const int fn_reg,
    const int arg_offset,
    const int arg_count,
    const int dst_reg,
    term_t **stack, size_t *stack_capacity,
    frame_t **frames, size_t *frames_capacity
)
{
    const term_t fn = resolve_indirection(regs[fn_reg]);
    int target = -1;
    term_t env_closure = 0;

    // Is it a closure?
    if (IS_PTR(fn) && AS_HEADER(fn)->id == SYM_CLOSURE)
    {
        target = labels[(int)GET_INT(AS_HEADER(fn)->children[0])];
        env_closure = fn;
    }

    // Is it a global symbol (potential function)?
    else if (IS_PTR(fn) && AS_HEADER(fn)->arity == 0)
    {
        const sym_id_t sym_id = AS_HEADER(fn)->id;

        if (sym_id < vm_ptr->env_ptr->dispatch_table_capacity)
        {
            dispatch_entry_t *entry = vm_ptr->env_ptr->dispatch_table[sym_id];

            while (entry != NULL) {
                // On utilise le VRAI arg_count passé en paramètre
                if (entry->arity == arg_count) {
                    target = labels[entry->label];
                    break;
                }
                entry = entry->next;
            }
        }
    }

    // Execution

    if (target != -1)
    {
        perform_call(
            vm_ptr, pc, sp, fp, bp,
            stack, stack_capacity, frames, frames_capacity,
            target,
            arg_count,
            arg_offset,
            dst_reg,
            env_closure
        );
    }
    else
    {
        // Fallback: data construction

        const sym_id_t sym_id = IS_PTR(fn) ? AS_HEADER(fn)->id : SYM_INT_NATIVE;
        const term_t value = arc_alloc_term(vm_ptr, sym_id, arg_count);
        term_header_t *h = AS_HEADER(value);

        for (int i = 0; i < arg_count; i++)
        {
            term_t arg = regs[arg_offset + i];
            if (arg && IS_PTR(arg)) rc_increment(arg);
            h->children[i] = arg;
        }

        vm_ptr->sp = *sp;
        arc_assign_reg(vm_ptr, regs, dst_reg, value);
    }

    return EXIT_SUCCESS;
}

static inline int instruction_force(
    vm_t *vm_ptr,
    term_t *regs,
    int *pc, int *sp, int *fp, int *bp,
    int *labels,
    const int dst_reg,
    const int src_reg,
    term_t **stack, size_t *stack_capacity,
    frame_t **frames, size_t *frames_capacity
)
{
    const term_t t = resolve_indirection(regs[src_reg]);

    // If not a pointer, it is a computed value.
    if (!IS_PTR(t))
    {
        arc_assign_reg(vm_ptr, regs, dst_reg, t);
        return EXIT_SUCCESS;
    }

    term_header_t *h = AS_HEADER(t);

    // Try to evaluate symbolic data ("outermost strategy") if it's not a system tag.
    if (IS_USER_DATA(h->id))
    {
        const sym_id_t sym_id = h->id;
        const int arg_count = h->arity;

        // Search dispatch table for a matching function
        int target = -1;
        if (sym_id < vm_ptr->env_ptr->dispatch_table_capacity)
        {
            dispatch_entry_t *entry = vm_ptr->env_ptr->dispatch_table[sym_id];
            while (entry != NULL)
            {
                if (entry->arity == arg_count)
                {
                    target = labels[entry->label];
                    break;
                }
                entry = entry->next;
            }
        }

        if (target != -1) // Found a function to call
        {
            perform_call_heap_args(
                vm_ptr, pc, sp, fp, bp,
                stack, stack_capacity, frames, frames_capacity,
                target,
                arg_count,
                h->children,    // Arguments are the children of the data
                dst_reg,        // Destination register
                0,              // No closure env
                0               // Not a thunk update
            );
            return EXIT_SUCCESS;
        }

        int ffi_target = -1;
        for (size_t i = 0; i < vm_ptr->env_ptr->ffi_count; i++)
        {
            if (vm_ptr->env_ptr->ffi_table[i]->sym_id == sym_id &&
                vm_ptr->env_ptr->ffi_table[i]->arity == arg_count)
            {
                ffi_target = (int)i;
                break;
            }
        }

        if (ffi_target != -1) // Found a FFI function
            return instruction_call_ffi(vm_ptr, regs, dst_reg, ffi_target, h->children);

        arc_assign_reg(vm_ptr, regs, dst_reg, t); // If no function found, it's just a symbolic data.
        return EXIT_SUCCESS;
    }

    // If it's not a Thunk, BlackHole or SuspendedCall, it's a value (Record, String, etc.)
    if (h->id != SYM_THUNK && h->id != SYM_BLACK_HOLE && h->id != SYM_SUSPENDED_CALL)
    {
        arc_assign_reg(vm_ptr, regs, dst_reg, t);
        return EXIT_SUCCESS;
    }

    lock_and_check_thunk(t);

    // Suspended Call (from substitution).
    if (h->id == SYM_SUSPENDED_CALL)
    {
        // Layout: [Closure, Arg1, Arg2, ...]
        const term_t closure_term = h->children[0];
        const term_header_t *closure_h = AS_HEADER(closure_term);
        const int target_label = (int)GET_INT(closure_h->children[0]);
        const int arg_count = h->arity - 1;

        perform_call_heap_args(
            vm_ptr, pc, sp, fp, bp,
            stack, stack_capacity, frames, frames_capacity,
            labels[target_label],
            arg_count,
            &h->children[1], // Arguments start at index 1
            dst_reg,
            closure_term,    // Use closure as environment
            t                // Update 't' with result (memoization)
        );
        return EXIT_SUCCESS;
    }

    // A thunk for lazy evaluation.
    // Layout: [Label, Capture1, Capture2...]
    const int target_label = (int)GET_INT(h->children[0]);

    // Note: Thunks have 0 arguments for the call itself (captured vars are in closure_env)
    perform_call_heap_args(
        vm_ptr, pc, sp, fp, bp,
        stack, stack_capacity, frames, frames_capacity,
        labels[target_label],
        0,                  // No stack arguments
        NULL,               // No source array needed
        dst_reg,
        (term_t)h,          // The thunk is its own environment
        t                   // Update 't' with result (memoization)
    );
    
    return EXIT_SUCCESS;
}

static inline int instruction_cast(
    vm_t *vm_ptr,
    term_t *regs,
    const int dst_reg,
    const int src_reg,
    const int target_type_id,
    const int source_type_id
)
{
    const term_t src = resolve_indirection(regs[src_reg]);
    const sym_id_t target_type = (sym_id_t)target_type_id;
    const sym_id_t source_type = (sym_id_t)source_type_id;

    // Check if the expected types are consistent.
    bool type_match = false;

    if (source_type == SYM_INT_NATIVE)
        type_match = IS_INT(src);

    else if (source_type == SYM_CHAR_NATIVE)
        type_match = IS_CHAR(src);

    else if (IS_PTR(src))
        type_match = (AS_HEADER(src)->id == source_type);

    if (!type_match)
    {
        // Mismatch between compiler expectation and runtime reality.
        const term_t value = make_cast_result(vm_ptr, false, MAKE_INT(0));
        arc_assign_reg(vm_ptr, regs, dst_reg, value); 
        return EXIT_SUCCESS;
    }

    term_t result_val = MAKE_INT(0); // default value when success = false
    bool success = true;

    if (source_type == SYM_INT_NATIVE)
    {
        int64_t val = GET_INT(src);

        // Int to Float
        if (target_type == SYM_FLOAT_NATIVE)
        {
            result_val = make_float(vm_ptr, (double)val);
        }

        // Int to Char
        else if (target_type == SYM_CHAR_NATIVE)
        {
            if (val < 0 || val > 0x10FFFF) success = false; // Invalid Unicode code point
            else result_val = MAKE_CHAR((uint32_t)val);
        }

        // Int to String
        else if (target_type == SYM_STRING_NATIVE)
        {
            char buffer[64];
            snprintf(buffer, 64, "%lld", (long long)val);
            result_val = make_string(vm_ptr, buffer);
        }

        // Int to Int
        else if (target_type == SYM_INT_NATIVE) 
        {
            result_val = src;
        }

        // Error
        else
        {
            success = false;
        }
    }
    else if (source_type == SYM_FLOAT_NATIVE)
    {
        double val = get_float(src);

        // Float to Int
        if (target_type == SYM_INT_NATIVE)
        {
            if (isnan(val) || isinf(val)) success = false;
            else if (val > (double)INT64_MAX || val < (double)INT64_MIN) success = false;
            else result_val = MAKE_INT((int64_t)val);
        }

        // Float to String
        else if (target_type == SYM_STRING_NATIVE)
        {
            char buffer[64];
            snprintf(buffer, 64, "%.*g", DBL_DIG, val);
            result_val = make_string(vm_ptr, buffer);
        }

        // Float to Float
        else if (target_type == SYM_FLOAT_NATIVE)
        {
            result_val = src;
        }

        // Error
        else
        {
            success = false;
        }
    }
    else if (source_type == SYM_CHAR_NATIVE)
    {
        uint32_t val = GET_CHAR(src);

        // Char to Int
        if (target_type == SYM_INT_NATIVE)
        {
            result_val = MAKE_INT((int64_t)val);
        }

        // Char to String
        else if (target_type == SYM_STRING_NATIVE)
        {
            char buffer[2] = { (char)val, '\0' };
            result_val = make_string(vm_ptr, buffer);
        }

        // Char to Char
        else if (target_type == SYM_CHAR_NATIVE)
        {
            result_val = src;
        }

        // Error
        else
        {
            success = false;
        }
    }
    else if (source_type == SYM_STRING_NATIVE)
    {
        const char *str = get_string_ptr(src);

        // String to Int
        if (target_type == SYM_INT_NATIVE)
        {
            char *endptr;
            long long res = strtoll(str, &endptr, 10);

            if (*str != '\0' && *endptr == '\0') result_val = MAKE_INT(res);
            else success = false;
        }

        // String to Float
        else if (target_type == SYM_FLOAT_NATIVE)
        {
            char *endptr;
            double res = strtod(str, &endptr);

            if (*str != '\0' && *endptr == '\0') result_val = make_float(vm_ptr, res);
            else success = false;
        }

        // String to Char
        else if (target_type == SYM_CHAR_NATIVE)
        {
            if (str[0] != '\0' && str[1] == '\0') result_val = MAKE_CHAR((uint32_t)str[0]);
            else success = false;
        }

        // String to String
        else if (target_type == SYM_STRING_NATIVE)
        {
            result_val = src;
        }

        else
        {
            success = false;
        }
    }
    else 
    {
        success = false;
    }

    // The result is a record { Success = (0 | 1), Value = <converted value or default> }
    const term_t value = make_cast_result(vm_ptr, success, success ? result_val : MAKE_INT(0));
    arc_assign_reg(vm_ptr, regs, dst_reg, value);
    
    return EXIT_SUCCESS;
}

/// Converts a C string array (argv) into a symbolic linked list: `cons[str, cons[... nil]]`.
/// This is used for the main arguments of the program.
term_t rcl_make_string_list(vm_t *vm_ptr, int argc, const char *argv[])
{
    const sym_id_t nil_id = intern_symbol(vm_ptr->env_ptr, "nil");
    const sym_id_t cons_id = intern_symbol(vm_ptr->env_ptr, "cons");

    term_t current_list = arc_alloc_term(vm_ptr, nil_id, 0);

    for (int i = argc - 1; i >= 0; i--)
    {
        term_t str_val = make_string(vm_ptr, argv[i]);

        term_t cons_term = arc_alloc_term(vm_ptr, cons_id, 2);
        term_header_t *h = AS_HEADER(cons_term);

        if (str_val && IS_PTR(str_val)) rc_increment(str_val);
        h->children[0] = str_val;

        if (current_list && IS_PTR(current_list)) rc_increment(current_list);
        h->children[1] = current_list;

        current_list = cons_term;
    }

    return current_list;
}

static void print_stack_trace(vm_t *vm_ptr)
{
    fprintf(stderr, "\n----------------------------------------------------------");
    fprintf(stderr, "\nStack trace:\n");
    fprintf(stderr, "  at pc: %d  <-- Crash occurred here\n", vm_ptr->pc - 1);

    for (int i = vm_ptr->fp - 1; i >= 0; i--)
    {
        frame_t *frame = &vm_ptr->frames[i];
        fprintf(stderr, "  at pc: %d\n", frame->ret_pc - 1); 
    }
    fprintf(stderr, "----------------------------------------------------------\n");
}

/// Evaluates the program at the given entry point. The return value is the return value of
/// the entry point ("main") as usual, and 0 by default. After the VM stopped, it is still
/// required to destroy the environment and the VM (`destroy_env` and `destroy_vm`).
int run_vm(vm_t *vm_ptr, const int entry, term_t program_args)
{
    if (entry >= (int)vm_ptr->env_ptr->labels_capacity || vm_ptr->env_ptr->labels[entry] < 0)
    {
        fprintf(stderr, "Invalid entry label: .L%d\n", entry);
        exit(1);
    }

    instr_t *program = vm_ptr->env_ptr->program;
    int *labels = vm_ptr->env_ptr->labels;

    term_t *stack = vm_ptr->stack;
    frame_t *frames = vm_ptr->frames;
    size_t stack_capacity = vm_ptr->stack_capacity;
    size_t farmes_capacity = vm_ptr->frames_capacity;

    int pc = labels[entry];
    int bp = 0;
    int sp = 256;
    int fp = 0;

    memset(stack, 0, stack_capacity * sizeof(term_t));
    arc_assign_reg(vm_ptr, stack, 0, program_args);

    #ifdef STATS

    stats_t stats[OPCODE_NUMBER + 1] = {};
    for (int i = 0; i <= OPCODE_NUMBER; i++)
    {
        stats[i].times_cap = 100;
        stats[i].times_size = 0;
        stats[i].times = malloc(100 * sizeof(double));
    }

    #endif

    bool run = true;
    int return_value = EXIT_SUCCESS;

    while (run)
    {
        const instr_t instr = program[pc++];
        term_t *regs = &stack[bp]; // virtual registers are indexed relative to the base pointer

        #ifdef STATS

        stats[instr.op].op = instr.op;
        stats[instr.op].used += 1;

        const clock_t begin = clock();

        #endif

        switch (instr.op)
        {

        // HALT exit_code
        case INSTR_HALT:
        {
            const int exit_code = instr.a;

            return_value = exit_code;
            run = false;
            break;
        }

        // MOV dst_reg, src_reg
        case INSTR_MOV:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;

            arc_assign_reg(vm_ptr, regs, dst_reg, regs[src_reg]);
            break;
        }

        // TEST_TAG src_reg, tag_id, fail_label
        case INSTR_TEST_TAG:
        {
            const int src_reg = instr.a;
            const int tag_id = instr.b;
            const int fail_label = instr.c;

            if (unlikely(instruction_test_tag(
                vm_ptr, regs, &pc, labels, src_reg, tag_id, fail_label) != EXIT_SUCCESS))
            {
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            break;
        }

        // DECONSTRUCT dst_reg, src_reg, index
        case INSTR_DECONSTRUCT:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;
            const int index = instr.c;

            const term_t t = resolve_indirection(regs[src_reg]);
            arc_assign_reg(vm_ptr, regs, dst_reg, AS_HEADER(t)->children[index]);
            break;
        }

        // RESERVE count
        case INSTR_RESERVE:
        {
            const int count = instr.a;
            const int needed = bp + count;

            if (unlikely(needed >= (int)stack_capacity))
                grow_stack_impl(vm_ptr, &stack, &stack_capacity, needed);

            if (needed > sp)
            {
                memset(stack + sp, 0, (needed - sp) * sizeof(term_t));
                sp = needed;
            }

            break;
        }

        // JUMP label
        case INSTR_JUMP:
        {
            const int label = instr.a;

            pc = labels[label];
            break;
        }

        // JUMP_FALSE src_reg, label
        case INSTR_JUMP_FALSE:
        {
            const int src_reg = instr.a;
            const int label = instr.b;

            const term_t val = regs[src_reg];

            if (!IS_BOOL(val)) 
            {
                char *s = term_to_string(vm_ptr->env_ptr, val, 3, NULL);
                fprintf(stderr, "Runtime Error: Condition must be a boolean (got value '%s').\n", s);
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            if (GET_BOOL(val) == 0)
                pc = labels[label];

            break;
        }

        // JUMP_TRUE src_reg, label
        case INSTR_JUMP_TRUE:
        {
            const int src_reg = instr.a;
            const int label = instr.b;

            const term_t val = regs[src_reg];

            if (!IS_BOOL(val))
            {
                char *s = term_to_string(vm_ptr->env_ptr, val, 3, NULL);
                fprintf(stderr, "Runtime Error: Condition must be a boolean (got value '%s').\n", s);
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            if (GET_BOOL(val) != 0)
                pc = labels[label];

            break;
        }

        // CALL label, arg_offset, arg_count, dst_reg
        case INSTR_CALL:
        {
            const int label = instr.a;
            const int arg_offset = instr.b;
            const int arg_count = instr.c;
            const int dst_reg = instr.d;

            perform_call(
                vm_ptr, &pc, &sp, &fp, &bp,
                &stack, &stack_capacity, &frames, &farmes_capacity,
                labels[label],  // traget label
                arg_count,      // arg count
                arg_offset,     // arg source offset
                dst_reg,        // destination register
                0               // no closure
            );
            break;
        }

        // CALL_FFI dst_reg, ffi_index, args_start_reg
        case INSTR_CALL_FFI:
        {
            const int dst_reg = instr.a;
            const int ffi_index = instr.b;
            const int args_start = instr.c;

            if (instruction_call_ffi(vm_ptr, regs, dst_reg, ffi_index, &regs[args_start]) != EXIT_SUCCESS)
            {
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            break;
        }

        // BUFFER_ALLOC dst_reg, size_reg
        case INSTR_BUFFER_ALLOC:
        {
            const int dst_reg = instr.a;
            const int size_reg = instr.b;

            const int64_t size = GET_INT(resolve_indirection(regs[size_reg]));

            const term_t value = arc_alloc_leaf(vm_ptr, SYM_BUFFER_NATIVE, 2 * sizeof(term_t));
            term_header_t *h = AS_HEADER(value);

            void *raw_mem = calloc(1, size);

            h->children[0] = (term_t)raw_mem;   // the buffer has a pointer adress
            h->children[1] = MAKE_INT(size);    // as well a size

            arc_assign_reg(vm_ptr, regs, dst_reg, (term_t)h);
            break;
        }

        // BUFFER_GET dst_reg, buf_reg, index_reg
        case INSTR_BUFFER_GET:
        {
            const int dst_reg = instr.a;
            const int buf_reg = instr.b;
            const int index_reg = instr.c;

            term_header_t *h = AS_HEADER(resolve_indirection(regs[buf_reg]));
            const int64_t index = GET_INT(resolve_indirection(regs[index_reg]));

            if (h->id == SYM_BUFFER_NATIVE)
            {
                uint8_t *buf_mem = (uint8_t *)h->children[0];
                const int64_t size = GET_INT(h->children[1]);

                if (index >= 0 && index < size)
                {
                    const term_t value = MAKE_INT(buf_mem[index]);
                    arc_assign_reg(vm_ptr, regs, dst_reg, value);
                }
                else
                {
                    fprintf(stderr, "Fatal error: Buffer Index Out of Bounds.\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
            }
            else
            {
                fprintf(stderr, "Fatal error: Expected Buffer.\n");
                return_value = EXIT_FAILURE;
                run = false;
            }
            break;
        }

        // BUFFER_SET buf_reg, index_reg, val_reg
        case INSTR_BUFFER_SET:
        {
            const int buf_reg = instr.a; 
            const int index_reg = instr.b ;
            const int val_reg = instr.c ;

            term_header_t *h = AS_HEADER(resolve_indirection(regs[buf_reg]));
            const int64_t index = GET_INT(resolve_indirection(regs[index_reg]));
            const int64_t val = GET_INT(resolve_indirection(regs[val_reg]));

            if (h->id == SYM_BUFFER_NATIVE)
            {
                uint8_t *buf_mem = (uint8_t *)h->children[0];
                const int64_t size = GET_INT(h->children[1]);

                if (index >= 0 && index < size)
                {
                    buf_mem[index] = (uint8_t)val;
                }
                else
                {
                    fprintf(stderr, "Fatal error: Bufer Index Out of Bounds.\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
            }
            else
            {
                fprintf(stderr, "Fatal error: Expected Buffer.\n");
                return_value = EXIT_FAILURE;
                run = false;
            }
            break;
        }

        // BUFFER_REALLOC buf_reg, new_size_reg
        case INSTR_BUFFER_REALLOC:
        {
            const int buf_reg = instr.a;
            const int new_size_reg = instr.b;

            term_header_t *h = AS_HEADER(resolve_indirection(regs[buf_reg]));
            const int64_t new_size = GET_INT(resolve_indirection(regs[new_size_reg]));

            if (h->id == SYM_BUFFER_NATIVE)
            {
                void *old_mem = (void *)h->children[0];
                const int64_t old_size = GET_INT(h->children[1]);

                void *new_mem = realloc(old_mem, new_size);

                if (new_size > old_size)
                {
                    memset((uint8_t *)new_mem + old_size, 0, new_size - old_size);
                }

                h->children[0] = (term_t)new_mem;
                h->children[1] = MAKE_INT(new_size);
            }
            else
            {
                fprintf(stderr, "Fatal error: Expected Buffer.\n");
                return_value = EXIT_FAILURE;
                run = false;
            }
            break;
        }

        // TAILCALL label, arg_offset, arg_count
        case INSTR_TAILCALL:
        {
            const int label = instr.a;
            const int arg_offset = instr.b;
            const int arg_count = instr.c;

            term_t args_buffer[arg_count];
            memcpy(args_buffer, &regs[arg_offset], arg_count * sizeof(term_t));

            // Temporarily increment the reference count of the arguments so that they are
            // not destroyed  by the subsequent frame cleanup.
            for (int i = 0; i < arg_count; i++)
            {
                if (args_buffer[i] && IS_PTR(args_buffer[i]))
                    rc_increment(args_buffer[i]);
            }

            // Clean the current frame
            if (sp > bp)
                arc_clean_stack_window(vm_ptr, bp, sp);

            // Initialize new arguments
            memcpy(&stack[bp], args_buffer, arg_count * sizeof(term_t));

            sp = bp + arg_count + STACK_FRAME_PADDING;
            pc = labels[instr.a];

            break;
        }

        // RET src_reg
        case INSTR_RET:
        {
            const int src_reg = instr.a;

            if (--fp < 0) // nothing else to do
                break;

            const term_t res = regs[src_reg];
            frame_t *f = &frames[fp];

            // We increment the refcount so that the value survive the cleaning.
            if (res && IS_PTR(res)) rc_increment(res);

            if (f->thunk != 0)
            {
                // This frame corresponds to the evaluation of a Thunk, so the original thunk is overwriten
                // with an indirection to the result `res`. The next time this thunk is `FORCE`, the function
                // `resolve_indirection` will leads directly to `res`, hence a lazy evaluation.
                overwrite_with_indirection(vm_ptr, f->thunk, res);

                // If the result itself is a thunk, then it is also evaluated.

                const term_t deep_res = resolve_indirection(res);
                if (IS_PTR(deep_res) && AS_HEADER(deep_res)->id == SYM_THUNK)
                {
                    // Check for cyclic thunk evaluation.
                    lock_and_check_thunk(deep_res);

                    // We reuse the current frame.
                    fp++;
                    f->thunk = deep_res;
                    f->closure_env = deep_res;

                    // Reinit the local stack.
                    sp = bp + STACK_FRAME_PADDING;

                    // Jump to the new thunk.
                    pc = labels[(int)GET_INT(AS_HEADER(deep_res)->children[0])];

                    if (res && IS_PTR(res)) rc_decrement(&vm_ptr->dec_queue, res);
                    break;
                }
            }

            // Clear the pointers from the current frame so that the GC no longer follows them.
            if (sp > bp)
                arc_clean_stack_window(vm_ptr, bp, sp);

            sp = bp;          // Resotre SP
            bp = f->prev_bp;  // Restore BP
            pc = f->ret_pc;   // Return jump

            regs = &stack[bp];
            arc_assign_reg(vm_ptr, regs, f->dst_reg, res); // Write the result in the caller register.

            if (res && IS_PTR(res)) rc_decrement(&vm_ptr->dec_queue, res);
            drain_queue(&vm_ptr->dec_queue, &vm_ptr->arena);

            break;
        }

        // APPLY fn_reg, arg_offset, arg_count, dst_reg
        case INSTR_APPLY:
        {
            const int fn_reg = instr.a;
            const int reg_offset = instr.b;
            const int arg_count = instr.c;
            const int dst_reg = instr.d;

            if (unlikely(instruction_apply(
                    vm_ptr, regs, &pc, &sp, &fp, &bp, labels,
                    fn_reg, reg_offset, arg_count, dst_reg,
                    &stack, &stack_capacity, &frames, &farmes_capacity) != EXIT_SUCCESS))
            {
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }
            break;
        }

        // CALL_CLOSURE cl_reg, arg_offset, arg_count, dst_reg
        case INSTR_CALL_CLOSURE:
        {
            const int cl_reg = instr.a;
            const int arg_offset = instr.b;
            const int arg_count = instr.c;
            const int dst_reg = instr.d;

            const term_t cl = resolve_indirection(regs[cl_reg]);
            const int target = (int)GET_INT(AS_HEADER(cl)->children[0]);

            perform_call(
                vm_ptr, &pc, &sp, &fp, &bp,
                &stack, &stack_capacity, &frames, &farmes_capacity,
                labels[target],
                arg_count,
                arg_offset,
                dst_reg,
                cl          // closure env
            );

            break;
        }

        // DELAY dst_reg, label, capture_count, capture_start
        case INSTR_DELAY:
        {
            const int dst_reg = instr.a;
            const int label = instr.b;
            const int capture_count = instr.c;
            const int capture_start = instr.d;

            vm_ptr->sp = sp;

            term_t t = arc_alloc_term(vm_ptr, SYM_THUNK, capture_count + 1);
            term_header_t *h = AS_HEADER(t);
            h->children[0] = MAKE_INT(label);

            for (int i = 0; i < capture_count; i++)
            {
                term_t captured = regs[capture_start + i];
                if (captured && IS_PTR(captured)) rc_increment(captured);
                h->children[i + 1] = captured;
            }

            arc_assign_reg(vm_ptr, regs, dst_reg, t);
            break;
        }

        // FORCE dst_reg, src_reg
        case INSTR_FORCE:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;

            if (unlikely(instruction_force(
                    vm_ptr, regs, &pc, &sp, &fp, &bp, labels,
                    dst_reg, src_reg,
                    &stack, &stack_capacity, &frames, &farmes_capacity) != EXIT_SUCCESS))
            {
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }
            break;
        }

        // LOAD_INT dst_reg, value
        case INSTR_LOAD_INT:
        {
            const int dst_reg = instr.a;
            const int value = instr.b;

            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_INT(value));
            break;
        }

        // LOAD_INT dst_reg, value
        case INSTR_LOAD_CHAR:
        {
            const int dst_reg = instr.a;
            const int value = instr.b;

            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_CHAR((uint32_t)value));
            break;
        }

        // LOAD_INT dst_reg, value
        case INSTR_LOAD_STRING:
        {
            const int dst_reg = instr.a;
            const int value = instr.b;

            const term_t res = make_string(vm_ptr, vm_ptr->env_ptr->string_pool[value]);
            arc_assign_reg(vm_ptr, regs, dst_reg, res);
            break;
        }

        // LOAD_INT dst_reg, value
        case INSTR_LOAD_BOOL:
        {
            const int dst_reg = instr.a;
            const int value = instr.b;

            arc_assign_reg(vm_ptr, regs, dst_reg, MAKE_BOOL(value));
            break;
        }

        // LOAD_FLOAT dst_reg, hi_bits, lo_bits
        case INSTR_LOAD_FLOAT:
        {
            // floats are encoded as two 32 bits integers

            const int dst_reg = instr.a;
            const int hi_bits = instr.b;
            const int lo_bits = instr.c;

            const uint32_t hi = (uint32_t)hi_bits;
            const uint32_t lo = (uint32_t)lo_bits;
            const uint64_t bits = ((uint64_t)(uint32_t)hi << 32) | (uint64_t)(uint32_t)lo;

            double value;
            memcpy(&value, &bits, sizeof(value));
            arc_assign_reg(vm_ptr, regs, dst_reg, make_float(vm_ptr, value));

            break;
        }

        // LOAD_ATOM dst_reg, sym_id
        case INSTR_LOAD_ATOM:
        {
            const int dst_reg = instr.a;
            const int sym_id = instr.b;

            // Allocation dans l'arène
            const term_t value = arc_alloc_term(vm_ptr, (sym_id_t)sym_id, 0);

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // native binary operations
        #define BINARY_OP(op) do { \
            const term_t l = regs[instr.b]; \
            const term_t r = regs[instr.c]; \
            \
            if (IS_INT(l) && IS_INT(r)) { \
                const term_t value = MAKE_INT(GET_INT(l) op GET_INT(r)); \
                arc_assign_reg(vm_ptr, regs, instr.a, value); \
            } \
            else if (IS_NUMERIC(l) && IS_NUMERIC(r)) { \
                const term_t value = make_float(vm_ptr, get_float(l) op get_float(r)); \
                arc_assign_reg(vm_ptr, regs, instr.a, value); \
            } \
            else { \
                char *sl = term_to_string(vm_ptr->env_ptr, l, 3, NULL); \
                char *sr = term_to_string(vm_ptr->env_ptr, r, 3, NULL); \
                fprintf(stderr, "Runtime Error: Invalid operands for arithmetic operation. Expected numbers, got '%s' and '%s'.\n", sl, sr); \
                return_value = EXIT_FAILURE; \
                run = false; \
            } \
        } while(0)

        // native comparison operations
        #define COMPARE_OP(op) do { \
            const term_t l = regs[instr.b]; \
            const term_t r = regs[instr.c]; \
            \
            if (IS_INT(l) && IS_INT(r)) { \
                const term_t value = MAKE_BOOL(GET_INT(l) op GET_INT(r)); \
                arc_assign_reg(vm_ptr, regs, instr.a, value); \
            } \
            else if (IS_NUMERIC(l) && IS_NUMERIC(r)) { \
                const term_t value = MAKE_BOOL(get_float(l) op get_float(r)); \
                arc_assign_reg(vm_ptr, regs, instr.a, value);  \
            } \
            else { \
                char *sl = term_to_string(vm_ptr->env_ptr, l, 3, NULL); \
                char *sr = term_to_string(vm_ptr->env_ptr, r, 3, NULL); \
                fprintf(stderr, "Runtime Error: Type mismatch in comparison. Expected numbers, got '%s' and '%s'.\n", sl, sr);                                                        \
                return_value = EXIT_FAILURE; \
                run = false; \
            }                                                                           \
        } while(0)

        // ADD dst_reg, lhs_reg, rhs_reg
        case INSTR_ADD:
        {
            BINARY_OP(+);
            break;
        }

        // SUB dst_reg, lhs_reg, rhs_reg
        case INSTR_SUB:
        {
            BINARY_OP(-);
            break;
        }

        // MUL dst_reg, lhs_reg, rhs_reg
        case INSTR_MUL:
        {
            BINARY_OP(*);
            break;
        }

        // DIV dst_reg, lhs_reg, rhs_reg
        case INSTR_DIV:
        {
            const int dst_reg = instr.a;
            const int lhs_reg = instr.b;
            const int rhs_reg = instr.c;

            const term_t l = regs[lhs_reg], r = regs[rhs_reg];

            if (IS_INT(l) && IS_INT(r))
            {
                const int64_t denominator = GET_INT(r);
                if (denominator == 0)
                {
                    fprintf(stderr, "Fatal error: Division by zero\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
                const term_t value = MAKE_INT(GET_INT(l) / denominator);
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }
            else
            {
                const double denominator = get_float(r);
                if (denominator == 0.0)
                {
                    fprintf(stderr, "Fatal error: Division by zero\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
                const term_t value = make_float(vm_ptr, get_float(l) / denominator);
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }
            break;
        }

        // MOD dst_reg, lhs_reg, rhs_reg
        case INSTR_MOD:
        {
            const int dst_reg = instr.a;
            const int lhs_reg = instr.b;
            const int rhs_reg = instr.c;

            const term_t l = regs[lhs_reg], r = regs[rhs_reg];

            if (IS_INT(l) && IS_INT(r)) {
                const int64_t denominator = GET_INT(r);
                if (denominator == 0)
                {
                    fprintf(stderr, "Fatal error: Division by zero\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
                const term_t value = MAKE_INT(GET_INT(l) % denominator);
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }
            else
            {
                const double numerator = get_float(l);
                const double denominator = get_float(r);

                if (denominator == 0.0)
                {
                    fprintf(stderr, "Fatal error: Division by zero\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
                const term_t value = make_float(vm_ptr, fmod(numerator, denominator));
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }
            break;
        }

        // NEG dst_reg, src_reg
        case INSTR_NEG:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;

            const term_t v = regs[src_reg];

            if (IS_INT(v))
            {
                const term_t value = MAKE_INT(-GET_INT(v));
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }
            else
            {
                const term_t value = make_float(vm_ptr, -get_float(v));
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }

            break;
        }

        // NOT dst_reg, src_reg
        case INSTR_NOT:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;

            const term_t v = regs[src_reg];
            
            if (IS_BOOL(v))
            {
                const term_t value = MAKE_BOOL(GET_BOOL(v) == 0);
                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }

            else
            {
                fprintf(stderr, "Fatal Error: Operator 'not' expects a boolean.\n");
                return_value = EXIT_FAILURE;
                run = false;
            }
            break;
        }

        // LE dst_reg, lhs_reg, rhs_reg
        case INSTR_LE:
        {
            COMPARE_OP(<);
            break;
        }

        // LEQ dst_reg, lhs_reg, rhs_reg
        case INSTR_LEQ:
        {
            COMPARE_OP(<=);
            break;
        }

        // GE dst_reg, lhs_reg, rhs_reg
        case INSTR_GE:
        {
            COMPARE_OP(>);
            break;
        }

        // GEQ dst_reg, lhs_reg, rhs_reg
        case INSTR_GEQ:
        {
            COMPARE_OP(>=);
            break;
        }

        #undef BINARY_OP
        #undef COMPARE_OP

        // EQUAL dst_reg, lhs_reg, rhs_reg
        case INSTR_EQUAL:
        {
            const int dst_reg = instr.a;
            const int lhs_reg = instr.b;
            const int rhs_reg = instr.c;

            const term_t value = MAKE_BOOL(term_equals(regs[lhs_reg], regs[rhs_reg]));
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // NOT_EQUAL dst_reg, lhs_reg, rhs_reg
        case INSTR_NOT_EQUAL:
        {
            const int dst_reg = instr.a;
            const int lhs_reg = instr.b;
            const int rhs_reg = instr.c;

            const term_t value = MAKE_BOOL(!term_equals(regs[lhs_reg], regs[rhs_reg]));
            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // ALLOC dst_reg, sym_id, arity, src_offset
        case INSTR_ALLOC:
        {
            const int dst_reg = instr.a;
            const int sym_id = instr.b;
            const int arity = instr.c;
            const int src_offset = instr.d;

            vm_ptr->sp = sp;

            const term_t value = arc_alloc_term(vm_ptr, (sym_id_t)sym_id, arity);
            term_header_t *h = AS_HEADER(value);

            for (int i = 0; i < arity; i++)
            {
                term_t child = regs[src_offset + i];
                if (child && IS_PTR(child)) rc_increment(child);
                h->children[i] = child;
            }

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // CLOSURE dst_reg, label, upval_count, upval_start
        case INSTR_CLOSURE:
        {
            const int dst_reg = instr.a;
            const int label = instr.b;
            const int upval_count = instr.c;
            const int upval_start = instr.d;

            vm_ptr->sp = sp;

            const term_t value = arc_alloc_term(vm_ptr, SYM_CLOSURE, upval_count + 1);
            term_header_t *h = AS_HEADER(value);
            h->children[0] = MAKE_INT(label);

            for (int i = 0; i < upval_count; i++)
            {
                term_t captured = regs[upval_start + i];
                if (captured && IS_PTR(captured)) rc_increment(captured);
                h->children[i + 1] = captured;
            }

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // SUBST dst_reg, src_reg, atom_reg, repl_reg
        case INSTR_SUBST:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;
            const int atom_reg = instr.c;
            const int repl_reg = instr.d;

            const term_t tree = regs[src_reg];
            const term_t toReplace = resolve_indirection(regs[atom_reg]);
            const term_t replacement = regs[repl_reg];

            if (!IS_PTR(toReplace)) // only atoms can be substitued
            {
                fprintf(stderr, "Runtime Error: Substitution must be onto atoms.\n");
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            const sym_id_t toReplaceId = AS_HEADER(toReplace)->id;
            const term_t value = perform_substitution(vm_ptr, tree, toReplaceId, replacement);

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // GET_UPVALUE dst_reg, upval_index
        case INSTR_GET_UPVALUE:
        {
            const int dst_reg = instr.a;
            const int upval_index = instr.b;

            const term_t cl = frames[fp - 1].closure_env;
            const term_t value = AS_HEADER(cl)->children[upval_index + 1];

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // MK_RECORD dst_reg, pair_count, start_reg
        case INSTR_MK_RECORD:
        {
            const int dst_reg = instr.a;
            const int pair_count = instr.b / 2;     // total regs ÷ 2
            const int start_reg = instr.c;

            record_field_t pairs[pair_count]; // VLA not to allocate memory onto the stack.

            for (int i = 0; i < pair_count; i++)
            {
                const term_t key_term = resolve_indirection(regs[start_reg + (i * 2)]);
                const term_t val_term = regs[start_reg + (i * 2) + 1];

                if (!IS_PTR(key_term))
                {
                    fprintf(stderr, "Fatal error: Record key must be an atom.\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                    break;
                }

                pairs[i].key = AS_HEADER(key_term)->id;
                pairs[i].value = val_term;
            }

            const term_t value = make_record_from_pairs(vm_ptr, pairs, pair_count);

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // EXTEND_RECORD dst_reg, base_reg, ext_count, ext_start
        case INSTR_EXTEND_RECORD:
        {
            const int dst_reg = instr.a;
            const int base_reg = instr.b;
            const int ext_count = instr.c;
            const int ext_start = instr.d;

            const term_t base = resolve_indirection(regs[base_reg]);

            if (!IS_PTR(base) || AS_HEADER(base)->id != SYM_RECORD_NATIVE)
            {
                fprintf(stderr, "Fatal error: expected a base record.\n");
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            term_header_t *base_header = AS_HEADER(base);
            const int base_arity = base_header->arity;
            const int base_pair_count = base_arity / 2;

            const int ext_total_regs = ext_count;
            const int ext_pair_count = ext_total_regs / 2;

            const int total_pairs = base_pair_count + ext_pair_count;

            record_field_t pairs[total_pairs];

            for (int i = 0; i < base_pair_count; i++)
            {
                pairs[i].key = (sym_id_t)GET_INT(base_header->children[i * 2]);
                pairs[i].value = base_header->children[i * 2 + 1];
            }

            for (int i = 0; i < ext_pair_count; i++)
            {
                const term_t key_term = resolve_indirection(regs[ext_start + (i * 2)]);
                const term_t val_term = regs[ext_start + (i * 2) + 1];

                if (!IS_PTR(key_term))
                {
                    fprintf(stderr, "Fatal error: Extension key must be an atom.\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                    break;
                }

                pairs[base_pair_count + i].key = AS_HEADER(key_term)->id;
                pairs[base_pair_count + i].value = val_term;
            }

            const term_t value = make_record_from_pairs(vm_ptr, pairs, total_pairs);

            arc_assign_reg(vm_ptr, regs, dst_reg, value);
            break;
        }

        // GET_FIELD dst_reg, record_reg, field_id, fail_label
        case INSTR_GET_FIELD:
        {
            const int dst_reg = instr.a;
            const int record_reg = instr.b;
            const int field_id = instr.c;
            const int fail_label = instr.d;

            const term_t t = resolve_indirection(regs[record_reg]);
            const sym_id_t needle = (sym_id_t)field_id;

            bool found = false;

            if (IS_PTR(t))
            {
                term_header_t *h = AS_HEADER(t);
                if (h->id == SYM_RECORD_NATIVE)
                {
                    const int count = h->arity / 2;
                    for (int i = 0; i < count; i++)
                    {
                        const sym_id_t key = (sym_id_t)GET_INT(h->children[i * 2]);
                        if (key == needle)
                        {
                            const term_t value = h->children[(i * 2) + 1];
                            arc_assign_reg(vm_ptr, regs, dst_reg, value);
                            found = true;
                            break;
                        }
                    }
                }
            }

            if (!found)
                pc = labels[fail_label];

            break;
        }

        // CAST dst_reg, src_reg, target_type_id, source_type_id
        case INSTR_CAST:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;
            const int target_type_id = instr.c;
            const int source_type_id = instr.d;

            if (unlikely(instruction_cast(
                vm_ptr, regs, dst_reg, src_reg, target_type_id, source_type_id) != EXIT_SUCCESS))
            {
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            break;
        }

        // STR_CAT dst_reg, lhs_reg, rhs_reg
        case INSTR_STR_CAT:
        {
            const int dst_reg = instr.a;
            const int lhs_reg = instr.b;
            const int rhs_reg = instr.c;

            const term_t t1 = resolve_indirection(regs[lhs_reg]);
            const term_t t2 = resolve_indirection(regs[rhs_reg]);

            const char *s1 = get_string_ptr(t1);
            const char *s2 = get_string_ptr(t2);

            const size_t len1 = get_string_len(t1);
            const size_t len2 = get_string_len(t2);

            char *buffer = malloc(len1 + len2 + 1);
            memcpy(buffer, s1, len1);
            memcpy(buffer + len1, s2, len2);
            buffer[len1 + len2] = '\0';

            term_t new_str = arc_alloc_leaf(vm_ptr, SYM_STRING_NATIVE, 2 * sizeof(term_t));
            term_header_t *h = AS_HEADER(new_str);

            h->children[0] = (term_t)buffer;
            h->children[1] = MAKE_INT(len1 + len2);

            arc_assign_reg(vm_ptr, regs, dst_reg, new_str);
            break;
        }

        // BUFFER_LENGTH dst_reg, buf_reg, _, _
        case INSTR_BUFFER_LENGTH:
        {
            const int dst_reg = instr.a;
            const int buf_reg = instr.b;

            const term_header_t *h = AS_HEADER(resolve_indirection(regs[buf_reg]));

            if (h->id == SYM_BUFFER_NATIVE)
            {
                arc_assign_reg(vm_ptr, regs, dst_reg, h->children[1]);
            }
            else
            {
                char *s = term_to_string(vm_ptr->env_ptr, regs[buf_reg], 3, NULL);
                fprintf(stderr, "Fatal error: Expected Buffer, but got `%s`.", s);
                free(s);
                run = false;
                return_value = EXIT_FAILURE;
            }

            break;
        }

        // BUFFER_TO_STRING dst_reg, buf_reg
        case INSTR_BUFFER_TO_STRING:
        {
            const int dst_reg = instr.a;
            const int buf_reg = instr.b;

            const term_header_t *h = AS_HEADER(resolve_indirection(regs[buf_reg]));

            if (h->id == SYM_BUFFER_NATIVE)
            {
                uint8_t *buf_mem = (uint8_t *)h->children[0];
                const int64_t size = GET_INT(h->children[1]);

                char *temp_str = malloc(size + 1);
                memcpy(temp_str, buf_mem, size);
                temp_str[size] = '\0';

                term_t new_str = arc_alloc_leaf(vm_ptr, SYM_STRING_NATIVE, 2 * sizeof(term_t));
                AS_HEADER(new_str)->children[0] = (term_t)temp_str;
                AS_HEADER(new_str)->children[1] = MAKE_INT(size);

                arc_assign_reg(vm_ptr, regs, dst_reg, new_str);
            }
            else
            {
                char *s = term_to_string(vm_ptr->env_ptr, regs[buf_reg], 3, NULL);
                fprintf(stderr, "Fatal error: Expected Buffer, but got `%s`.", s);
                free(s);
                run = false;
                return_value = EXIT_FAILURE;
            }
            break;
        }

        // STRING_TO_BUFFER dst_reg, str_reg, _, _
        case INSTR_STRING_TO_BUFFER:
        {
            const int dst_reg = instr.a;
            const int str_reg = instr.b;

            const term_t t = resolve_indirection(regs[str_reg]);

            if (IS_PTR(t) && AS_HEADER(t)->id == SYM_STRING_NATIVE)
            {
                const char *str = get_string_ptr(t);
                const int64_t size = get_string_len(t);

                const term_t value = arc_alloc_leaf(vm_ptr, SYM_BUFFER_NATIVE, 2 * sizeof(term_t));
                term_header_t *h = AS_HEADER(value);

                void *raw_mem = malloc(size);
                memcpy(raw_mem, str, size);

                h->children[0] = (term_t)raw_mem;
                h->children[1] = MAKE_INT(size);

                arc_assign_reg(vm_ptr, regs, dst_reg, value);
            }
            else
            {
                char *s = term_to_string(vm_ptr->env_ptr, regs[str_reg], 3, NULL);
                fprintf(stderr, "Fatal error: Expected String, but got `%s`.", s);
                free(s);
                run = false;
                return_value = EXIT_FAILURE;
            }

            break;
        }

        // PPSHOW dst_reg, src_reg
        case INSTR_PPSHOW:
        {
            const int dst_reg = instr.a;
            const int src_reg = instr.b;

            char *s = term_to_string(vm_ptr->env_ptr, regs[src_reg], 0, NULL);
            
            term_t new_str = make_string(vm_ptr, s);
            free(s);
            arc_assign_reg(vm_ptr, regs, dst_reg, new_str);

            break;
        }

        // PRINT str_reg
        case INSTR_PRINT:
        {
            const int str_reg = instr.a;

            const char *s = get_string_ptr(regs[str_reg]);
            fputs(s, stdout);
            break;
            // io_print_term(vm_ptr->env_ptr, regs[instr.a]);
            // printf("\n");
            // break;
        }

        default:
            fprintf(stderr, "Op %s not impl\n", opcode_names[instr.op]);
            return_value = EXIT_FAILURE;
            run = false;
            break;
        }

        #ifdef STATS

        const clock_t end = clock();
        double time_spent = ((double)(end - begin) / CLOCKS_PER_SEC) * 1000000.0; // result in µs

        if (stats[instr.op].times_size >= stats[instr.op].times_cap)
        {
            const int new_cap = stats[instr.op].times_cap * 2;
            double* new_times = realloc(stats[instr.op].times, new_cap * sizeof(double));

            stats[instr.op].times = new_times;
            stats[instr.op].times_cap = new_cap;
        }

        stats[instr.op].times[stats[instr.op].times_size++] = time_spent;

        #endif
    }

    #ifdef STATS

    display_vm_stats(stats, opcode_names);
    for (int i = 0; i <= OPCODE_NUMBER; i++)
        free(stats[i].times);

    #endif

    if (return_value == EXIT_FAILURE) // we should add a real check for runtime error
    {
        vm_ptr->pc = pc;
        vm_ptr->fp = fp;
        vm_ptr->bp = bp;
        vm_ptr->sp = sp;

        print_stack_trace(vm_ptr);
    }

    return return_value;
}

#ifdef EMBEDDED

/*
* In 'AOT compilation', the runtime and VM are integrated into a C file that will be compiled with the
* generated bytecode directly integrated. The resulting executable will therefore still be interpreted
* code, but with instant start-up time.
* */

int main(int argc, char *argv[])
{
    gc_init();

    vm_env_t *env_ptr = create_env();
    vm_t *vm_ptr = create_vm(env_ptr);

    <FILL-PROGRAM>

    term_t args_list = rcl_make_string_list(vm_ptr, argc - 1, (const char **)(argv + 1));

    const int entry_point = <ENTRY-POINT>;
    const int exit_value = run_vm(vm_ptr, entry_point, args_list);

    destroy_env(env_ptr);
    destroy_vm(vm_ptr);

    return exit_value;
}

#endif

