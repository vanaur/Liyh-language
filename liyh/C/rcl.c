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

// We use Boehm GC for the automatic memory management. It is assumed that the user or
// installer has installed the required dependencies.

#if __has_include(<gc.h>)
#  include <gc.h>
#else
#  error ‘Boehm GC (gc.h) not found: please install libgc-dev / bdw-gc.’
#endif


// --- Types, environment and useful macros --- //


typedef uintptr_t term_t;
typedef uint32_t sym_id_t;

#define TAG_PTR         0x0 // tagged pointer (ptr)
#define TAG_INT         0x1 // tagged pointer (int)
#define TAG_CHAR        0x2 // tagged pointer (char)
#define TAG_MASK        0x3

#define IS_PTR(x)       (((x) & TAG_MASK) == TAG_PTR)
#define IS_INT(x)       (((x) & TAG_MASK) == TAG_INT)

#define IS_CHAR(x)      (((x) & TAG_MASK) == TAG_CHAR)
#define MAKE_INT(val)   ((((int64_t)(val)) << 2) | TAG_INT)
#define GET_INT(val)    (((int64_t)(val)) >> 2)
#define MAKE_CHAR(val)  ((((uintptr_t)(val)) << 2) | TAG_CHAR)
#define GET_CHAR(val)   ((uint32_t)(((uintptr_t)(val)) >> 2))

#define SYM_CONTINUATION    0xFFFFFFFA  // continuation for symbolic computations and substitutions

#define SYM_STRING_NATIVE   0xFFFFFFFB  // strings
#define SYM_RECORD_NATIVE   0xFFFFFFFC  // records
#define SYM_FLOAT_NATIVE    0xFFFFFFFD  // floats
#define SYM_CLOSURE         0xFFFFFFFE  // closures
#define SYM_INT_NATIVE      0xFFFFFFFF  // integers
#define SYM_CHAR_NATIVE     0xFFFFFFF0  // characters

#define SYM_SUSPENDED_CALL  0xFFFFFFF6  // Indicates a function application that has been created dynamically.
#define SYM_BLACK_HOLE      0xFFFFFFF7  // Indicates that a thunk is currently being evaluated.
#define SYM_THUNK           0xFFFFFFF8  // Thunk for lazy evaluation (delays)
#define SYM_INDIRECT        0xFFFFFFF9  // Indirections in lazy evaluation

#define IS_SYSTEM_TAG(id)   ((id) >= SYM_CHAR_NATIVE)
#define IS_USER_DATA(id)    ((id) < SYM_CHAR_NATIVE)

typedef struct
{
    sym_id_t id;
    uint32_t arity;
    term_t children[];
} term_header_t;

#define AS_HEADER(val)  ((term_header_t *)(val))

typedef enum
{
    // jump instructions

    INSTR_HALT,
    INSTR_JUMP,
    INSTR_JUMP_FALSE,
    INSTR_JUMP_TRUE,

    // function calling instructions

    INSTR_RESERVE,
    INSTR_CALL,
    INSTR_TAILCALL,
    INSTR_RET,
    INSTR_APPLY,
    INSTR_MOV,

    // literal and atom loading instructions

    INSTR_LOAD_INT,
    INSTR_LOAD_ATOM,
    INSTR_LOAD_FLOAT,
    INSTR_LOAD_CHAR,
    INSTR_LOAD_STRING,

    // native arithmetic instructions

    INSTR_ADD,
    INSTR_SUB,
    INSTR_MUL,
    INSTR_DIV,
    INSTR_MOD,
    INSTR_NEG,

    // native boolean instructions

    INSTR_EQUAL,
    INSTR_NOT_EQUAL,
    INSTR_NOT,
    INSTR_LEQ,
    INSTR_LE,
    INSTR_GE,
    INSTR_GEQ,

    // native string concatenation instruction

    INSTR_STR_CAT,

    // record specific instructions

    INSTR_MK_RECORD,
    INSTR_EXTEND_RECORD,
    INSTR_GET_FIELD,

    // symbolic data allocation instruction

    INSTR_ALLOC,
    INSTR_SUBST,

    // closure specific instructions

    INSTR_CLOSURE,
    INSTR_CALL_CLOSURE,
    INSTR_GET_UPVALUE,

    // pattern matching specific instructions

    INSTR_TEST_TAG,
    INSTR_DECONSTRUCT,

    // lazy evaluation instructions

    INSTR_DELAY,
    INSTR_FORCE,

    // debugging instruction

    INSTR_PPSHOW,
    INSTR_PRINT,
} opcode_t;

/// The number of opcdes.
#define OPCODE_NUMBER ((int)INSTR_PRINT)

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
    [INSTR_PRINT] =         "PRINT",
};

/// Four-address code instruction.
typedef struct
{
    opcode_t op;
    int a, b, c, d;
} instr_t;

typedef struct atom
{
    char *name;
    sym_id_t id;
    struct atom *next;
} atom_t;

typedef struct dispatch_entry
{
    int arity;
    int label;
    struct dispatch_entry *next;
} dispatch_entry_t;

typedef struct
{
    instr_t *program;
    size_t program_size;
    size_t program_capacity;

    int *labels;
    size_t labels_capacity;

    // Strings are constant and cached.

    char **string_pool;
    size_t string_pool_count;
    size_t string_pool_capacity;

    // Symbols are constants and cached.

    atom_t **symbol_pool;
    size_t symbol_pool_count;
    size_t symbol_counter;

    dispatch_entry_t **dispatch_table;
    size_t dispatch_table_capacity;
} vm_env_t;

#define INITIAL_CAPACITY    1024    // arbitrary
#define HASH_MAP_SIZE       4096    // arbitrary

/// Initializes a new VM environment and returns a pointer to it.
vm_env_t *create_env()
{
    vm_env_t *env = (vm_env_t *)GC_MALLOC(sizeof(vm_env_t));

    env->program_capacity = INITIAL_CAPACITY;
    env->program = GC_MALLOC_ATOMIC(env->program_capacity * sizeof(instr_t));
    env->program_size = 0;

    env->labels_capacity = INITIAL_CAPACITY;
    env->labels = GC_MALLOC_ATOMIC(env->labels_capacity * sizeof(int));
    memset(env->labels, -1, env->labels_capacity * sizeof(int));

    env->string_pool_capacity = 256;
    env->string_pool = GC_MALLOC(env->string_pool_capacity * sizeof(char *));
    env->string_pool_count = 0;

    env->symbol_pool_count = HASH_MAP_SIZE;
    env->symbol_pool = GC_MALLOC(env->symbol_pool_count * sizeof(atom_t *));
    env->symbol_counter = 0;

    env->dispatch_table_capacity = INITIAL_CAPACITY;
    env->dispatch_table = GC_MALLOC(env->dispatch_table_capacity * sizeof(dispatch_entry_t*));

    return env;
}

/// Releases the given environment.
void destroy_env(vm_env_t *env_ptr)
{
    if (env_ptr == NULL)
        return;

    for (size_t i = 0; i < env_ptr->string_pool_count; i++)
        free(env_ptr->string_pool[i]);

    env_ptr = NULL;
}

/// Initialize the garbage collector.
void gc_init()
{
    GC_INIT();
}


// --- Symbols & strings --- //


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

    atom_t *new_atom = GC_MALLOC(sizeof(atom_t));

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
        char **new_pool = GC_MALLOC(new_capacity * sizeof(char *));
        memcpy(new_pool, env_ptr->string_pool, env_ptr->string_pool_count * sizeof(char *));
        env_ptr->string_pool = new_pool;
        env_ptr->string_pool_capacity = new_capacity;
    }

    char *copy = malloc(strlen(s) + 1);
    strcpy(copy, s);

    env_ptr->string_pool[env_ptr->string_pool_count] = copy;
    return env_ptr->string_pool_count++;
}


// --- Bytecode emit --- //


/// Emits a bytecode instruction as a four address-code instruction.
void emit(vm_env_t *env_ptr, opcode_t op, const int a, const int b, const int c, const int d)
{
    if (env_ptr->program_size >= env_ptr->program_capacity)
    {
        const size_t new_capacity = env_ptr->program_capacity * 2;
        instr_t *new_program = GC_MALLOC_ATOMIC(new_capacity * sizeof(instr_t));
        memcpy(new_program, env_ptr->program, env_ptr->program_size * sizeof(instr_t));
        env_ptr->program = new_program;
        env_ptr->program_capacity = new_capacity;
    }

    env_ptr->program[env_ptr->program_size++] = (instr_t){ op, a, b, c, d };
}

/// Emits a label.
void set_label(vm_env_t *env_ptr, const int label)
{
    if (label >= (int)env_ptr->labels_capacity)
    {
        const size_t new_cap = (label < 1024) ? 2048 : (label + 1) * 2; // Since the labels are dispersed, this avoids allocating too much into the void.
        int *new_labels = (int *)GC_MALLOC_ATOMIC(new_cap * sizeof(int));
        memset(new_labels, -1, new_cap * sizeof(int));
        if (env_ptr->labels != NULL && env_ptr->labels_capacity > 0)
            memcpy(new_labels, env_ptr->labels, env_ptr->labels_capacity * sizeof(int));

        env_ptr->labels = new_labels;
        env_ptr->labels_capacity = new_cap;
    }

    env_ptr->labels[label] = (int)env_ptr->program_size;
}

/// Emits a function's label for the given symbol id.
void intern_function(vm_env_t *env_ptr, const sym_id_t symbol_id, const int arity, const int label)
{
    if (symbol_id >= (sym_id_t)env_ptr->dispatch_table_capacity)
    {
        size_t old_cap = env_ptr->dispatch_table_capacity;
        const size_t new_cap = (symbol_id + 1) * 2;
        dispatch_entry_t **new_tbl = GC_MALLOC(new_cap * sizeof(dispatch_entry_t *));

        if (env_ptr->dispatch_table != NULL) {
            memcpy(new_tbl, env_ptr->dispatch_table, old_cap * sizeof(dispatch_entry_t *));
        }

        env_ptr->dispatch_table = new_tbl;
        env_ptr->dispatch_table_capacity = new_cap;
    }

    dispatch_entry_t *entry = GC_MALLOC(sizeof(dispatch_entry_t));
    entry->arity = arity;
    entry->label = label;

    entry->next = env_ptr->dispatch_table[symbol_id];
    env_ptr->dispatch_table[symbol_id] = entry;
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


// --- Runtime helpers --- //


/// Follows a chain of indirection pointers until it reaches a concrete value or a term that
/// is no longer an indirection, and returns that final term.
static term_t resolve_indirection(term_t term)
{
    while (IS_PTR(term) && AS_HEADER(term)->id == SYM_INDIRECT)
        term = AS_HEADER(term)->children[0];

    return term;
}

/// Transforms a thunk (or any other object) into an indirection to a target value.
/// This allows for memoization to take place.
static void overwrite_with_indirection(const term_t thunk_ptr, const term_t value)
{
    term_header_t *h = AS_HEADER(thunk_ptr);
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

/// Creates a boxed value for a float (64 bits).
static term_t make_float(const double value)
{
    term_header_t *term = GC_MALLOC(sizeof(term_header_t) + sizeof(double));

    term->id = SYM_FLOAT_NATIVE;
    term->arity = 0;

    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    memcpy(&term->children[0], &bits, sizeof(bits));

    return (term_t)term;
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
static term_t make_string(const char *s)
{
    term_header_t *term = GC_MALLOC(sizeof(term_header_t) + sizeof(term_t));
    term->id = SYM_STRING_NATIVE;
    term->arity = 0;

    char *buff = GC_MALLOC_ATOMIC(strlen(s) + 1);
    strcpy(buff, s);

    term->children[0] = (term_t)buff;
    return (term_t)term;
}

/// Gets a string from the given term.
static const char *get_string_ptr(term_t term)
{
    term = resolve_indirection(term);
    return (const char *)AS_HEADER(term)->children[0];
}

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

static term_t make_record_from_pairs(record_field_t *pairs, const int count)
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
    term_header_t *header = GC_MALLOC(sizeof(term_header_t) + arity * sizeof(term_t));

    header->id = SYM_RECORD_NATIVE;
    header->arity = arity;

    for (int i = 0; i < unique_count; i++)
    {
        header->children[i * 2] = MAKE_INT(pairs[i].key);
        header->children[i * 2 + 1] = pairs[i].value;
    }

    return (term_t)header;
}

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

/// Performs a structural and recursive substitution: replaces occurrences of `toRepId` with
/// `repl` in `root`. Returns a new term (or the original if no changes were made).
static term_t perform_substitution(term_t root, sym_id_t toRepId, term_t repl)
{
    // NOTE: this function can overflow the stack, for now.

    root = resolve_indirection(root);
    if (!IS_PTR(root)) return root;

    term_header_t *h = AS_HEADER(root);

    if (h->arity == 0 && h->id == toRepId)
        return repl;

    if (h->id == SYM_RECORD_NATIVE)
    {
        const int count = h->arity / 2;
        bool changed = false;

        term_t new_children[h->arity];
        memcpy(new_children, h->children, h->arity * sizeof(term_t));

        for (int i = 0; i < count; i++)
        {
            // children[i*2] is th key, children[i*2+1] is the value.
            const term_t old_val = h->children[i * 2 + 1];
            const term_t new_val = perform_substitution(old_val, toRepId, repl);

            if (old_val != new_val)
            {
                new_children[i * 2 + 1] = new_val;
                changed = true;
            }
        }

        if (!changed) return root;

        term_header_t *new_rec = GC_MALLOC(sizeof(term_header_t) + h->arity * sizeof(term_t));
        new_rec->id = SYM_RECORD_NATIVE;
        new_rec->arity = h->arity;
        memcpy(new_rec->children, new_children, h->arity * sizeof(term_t));

        return (term_t)new_rec;
    }

    if ((h->id < SYM_CONTINUATION) && h->arity > 0)
    {
        bool changed = false;
        term_t new_children[h->arity];

        for (uint32_t i = 0; i < h->arity; i++)
        {
            new_children[i] = perform_substitution(h->children[i], toRepId, repl);
            if (new_children[i] != h->children[i]) changed = true;
        }

        if (h->id == toRepId)
        {
            changed = true;

            // If the replacement is a closure, a "suspended call" is created.
            if (IS_PTR(repl) && AS_HEADER(repl)->id == SYM_CLOSURE)
            {
                // Layout of SUSPENDED_CALL: [Closure, Arg1, Arg2, ...]
                // Arity = 1 + h->arity

                const int new_arity = h->arity + 1;
                term_header_t *susp = GC_MALLOC(sizeof(term_header_t) + new_arity * sizeof(term_t));
                susp->id = SYM_SUSPENDED_CALL;
                susp->arity = new_arity;

                susp->children[0] = repl;
                memcpy(&susp->children[1], new_children, h->arity * sizeof(term_t));

                return (term_t)susp;
            }

            else if (IS_PTR(repl))
            {
                const sym_id_t new_id = AS_HEADER(repl)->id;
                term_header_t *new_term = GC_MALLOC(sizeof(term_header_t) + h->arity * sizeof(term_t));
                new_term->id = new_id;
                new_term->arity = h->arity;
                memcpy(new_term->children, new_children, h->arity * sizeof(term_t));
                return (term_t)new_term;
            }
        }

        if (!changed)
            return root;

        term_header_t *new_term = GC_MALLOC(sizeof(term_header_t) + h->arity * sizeof(term_t));
        new_term->id = h->id;
        new_term->arity = h->arity;
        memcpy(new_term->children, new_children, h->arity * sizeof(term_t));
        return (term_t)new_term;
    }

    return root;
}

#define MAX_PRETTY_PRINT_DEPTH  50

/// Return a pointer to a string associated to a pretty print of the term.
/// The returned memory is managed by the GC.
static char *term_to_string(vm_env_t *env_ptr, term_t term, const int depth, size_t *out_len)
{
    term = resolve_indirection(term);

    size_t capacity = 256;
    size_t length = 0;
    char *buffer = GC_malloc(capacity);
    if (!buffer) return NULL;

    #define APPEND(fmt, ...) do { \
        int needed = snprintf(buffer + length, capacity - length, fmt, ##__VA_ARGS__); \
        if (needed >= (int)(capacity - length)) { \
            capacity = length + needed + 256; \
            char *new_buf = GC_realloc(buffer, capacity); \
            if (!new_buf) { GC_free(buffer); return NULL; } \
            buffer = new_buf; \
            snprintf(buffer + length, capacity - length, fmt, ##__VA_ARGS__); \
        } \
        length += needed; \
    } while(0)

    if (IS_INT(term))
        APPEND("%lld", (long long)GET_INT(term));

    else if (IS_CHAR(term))
        APPEND("'%c'", (char)GET_CHAR(term));

    else if (IS_PTR(term))
    {
        const term_header_t *header = AS_HEADER(term);

        if (header->id == SYM_STRING_NATIVE)
            //APPEND("\"%s\"", (char *)header->children[0]);
            APPEND("%s", (char *)header->children[0]);

        else if (header->id == SYM_FLOAT_NATIVE)
            APPEND("%.*g", DBL_DIG, get_float(term));

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
                APPEND("%s", child_str);
            }
            APPEND(" }");
        }

        else if (header->id == SYM_CLOSURE)
            APPEND("<closure@%lld>", (long long)GET_INT(header->children[0]));

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
                        APPEND("%s", child_str);
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
    GC_free(s);
}


// --- VM Core --- //


#define INITIAL_STACK_CAPACITY  8192 // arbitrary
#define INITIAL_FRAMES_CAPACITY 2048 // arbitrary
#define STACK_FRAME_PADDING     16

typedef struct
{
    int ret_pc;
    int prev_bp;
    int dst_reg;
    term_t closure_env;
    term_t thunk;
} frame_t;

typedef struct
{
    term_t *stack;
    size_t stack_capacity;

    frame_t *frames;
    size_t frames_capacity;

    int sp, bp, fp, pc;
    vm_env_t *env_ptr;
} vm_t;

/// Creates a new VM and returns a pointer to it.
vm_t *create_vm(vm_env_t *env_ptr)
{
    vm_t *vm = GC_malloc(sizeof(vm_t));

    vm->stack_capacity = INITIAL_STACK_CAPACITY;
    vm->stack = GC_MALLOC(vm->stack_capacity * sizeof(term_t));

    vm->frames_capacity = INITIAL_FRAMES_CAPACITY;
    vm->frames = GC_MALLOC(vm->frames_capacity * sizeof(frame_t));

    vm->sp = 0;
    vm->bp = 0;
    vm->fp = 0;
    vm->pc = 0;
    vm->env_ptr = env_ptr;

    return vm;
}

/// Destroys the VM.
void destroy_vm(vm_t *vm_ptr)
{
    if (vm_ptr == NULL)
        return;

    // if (vm_ptr->env_ptr != NULL)
    //     destroy_env(vm_ptr->env_ptr);

    // heap content of the vm is handled by the garbage collector

    GC_gcollect();
    vm_ptr = NULL;
}

/// Sets a recursion limit by limmiting the number of frames.

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

        GC_gcollect();
        exit(1);
    }

    term_t *new_stack = GC_REALLOC(vm_ptr->stack, new_capacity * sizeof(term_t));

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

        GC_gcollect();
        exit(1);
    }

    frame_t *new_frames = GC_REALLOC(vm_ptr->frames, new_capacity * sizeof(frame_t));

    const size_t old_size_bytes = vm_ptr->frames_capacity * sizeof(frame_t);
    memset((char*)new_frames + old_size_bytes, 0, new_size_bytes - old_size_bytes);

    vm_ptr->frames = new_frames;
    vm_ptr->frames_capacity = new_capacity;
}

static inline void grow_stack_impl(vm_t *vm, term_t **stack, size_t *cap, int needed)
{
    vm->stack = *stack; // Sync
    grow_stack(vm, needed);
    *stack = vm->stack; // Reload
    *cap = vm->stack_capacity;
}

static inline void grow_frames_impl(vm_t *vm, frame_t **frames, size_t *cap)
{
    vm->frames = *frames; // Sync
    grow_frames(vm);
    *frames = vm->frames; // Reload
    *cap = vm->frames_capacity;
}

static inline void perform_call(
    vm_t *vm,
    int *pc, int *sp, int *fp, int *bp,
    term_t **stack, size_t *stack_cap,
    frame_t **frames, size_t *frames_cap,
    int target_label, int arg_count, int args_src_offset, int dst_reg, term_t closure_env
) {
    // Check frame capacity.
    if (__builtin_expect(*fp + 1 >= (int)*frames_cap, 0)) {
        grow_frames_impl(vm, frames, frames_cap);
    }

    // Check stack capacity.
    int needed = arg_count + STACK_FRAME_PADDING;
    if (__builtin_expect(*sp + needed >= (int)*stack_cap, 0)) {
        grow_stack_impl(vm, stack, stack_cap, needed);
    }

    // Save the current frame.
    (*frames)[(*fp)++] = (frame_t){ *pc, *bp, dst_reg, closure_env, 0 };

    // Copy the arguments.
    term_t *src_args = (*stack) + (*bp) + args_src_offset;
    term_t *dst_args = (*stack) + (*sp);

    if (arg_count > 0)
        memcpy(dst_args, src_args, arg_count * sizeof(term_t));

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
) {
    if (__builtin_expect(*fp + 1 >= (int)*frames_cap, 0)) {
        grow_frames_impl(vm, frames, frames_cap);
    }

    int needed = arg_count + STACK_FRAME_PADDING;
    if (__builtin_expect(*sp + needed >= (int)*stack_cap, 0)) {
        grow_stack_impl(vm, stack, stack_cap, needed);
    }

    (*frames)[(*fp)++] = (frame_t){ *pc, *bp, dst_reg, closure_env, thunk_ptr };

    term_t *dst_args = (*stack) + (*sp);
    if (arg_count > 0)
        memcpy(dst_args, args_array, arg_count * sizeof(term_t));

    memset(dst_args + arg_count, 0, STACK_FRAME_PADDING * sizeof(term_t));

    // 6. Update VM registers
    *bp = *sp;
    *sp = *sp + needed;
    *pc = target_label;
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

/// Evaluates the program at the given entry point. The return value is the return value of
/// the entry point ("main") as usual, and 0 by default. After the VM stopped, it is still
/// required to destroy the environment and the VM (`destroy_env` and `destroy_vm`).
int run_vm(vm_t *vm_ptr, const int entry)
{
    if (entry >= (int)vm_ptr->env_ptr->labels_capacity || vm_ptr->env_ptr->labels[entry] < 0)
    {
        fprintf(stderr, "Invalid entry label: .L%d\n", entry);
        GC_gcollect();
        exit(1);
    }

    instr_t *program = vm_ptr->env_ptr->program;
    int *labels = vm_ptr->env_ptr->labels;
    dispatch_entry_t **dispatch_table = vm_ptr->env_ptr->dispatch_table;

    term_t *stack = vm_ptr->stack;
    frame_t *frames = vm_ptr->frames;
    size_t stack_capacity = vm_ptr->stack_capacity;
    size_t farmes_capacity = vm_ptr->frames_capacity;

    int pc = labels[entry];
    int bp = 0;
    int sp = 256;
    int fp = 0;

    memset(stack, 0, stack_capacity * sizeof(term_t));

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
        term_t *regs = &stack[bp];

        #ifdef STATS

        stats[instr.op].op = instr.op;
        stats[instr.op].used += 1;

        const clock_t begin = clock();

        #endif

        switch (instr.op)
        {
        case INSTR_HALT:
        {
            return_value = instr.a;
            run = false;
            break;
        }

        case INSTR_MOV:
        {
            regs[instr.a] = regs[instr.b];
            break;
        }

        case INSTR_TEST_TAG:
        {
            const term_t val = resolve_indirection(regs[instr.a]);
            const sym_id_t toTest = (sym_id_t)instr.b;

            bool matches = false;

            if (IS_INT(val))
                matches = (toTest == SYM_INT_NATIVE);

            else if (IS_CHAR(val))
                matches = (toTest == SYM_CHAR_NATIVE);

            else if (IS_PTR(val))
                matches = (AS_HEADER(val)->id == toTest);

            // If it's a float (PTR with SYM_FLOAT), it matches here because toTest == SYM_FLOAT
            // If it's a string (PTR with SYM_STRING), it matches here because toTest == SYM_STRING

            if (!matches)
                pc = labels[instr.c];

            break;
        }

        case INSTR_DECONSTRUCT:
        {
            const term_t t = resolve_indirection(regs[instr.b]);
            regs[instr.a] = AS_HEADER(t)->children[instr.c];
            break;
        }

        case INSTR_RESERVE:
        {
            const int needed = bp + instr.a;

            if (__builtin_expect(needed >= (int)stack_capacity, 0))
                grow_stack_impl(vm_ptr, &stack, &stack_capacity, needed);

            if (needed > sp)
            {
                memset(stack + sp, 0, (needed - sp) * sizeof(term_t));
                sp = needed;
            }

            break;
        }

        case INSTR_JUMP:
        {
            pc = labels[instr.a];
            break;
        }

        // jump if false, otherwise continue;
        case INSTR_JUMP_FALSE:
        {
            if (IS_INT(regs[instr.a]) && GET_INT(regs[instr.a]) == 0)
                pc = labels[instr.b];

            break;
        }

        // jump if true, otherwise continue;
        case INSTR_JUMP_TRUE:
        {
            if (IS_INT(regs[instr.a] && GET_INT(regs[instr.b])) != 0)
                pc = labels[instr.b];

            break;
        }

        case INSTR_CALL:
        {
            perform_call(
                vm_ptr, &pc, &sp, &fp, &bp,
                &stack, &stack_capacity, &frames, &farmes_capacity,
                labels[instr.a],    // traget label
                instr.c,            // arg count
                instr.b,            // arg source offset
                instr.d,            // destination register
                0                   // no closure
            );
            break;
        }

        // lighter call that do not consume frames for tail calls
        case INSTR_TAILCALL:
        {
            const int arg_count = instr.c;
            term_t args_buffer[arg_count]; // VLA not to allocate memory onto the stack.
            memcpy(args_buffer, &regs[instr.b], arg_count * sizeof(term_t));

            // Clean the current frame.
            if (sp > bp)
                memset(&stack[bp], 0, (sp - bp) * sizeof(term_t));

            // Initialize new arguments for the begining of the new frame.
            memcpy(&stack[bp], args_buffer, arg_count * sizeof(term_t));

            sp = bp + arg_count + STACK_FRAME_PADDING;
            pc = labels[instr.a];

            break;
        }

        case INSTR_RET:
        {
            const term_t res = regs[instr.a];

            if (--fp < 0) // nothing else to do
                break;

            frame_t *f = &frames[fp];

            if (f->thunk != 0)
            {
                // This frame corresponds to the evaluation of a Thunk, so the original thunk is overwriten
                // with an indirection to the result `res`. The next time this thunk is `FORCE`, the function
                // `resolve_indirection` will leads directly to `res`, hence a lazy evaluation.
                overwrite_with_indirection(f->thunk, res);

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
                    break;
                }
            }

            // Clear the pointers from the current frame so that the GC no longer follows them.
            if (sp > bp)
                memset(&stack[bp], 0, (sp - bp) * sizeof(term_t));

            sp = bp;          // Resotre SP
            bp = f->prev_bp;  // Restore BP
            pc = f->ret_pc;   // Return jump

            regs = &stack[bp];
            regs[f->dst_reg] = res; // Write the result in the caller register.

            break;
        }

        case INSTR_APPLY:
        {
            const term_t fn = resolve_indirection(regs[instr.a]);
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
                const int arg_count = instr.c;

                if (sym_id < vm_ptr->env_ptr->dispatch_table_capacity)
                {
                    dispatch_entry_t *entry = vm_ptr->env_ptr->dispatch_table[sym_id];

                    while (entry != NULL) {
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
                // Call the function

                perform_call(
                    vm_ptr, &pc, &sp, &fp, &bp,
                    &stack, &stack_capacity, &frames, &farmes_capacity,
                    target,
                    instr.c,
                    instr.b,
                    instr.d,
                    env_closure
                );
            }
            else
            {
                // Fallback: data construction

                const sym_id_t sym_id = IS_PTR(fn) ? AS_HEADER(fn)->id : SYM_INT_NATIVE;
                const int count = instr.c;

                vm_ptr->sp = sp;
                term_header_t *h = GC_MALLOC(sizeof(term_header_t) + count * sizeof(term_t));
                h->id = sym_id;
                h->arity = count;

                for (int i = 0; i < count; i++)
                    h->children[i] = regs[instr.b + i];

                regs[instr.d] = (term_t)h;
            }
            break;
        }

        case INSTR_CALL_CLOSURE:
        {
            const term_t cl = resolve_indirection(regs[instr.a]);
            const int target = (int)GET_INT(AS_HEADER(cl)->children[0]);

            perform_call(
                vm_ptr, &pc, &sp, &fp, &bp,
                &stack, &stack_capacity, &frames, &farmes_capacity,
                labels[target],
                instr.c,
                instr.b,
                instr.d,
                cl          // closure env
            );

            break;
        }

        case INSTR_DELAY:
        {
            // instr.a = dst register
            // instr.b = label of the thunk
            // instr.c = number of values to capture
            // instr.d = initial register for the capture

            vm_ptr->sp = sp;

            term_header_t *h = GC_MALLOC(sizeof(term_header_t) + (instr.c + 1) * sizeof(term_t));
            h->id = SYM_THUNK;
            h->arity = instr.c + 1;
            h->children[0] = MAKE_INT(instr.b); // the label to jump in

            for (int i = 0; i < instr.c; i++)
                h->children[i + 1] = regs[instr.d + i];

            regs[instr.a] = (term_t)h;
            break;
        }

        case INSTR_FORCE:
        {
            // instr.a = dst register
            // instr.b = src register

            const term_t t = resolve_indirection(regs[instr.b]);

            // If not a pointer, it is a computed value.
            if (!IS_PTR(t))
            {
                regs[instr.a] = t;
                break;
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
                        vm_ptr, &pc, &sp, &fp, &bp,
                        &stack, &stack_capacity, &frames, &farmes_capacity,
                        target,
                        arg_count,
                        h->children,    // Arguments are the children of the data
                        instr.a,        // Destination register
                        0,              // No closure env
                        0               // Not a thunk update
                    );
                    break;
                }

                // If no function found, it's just a symbolic data.
                regs[instr.a] = t;
                break;
            }

            // If it's not a Thunk, BlackHole or SuspendedCall, it's a value (Record, String, etc.)
            if (h->id != SYM_THUNK && h->id != SYM_BLACK_HOLE && h->id != SYM_SUSPENDED_CALL)
            {
                regs[instr.a] = t;
                break;
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
                    vm_ptr, &pc, &sp, &fp, &bp,
                    &stack, &stack_capacity, &frames, &farmes_capacity,
                    labels[target_label],
                    arg_count,
                    &h->children[1], // Arguments start at index 1
                    instr.a,
                    closure_term,    // Use closure as environment
                    t                // Update 't' with result (memoization)
                );
                break;
            }

            // A thunk for lazy evaluation.
            // Layout: [Label, Capture1, Capture2...]
            const int target_label = (int)GET_INT(h->children[0]);

            // Note: Thunks have 0 arguments for the call itself (captured vars are in closure_env)
            perform_call_heap_args(
                vm_ptr, &pc, &sp, &fp, &bp,
                &stack, &stack_capacity, &frames, &farmes_capacity,
                labels[target_label],
                0,                  // No stack arguments
                NULL,               // No source array needed
                instr.a,
                (term_t)h,          // The thunk is its own environment
                t                   // Update 't' with result (memoization)
            );
            break;
        }

        case INSTR_LOAD_INT:
        {
            regs[instr.a] = MAKE_INT(instr.b);
            break;
        }

        case INSTR_LOAD_CHAR:
        {
            regs[instr.a] = MAKE_CHAR((uint32_t)instr.b);
            break;
        }

        case INSTR_LOAD_STRING:
        {
            regs[instr.a] = make_string(vm_ptr->env_ptr->string_pool[instr.b]);
            break;
        }

        case INSTR_LOAD_FLOAT:
        {
            // floats are encoded as two 32 bits integers

            const uint32_t hi = (uint32_t)instr.b;
            const uint32_t lo = (uint32_t)instr.c;
            const uint64_t bits = ((uint64_t)(uint32_t)hi << 32) | (uint64_t)(uint32_t)lo;

            double value;
            memcpy(&value, &bits, sizeof(value));
            regs[instr.a] = make_float(value);

            break;
        }

        case INSTR_LOAD_ATOM:
        {
            vm_ptr->sp = sp;
            term_header_t *t = GC_MALLOC(sizeof(term_header_t));
            t->id = (sym_id_t)instr.b;
            t->arity = 0;
            regs[instr.a] = (term_t)t;
            break;
        }

        // native binary operations
        #define BINARY_OP(op) do {                                                      \
            const term_t l = regs[instr.b];                                             \
            const term_t r = regs[instr.c];                                             \
                                                                                        \
            if (IS_INT(l) && IS_INT(r))                                                 \
                regs[instr.a] = MAKE_INT(GET_INT(l) op GET_INT(r));                     \
            else                                                                        \
                regs[instr.a] = make_float(get_float(l) op get_float(r));               \
                                                                                        \
        } while(0)

        // native comparison operations
        #define COMPARE_OP(op) do {                                                     \
            const term_t l = regs[instr.b];                                             \
            const term_t r = regs[instr.c];                                             \
                                                                                        \
            if (IS_INT(l) && IS_INT(r))                                                 \
                regs[instr.a] = MAKE_INT((GET_INT(l) op GET_INT(r)) ? 1 : 0);           \
            else                                                                        \
                regs[instr.a] = MAKE_INT((get_float(l) op get_float(r)) ? 1 : 0);       \
                                                                                        \
        } while(0)

        case INSTR_ADD:
        {
            BINARY_OP(+);
            break;
        }

        case INSTR_SUB:
        {
            BINARY_OP(-);
            break;
        }

        case INSTR_MUL:
        {
            BINARY_OP(*);
            break;
        }

        case INSTR_DIV:
        {
            const term_t l = regs[instr.b], r = regs[instr.c];

            if (IS_INT(l) && IS_INT(r))
            {
                const int64_t denominator = GET_INT(r);
                if (denominator == 0)
                {
                    fprintf(stderr, "Fatal error: Division by zero\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
                regs[instr.a] = MAKE_INT(GET_INT(l) / denominator);
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
                regs[instr.a] = make_float(get_float(l) / denominator);
            }
            break;
        }

        case INSTR_MOD:
        {
            const term_t l = regs[instr.b], r = regs[instr.c];

            if (IS_INT(l) && IS_INT(r)) {
                const int64_t denominator = GET_INT(r);
                if (denominator == 0)
                {
                    fprintf(stderr, "Fatal error: Division by zero\n");
                    return_value = EXIT_FAILURE;
                    run = false;
                }
                regs[instr.a] = MAKE_INT(GET_INT(l) % denominator);
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
                regs[instr.a] = make_float(fmod(numerator, denominator));
            }
            break;
        }

        case INSTR_NEG:
        {
            const term_t v = regs[instr.b];
            if (IS_INT(v)) regs[instr.a] = MAKE_INT(-GET_INT(v));
            else regs[instr.a] = make_float(-get_float(v));
            break;
        }

        case INSTR_NOT:
        {
            const term_t v = regs[instr.b];
            const bool is_false = IS_INT(v) ? (GET_INT(v) == 0) : (get_float(v) == 0.0);
            regs[instr.a] = MAKE_INT(is_false ? 1 : 0);
            break;
        }

        case INSTR_LE:
        {
            COMPARE_OP(<);
            break;
        }
        case INSTR_LEQ:
        {
            COMPARE_OP(<=);
            break;
        }
        case INSTR_GE:
        {
            COMPARE_OP(>);
            break;
        }
        case INSTR_GEQ:
        {
            COMPARE_OP(>=);
            break;
        }

        #undef BINARY_OP
        #undef COMPARE_OP

        case INSTR_EQUAL:
        {
            regs[instr.a] = MAKE_INT(term_equals(regs[instr.b], regs[instr.c]) ? 1 : 0);
            break;
        }

        case INSTR_NOT_EQUAL:
        {
            regs[instr.a] = MAKE_INT(!term_equals(regs[instr.b], regs[instr.c]) ? 1 : 0);
            break;
        }

        case INSTR_ALLOC:
        {
            vm_ptr->sp = sp;

            term_header_t *h = GC_MALLOC(sizeof(term_header_t) + instr.c * sizeof(term_t));
            h->id = (sym_id_t)instr.b;
            h->arity = instr.c;

            for (int i = 0; i < instr.c; i++)
                h->children[i] = regs[instr.d + i];

            regs[instr.a] = (term_t)h;
            break;
        }

        case INSTR_CLOSURE:
        {
            vm_ptr->sp = sp;

            term_header_t *h = GC_MALLOC(sizeof(term_header_t) + (instr.c + 1) * sizeof(term_t));
            h->id = SYM_CLOSURE;
            h->arity = instr.c + 1;
            h->children[0] = MAKE_INT(instr.b);

            for (int i = 0; i < instr.c; i++)
                h->children[i + 1] = regs[instr.d + i];

            regs[instr.a] = (term_t)h;
            break;
        }

        case INSTR_SUBST:
        {
            // instr.a = dst register
            // instr.b = src register
            // instr.c = symbol atom to find
            // instr.d = replacement value

            const term_t tree = regs[instr.b];
            const term_t toReplace = resolve_indirection(regs[instr.c]);
            const term_t replacement = regs[instr.d];

            if (!IS_PTR(toReplace)) // only atoms can be substitued
            {
                fprintf(stderr, "Runtime Error: Substitution must be onto atoms.\n");
                return_value = EXIT_FAILURE;
                run = false;
                break;
            }

            const sym_id_t toReplaceId = AS_HEADER(toReplace)->id;
            regs[instr.a] = perform_substitution(tree, toReplaceId, replacement);

            break;
        }

        // gets a value from a closure env
        case INSTR_GET_UPVALUE:
        {
            const term_t cl = frames[fp - 1].closure_env;
            regs[instr.a] = AS_HEADER(cl)->children[instr.b + 1];
            break;
        }

        case INSTR_MK_RECORD:
        {
            // instr.b = count
            // instr.c = start

            const int total_regs = instr.b;
            const int start_reg = instr.c;
            const int pair_count = total_regs / 2;

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

            regs[instr.a] = make_record_from_pairs(pairs, pair_count);
            break;
        }

        case INSTR_EXTEND_RECORD:
        {
            // instr.a = dst
            // instr.b = base record reg
            // instr.c = count (extension)
            // instr.d = extension start reg

            const term_t base = resolve_indirection(regs[instr.b]);

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

            const int ext_total_regs = instr.c;
            const int ext_pair_count = ext_total_regs / 2;
            const int ext_start = instr.d;

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

            regs[instr.a] = make_record_from_pairs(pairs, total_pairs);
            break;
        }

        case INSTR_GET_FIELD:
        {
            // instr.b = record reg
            // instr.c = field id
            // instr.d = fail label

            const term_t t = resolve_indirection(regs[instr.b]);
            const sym_id_t needle = (sym_id_t)instr.c;
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
                            regs[instr.a] = h->children[(i * 2) + 1];
                            found = true;
                            break;
                        }
                    }
                }
            }

            if (!found)
                pc = labels[instr.d];
            break;
        }

        /// Optimized `strcat` for string concatenation. Mainly used for string interpolation.
        case INSTR_STR_CAT:
        {
            const char *s1 = get_string_ptr(regs[instr.b]);
            const char *s2 = get_string_ptr(regs[instr.c]);

            const size_t len1 = strlen(s1);
            const size_t len2 = strlen(s2);
            const size_t total_len = len1 + len2;

            const size_t alloc_size = sizeof(term_header_t) + sizeof(term_t) + total_len + 1;
            term_header_t *term = GC_MALLOC_ATOMIC(alloc_size);

            term->id = SYM_STRING_NATIVE;
            term->arity = 0;

            char *buffer = (char*)((uintptr_t)term + sizeof(term_header_t) + sizeof(term_t));

            memcpy(buffer, s1, len1);
            memcpy(buffer + len1, s2, len2);
            buffer[total_len] = '\0';

            term->children[0] = (term_t)buffer;
            regs[instr.a] = (term_t)term;

            break;
        }

        case INSTR_PPSHOW:
        {
            const char *s = term_to_string(vm_ptr->env_ptr, regs[instr.b], 0, NULL);
            term_header_t *term = GC_MALLOC(sizeof(term_header_t) + sizeof(term_t));

            term->id = SYM_STRING_NATIVE;
            term->arity = 0;

            term->children[0] = (term_t)s;
            regs[instr.a] = (term_t)term;

            break;
        }

        // print a pretty printed version of an "expression" from the VM for debbuging purpose
        case INSTR_PRINT:
        {
            const char *s = get_string_ptr(regs[instr.a]);
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

    return return_value;
}

#ifdef EMBEDDED

/*
* In ‘AOT compilation’, the runtime and VM are integrated into a C file that will be compiled with the
* generated bytecode directly integrated. The resulting executable will therefore still be interpreted
* code, but with instant start-up time.
* */

int main(int argc, char *argv[])
{
    gc_init();

    vm_env_t *env_ptr = create_env();
    vm_t *vm_ptr = create_vm(env_ptr);

    <FILL-PROGRAM>

    const int entry_point = <ENTRY-POINT>;
    const int exit_value = run_vm(vm_ptr, entry_point);

    destroy_env(env_ptr);
    destroy_vm(vm_ptr);

    return exit_value;
}

#endif

