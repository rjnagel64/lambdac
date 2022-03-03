
#include "alloc.h"
#include "panic.h"

// All allocations.
static struct alloc_header *first_allocation;
static uint64_t num_allocs = 0;
static uint64_t gc_threshold = 256;

// The locals vector serves as an extra set of GC roots, for values allocated
// during the lifetime of a function.
static struct alloc_header **locals = NULL;
static size_t num_locals = 0;
static size_t locals_capacity = 0;

void init_locals(void) {
    locals_capacity = 8;
    locals = malloc(locals_capacity * sizeof(struct alloc_header *));
    num_locals = 0;
}

void destroy_locals(void) {
    free(locals);
    locals = NULL;
    num_locals = 0;
    locals_capacity = 0;
}

void reset_locals(void) {
    num_locals = 0;
}

void push_local(struct alloc_header *local) {
    if (num_locals == locals_capacity) {
        locals_capacity *= 2;
        locals = realloc(locals, locals_capacity * sizeof(struct alloc_header *));
    }
    locals[num_locals] = local;
    num_locals++;
}

// Some sort of tracing GC.
// Linked list of all allocations.
// alloc pushes on front of list.
// the activation record stack contains the roots. (Are there others?) (No, I
// don't think so. I don't remove the record until it returns, and I invoke the
// function+arguments only from the record.) (... Hang on, allocations local to
// a function are a thing. AAGH.)
// AAGH. I need to trace through environments as well. But environments are
// void*, so I can't really. I could generate trace_k0_env, etc., but how would
// I know to invoke it? Maybe 'struct fun' and 'struct cont' can store pointers
// to a tracing method? That's weird, but it would probably work.
// Or instead of void *env, struct env { bitmap tracing_fields; ... }, with a
// bitmap to specify what/how to trace each field of the environment. (00: no
// trace. 01: cont trace. 10: fun trace, 11: val trace) That involves less
// indirection, but the bitmap may be large (if you have like 32 values or
// whatever.) (This requires that all fields in the environment have the same
// size, which is mostly reasonable. Everything is word-sized except int32, and
// I don't have unboxed values yet.)
//
// Or I could store the bitmap in the activation record. (I think.)
// Well, a bitmap for the continuation and a bitmap for the function, but yes.
// (No, I can't. Because I need to allocate/construct continuations and other
// closures in the compiled code, those things aren't on the stack yet. Thus,
// every 'struct fun' and 'struct cont' needs a tracing map.)

static uint32_t current_mark = 0;

// TODO: Remember to mark values after tracing subterms
// TODO: What if there is a cycle? I think I will stack overflow, then.
// (=> tricolor mark-sweep?)
void trace_prod(struct value *v) {
    trace_value((struct value *)v->words[0]);
    trace_value((struct value *)v->words[1]);
}

void trace_sum(struct value *v) {
    // Skip the discriminant.
    trace_value((struct value *)v->words[1]);
}

// TODO: Eventually, this will become redundant with trace_alloc.
void trace_value(struct value *v) {
    switch (v->header.type) {
    case ALLOC_CONST:
        break;
    case ALLOC_PROD:
        trace_prod(v);
        break;
    case ALLOC_SUM:
        trace_sum(v);
        break;
    default:
        panic("unreachable allocation type");
    }
}

void trace_fun(struct fun *f) {
    f->header.mark = current_mark;
    f->trace_env(f->env);
}

void trace_cont(struct cont *k) {
    k->header.mark = current_mark;
    k->trace_env(k->env);
}

void trace_alloc(struct alloc_header *alloc) {
    switch (alloc->type) {
    case ALLOC_FUN:
        trace_fun((struct fun *)alloc);
        break;
    case ALLOC_CONT:
        trace_cont((struct cont *)alloc);
        break;
    case ALLOC_CONST:
        // No fields to trace
        break;
    case ALLOC_PROD:
        trace_prod((struct value *)alloc);
        break;
    case ALLOC_SUM:
        trace_sum((struct value *)alloc);
        break;
    }
}


// Hook to trace any roots known to the driver program.
// Provided at runtime startup, by the main driver.
void (*trace_roots)(void);

void trace_locals(void) {
    for (size_t i = 0; i < num_locals; i++) {
        // Mark based on allocation type.
        struct alloc_header *local = locals[i];
        trace_alloc(local);
    }
}

void sweep(void) {
    // Delete unmarked items from the allocation list.
    // Release memory associated with closure environments.
    struct alloc_header *prev = NULL;
    for (struct alloc_header *alloc = first_allocation; alloc != NULL; ) {
        struct alloc_header *next = alloc->next;

        switch (alloc->type) {
        case ALLOC_FUN:
            // We use != instead of < because of overflow.
            if (alloc->mark != current_mark) {
                free(((struct fun *)alloc)->env);
                free(alloc);
                if (prev != NULL) {
                    prev->next = next;
                } else {
                    first_allocation = next;
                }
            }
            break;
        case ALLOC_CONT:
            if (alloc->mark != current_mark) {
                free(((struct cont *)alloc)->env);
                free(alloc);
                if (prev != NULL) {
                    prev->next = next;
                } else {
                    first_allocation = next;
                }
            }
            break;
        case ALLOC_CONST:
        case ALLOC_PROD:
        case ALLOC_SUM:
            if (alloc->mark != current_mark) {
                // All fields are managed by GC.
                free(alloc);
                if (prev != NULL) {
                    prev->next = next;
                } else {
                    first_allocation = next;
                }
            }
            break;
        }

        alloc = next;
    }
}

void collect(void) {
    current_mark++;
    trace_roots();
    trace_locals();
    sweep();
    gc_threshold *= 2;
}

void sweep_all_allocations(void) {
    for (struct alloc_header *alloc = first_allocation; alloc != NULL;) {
        struct alloc_header *next = alloc->next;
        switch (alloc->type) {
        case ALLOC_FUN:
            // Fields in env are managed by GC.
            free(((struct fun *)alloc)->env);
            free(alloc);
            break;
        case ALLOC_CONT:
            // Fields in env are managed by GC.
            free(((struct cont *)alloc)->env);
            free(alloc);
            break;
        case ALLOC_CONST:
        case ALLOC_PROD:
        case ALLOC_SUM:
            // All fields are managed by GC.
            free(alloc);
            break;
        }
        alloc = next;
    }
}

struct cont *allocate_cont(
        void *env,
        void (*code)(void *env, struct alloc_header *arg),
        void (*trace_env)(void *env)) {
    struct cont *k = malloc(sizeof(struct cont));
    k->header.type = ALLOC_CONT;
    k->header.next = first_allocation;
    k->env = env;
    k->code = code;
    k->trace_env = trace_env;

    first_allocation = (struct alloc_header *)k;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return k;
}

struct fun *allocate_fun(
        void *env,
        void (*code)(void *env, struct alloc_header *arg, struct cont *kont),
        void (*trace_env)(void *env)) {
    struct fun *f = malloc(sizeof(struct fun));
    f->header.type = ALLOC_FUN;
    f->header.next = first_allocation;
    f->env = env;
    f->code = code;
    f->trace_env = trace_env;

    first_allocation = (struct alloc_header *)f;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return f;
}

struct value *allocate_int32(int32_t x) {
    struct value *v = malloc(sizeof(struct value) + 1 * sizeof(uintptr_t));
    v->header.type = ALLOC_CONST;
    v->header.next = first_allocation;
    v->words[0] = (uintptr_t)x;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}

// TODO: This does not allow allocating (id, not). Functions and continuations are not 'struct value'.
// To rectify this, I think I need to move towards the info-table approach.
// All GC objects are info pointer followed by fields. For product, fields are
// components. For sum, fields are discriminant and payload. For closure,
// fields are captures. For constants, fields are value.
struct value *allocate_pair(struct value *x, struct value *y) {
    struct value *v = malloc(sizeof(struct value) + 2 * sizeof(uintptr_t));
    v->header.type = ALLOC_PROD;
    v->header.next = first_allocation;
    v->words[0] = (uintptr_t)x;
    v->words[1] = (uintptr_t)y;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}

struct value *allocate_nil(void) {
    struct value *v = malloc(sizeof(struct value));
    v->header.type = ALLOC_CONST;
    v->header.next = first_allocation;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}

// TODO: Make booleans like 0/1, instead of inl ()/inr ()
struct value *allocate_true(void) {
    struct value *v = malloc(sizeof(struct value) + 1 * sizeof(uintptr_t));
    v->header.type = ALLOC_CONST;
    v->header.next = first_allocation;
    v->words[0] = 0;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}

struct value *allocate_false(void) {
    struct value *v = malloc(sizeof(struct value) + 1 * sizeof(uintptr_t));
    v->header.type = ALLOC_CONST;
    v->header.next = first_allocation;
    v->words[0] = 1;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}

struct value *allocate_inl(struct value *x) {
    struct value *v = malloc(sizeof(struct value) + 2 * sizeof(uintptr_t));
    v->header.type = ALLOC_SUM;
    v->header.next = first_allocation;
    v->words[0] = 0;
    v->words[1] = (uintptr_t)x;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}

struct value *allocate_inr(struct value *y) {
    struct value *v = malloc(sizeof(struct value) + 2 * sizeof(uintptr_t));
    v->header.type = ALLOC_SUM;
    v->header.next = first_allocation;
    v->words[0] = 1;
    v->words[1] = (uintptr_t)y;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
    return v;
}


int32_t int32_value(struct value *v) {
    // Unchecked. Use only on int32 values.
    return (int32_t)v->words[0];
}

struct alloc_header *project_fst(struct value *v) {
    // Unchecked. Use only on (a, b) values.
    return (struct alloc_header *)v->words[0];
}

struct alloc_header *project_snd(struct value *v) {
    // Unchecked. Use only on (a, b) values.
    return (struct alloc_header *)v->words[1];
}

