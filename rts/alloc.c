
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

// TODO: Replace this with a tricolor mark-sweep scheme, as in Crafting Interpreters.
static uint32_t current_mark = 0;

void trace_const(struct value *v) {
    // No fields, but mark as reachable.
    v->header.mark = current_mark;
}

void trace_prod(struct value *v) {
    v->header.mark = current_mark;
    trace_value((struct value *)v->words[0]);
    trace_value((struct value *)v->words[1]);
}

void trace_sum(struct value *v) {
    v->header.mark = current_mark;
    // Skip the discriminant.
    trace_alloc((struct alloc_header *)v->words[1]);
}

// TODO: Eventually, this will become redundant once value is divided into
// separate sorts.
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

void trace_closure(struct closure *cl) {
    cl->header.mark = current_mark;
    cl->trace(cl->env);
}

void trace_alloc(struct alloc_header *alloc) {
    switch (alloc->type) {
    case ALLOC_CLOSURE:
        trace_closure(AS_CLOSURE(alloc));
        break;
    case ALLOC_CONST:
        trace_const(AS_VALUE(alloc));
        break;
    case ALLOC_PROD:
        trace_prod(AS_VALUE(alloc));
        break;
    case ALLOC_SUM:
        trace_sum(AS_VALUE(alloc));
        break;
    }
}


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
        case ALLOC_CLOSURE:
            if (alloc->mark != current_mark) {
                free(AS_CLOSURE(alloc)->env);
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
        case ALLOC_CLOSURE:
            free(AS_CLOSURE(alloc)->env);
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

struct closure *allocate_closure(
        void *env,
        void (*trace)(void *env),
        void (*code)(void)) {
    if (num_allocs > gc_threshold) {
        collect();
    }
    struct closure *cl = malloc(sizeof(struct closure));
    cl->header.type = ALLOC_CLOSURE;
    cl->env = env;
    cl->trace = trace;
    cl->code = code;

    cl->header.next = first_allocation;
    first_allocation = (struct alloc_header *)cl;
    num_allocs++;
    push_local(first_allocation);
    return cl;
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

