
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

// The gray list contains allocations in process of being traced. This avoids
// overflow when exploring deeply, and also can avoid cycles. 
static struct alloc_header **gray_list = NULL;
static uint64_t num_gray = 0;
static uint64_t gray_capacity = 0;
void mark_gray(struct alloc_header *alloc) {
    if (num_gray == gray_capacity) {
        gray_capacity *= 2;
        gray_list = realloc(gray_list, gray_capacity * sizeof(struct alloc_header *));
    }
    gray_list[num_gray++] = alloc;
}

void trace_const(struct constant *v) {
}

void trace_prod(struct product *v) {
    for (uint32_t i = 0; i < v->num_fields; i++) {
        mark_gray(AS_ALLOC(v->words[i]));
    }
}

void trace_sum(struct sum *v) {
    for (uint32_t i = 0; i < v->num_fields; i++) {
        mark_gray(AS_ALLOC(v->words[i]));
    }
}

void trace_closure(struct closure *cl) {
    cl->trace(cl->env);
}

void trace_alloc(struct alloc_header *alloc) {
    switch (alloc->type) {
    case ALLOC_CLOSURE:
        trace_closure(AS_CLOSURE(alloc));
        break;
    case ALLOC_CONST:
        trace_const(AS_CONST(alloc));
        break;
    case ALLOC_PROD:
        trace_prod(AS_PRODUCT(alloc));
        break;
    case ALLOC_SUM:
        trace_sum(AS_SUM(alloc));
        break;
    }
}


void collect(void) {
    // Alternatively, malloc at startup, realloc/resize here.
    gray_capacity = 8;
    num_gray = 0;
    gray_list = malloc(gray_capacity * sizeof(struct alloc_header *));

    // Push each local onto gray_list
    for (size_t i = 0; i < num_locals; i++) {
        mark_gray(locals[i]);
    }
    // Push each field of next_step onto gray_list
    trace_roots();

    while (num_gray > 0) {
        // Pick an item
        struct alloc_header *alloc = gray_list[--num_gray];
        if (alloc->mark != 0) {
            // if marked already, continue (avoid cycles.)
            continue;
        }
        // mark as reachable
        alloc->mark = 1;
        // push all subfields as gray (trace)
        trace_alloc(alloc);
    }

    free(gray_list);
    gray_list = NULL;
    gray_capacity = 0;

    // Sweep alloc list for mark = 0, and also reset mark to 0 for other allocations.
    struct alloc_header *prev = NULL;
    for (struct alloc_header *alloc = first_allocation; alloc != NULL; ) {
        struct alloc_header *next = alloc->next;
        if (alloc->mark == 0) {
            if (prev == NULL) {
                first_allocation = next;
            } else {
                prev->next = next;
            }
            free(alloc);
            num_allocs--;
        } else {
            alloc->mark = 0;
            prev = alloc;
        }
        alloc = next;
    }

    // Set new threshold.
    // By using twice the current number of objects, the GC is sort of
    // "adaptive".
    gc_threshold = num_allocs * 2;
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

void cons_new_alloc(struct alloc_header *alloc) {
    alloc->next = first_allocation;
    first_allocation = alloc;
    num_allocs++;
    push_local(first_allocation);
    if (num_allocs > gc_threshold) {
        collect();
    }
}

struct sum *make_sum(uint32_t discriminant, uint32_t num_fields) {
    struct sum *v = malloc(sizeof(struct sum) + num_fields * sizeof(uintptr_t));
    v->header.type = ALLOC_SUM;
    v->discriminant = discriminant;
    v->num_fields = num_fields;
    return v;
}

struct product *make_product(uint32_t num_fields) {
    struct product *v = malloc(sizeof(struct product) + num_fields * sizeof(uintptr_t));
    v->header.type = ALLOC_PROD;
    v->num_fields = num_fields;
    return v;
}

struct closure *allocate_closure(
        void *env,
        void (*trace)(void *env),
        void (*code)(void)) {
    struct closure *cl = malloc(sizeof(struct closure));
    cl->header.type = ALLOC_CLOSURE;
    cl->env = env;
    cl->trace = trace;
    cl->code = code;

    cons_new_alloc(AS_ALLOC(cl));
    return cl;
}

struct constant *allocate_int32(int32_t x) {
    struct constant *v = malloc(sizeof(struct constant));
    v->header.type = ALLOC_CONST;
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v));
    return v;
}

struct product *allocate_pair(struct alloc_header *x, struct alloc_header *y) {
    struct product *v = make_product(2);
    v->words[0] = (uintptr_t)x;
    v->words[1] = (uintptr_t)y;

    cons_new_alloc(AS_ALLOC(v));
    return v;
}

struct product *allocate_nil(void) {
    struct product *v = make_product(0);

    cons_new_alloc(AS_ALLOC(v));
    return v;
}

struct sum *allocate_true(void) {
    struct sum *v = make_sum(1, 0);

    cons_new_alloc(AS_ALLOC(v));
    return v;
}

struct sum *allocate_false(void) {
    struct sum *v = make_sum(0, 0);

    cons_new_alloc(AS_ALLOC(v));
    return v;
}

struct sum *allocate_inl(struct alloc_header *x) {
    struct sum *v = make_sum(0, 1);
    v->words[0] = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v));
    return v;
}

struct sum *allocate_inr(struct alloc_header *y) {
    struct sum *v = make_sum(1, 1);
    v->words[0] = (uintptr_t)y;

    cons_new_alloc(AS_ALLOC(v));
    return v;
}


int32_t int32_value(struct constant *v) {
    return (int32_t)v->value;
}

struct alloc_header *project_fst(struct product *v) {
    return (struct alloc_header *)v->words[0];
}

struct alloc_header *project_snd(struct product *v) {
    return (struct alloc_header *)v->words[1];
}

