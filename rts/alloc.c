
#include "alloc.h"
#include "panic.h"

// All allocations.
static struct alloc_header *first_allocation;
static uint64_t num_allocs = 0;
static uint64_t gc_threshold = 256;

// The locals vector serves as an extra set of GC roots, for values allocated
// during the lifetime of a function.
struct local_entry {
    struct alloc_header *alloc;
    type_info info;
};
static struct local_entry *locals = NULL;
static size_t num_locals = 0;
static size_t locals_capacity = 0;

void init_locals(void) {
    locals_capacity = 8;
    locals = malloc(locals_capacity * sizeof(struct local_entry));
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

void push_local(struct alloc_header *local, type_info info) {
    if (num_locals == locals_capacity) {
        locals_capacity *= 2;
        locals = realloc(locals, locals_capacity * sizeof(struct local_entry));
    }
    locals[num_locals].alloc = local;
    locals[num_locals].info = info;
    num_locals++;
}

// The gray list contains allocations in process of being traced. This avoids
// overflow when exploring deeply, and also can avoid cycles. 
struct gray_entry {
    struct alloc_header *alloc;
    type_info info;
};
static struct gray_entry *gray_list = NULL;
static uint64_t num_gray = 0;
static uint64_t gray_capacity = 0;
void mark_gray(struct alloc_header *alloc, type_info info) {
    if (num_gray == gray_capacity) {
        gray_capacity *= 2;
        gray_list = realloc(gray_list, gray_capacity * sizeof(struct gray_entry));
    }
    gray_list[num_gray].alloc = alloc;
    gray_list[num_gray].info = info;
    num_gray++;
}

void trace_constant(struct alloc_header *alloc) {
}

type_info constant_info = { trace_constant };

void trace_sum(struct alloc_header *alloc) {
    struct sum *v = AS_SUM(alloc);
    mark_gray(v->payload, v->info);
}

type_info sum_info = { trace_sum };

void trace_bool_value(struct alloc_header *alloc) {
}

type_info bool_value_info = { trace_bool_value };

void trace_closure(struct alloc_header *alloc) {
    struct closure *cl = AS_CLOSURE(alloc);
    cl->trace(cl->env);
}

type_info closure_info = { trace_closure };


void trace_product(struct alloc_header *alloc) {
    struct product *v = AS_PRODUCT(alloc);
    for (uint32_t i = 0; i < v->num_fields; i++) {
        mark_gray(AS_ALLOC(v->words[i]), any_info);
    }
}

void trace_alloc(struct alloc_header *alloc) {
    switch (alloc->type) {
    case ALLOC_CLOSURE:
        trace_closure(alloc);
        break;
    case ALLOC_CONST:
        trace_constant(alloc);
        break;
    case ALLOC_PROD:
        trace_product(alloc);
        break;
    case ALLOC_SUM:
        trace_sum(alloc);
        break;
    case ALLOC_BOOL:
        trace_bool_value(alloc);
        break;
    }
}

type_info any_info = { trace_alloc };


void collect(void) {
    // Alternatively, malloc at startup, realloc/resize here.
    // That probably would be better, GC happens when there isn't much memory
    // available to allocate for the gray list.
    gray_capacity = 8;
    num_gray = 0;
    gray_list = malloc(gray_capacity * sizeof(struct gray_entry));

    // Push each local onto gray_list
    for (size_t i = 0; i < num_locals; i++) {
        mark_gray(locals[i].alloc, locals[i].info);
    }
    // Push each field of next_step onto gray_list
    trace_roots();

    while (num_gray > 0) {
        // Pick an item
        struct gray_entry gray = gray_list[--num_gray];
        if (gray.alloc->mark != 0) {
            // if marked already, continue (avoid cycles.)
            continue;
        }
        // mark as reachable
        gray.alloc->mark = 1;
        // push all subfields as gray (trace)
        gray.info.trace(gray.alloc);
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
        case ALLOC_BOOL:
        case ALLOC_PROD:
        case ALLOC_SUM:
            // All fields are managed by GC.
            free(alloc);
            break;
        }
        alloc = next;
    }
}

void cons_new_alloc(struct alloc_header *alloc, type_info info) {
    alloc->mark = 0;
    alloc->next = first_allocation;
    first_allocation = alloc;
    num_allocs++;
    push_local(first_allocation, info);
    if (num_allocs > gc_threshold) {
        collect();
    }
}

struct closure *allocate_closure(
        void *env,
        void (*trace)(void *env),
        void (*code)(void),
        void (*enter)(void)) {
    struct closure *cl = malloc(sizeof(struct closure));
    cl->header.type = ALLOC_CLOSURE;
    cl->env = env;
    cl->trace = trace;
    cl->code = code;
    cl->enter = enter;

    cons_new_alloc(AS_ALLOC(cl), closure_info);
    return cl;
}

struct constant *allocate_int64(int64_t x) {
    struct constant *v = malloc(sizeof(struct constant));
    v->header.type = ALLOC_CONST;
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v), constant_info);
    return v;
}

struct bool_value *allocate_true(void) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->header.type = ALLOC_BOOL;
    v->discriminant = 1;

    cons_new_alloc(AS_ALLOC(v), bool_value_info);
    return v;
}

struct bool_value *allocate_false(void) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->header.type = ALLOC_BOOL;
    v->discriminant = 0;

    cons_new_alloc(AS_ALLOC(v), bool_value_info);
    return v;
}

struct sum *allocate_inl(struct alloc_header *x, type_info x_info) {
    struct sum *v = malloc(sizeof(struct sum));
    v->header.type = ALLOC_SUM;
    v->discriminant = 0;
    v->info = x_info;
    v->payload = x;

    cons_new_alloc(AS_ALLOC(v), sum_info);
    return v;
}

struct sum *allocate_inr(struct alloc_header *y, type_info y_info) {
    struct sum *v = malloc(sizeof(struct sum));
    v->header.type = ALLOC_SUM;
    v->discriminant = 1;
    v->info = y_info;
    v->payload = y;

    cons_new_alloc(AS_ALLOC(v), sum_info);
    return v;
}


int64_t int64_value(struct constant *v) {
    return (int64_t)v->value;
}

