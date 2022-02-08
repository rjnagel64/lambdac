
#include <stdio.h>
#include <string.h>

#include "rts.h"

void not_implemented(const char *msg) {
    printf("Not implemented: %s\n", msg);
    exit(1);
}

enum next_type {
    JUMP_NEXT,
    TAILCALL_NEXT,
    HALT_NEXT,
};

struct next_action {
    enum next_type type;
    struct fun *fun;
    struct value *arg;
    struct cont *kont;
};

// Next action to take. A GC root.
static struct next_action next_step;


// All allocations.
static struct alloc_header *first_allocation;
static uint64_t num_allocs = 0;
static uint64_t gc_threshold = 256;

// Local variables in current function.
static struct alloc_header **locals = NULL;

// Idea: The need for a global 'locals' (oxymoron) array can be obviated by
// having each code block stack-allocate appropriately-sized arrays to hold the
// locals.
//
// Then, calls to allocate_fun, allocate_cont, allocate_int32, etc. can take
// the "locals pointer" as an argument and use that as an extra set of roots.
void allocate_locals(size_t count) {
    locals = realloc(locals, count * sizeof(struct alloc_header *));
    num_locals = count;
    memset(locals, 0, count * sizeof(struct alloc_header *));
}

void store_local(size_t i, struct alloc_header *alloc) {
    locals[i] = alloc;
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

void trace_value(struct value *v) {
    v->header.mark = current_mark;
    // TODO: Add fields/variants to 'struct value'
}

void trace_fun(struct fun *f) {
    f->header.mark = current_mark;
    f->trace_env(f->env);
}

void trace_cont(struct cont *k) {
    k->header.mark = current_mark;
    k->trace_env(k->env);
}


void mark_root(void) {
    switch (next_step.type) {
    case TAILCALL_NEXT:
        trace_fun(next_step.fun);
        trace_cont(next_step.kont);
        trace_value(next_step.arg);
        break;
    case JUMP_NEXT:
        trace_cont(next_step.kont);
        trace_value(next_step.arg);
        break;
    case HALT_NEXT:
        trace_value(next_step.arg);
        break;
    }
}

void mark_locals(void) {
    for (uint64_t i = 0; i < num_locals; i++) {
        // Mark based on allocation type.
        struct alloc_header *local = locals[i];
        if (local == NULL) {
            continue;
        }
        switch (local->type) {
        case ALLOC_FUN:
            trace_fun((struct fun *)local);
            break;
        case ALLOC_CONT:
            trace_cont((struct cont *)local);
            break;
        case ALLOC_VALUE:
            trace_value((struct value *)local);
            break;
        }
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
        case ALLOC_VALUE:
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

// These three functions can be merged by outlining the "trace relevant
// structure" into the allocate_whatever functions.
void collect_from_cont(struct cont *k) {
    current_mark++;
    trace_cont(k);

    mark_root();
    mark_locals();
    sweep();
    gc_threshold *= 2;
}

void collect_from_fun(struct fun *f) {
    current_mark++;
    trace_fun(f);

    mark_root();
    mark_locals();
    sweep();
    gc_threshold *= 2;
}

void collect_from_value(struct value *v) {
    current_mark++;
    trace_value(v);

    mark_root();
    mark_locals();
    sweep();
    gc_threshold *= 2;
}

struct cont *allocate_cont(
        void *env,
        void (*code)(void *env, struct value *arg),
        void (*trace_env)(void *env)) {
    struct cont *k = malloc(sizeof(struct cont));
    k->header.type = ALLOC_CONT;
    k->header.next = first_allocation;
    k->env = env;
    k->code = code;
    k->trace_env = trace_env;

    first_allocation = (struct alloc_header *)k;
    num_allocs++;
    if (num_allocs > gc_threshold) {
        collect_from_cont(k);
    }
    return k;
}

struct fun *allocate_fun(
        void *env,
        void (*code)(void *env, struct value *arg, struct cont *kont),
        void (*trace_env)(void *env)) {
    struct fun *f = malloc(sizeof(struct fun));
    f->header.type = ALLOC_FUN;
    f->header.next = first_allocation;
    f->env = env;
    f->code = code;
    f->trace_env = trace_env;

    first_allocation = (struct alloc_header *)f;
    num_allocs++;
    if (num_allocs > gc_threshold) {
        collect_from_fun(f);
    }
    return f;
}

struct value *allocate_int32(int32_t x) {
    struct value *v = malloc(sizeof(struct value));
    v->header.type = ALLOC_VALUE;
    v->header.next = first_allocation;
    v->int_value = x;

    first_allocation = (struct alloc_header *)v;
    num_allocs++;
    if (num_allocs > gc_threshold) {
        collect_from_value(v);
    }
    return v;
}


int32_t int32_value(struct value *v) {
    // Unchecked.
    return v->int_value;
}


void control_jump(struct cont *k, struct value *x) {
    next_step.type = JUMP_NEXT;
    next_step.fun = NULL;
    next_step.arg = x;
    next_step.kont = k;
}

void control_call(struct fun *f, struct value *x, struct cont *k) {
    next_step.type = TAILCALL_NEXT;
    next_step.fun = f;
    next_step.arg = x;
    next_step.kont = k;
}

void control_halt(struct value *x) {
    next_step.type = HALT_NEXT;
    next_step.fun = NULL;
    next_step.arg = x;
    next_step.kont = NULL;
}



// Provided by user.
void program_entry(void);

int main(void) {
    // Initialize halt continuation.
    /* halt = allocate_cont(NULL, halt_code); */

    // Push initial activation record on stack
    program_entry();

    int keep_running = 1;
    while (keep_running) {
        switch (next_step.type) {
        case JUMP_NEXT:
            next_step.kont->code(next_step.kont->env, next_step.arg);
            // fun, cont, and arg will be collected by GC.
            break;
        case TAILCALL_NEXT:
            next_step.fun->code(next_step.fun->env, next_step.arg, next_step.kont);
            // fun, cont, and arg will be collected by GC.
            break;
        case HALT_NEXT:
            printf("done.\n");
            int32_t result = int32_value(next_step.arg);
            printf("result = %d\n", result);
            keep_running = 0;
            // fun, cont, and arg will be collected by GC.
            break;
        }
    }

    // Cleanup.
    free(locals);
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
        case ALLOC_VALUE:
            // All fields are managed by GC.
            free(alloc);
            break;
        }
        alloc = next;
    }
}

struct value *prim_addint32(struct value *x, struct value *y) {
    return allocate_int32(int32_value(x) + int32_value(y));
}

struct value *prim_subint32(struct value *x, struct value *y) {
    return allocate_int32(int32_value(x) - int32_value(y));
}

struct value *prim_mulint32(struct value *x, struct value *y) {
    return allocate_int32(int32_value(x) * int32_value(y));
}

// vim: set et sts=4 sw=4:
