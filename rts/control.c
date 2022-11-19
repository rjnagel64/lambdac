
#include "control.h"
#include "alloc.h"
#include "prim.h" // for closure_info

static struct alloc_header *result_value = NULL;
static type_info result_info;

bool has_halted(void) {
    return result_value != NULL;
}

void halt_with(struct alloc_header *x, type_info info) {
    result_value = x;
    result_info = info;
}

struct alloc_header *get_result_value(void) {
    return result_value;
}

type_info get_result_info(void) {
    return result_info;
}

// Note: the trace_roots function
// There is a circular dependency between 'alloc.c' and 'control.c'.
// Specifically, control.c needs to be able to allocate and collect memory
// using alloc.c, but alloc.c needs to know about the GC roots, such as the
// next thunk from control.c.
//
// The solution is that alloc.h marks the function (pointer) to trace the thunk
// as 'extern void (*trace_roots)(void)': a declaration, that can be included
// in multiple files without issue.
//
// Then, control.c *defines* 'trace_roots' exactly once, right here.
void (*trace_roots)(void) = mark_root;

void mark_root(void) {
    mark_gray(AS_ALLOC(next_step->closure), closure_info);
    for (size_t i = 0; i < next_step->args.num_values; i++) {
        mark_gray(next_step->args.values[i].alloc, next_step->args.values[i].info);
    }
}

struct thunk *next_step = NULL;

void reserve_args(size_t num_values, size_t num_infos) {
    // I could save the capacity and then only realloc when expanding, but I
    // don't really care.
    next_step->args.num_values = num_values;
    next_step->args.values = realloc(next_step->args.values, num_values * sizeof(struct value_arg));
    next_step->args.num_infos = num_infos;
    next_step->args.infos = realloc(next_step->args.infos, num_infos * sizeof(type_info));
}
