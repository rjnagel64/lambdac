
#include "control.h"

static struct alloc_header *result_value = NULL;

bool has_halted(void) {
    return result_value != NULL;
}

void halt_with(struct alloc_header *x) {
    result_value = x;
}

struct alloc_header *get_result_value(void) {
    return result_value;
}


static size_t argument_data_capacity;
char *argument_data;

void init_args(void) {
    // The argument_data array is initialized with enough capacity that
    // reallocations should be rare: 1KB for arguments.
    argument_data_capacity = 1024;
    argument_data = malloc(argument_data_capacity * sizeof(char));
}

void destroy_args(void) {
    free(argument_data);
    argument_data = NULL;
    argument_data_capacity = 0;
}

void reserve_args(size_t arguments_size) {
    if (arguments_size > argument_data_capacity) {
        argument_data = realloc(argument_data, arguments_size * sizeof(char));
        argument_data_capacity = arguments_size;
    }
}


void (*next_entry_code)(void);
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
void (*trace_roots)(void);

void set_next(void (*enter)(void), void (*trace_args)(void)) {
    next_entry_code = enter;
    trace_roots = trace_args;
}

