#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

// TODO: Use uniform arrays for value and info arguments
// This allows us to not generate 'thunk_*' types, not generate 'trace_*'
// methods, and do less pointer-casting overall. 'mark_root' also becomes less
// necessary.
struct thunk {
    void (*enter)(void);
    void (*trace)(void);
    struct args *args;
};

// Next action to take. A GC root. A delayed function/continuation application.
struct thunk *next_step;
struct closure *next_closure;
void mark_root(void);

struct alloc_header *result_value;
type_info result_info;
void halt_with(struct alloc_header *x, type_info info);

struct value_arg {
    struct alloc_header *alloc;
    type_info info;
};

struct args {
    size_t num_values;
    size_t num_infos;
    struct value_arg *values;
    type_info *infos;
};

struct args *make_args(size_t num_values, size_t num_infos);
// TODO: Destroy old arguments when suspending new closure
// (Or realloc args->values, args->infos)
void destroy_args(struct args *args);
void trace_args(struct args *args);

#endif
