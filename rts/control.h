#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

struct thunk {
    void (*enter)(void);
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

void reserve_args(size_t num_values, size_t num_infos);
void trace_args(struct args *args);

#endif
