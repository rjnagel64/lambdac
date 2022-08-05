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
};

// Next action to take. A GC root. A delayed function/continuation application.
struct thunk *next_step;
void mark_root(void);

struct alloc_header *result_value;
type_info result_info;
void halt_with(struct alloc_header *x, type_info info);

struct value_arg {
    struct alloc_header *alloc;
    type_info info;
};
struct value_arg *value_args;
type_info *info_args;

void init_args(void);
void destroy_args(void);
void reserve_args(size_t num_values, size_t num_infos);
void trace_args(void);

#endif
