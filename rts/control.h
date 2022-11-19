#ifndef __CONTROL_H__
#define __CONTROL_H__

#include <stdbool.h>

#include "alloc.h"

bool has_halted(void);
void halt_with(struct alloc_header *x, type_info info);
struct alloc_header *get_result_value(void);
type_info get_result_info(void);

// Next action to take. A GC root. A delayed function/continuation application.
extern struct thunk *next_step;
void mark_root(void);

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

struct thunk {
    void (*enter)(void);
    struct closure *closure;
    struct args args;
};

#endif
