#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

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

#endif
