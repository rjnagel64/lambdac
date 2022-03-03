#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

enum next_type {
    JUMP_NEXT,
    TAILCALL_NEXT,
};

struct next_action {
    enum next_type type;
    struct fun *fun;
    struct alloc_header *arg;
    struct cont *kont;
};

// Next action to take. A GC root. Basically a thunk: a delayed
// function/continuation application.
struct next_action next_step;
void mark_root(void);

struct alloc_header *result_value;
void halt_with(struct alloc_header *x);

void control_jump(struct cont *k, struct alloc_header *x);
void control_call(struct fun *f, struct alloc_header *x, struct cont *k);
void control_case(struct value *x, struct cont *k1, struct cont *k2);

#define HALT(x) { halt_with(x); return; }
#define JUMP(k, x) { control_jump(k, x); return; }
#define TAILCALL(f, x, k) { control_call(f, x, k); return; }
#define CASE(x, k1, k2) { control_case(x, k1, k2); return; }

#endif
