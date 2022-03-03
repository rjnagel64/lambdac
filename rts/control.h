#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

enum next_type {
    JUMP_NEXT,
    TAILCALL_NEXT,
    HALT_NEXT,
};

struct next_action {
    enum next_type type;
    struct fun *fun;
    struct alloc_header *arg;
    struct cont *kont;
};

// Next action to take. A GC root.
// This would be easier if each function returned the next step, instead.
struct next_action next_step;

void mark_root(void);

void control_jump(struct cont *k, struct alloc_header *x);
void control_call(struct fun *f, struct alloc_header *x, struct cont *k);
void control_halt(struct alloc_header *x);
void control_case(struct value *x, struct cont *k1, struct cont *k2);

#define JUMP(k, x) { control_jump(k, x); return; }
#define TAILCALL(f, x, k) { control_call(f, x, k); return; }
#define HALT(x) { control_halt(x); return; }
#define CASE(x, k1, k2) { control_case(x, k1, k2); return; }


#endif
