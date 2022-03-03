#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

struct thunk {
    void (*enter)(void);
    void (*trace)(void);
};

struct fun_thunk {
    struct thunk header;
    struct fun *fun;
    struct alloc_header *arg;
    struct cont *kont;
};

struct cont_thunk {
    struct thunk header;
    struct cont *kont;
    struct alloc_header *arg;
};

// Next action to take. A GC root. A delayed function/continuation application.
struct thunk *next_step;
void mark_root(void);

struct alloc_header *result_value;
void halt_with(struct alloc_header *x);

// There currently are built-in thunk types for `(alloc) -> Ans` (struct cont)
// and for `(alloc, (alloc) -> Ans) -> Ans` (struct fun).
// Eventually, the compiler should emit all necessary thunk types.
void suspend_jump(struct cont *k, struct alloc_header *x);
void suspend_call(struct fun *f, struct alloc_header *x, struct cont *k);
void suspend_case(struct value *x, struct cont *k1, struct cont *k2);

#define HALT(x) { halt_with(x); return; }
#define JUMP(k, x) { suspend_jump(k, x); return; }
#define TAILCALL(f, x, k) { suspend_call(f, x, k); return; }
#define CASE(x, k1, k2) { suspend_case(x, k1, k2); return; }

#endif
