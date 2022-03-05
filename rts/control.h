#ifndef __CONTROL_H__
#define __CONTROL_H__

#include "alloc.h"

struct thunk {
    void (*enter)(void);
    void (*trace)(void);
};

// I'm pretty sure that these are doing UB right now.
// Basically, when I create a closure, I cast from void (*)(env, value) to
// void (*)(void) to void (*)(env, alloc) and then call it, which is UB.
// Yes. Compiling with optimizations produces a segfault.

// TODO: Emit these thunk types as part of Emit.hs
// More generally, emit thunk types appropriate to the closures used by the
// program.
struct fun_thunk {
    struct thunk header;
    struct closure *fun;
    struct alloc_header *arg;
    struct closure *kont;
};

struct cont_thunk {
    struct thunk header;
    struct closure *kont;
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
void suspend_jump(struct closure *k, struct alloc_header *x);
void suspend_call(struct closure *f, struct alloc_header *x, struct closure *k);

#define HALT(x) { halt_with(x); return; }
#define JUMP(k, x) { suspend_jump(k, x); return; }
#define TAILCALL(f, x, k) { suspend_call(f, x, k); return; }

#endif
