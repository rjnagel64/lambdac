
#include "control.h"
#include "panic.h"
#include "alloc.h"

void mark_root(void) {
    next_step->trace();
}

void halt_with(struct alloc_header *x) {
    result_value = x;
}

void enter_call(void) {
    struct fun_thunk *next = (struct fun_thunk *)next_step;
    next->fun->code(next->fun->env, next->arg, next->kont);
}

void trace_call(void) {
    struct fun_thunk *next = (struct fun_thunk *)next_step;
    trace_fun(next->fun);
    trace_cont(next->kont);
    trace_alloc(next->arg);
}

void suspend_call(struct fun *f, struct alloc_header *x, struct cont *k) {
    struct fun_thunk *next = realloc(next_step, sizeof(struct fun_thunk));
    next->header.enter = enter_call;
    next->header.trace = trace_call;
    next->fun = f;
    next->arg = x;
    next->kont = k;
    next_step = (struct thunk *)next;
}

void enter_jump(void) {
    struct cont_thunk *next = (struct cont_thunk *)next_step;
    next->kont->code(next->kont->env, next->arg);
}

void trace_jump(void) {
    struct cont_thunk *next = (struct cont_thunk *)next_step;
    trace_cont(next->kont);
    trace_alloc(next->arg);
}

void suspend_jump(struct cont *k, struct alloc_header *x) {
    struct cont_thunk *next = realloc(next_step, sizeof(struct cont_thunk));
    next->header.enter = enter_jump;
    next->header.trace = trace_jump;
    next->arg = x;
    next->kont = k;
    next_step = (struct thunk *)next;
}

// In the future, with many-branched switches and/or other calling conventions,
// it probably will be necessary to inline this as part of function code
// generation.
void suspend_case(struct value *x, struct cont *k1, struct cont *k2) {
    switch (x->words[0]) {
    case 0:
        suspend_jump(k1, AS_ALLOC(x->words[1]));
        break;
    case 1:
        suspend_jump(k2, AS_ALLOC(x->words[1]));
        break;
    default:
        panic("invalid discriminant");
    }
}

