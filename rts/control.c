
#include "control.h"
#include "panic.h"
#include "alloc.h"

void mark_root(void) {
    switch (next_step.type) {
    case TAILCALL_NEXT:
        trace_fun(next_step.fun);
        trace_cont(next_step.kont);
        trace_value(next_step.arg);
        break;
    case JUMP_NEXT:
        trace_cont(next_step.kont);
        trace_value(next_step.arg);
        break;
    case HALT_NEXT:
        trace_value(next_step.arg);
        break;
    }
}

void control_jump(struct cont *k, struct value *x) {
    next_step.type = JUMP_NEXT;
    next_step.fun = NULL;
    next_step.arg = x;
    next_step.kont = k;
}

void control_call(struct fun *f, struct value *x, struct cont *k) {
    next_step.type = TAILCALL_NEXT;
    next_step.fun = f;
    next_step.arg = x;
    next_step.kont = k;
}

void control_halt(struct value *x) {
    next_step.type = HALT_NEXT;
    next_step.fun = NULL;
    next_step.arg = x;
    next_step.kont = NULL;
}

void control_case(struct value *x, struct cont *k1, struct cont *k2) {
    next_step.type = JUMP_NEXT;
    next_step.fun = NULL;
    next_step.arg = (struct value *)x->words[1];
    switch (x->words[0]) {
    case 0:
        next_step.kont = k1;
        break;
    case 1:
        next_step.kont = k2;
        break;
    default:
        panic("invalid discriminant");
    }
}

