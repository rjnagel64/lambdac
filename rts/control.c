
#include "control.h"
#include "alloc.h"

void (*trace_roots)(void) = mark_root;

void mark_root(void) {
    next_step->trace();
}

void halt_with(struct alloc_header *x) {
    result_value = x;
}

