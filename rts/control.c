
#include "control.h"
#include "alloc.h"

void (*trace_roots)(void) = mark_root;

void mark_root(void) {
    next_step->trace();
}

void halt_with(struct alloc_header *x, type_info info) {
    result_value = x;
    result_info = info;
}

