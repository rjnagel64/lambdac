
#include "control.h"
#include "alloc.h"

void mark_root(void) {
    next_step->trace();
}

void halt_with(struct alloc_header *x) {
    result_value = x;
}

