
#include "control.h"
#include "alloc.h"

void (*trace_roots)(void) = mark_root;

void mark_root(void) {
    mark_gray(AS_ALLOC(next_closure), closure_info);
    trace_args(next_step->args);
}

void halt_with(struct alloc_header *x, type_info info) {
    result_value = x;
    result_info = info;
}

void destroy_args(struct args *args) {
    if (args == NULL) {
        return;
    }
    free(args->values);
    free(args->infos);
    free(args);
}

void reserve_args(size_t num_values, size_t num_infos) {
    if (next_step->args == NULL) {
        next_step->args = malloc(sizeof(struct args));
    }
    // I could save the capacity and then only realloc when expanding, but I
    // don't really care.
    next_step->args->num_values = num_values;
    next_step->args->values = realloc(next_step->args->values, num_values * sizeof(struct value_arg));
    next_step->args->num_infos = num_infos;
    next_step->args->infos = realloc(next_step->args->infos, num_infos * sizeof(type_info));
}

void trace_args(struct args *args) {
    for (size_t i = 0; i < args->num_values; i++) {
        mark_gray(args->values[i].alloc, args->values[i].info);
    }
}
