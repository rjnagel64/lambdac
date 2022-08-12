
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

struct args *make_args(size_t num_values, size_t num_infos) {
    struct args *args = malloc(sizeof(struct args));
    args->num_values = num_values;
    args->values = malloc(num_values * sizeof(struct value_arg));
    args->num_infos = num_infos;
    args->infos = malloc(num_infos * sizeof(type_info));
    return args;
}

void reserve_args(size_t num_values, size_t num_infos) {
    // TODO: Directly reallocate args
    destroy_args(next_step->args);
    next_step->args = make_args(num_values, num_infos);
}

void trace_args(struct args *args) {
    for (size_t i = 0; i < args->num_values; i++) {
        mark_gray(args->values[i].alloc, args->values[i].info);
    }
}
