
#include "control.h"
#include "alloc.h"

void (*trace_roots)(void) = mark_root;

void mark_root(void) {
    mark_gray(AS_ALLOC(next_closure), closure_info);
    next_step->trace();
}

void halt_with(struct alloc_header *x, type_info info) {
    result_value = x;
    result_info = info;
}


static size_t value_capacity;
static size_t value_len;
static size_t info_capacity;
static size_t info_len;

void init_args(void) {
    value_capacity = 8;
    value_len = 0;
    value_args = malloc(value_capacity * sizeof(struct value_arg));
    info_capacity = 8;
    info_len = 0;
    info_args = malloc(info_capacity * sizeof(type_info));
}

void destroy_args(void) {
    free(value_args);
    value_args = NULL;
    free(info_args);
    info_args = NULL;
}

void reserve_args(size_t num_values, size_t num_infos) {
    if (num_values > value_capacity) {
        while (num_values > value_capacity) {
            value_capacity *= 2;
        }
        value_args = realloc(value_args, value_capacity * sizeof(struct value_arg));
        value_len = num_values;
    }
    if (num_infos > info_capacity) {
        while (num_infos > info_capacity) {
            info_capacity *= 2;
        }
        info_args = realloc(info_args, info_capacity * sizeof(type_info));
        info_len = num_infos;
    }
}

void trace_args(void) {
    for (size_t i = 0; i < value_len; i++) {
        mark_gray(value_args[i].alloc, value_args[i].info);
    }
}
