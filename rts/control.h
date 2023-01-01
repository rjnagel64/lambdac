#ifndef __CONTROL_H__
#define __CONTROL_H__

#include <stdbool.h>

#include "alloc.h"

bool has_halted(void);
void halt_with(struct alloc_header *x);
struct alloc_header *get_result_value(void);

extern char *argument_data;
extern void (*next_entry_code)(void);
void init_args(void);
void destroy_args(void);
void reserve_args(size_t arguments_size);
void set_next(void (*enter)(void), void (*trace_args)(void));

#endif
