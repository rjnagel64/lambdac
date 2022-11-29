#ifndef __CONTROL_H__
#define __CONTROL_H__

#include <stdbool.h>

#include "alloc.h"

bool has_halted(void);
void halt_with(struct alloc_header *x, type_info info);
struct alloc_header *get_result_value(void);
type_info get_result_info(void);

extern char *argument_data;
extern type_info *argument_infos;
extern void (*next_entry_code)(void);
void init_args(void);
void destroy_args(void);
void reserve_args(size_t arguments_size, size_t num_infos);
void set_next(void (*enter)(void), void (*trace_args)(void));

#endif
