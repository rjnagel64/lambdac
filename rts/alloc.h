#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

#include "string_buf.h" // Needed for type_info.display

struct alloc_header {
    uint32_t mark;
    struct alloc_header *next;
};

struct _type_info {
    void (*trace)(struct alloc_header *alloc);
    void (*display)(struct alloc_header *alloc, struct string_buf *sb);
};
typedef struct _type_info type_info;

#define AS_ALLOC(v) ((struct alloc_header *)(v))


void init_gc(void);
void destroy_gc(void);

// The 'locals' vector acts as an additional set of GC roots for values between
// 'suspend' calls. When suspending, this vector is cleared.
void reset_locals(void);

extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc, type_info info);
void sweep_all_allocations(void);
void cons_new_alloc(struct alloc_header *alloc, type_info info);

#endif
