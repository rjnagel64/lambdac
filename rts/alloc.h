#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

#include "string_buf.h" // Needed for type_info.display

// Forward declaration, because type_info accepts alloc_header argument, while
// alloc_header contains type_info.
struct alloc_header;

struct _type_info {
    void (*trace)(struct alloc_header *alloc);
    void (*display)(struct alloc_header *alloc, struct string_buf *sb);
};
typedef struct _type_info type_info;

// Every GC-managed value contains a 'struct alloc_header header;' as its first
// field.
//
// The header contains an integer mark (for mark-sweep), a pointer to the next
// allocation (for precise sweeping), and an info table that tells how to trace
// the value.
//
// TODO: alloc_header.info should be a pointer, so that I can have static
// and/or constant info tables shared across many values.
struct alloc_header {
    uint32_t mark;
    struct alloc_header *next;
    type_info info;
};

#define AS_ALLOC(v) ((struct alloc_header *)(v))


void init_gc(void);
void destroy_gc(void);

// The 'locals' vector acts as an additional set of GC roots for values between
// 'suspend' calls. When suspending, this vector is cleared.
void reset_locals(void);

extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc);
void sweep_all_allocations(void);
void cons_new_alloc(struct alloc_header *alloc, type_info info);

#endif
