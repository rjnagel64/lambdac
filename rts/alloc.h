#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

// Hmm. What if ALLOC_INFORMED, for things that have had their fields traced
// already (through some external type info, such as a closure environment)
//
// Then, pair this with 'void mark_gray_with_info(type_info info, void *alloc)'?
enum allocation_type {
    ALLOC_CLOSURE,
    ALLOC_CONST,
    ALLOC_PROD,
    ALLOC_SUM,
};

struct alloc_header {
    enum allocation_type type;
    uint32_t mark;
    struct alloc_header *next;
};

void trace_alloc(struct alloc_header *alloc);

#define AS_ALLOC(v) ((struct alloc_header *)(v))

struct constant {
    struct alloc_header header;
    uintptr_t value;
};

void trace_constant(struct alloc_header *alloc);

#define AS_CONST(v) ((struct constant *)(v))

struct closure {
    struct alloc_header header;
    // Note: 'void *env' and 'void (*trace)(void *env)' is effectively the
    // proposed type_info formulation of this stuff.
    // The 'trace_const' methods in alloc.c are almost type_info, but need to
    // take 'void *' as argument.
    void *env;
    void (*trace)(void *env);
    void (*code)(void);
    void (*enter)(void);
};

void trace_closure(struct alloc_header *alloc);

#define AS_CLOSURE(v) ((struct closure *)(v))

struct sum {
    struct alloc_header header;
    uint32_t discriminant;
    uint32_t num_fields;
    uintptr_t words[];
};

void trace_sum(struct alloc_header *alloc);

#define AS_SUM(v) ((struct sum *)(v))

struct product {
    struct alloc_header header;
    uint32_t num_fields;
    uintptr_t words[];
};

void trace_product(struct alloc_header *alloc);

#define AS_PRODUCT(v) ((struct product *)(v))


void init_locals(void);
void destroy_locals(void);
void reset_locals(void);

extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc);
void mark_gray_with_info(struct alloc_header *alloc, void (*trace)(struct alloc_header *));
void sweep_all_allocations(void);
void cons_new_alloc(struct alloc_header *alloc);

struct closure *allocate_closure(void *env, void (*trace)(void *env), void (*code)(void), void (*enter)(void));
struct sum *allocate_inl(struct alloc_header *v);
struct sum *allocate_inr(struct alloc_header *v);
// Corresponds to Int64# constructor? No discriminant, though.
struct constant *allocate_int64(int64_t x);
struct sum *allocate_true(void);
struct sum *allocate_false(void);

int64_t int64_value(struct constant *v);


#endif
