#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

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

#define AS_ALLOC(v) ((struct alloc_header *)(v))

void init_locals(void);
void destroy_locals(void);
void reset_locals(void);

// TODO: This representation with variable number of fields is getting somewhat inconvenient.
// Replace it with 'struct pair_value', 'struct sum_value', 'struct int_value', etc.
struct value {
    struct alloc_header header;
    // Count of words is not necessary? In-bounds access of fields is
    // guaranteed by static typing. (Might be necessary for GC.)
    uintptr_t words[];
};

#define AS_VALUE(v) ((struct value *)(v))

struct closure {
    struct alloc_header header;
    void *env;
    void (*trace)(void *env);
    void (*code)(void);
};

#define AS_CLOSURE(v) ((struct closure *)(v))

struct sum {
    struct alloc_header header;
    uint32_t discriminant;
    uint32_t num_fields;
    uintptr_t words[];
};

#define AS_SUM(v) ((struct sum *)(v))


extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc);
void sweep_all_allocations(void);

struct closure *allocate_closure(void *env, void (*trace)(void *env), void (*code)(void));
struct value *allocate_pair(struct alloc_header *x, struct alloc_header *y);
struct sum *allocate_inl(struct alloc_header *v);
struct sum *allocate_inr(struct alloc_header *v);
// Corresponds to Int32# constructor? No discriminant, though.
struct value *allocate_int32(int32_t x);
struct value *allocate_nil(void);
struct sum *allocate_true(void);
struct sum *allocate_false(void);

// TODO: Restrict project_{fst,snd} to struct pair_value *?
struct alloc_header *project_fst(struct value *v);
struct alloc_header *project_snd(struct value *v);
int32_t int32_value(struct value *v); // partial


#endif
