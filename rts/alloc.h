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

struct constant {
    struct alloc_header header;
    uintptr_t value;
};

#define AS_CONST(v) ((struct constant *)(v))

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

struct product {
    struct alloc_header header;
    uint32_t num_fields;
    uintptr_t words[];
};

#define AS_PRODUCT(v) ((struct product *)(v))


extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc);
void sweep_all_allocations(void);

struct closure *allocate_closure(void *env, void (*trace)(void *env), void (*code)(void));
struct product *allocate_pair(struct alloc_header *x, struct alloc_header *y);
struct sum *allocate_inl(struct alloc_header *v);
struct sum *allocate_inr(struct alloc_header *v);
// Corresponds to Int32# constructor? No discriminant, though.
struct constant *allocate_int32(int32_t x);
struct product *allocate_nil(void);
struct sum *allocate_true(void);
struct sum *allocate_false(void);

struct alloc_header *project_fst(struct product *v);
struct alloc_header *project_snd(struct product *v);
int32_t int32_value(struct constant *v);


#endif
