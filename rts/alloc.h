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

void trace_value(struct value *v);
void trace_closure(struct closure *cl);
void trace_alloc(struct alloc_header *v);

extern void (*trace_roots)(void);
void collect(void);
void sweep_all_allocations(void);

struct closure *allocate_closure(void *env, void (*trace)(void *env), void (*code)(void));
// TODO: Make these take struct alloc_header * instead
// (This way, function and continuation closures can be stored in pairs and sums)
struct value *allocate_pair(struct value *x, struct value *y);
struct value *allocate_inl(struct value *v);
struct value *allocate_inr(struct value *v);
// Corresponds to Int32# constructor? No discriminant, though.
struct value *allocate_int32(int32_t x);
// TODO: true, false, and nil are truly constant. Return a single shared
// instance of them?
struct value *allocate_nil(void);
struct value *allocate_true(void);
struct value *allocate_false(void);

// TODO: Restrict project_{fst,snd} to struct pair_value *?
struct alloc_header *project_fst(struct value *v);
struct alloc_header *project_snd(struct value *v);
int32_t int32_value(struct value *v); // partial


#endif
