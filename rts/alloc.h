#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

enum allocation_type {
    ALLOC_FUN,
    ALLOC_CONT,
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

// New value layout:
// inl x is [hdr|0|&x],
// inr y in [hdr|1|&y],
// (x, y) is [hdr|&x|&y],
// () is [hdr|0],
// n is [hdr|n]
// Other sums and products proceed in analogous manner.
// No unboxed sums, though?
//
// TODO: Figure out how to trace these. (number & location of GC fields)
// (CHICKEN has different allocation types for 'GC all fields' 'GC all but
// first', 'GC none', etc.)
// (GHC has info tables, value carries pointer to info table?)
//
// TODO: Currently, pairs cannot contain functions. To fix this, I need to
// merge 'struct fun' and 'struct cont' into 'struct value', having envp, code,
// trace being words[0], [1], and [2], I guess. Alternately, break each class
// of value out into its own struct, and use 'struct alloc_header *' as the
// type of generic values instead.
struct value {
    struct alloc_header header;
    // Count of words is not necessary? In-bounds access of fields is
    // guaranteed by static typing. (Might be necessary for GC.)
    uintptr_t words[];
};

#define AS_VALUE(v) ((struct value *)(v))

struct cont {
    struct alloc_header header;
    void *env;
    void (*code)(void *env, struct value *arg);
    void (*trace_env)(void *env);
};

#define AS_CONT(v) ((struct cont *)(v))

// TODO: Functions need to be a type of value, so I can have 'let f y h = ...; in k f'.
// I think I generally need to make closures take a `struct alloc_header *` as
// their argument, not `struct value *`.
struct fun {
    struct alloc_header header;
    void *env;
    void (*code)(void *env, struct value *arg, struct cont *kont);
    void (*trace_env)(void *env);
};

#define AS_FUN(v) ((struct fun *)(v))

void trace_value(struct value *v);
void trace_fun(struct fun *f);
void trace_cont(struct cont *k);

void (*trace_roots)(void);
void collect(void);
void sweep_all_allocations(void);

struct cont *allocate_cont(
        void *env,
        void (*code)(void *env, struct value *arg),
        void (*trace_env)(void *env));
struct fun *allocate_fun(
        void *env,
        void (*code)(void *env, struct value *arg, struct cont *kont),
        void (*trace_env)(void *env));

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
