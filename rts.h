#ifndef __RTS_H__
#define __RTS_H__

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

// int32#, nil, pair, inl, or inr
// struct value {
//     struct alloc_header header;
//     // TODO: Other value types.
//     // TODO: Specialized value layouts based on type? (Overlaps with smarter
//     // calling conventions)
//     // (That is, a function that accepts an 'Int32' should only have variants
//     // for the 'Int32#' constructor; a function that returns 'Either a b'
//     // should only have 'inl' and 'inr' variants, etc, etc.)
//     int32_t int_value;
// };

// New value layout:
// inl x is [hdr|0|&x],
// inr y in [hdr|1|&y],
// (x, y) is [hdr|&x|&y],
// () is [hdr|0],
// n is [hdr|0|n]
// Other sums and products proceed in analogous manner.
// No unboxed sums, though?
//
// TODO: Figure out how to trace these. (number & location of GC fields)
// (CHICKEN has different allocation types for 'GC all fields' 'GC all but
// first', 'GC none', etc.)
// (GHC has info tables, value carries pointer to info table?)
//
// TODO: Currently, pairs cannot contain functions. To fix this, I think I need to move to the info-table version of things.
struct value {
    struct alloc_header header;
    // uint32_t discriminant;
    // Count of words is not necessary? In-bounds access of fields is
    // guaranteed by static typing. (Might be necessary for GC.)
    uintptr_t words[]; // TODO: Rename this to cells?
};

struct value *allocate_int32(int32_t x); // Corresponds to Int32# constructor.
int32_t int32_value(struct value *v); // partial

struct value *allocate_pair(struct value *x, struct value *y);
struct value *project_fst(struct value *v);
struct value *project_snd(struct value *v);

// TODO: true, false, and nil are truly constant. Return a single shared
// instance of them?
struct value *allocate_nil(void);
struct value *allocate_true(void);
struct value *allocate_false(void);
struct value *allocate_inl(struct value *v);
struct value *allocate_inr(struct value *v);

struct cont {
    struct alloc_header header;
    struct env_header *env;
    void (*code)(void *env, struct value *arg);
    void (*trace_env)(void *env);
};

struct fun {
    struct alloc_header header;
    struct env_header *env;
    void (*code)(void *env, struct value *arg, struct cont *kont);
    void (*trace_env)(void *env);
};

void trace_value(struct value *v);
void trace_fun(struct fun *f);
void trace_cont(struct cont *k);

static struct cont *halt;

struct cont *allocate_cont(
        void *env,
        void (*code)(void *env, struct value *arg),
        void (*trace_env)(void *env));
struct fun *allocate_fun(
        void *env,
        void (*code)(void *env, struct value *arg, struct cont *kont),
        void (*trace_env)(void *env));

static uint64_t num_locals = 0;
void allocate_locals(size_t count);
void store_local(size_t i, struct alloc_header *alloc);

void control_jump(struct cont *k, struct value *x);
void control_call(struct fun *f, struct value *x, struct cont *k);
void control_halt(struct value *x);

#define JUMP(k, x) { control_jump(k, x); return; }
#define TAILCALL(f, x, k) { control_call(f, x, k); return; }
#define HALT(x) { control_halt(x); return; }

struct value *prim_addint32(struct value *x, struct value *y);
struct value *prim_subint32(struct value *x, struct value *y);
struct value *prim_mulint32(struct value *x, struct value *y);
struct value *prim_iszero(struct value *x);

#endif
