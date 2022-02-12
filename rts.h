#ifndef __RTS_H__
#define __RTS_H__

#include <stdint.h>
#include <stdlib.h>

enum allocation_type {
    ALLOC_FUN,
    ALLOC_CONT,
    ALLOC_VALUE,
};

struct alloc_header {
    enum allocation_type type;
    uint32_t mark;
    struct alloc_header *next;
};

// int32#, nil, pair, inl, or inr
struct value {
    struct alloc_header header;
    // TODO: Other value types.
    // TODO: Specialized value layouts based on type? (Overlaps with smarter
    // calling conventions)
    // (That is, a function that accepts an 'Int32' should only have variants
    // for the 'Int32#' constructor; a function that returns 'Either a b'
    // should only have 'inl' and 'inr' variants, etc, etc.)
    int32_t int_value;
};

struct value *allocate_int32(int32_t x);
int32_t int32_value(struct value *v); // partial

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

#endif
