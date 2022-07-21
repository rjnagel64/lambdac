#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

#include "string_buf.h"

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

struct int64_value {
    struct alloc_header header;
    int64_t value;
};

type_info int64_value_info;

#define AS_INT64(v) ((struct int64_value *)(v))

struct closure {
    struct alloc_header header;
    struct alloc_header *env;
    type_info env_info;
    void (*enter)(void);
};

type_info closure_info;

void display_env(struct alloc_header *alloc, struct string_buf *sb);

#define AS_CLOSURE(v) ((struct closure *)(v))

struct sum {
    struct alloc_header header;
    uint32_t discriminant;
    type_info info;
    struct alloc_header *payload;
};

type_info sum_info;

#define AS_SUM(v) ((struct sum *)(v))
#define AS_SUM_INL(v) (v)
#define AS_SUM_INR(v) (v)

struct bool_value {
    struct alloc_header header;
    uint8_t discriminant;
};

type_info bool_value_info;

#define AS_BOOL(v) ((struct bool_value *)(v))
#define AS_BOOL_FALSE(v) (v)
#define AS_BOOL_TRUE(v) (v)

struct pair {
    struct alloc_header header;
    type_info fst_info;
    type_info snd_info;
    struct alloc_header *fst;
    struct alloc_header *snd;
};

type_info pair_info;

#define AS_PAIR(v) ((struct pair *)(v))

struct unit {
    struct alloc_header header;
};

type_info unit_info;

#define AS_UNIT(v) ((struct unit *)(v))

struct list {
    struct alloc_header header;
    uint32_t discriminant;
};

struct list_nil {
    struct list header;
};

struct list_cons {
    struct list header;
    // Hmm. I guess I need to have info for every element.
    // Annoying, but manageable.
    type_info head_info;
    struct alloc_header *head;
    struct list *tail;
};

type_info list_info;

#define AS_LIST(v) ((struct list *)(v))
#define AS_LIST_NIL(v) ((struct list_nil *)(v))
#define AS_LIST_CONS(v) ((struct list_cons *)(v))


void init_locals(void);
void destroy_locals(void);
void reset_locals(void);

extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc, type_info info);
void sweep_all_allocations(void);
void cons_new_alloc(struct alloc_header *alloc, type_info info);

struct closure *allocate_closure(struct alloc_header *env, type_info env_info, void (*enter)(void));
struct sum *allocate_inl(struct alloc_header *v, type_info info);
struct sum *allocate_inr(struct alloc_header *v, type_info info);
// Corresponds to Int64# constructor? No discriminant, though.
struct int64_value *allocate_int64(int64_t x);
struct bool_value *allocate_true(void);
struct bool_value *allocate_false(void);
struct list *allocate_list_nil(void);
struct list *allocate_list_cons(struct alloc_header *x, type_info info, struct list *xs);

struct pair *allocate_pair(type_info a_info, type_info b_info, struct alloc_header *x, struct alloc_header *y);
struct unit *allocate_unit(void);

#endif
