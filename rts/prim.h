#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct int64_value {
    struct alloc_header header;
    int64_t value;
};

type_info int64_value_info;

// Corresponds to Int64# constructor? No discriminant, though.
struct int64_value *allocate_int64(int64_t x);

#define AS_INT64(v) ((struct int64_value *)(v))

struct closure {
    struct alloc_header header;
    struct alloc_header *env;
    type_info env_info;
    void (*enter)(void);
};

type_info closure_info;

// Public b/c generated code needs to define info for environment types.
void display_env(struct alloc_header *alloc, struct string_buf *sb);

struct closure *allocate_closure(struct alloc_header *env, type_info env_info, void (*enter)(void));

#define AS_CLOSURE(v) ((struct closure *)(v))

struct sum {
    struct alloc_header header;
    uint32_t discriminant;
    type_info info;
    struct alloc_header *payload;
};

type_info sum_info;

struct sum *allocate_inl(struct alloc_header *v, type_info info);
struct sum *allocate_inr(struct alloc_header *v, type_info info);

#define AS_SUM(v) ((struct sum *)(v))
#define AS_SUM_INL(v) (v)
#define AS_SUM_INR(v) (v)

struct bool_value {
    struct alloc_header header;
    uint8_t discriminant;
};

type_info bool_value_info;

struct bool_value *allocate_true(void);
struct bool_value *allocate_false(void);

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

struct pair *allocate_pair(type_info a_info, type_info b_info, struct alloc_header *x, struct alloc_header *y);

#define AS_PAIR(v) ((struct pair *)(v))

struct unit {
    struct alloc_header header;
};

type_info unit_info;

struct unit *allocate_unit(void);

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

struct list *allocate_list_nil(void);
struct list *allocate_list_cons(struct alloc_header *x, type_info info, struct list *xs);

#define AS_LIST(v) ((struct list *)(v))
#define AS_LIST_NIL(v) ((struct list_nil *)(v))
#define AS_LIST_CONS(v) ((struct list_cons *)(v))

// TODO: Primitive values for strings.
// I considered doing something like
// struct string_value {
//     struct alloc_header header;
//     uint64_t len;
//     char *data;
// };
// However, freeing this is tricky in the type_info based setting.
// I would need to introduce some notion of a GC finalizer, basically.
// (More generally, a GC value cannot own its fields, all fields have to be
// either ignored by GC, or managed by GC.)
// I suppose this means I'll have to use a flexible array member thing?
// Could be worse, I guess.
// Fortunately, strings are immutable, so I don't have to worry about resizing them.

// Primitive operators on integers: arithmetic
struct int64_value *prim_addint64(struct int64_value *x, struct int64_value *y);
struct int64_value *prim_subint64(struct int64_value *x, struct int64_value *y);
struct int64_value *prim_mulint64(struct int64_value *x, struct int64_value *y);
struct int64_value *prim_negint64(struct int64_value *x);

// Primitive operators on integers: comparison
struct bool_value *prim_eqint64(struct int64_value *x, struct int64_value *y);
struct bool_value *prim_neint64(struct int64_value *x, struct int64_value *y);
struct bool_value *prim_ltint64(struct int64_value *x, struct int64_value *y);
struct bool_value *prim_leint64(struct int64_value *x, struct int64_value *y);
struct bool_value *prim_gtint64(struct int64_value *x, struct int64_value *y);
struct bool_value *prim_geint64(struct int64_value *x, struct int64_value *y);


#endif
