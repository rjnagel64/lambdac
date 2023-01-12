#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct int64_value {
    struct alloc_header header;
    int64_t value;
};

// Corresponds to Int64# constructor? No discriminant, though.
struct int64_value *allocate_int64(int64_t x);

#define CAST_INT64(v) ((struct int64_value *)(v))

struct closure {
    struct alloc_header header;
    struct alloc_header *env;
    void (*enter)(void);
};

// Public b/c generated code needs to define info for environment types.
void display_env(struct alloc_header *alloc, struct string_buf *sb);

struct closure *allocate_closure(struct alloc_header *env, void (*enter)(void));

#define CAST_CLOSURE(v) ((struct closure *)(v))

struct sum {
    struct alloc_header header;
    uint32_t discriminant;
    struct alloc_header *payload;
};

struct sum *allocate_inl(struct alloc_header *v);
struct sum *allocate_inr(struct alloc_header *v);

#define CAST_SUM(v) ((struct sum *)(v))
#define CAST_SUM_INL(v) (v)
#define CAST_SUM_INR(v) (v)

struct bool_value {
    struct alloc_header header;
    uint8_t discriminant;
};

struct bool_value *allocate_true(void);
struct bool_value *allocate_false(void);

#define CAST_BOOL(v) ((struct bool_value *)(v))
#define CAST_BOOL_FALSE(v) (v)
#define CAST_BOOL_TRUE(v) (v)

struct pair {
    struct alloc_header header;
    struct alloc_header *fst;
    struct alloc_header *snd;
};

struct pair *allocate_pair(struct alloc_header *x, struct alloc_header *y);

#define CAST_PAIR(v) ((struct pair *)(v))

struct unit {
    struct alloc_header header;
};

struct unit *allocate_unit(void);

#define CAST_UNIT(v) ((struct unit *)(v))

struct list {
    struct alloc_header header;
    uint32_t discriminant;
};

struct list_nil {
    struct list header;
};

struct list_cons {
    struct list header;
    struct alloc_header *head;
    struct list *tail;
};

struct list *allocate_list_nil(void);
struct list *allocate_list_cons(struct alloc_header *x, struct list *xs);

#define CAST_LIST(v) ((struct list *)(v))
#define CAST_LIST_NIL(v) ((struct list_nil *)(v))
#define CAST_LIST_CONS(v) ((struct list_cons *)(v))

struct string_value {
    struct alloc_header header;
    uint64_t len;
    // Note: I use a flexible array member here, rather than having 'char
    // *contents' because GC values cannot take ownership of their fields.
    // More specifically, because I do not have a notion of GC finalizers, I
    // cannot free that 'char *contents' upon collection of this
    // 'string_value', which would lead to a memory leak.
    //
    // One consequence of using a flexible array member is that it isn't easy
    // to resize the contents of a 'string_value'. However, all strings are
    // immutable, so that is a non-issue.
    char contents[];
};

struct string_value *allocate_string(char *contents);

#define CAST_STRING(v) ((struct string_value *)(v))

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

// Primitive operators on strings
struct string_value *prim_concatenate(struct string_value *x, struct string_value *y);
struct int64_value *prim_strlen(struct string_value *x);

#endif
