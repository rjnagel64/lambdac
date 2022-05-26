#ifndef __ALLOC_H__
#define __ALLOC_H__

#include <stdint.h>
#include <stdlib.h>

#include "string_buf.h"

// Hmm. What if ALLOC_INFORMED, for things that have had their fields traced
// already (through some external type info, such as a closure environment)
//
// Then, pair this with 'void mark_gray_with_info(type_info info, void *alloc)'?
enum allocation_type {
    ALLOC_CLOSURE,
    ALLOC_CONST,
    ALLOC_BOOL,
    ALLOC_PROD,
    ALLOC_SUM,
    ALLOC_LIST,
};

struct alloc_header {
    enum allocation_type type;
    uint32_t mark;
    struct alloc_header *next;
};

struct _type_info {
    void (*trace)(struct alloc_header *alloc);
    void (*display)(struct alloc_header *alloc, struct string_buf *sb);
};
typedef struct _type_info type_info;

type_info any_info;

#define AS_ALLOC(v) ((struct alloc_header *)(v))

struct int64_value {
    struct alloc_header header;
    int64_t value;
};

type_info int64_value_info;

#define AS_INT64(v) ((struct int64_value *)(v))

struct closure {
    struct alloc_header header;
    // Note: 'void *env' and 'void (*trace)(void *env)' is effectively the
    // proposed type_info formulation of this stuff.
    // The 'trace_const' methods in alloc.c are almost type_info, but need to
    // take 'void *' as argument.
    //
    // Hmm. Can't quite just have 'type_info env_info', because the environment
    // is not managed by the GC, even though we trace through it.
    void *env;
    void (*trace)(void *env);
    void (*code)(void);
    void (*enter)(void);
};

type_info closure_info;

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

struct product {
    struct alloc_header header;
    uint32_t num_fields;
    uintptr_t words[];
};

#define AS_PRODUCT(v) ((struct product *)(v))

struct list {
    struct alloc_header header;
    uint32_t discriminant;
};

struct nil {
    struct list header;
};

struct cons {
    struct list header;
    // Hmm. I guess I need to have info for every element.
    // Annoying, but manageable.
    type_info head_info;
    struct alloc_header *head;
    struct list *tail;
};

type_info list_info;

#define AS_LIST(v) ((struct list *)(v))
#define AS_LIST_NIL(v) ((struct nil *)(v))
#define AS_LIST_CONS(v) ((struct cons *)(v))


void init_locals(void);
void destroy_locals(void);
void reset_locals(void);

extern void (*trace_roots)(void);
void mark_gray(struct alloc_header *alloc, type_info info);
void sweep_all_allocations(void);
void cons_new_alloc(struct alloc_header *alloc, type_info info);

struct closure *allocate_closure(void *env, void (*trace)(void *env), void (*code)(void), void (*enter)(void));
struct sum *allocate_inl(struct alloc_header *v, type_info info);
struct sum *allocate_inr(struct alloc_header *v, type_info info);
// Corresponds to Int64# constructor? No discriminant, though.
struct int64_value *allocate_int64(int64_t x);
struct bool_value *allocate_true(void);
struct bool_value *allocate_false(void);
struct list *allocate_nil(void);
struct list *allocate_cons(struct alloc_header *x, type_info info, struct list *xs);


#endif
