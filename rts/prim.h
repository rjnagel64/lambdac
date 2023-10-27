#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct int64_value {
    struct alloc_header header;
    int64_t value;
};

// Corresponds to Int64# constructor?
struct int64_value *allocate_int64(int64_t x);

#define CAST_INT64(v) ((struct int64_value *)(v))

struct bool_value {
    struct alloc_header header;
    uint8_t value;
};

struct bool_value *allocate_bool_value(uint8_t x);

#define CAST_BOOL(v) ((struct bool_value *)(v))

struct char_value {
    struct alloc_header header;
    uint32_t value;
};

struct char_value *allocate_char(uint32_t x);

#define CAST_CHAR(v) ((struct char_value *)(v))

struct code {
    void (*enter)(void);
};

struct closure {
    struct alloc_header header;
    struct alloc_header *env;
    struct code code;
};

struct closure *allocate_closure(struct alloc_header *env, struct code code);

#define CAST_CLOSURE(v) ((struct closure *)(v))

struct empty_env {
    struct alloc_header header;
};

// Public b/c generated code needs to define info for environment types.
void display_env(struct alloc_header *alloc, struct string_buf *sb);

extern struct empty_env *the_empty_env;

#define CAST_EMPTY_ENV(v) ((struct empty_env *)(v))

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

// Note: Why 'string_value' uses a flexible array member
//
// The obvious representation of a string (a length and a pointer to the
// contents) does not work well with my GC design.
//
// The essential problem is that when a 'string_value' is freed, it must also
// release the memory for its contents. I do not have a notion of GC
// finalizers, nor do I have means to special-case the 'type_info' for
// 'string_value'.
//
// Consequently, the contents of the string must be kept in the same allocation
// as the 'string_value' itself: using a flexible array member.
//
// One consequence of this is that if I needed to mutate or grow the contents
// of a 'string_value', I would run into issues, but all strings are immutable,
// so that is a non-issue.

// Invariants:
// * .contents is an array of (.len + 1) characters
// * .len == strlen(.contents)
// * .contents[.len] == '\0' (I.E., .contents is null-terminated)
// * .contents contains well-formed ASCII data
//   (Note: I should eventually make this UTF-8 data instead.)
struct string_value {
    struct alloc_header header;
    uint64_t len;
    char contents[];
};

struct string_value *allocate_string(const char *src, size_t len);

#define CAST_STRING(v) ((struct string_value *)(v))

struct token {
    struct alloc_header header;
};

struct token *allocate_token(void);

#define CAST_TOKEN(v) ((struct token *)(v))

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

struct bool_value *prim_eqchar(struct char_value *x, struct char_value *y);

// Primitive operators on strings
struct string_value *prim_concatenate(struct string_value *x, struct string_value *y);
struct int64_value *prim_strlen(struct string_value *x);
struct char_value *prim_strindex(struct string_value *x, struct int64_value *idx);

// IO primitives
// Note: I/O primitives desperately need better error handling strategies.
void prim_getLine(struct token *x, struct token **out_x, struct string_value **out_y);
void prim_putLine(struct token *x, struct string_value *msg, struct token **out_x, struct unit **out_y);

// runtime_error# : forall (a : *). string -> a
struct alloc_header *prim_runtime_error(struct string_value *msg);

#endif
