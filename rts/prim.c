
#include "prim.h"

#include "alloc.h"

#include <stdio.h> // sprintf for display_int64_value
#include <string.h>

void trace_int64_value(struct alloc_header *alloc) {
}

void display_int64_value(struct alloc_header *alloc, struct string_buf *sb) {
    // int64_t can have ~20 decimal digits, plus sign, so use a 32-byte buffer.
    static char buf[32];
    struct int64_value *v = CAST_INT64(alloc);
    int64_t value = (int64_t)v->value;
    sprintf(buf, "%lld", value);
    string_buf_push(sb, buf);
}

const type_info int64_value_info = { trace_int64_value, display_int64_value };

struct int64_value *allocate_int64(int64_t x) {
    struct int64_value *v = malloc(sizeof(struct int64_value));
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v), &int64_value_info);
    return v;
}

void trace_closure(struct alloc_header *alloc) {
    struct closure *cl = CAST_CLOSURE(alloc);
    mark_gray(AS_ALLOC(cl->env));
}

void display_closure(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "<closure>");
}

const type_info closure_info = { trace_closure, display_closure };

void display_env(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "<env>");
}

struct closure *allocate_closure(
        struct alloc_header *env,
        void (*enter)(void)) {
    struct closure *cl = malloc(sizeof(struct closure));
    cl->env = env;
    cl->enter = enter;

    cons_new_alloc(AS_ALLOC(cl), &closure_info);
    return cl;
}

void trace_sum(struct alloc_header *alloc) {
    struct sum *v = CAST_sum(alloc);
    mark_gray(v->payload);
}

void display_sum(struct alloc_header *alloc, struct string_buf *sb) {
    struct sum *v = CAST_sum(alloc);
    switch (v->discriminant) {
    case 0:
        string_buf_push(sb, "inl ");
        v->payload->info->display(v->payload, sb);
        break;
    case 1:
        string_buf_push(sb, "inr ");
        v->payload->info->display(v->payload, sb);
        break;
    }
}

const type_info sum_info = { trace_sum, display_sum };

struct sum *allocate_sum_inl(struct alloc_header *x) {
    struct sum *v = malloc(sizeof(struct sum));
    v->discriminant = 0;
    v->payload = x;

    cons_new_alloc(AS_ALLOC(v), &sum_info);
    return v;
}

struct sum *allocate_sum_inr(struct alloc_header *y) {
    struct sum *v = malloc(sizeof(struct sum));
    v->discriminant = 1;
    v->payload = y;

    cons_new_alloc(AS_ALLOC(v), &sum_info);
    return v;
}

void trace_bool_value(struct alloc_header *alloc) {
}

void display_bool_value(struct alloc_header *alloc, struct string_buf *sb) {
    struct vbool *v = CAST_vbool(alloc);
    if (v->discriminant) {
        string_buf_push(sb, "true");
    } else {
        string_buf_push(sb, "false");
    }
}

const type_info bool_value_info = { trace_bool_value, display_bool_value };

struct vbool *allocate_vbool_true(void) {
    struct vbool *v = malloc(sizeof(struct vbool));
    v->discriminant = 1;

    cons_new_alloc(AS_ALLOC(v), &bool_value_info);
    return v;
}

struct vbool *allocate_vbool_false(void) {
    struct vbool *v = malloc(sizeof(struct vbool));
    v->discriminant = 0;

    cons_new_alloc(AS_ALLOC(v), &bool_value_info);
    return v;
}

void trace_pair(struct alloc_header *alloc) {
    struct pair *p = CAST_PAIR(alloc);
    mark_gray(p->fst);
    mark_gray(p->snd);
}

void display_pair(struct alloc_header *alloc, struct string_buf *sb) {
    struct pair *p = CAST_PAIR(alloc);
    string_buf_push(sb, "(");
    p->fst->info->display(p->fst, sb);
    string_buf_push(sb, ", ");
    p->snd->info->display(p->snd, sb);
    string_buf_push(sb, ")");
}

const type_info pair_info = { trace_pair, display_pair };

struct pair *allocate_pair(struct alloc_header *x, struct alloc_header *y) {
    struct pair *p = malloc(sizeof(struct pair));
    p->fst = x;
    p->snd = y;
    cons_new_alloc(AS_ALLOC(p), &pair_info);
    return p;
}

void trace_unit(struct alloc_header *alloc) {
}

void display_unit(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "()");
}

const type_info unit_info = { trace_unit, display_unit };

struct unit *allocate_unit(void) {
    struct unit *n = malloc(sizeof(struct unit));
    cons_new_alloc(AS_ALLOC(n), &unit_info);
    return n;
}

void trace_string(struct alloc_header *alloc) {
}

void display_string(struct alloc_header *alloc, struct string_buf *sb) {
    // Actually, since 'display' is supposed to emit a debug representation of
    // the value, this should add quotes and maybe do escaping.
    struct string_value *s = CAST_STRING(alloc);
    string_buf_push(sb, "\"");
    string_buf_push(sb, s->contents);
    string_buf_push(sb, "\"");
}

const type_info string_info = { trace_string, display_string };

struct string_value *allocate_string(char *contents) {
    uint64_t len = strlen(contents);
    struct string_value *s = malloc(sizeof(struct string_value) + len * sizeof(char));
    memcpy(s->contents, contents, len+1); // Include null terminator.
    cons_new_alloc(AS_ALLOC(s), &string_info);
    return s;
}

void trace_token(struct alloc_header *alloc) {
}

void display_token(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "WORLD#");
}

const type_info token_info = { trace_token, display_token };

struct token *allocate_token(void) {
    struct token *n = malloc(sizeof(struct token));
    cons_new_alloc(AS_ALLOC(n), &token_info);
    return n;
}

struct int64_value *prim_addint64(struct int64_value *x, struct int64_value *y) {
    return allocate_int64(x->value + y->value);
}

struct int64_value *prim_subint64(struct int64_value *x, struct int64_value *y) {
    return allocate_int64(x->value - y->value);
}

struct int64_value *prim_mulint64(struct int64_value *x, struct int64_value *y) {
    return allocate_int64(x->value * y->value);
}

struct int64_value *prim_negint64(struct int64_value *x) {
    return allocate_int64(-x->value);
}

struct vbool *prim_eqint64(struct int64_value *x, struct int64_value *y) {
    if (x->value == y->value) {
        return allocate_vbool_true();
    } else {
        return allocate_vbool_false();
    }
}

struct vbool *prim_neint64(struct int64_value *x, struct int64_value *y) {
    if (x->value != y->value) {
        return allocate_vbool_true();
    } else {
        return allocate_vbool_false();
    }
}

struct vbool *prim_ltint64(struct int64_value *x, struct int64_value *y) {
    if (x->value < y->value) {
        return allocate_vbool_true();
    } else {
        return allocate_vbool_false();
    }
}

struct vbool *prim_leint64(struct int64_value *x, struct int64_value *y) {
    if (x->value <= y->value) {
        return allocate_vbool_true();
    } else {
        return allocate_vbool_false();
    }
}

struct vbool *prim_gtint64(struct int64_value *x, struct int64_value *y) {
    if (x->value > y->value) {
        return allocate_vbool_true();
    } else {
        return allocate_vbool_false();
    }
}

struct vbool *prim_geint64(struct int64_value *x, struct int64_value *y) {
    if (x->value >= y->value) {
        return allocate_vbool_true();
    } else {
        return allocate_vbool_false();
    }
}

struct string_value *prim_concatenate(struct string_value *x, struct string_value *y) {
    struct string_buf *sb = string_buf_new();
    string_buf_push(sb, x->contents);
    string_buf_push(sb, y->contents);
    char *contents = string_buf_contents(sb); // Non-owning reference
    struct string_value *s = allocate_string(contents); // Copy contents into new string.
    string_buf_destroy(sb); // Destroy temporary buffer.
    return s;
}

struct int64_value *prim_strlen(struct string_value *x) {
    return allocate_int64(x->len);
}
