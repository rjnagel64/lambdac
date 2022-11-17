
#include "prim.h"

#include "alloc.h"

#include <stdio.h> // sprintf for display_int64_value

void trace_int64_value(struct alloc_header *alloc) {
}

void display_int64_value(struct alloc_header *alloc, struct string_buf *sb) {
    // int64_t can have ~20 decimal digits, plus sign, so use a 32-byte buffer.
    static char buf[32];
    struct int64_value *v = AS_INT64(alloc);
    int64_t value = (int64_t)v->value;
    sprintf(buf, "%lld", value);
    string_buf_push(sb, buf);
}

type_info int64_value_info = { trace_int64_value, display_int64_value };

void trace_sum(struct alloc_header *alloc) {
    struct sum *v = AS_SUM(alloc);
    mark_gray(v->payload, v->info);
}

void display_sum(struct alloc_header *alloc, struct string_buf *sb) {
    struct sum *v = AS_SUM(alloc);
    switch (v->discriminant) {
    case 0:
        string_buf_push(sb, "inl ");
        v->info.display(v->payload, sb);
        break;
    case 1:
        string_buf_push(sb, "inr ");
        v->info.display(v->payload, sb);
        break;
    }
}

type_info sum_info = { trace_sum, display_sum };

void trace_bool_value(struct alloc_header *alloc) {
}

void display_bool_value(struct alloc_header *alloc, struct string_buf *sb) {
    struct bool_value *v = AS_BOOL(alloc);
    if (v->discriminant) {
        string_buf_push(sb, "true");
    } else {
        string_buf_push(sb, "false");
    }
}

type_info bool_value_info = { trace_bool_value, display_bool_value };

void trace_closure(struct alloc_header *alloc) {
    struct closure *cl = AS_CLOSURE(alloc);
    mark_gray(AS_ALLOC(cl->env), cl->env_info);
}

void display_closure(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "<closure>");
}

type_info closure_info = { trace_closure, display_closure };

void display_env(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "<env>");
}

void trace_list(struct alloc_header *alloc) {
    struct list *l = AS_LIST(alloc);
    switch (l->discriminant) {
    case 0:
        // nil
        {
        struct list_nil *n = AS_LIST_NIL(l);
        }
        break;
    case 1:
        // cons
        {
        struct list_cons *c = AS_LIST_CONS(l);
        mark_gray(c->head, c->head_info);
        mark_gray(AS_ALLOC(c->tail), list_info);
        }
        break;
    }
}

void display_list(struct alloc_header *alloc, struct string_buf *sb) {
    struct list *l = AS_LIST(alloc);
    switch (l->discriminant) {
    case 0:
        string_buf_push(sb, "nil");
        break;
    case 1:
        {
        struct list_cons *c = AS_LIST_CONS(l);
        string_buf_push(sb, "cons ");
        c->head_info.display(c->head, sb);
        string_buf_push(sb, " ");
        list_info.display(AS_ALLOC(c->tail), sb);
        }
        break;
    }
}

type_info list_info = { trace_list, display_list };

void trace_pair(struct alloc_header *alloc) {
    struct pair *p = AS_PAIR(alloc);
    mark_gray(p->fst, p->fst_info);
    mark_gray(p->snd, p->snd_info);
}

void display_pair(struct alloc_header *alloc, struct string_buf *sb) {
    struct pair *p = AS_PAIR(alloc);
    string_buf_push(sb, "(");
    p->fst_info.display(p->fst, sb);
    string_buf_push(sb, ", ");
    p->snd_info.display(p->snd, sb);
    string_buf_push(sb, ")");
}

type_info pair_info = { trace_pair, display_pair };

void trace_unit(struct alloc_header *alloc) {
}

void display_unit(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push(sb, "()");
}

type_info unit_info = { trace_unit, display_unit };

struct closure *allocate_closure(
        struct alloc_header *env,
        type_info env_info,
        void (*enter)(void)) {
    struct closure *cl = malloc(sizeof(struct closure));
    cl->env = env;
    cl->env_info = env_info;
    cl->enter = enter;

    cons_new_alloc(AS_ALLOC(cl), closure_info);
    return cl;
}

struct int64_value *allocate_int64(int64_t x) {
    struct int64_value *v = malloc(sizeof(struct int64_value));
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v), int64_value_info);
    return v;
}

struct bool_value *allocate_true(void) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->discriminant = 1;

    cons_new_alloc(AS_ALLOC(v), bool_value_info);
    return v;
}

struct bool_value *allocate_false(void) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->discriminant = 0;

    cons_new_alloc(AS_ALLOC(v), bool_value_info);
    return v;
}

struct sum *allocate_inl(struct alloc_header *x, type_info x_info) {
    struct sum *v = malloc(sizeof(struct sum));
    v->discriminant = 0;
    v->info = x_info;
    v->payload = x;

    cons_new_alloc(AS_ALLOC(v), sum_info);
    return v;
}

struct sum *allocate_inr(struct alloc_header *y, type_info y_info) {
    struct sum *v = malloc(sizeof(struct sum));
    v->discriminant = 1;
    v->info = y_info;
    v->payload = y;

    cons_new_alloc(AS_ALLOC(v), sum_info);
    return v;
}

struct list *allocate_list_nil(void) {
    struct list_nil *n = malloc(sizeof(struct list_nil));
    n->header.discriminant = 0;

    cons_new_alloc(AS_ALLOC(n), list_info);
    return AS_LIST(n);
}

struct list *allocate_list_cons(struct alloc_header *x, type_info info, struct list *xs) {
    struct list_cons *c = malloc(sizeof(struct list_cons));
    c->header.discriminant = 1;
    c->head_info = info;
    c->head = x;
    c->tail = xs;

    cons_new_alloc(AS_ALLOC(c), list_info);
    return AS_LIST(c);
}

struct pair *allocate_pair(type_info a_info, type_info b_info, struct alloc_header *x, struct alloc_header *y) {
    struct pair *p = malloc(sizeof(struct pair));
    p->fst_info = a_info;
    p->snd_info = b_info;
    p->fst = x;
    p->snd = y;
    cons_new_alloc(AS_ALLOC(p), pair_info);
    return p;
}

struct unit *allocate_unit(void) {
    struct unit *n = malloc(sizeof(struct unit));
    cons_new_alloc(AS_ALLOC(n), unit_info);
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

struct bool_value *prim_eqint64(struct int64_value *x, struct int64_value *y) {
    if (x->value == y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_neint64(struct int64_value *x, struct int64_value *y) {
    if (x->value != y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_ltint64(struct int64_value *x, struct int64_value *y) {
    if (x->value < y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_leint64(struct int64_value *x, struct int64_value *y) {
    if (x->value <= y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_gtint64(struct int64_value *x, struct int64_value *y) {
    if (x->value > y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_geint64(struct int64_value *x, struct int64_value *y) {
    if (x->value >= y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

