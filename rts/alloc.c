
#include "alloc.h"
#include "panic.h"

#include <stdio.h> // sprintf

// All allocations.
static struct alloc_header *first_allocation;
static uint64_t num_allocs = 0;
static uint64_t gc_threshold = 256;

// The locals vector serves as an extra set of GC roots, for values allocated
// during the lifetime of a function.
struct local_entry {
    struct alloc_header *alloc;
    type_info info;
};
static struct local_entry *locals = NULL;
static size_t num_locals = 0;
static size_t locals_capacity = 0;

void init_locals(void) {
    locals_capacity = 8;
    locals = malloc(locals_capacity * sizeof(struct local_entry));
    num_locals = 0;
}

void destroy_locals(void) {
    free(locals);
    locals = NULL;
    num_locals = 0;
    locals_capacity = 0;
}

void reset_locals(void) {
    num_locals = 0;
}

void push_local(struct alloc_header *local, type_info info) {
    if (num_locals == locals_capacity) {
        locals_capacity *= 2;
        locals = realloc(locals, locals_capacity * sizeof(struct local_entry));
    }
    locals[num_locals].alloc = local;
    locals[num_locals].info = info;
    num_locals++;
}

// The gray list contains allocations in process of being traced. This avoids
// overflow when exploring deeply, and also can avoid cycles. 
struct gray_entry {
    struct alloc_header *alloc;
    type_info info;
};
static struct gray_entry *gray_list = NULL;
static uint64_t num_gray = 0;
static uint64_t gray_capacity = 0;
void mark_gray(struct alloc_header *alloc, type_info info) {
    if (alloc == NULL) {
        // Currently, I allocate empty closure environments as 'NULL'.
        // Do not put NULLs in the gray list.
        return;
    }
    if (num_gray == gray_capacity) {
        gray_capacity *= 2;
        gray_list = realloc(gray_list, gray_capacity * sizeof(struct gray_entry));
    }
    gray_list[num_gray].alloc = alloc;
    gray_list[num_gray].info = info;
    num_gray++;
}

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




void collect(void) {
    // Alternatively, malloc at startup, realloc/resize here.
    // That probably would be better, GC happens when there isn't much memory
    // available to allocate for the gray list.
    gray_capacity = 8;
    num_gray = 0;
    gray_list = malloc(gray_capacity * sizeof(struct gray_entry));

    // Push each local onto gray_list
    for (size_t i = 0; i < num_locals; i++) {
        mark_gray(locals[i].alloc, locals[i].info);
    }
    // Push each field of next_step onto gray_list
    trace_roots();

    while (num_gray > 0) {
        // Pick an item
        struct gray_entry gray = gray_list[--num_gray];
        if (gray.alloc->mark != 0) {
            // if marked already, continue (avoid cycles.)
            continue;
        }
        // mark as reachable
        gray.alloc->mark = 1;
        // push all subfields as gray (trace)
        gray.info.trace(gray.alloc);
    }

    free(gray_list);
    gray_list = NULL;
    gray_capacity = 0;

    // Sweep alloc list for mark = 0, and also reset mark to 0 for other allocations.
    struct alloc_header *prev = NULL;
    for (struct alloc_header *alloc = first_allocation; alloc != NULL; ) {
        struct alloc_header *next = alloc->next;
        if (alloc->mark == 0) {
            if (prev == NULL) {
                first_allocation = next;
            } else {
                prev->next = next;
            }
            free(alloc);
            num_allocs--;
        } else {
            alloc->mark = 0;
            prev = alloc;
        }
        alloc = next;
    }

    // Set new threshold.
    // By using twice the current number of objects, the GC is sort of
    // "adaptive".
    gc_threshold = num_allocs * 2;
}

void sweep_all_allocations(void) {
    for (struct alloc_header *alloc = first_allocation; alloc != NULL;) {
        struct alloc_header *next = alloc->next;
        // All fields are managed by GC.
        free(alloc);
        alloc = next;
    }
}

void cons_new_alloc(struct alloc_header *alloc, type_info info) {
    alloc->mark = 0;
    alloc->next = first_allocation;
    first_allocation = alloc;
    num_allocs++;
    push_local(first_allocation, info);
    if (num_allocs > gc_threshold) {
        collect();
    }
}

struct closure *allocate_closure(
        struct alloc_header *env,
        type_info env_info,
        void (*code)(void),
        void (*enter)(void)) {
    struct closure *cl = malloc(sizeof(struct closure));
    cl->header.type = ALLOC_CLOSURE;
    cl->env = env;
    cl->env_info = env_info;
    cl->code = code;
    cl->enter = enter;

    cons_new_alloc(AS_ALLOC(cl), closure_info);
    return cl;
}

struct int64_value *allocate_int64(int64_t x) {
    struct int64_value *v = malloc(sizeof(struct int64_value));
    v->header.type = ALLOC_CONST;
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v), int64_value_info);
    return v;
}

struct bool_value *allocate_true(void) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->header.type = ALLOC_BOOL;
    v->discriminant = 1;

    cons_new_alloc(AS_ALLOC(v), bool_value_info);
    return v;
}

struct bool_value *allocate_false(void) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->header.type = ALLOC_BOOL;
    v->discriminant = 0;

    cons_new_alloc(AS_ALLOC(v), bool_value_info);
    return v;
}

struct sum *allocate_inl(struct alloc_header *x, type_info x_info) {
    struct sum *v = malloc(sizeof(struct sum));
    v->header.type = ALLOC_SUM;
    v->discriminant = 0;
    v->info = x_info;
    v->payload = x;

    cons_new_alloc(AS_ALLOC(v), sum_info);
    return v;
}

struct sum *allocate_inr(struct alloc_header *y, type_info y_info) {
    struct sum *v = malloc(sizeof(struct sum));
    v->header.type = ALLOC_SUM;
    v->discriminant = 1;
    v->info = y_info;
    v->payload = y;

    cons_new_alloc(AS_ALLOC(v), sum_info);
    return v;
}

struct list *allocate_list_nil(void) {
    struct list_nil *n = malloc(sizeof(struct list_nil));
    n->header.header.type = ALLOC_LIST;
    n->header.discriminant = 0;

    cons_new_alloc(AS_ALLOC(n), list_info);
    return AS_LIST(n);
}

struct list *allocate_list_cons(struct alloc_header *x, type_info info, struct list *xs) {
    struct list_cons *c = malloc(sizeof(struct list_cons));
    c->header.header.type = ALLOC_LIST;
    c->header.discriminant = 1;
    c->head_info = info;
    c->head = x;
    c->tail = xs;

    cons_new_alloc(AS_ALLOC(c), list_info);
    return AS_LIST(c);
}

struct pair *allocate_pair(type_info a_info, type_info b_info, struct alloc_header *x, struct alloc_header *y) {
    struct pair *p = malloc(sizeof(struct pair));
    p->header.type = ALLOC_PAIR;
    p->fst_info = a_info;
    p->snd_info = b_info;
    p->fst = x;
    p->snd = y;
    cons_new_alloc(AS_ALLOC(p), pair_info);
    return p;
}

struct unit *allocate_unit(void) {
    struct unit *n = malloc(sizeof(struct unit));
    n->header.type = ALLOC_UNIT;
    cons_new_alloc(AS_ALLOC(n), unit_info);
    return n;
}

