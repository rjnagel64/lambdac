
#include "prim.h"

#include "panic.h"

#include <stdio.h> // sprintf for display_int64_value
#include <string.h>

void trace_int64_value(struct alloc_header *alloc) {
}

void display_int64_value(struct alloc_header *alloc, struct string_buf *sb) {
    // int64_t can have ~20 decimal digits, plus sign, so use a 32-byte buffer.
    static char buf[32];
    struct int64_value *v = CAST_INT64(alloc);
    int64_t value = (int64_t)v->value;
    int num_len = sprintf(buf, "%lld", value);
    string_buf_push_slice(sb, buf, num_len);
}

const type_info int64_value_info = { trace_int64_value, display_int64_value, 0 };

struct int64_value *allocate_int64(int64_t x) {
    struct int64_value *v = malloc(sizeof(struct int64_value));
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v), &int64_value_info);
    return v;
}

void trace_bool_value(struct alloc_header *alloc) {
}

void display_bool_value(struct alloc_header *alloc, struct string_buf *sb) {
    struct bool_value *v = CAST_BOOL(alloc);
    if (v->value) {
        string_buf_push_slice(sb, "true", 4);
    } else {
        string_buf_push_slice(sb, "false", 5);
    }
}

const type_info bool_value_info = { trace_bool_value, display_bool_value, 0 };

struct bool_value *allocate_bool_value(uint8_t x) {
    struct bool_value *v = malloc(sizeof(struct bool_value));
    v->value = x;

    cons_new_alloc(AS_ALLOC(v), &bool_value_info);
    return v;
}

void trace_char_value(struct alloc_header *alloc) {
}

void display_char_value(struct alloc_header *alloc, struct string_buf *sb) {
    // Oh no, unicode. char_value's payload is a unicode code point, 32 bits.
    // (Like rust 'char')
    //
    // ...
    // I'm just going to assume that all characters are ASCII, so I can just
    // mask off the lowest byte.
    // Doing this properly would probably involve encoding the codepoint into a
    // few UTF-8 bytes, then pushing those bytes onto the string_buf
    
    struct char_value *v = CAST_CHAR(alloc);
    if (v->value == '\n') {
        string_buf_push_slice(sb, "'\\n'", 4);
    } else if (v->value == '\t') {
        string_buf_push_slice(sb, "'\\t'", 4);
    } else if (v->value == '\\') {
        string_buf_push_slice(sb, "'\\\\'", 4);
    } else if (v->value == '\'') {
        string_buf_push_slice(sb, "'\\''", 4);
    } else {
        char value[1]; // maximum 7 bytes?
        value[0] = (char)(v->value & 0x7F);
        string_buf_push_slice(sb, "'", 1);
        string_buf_push_slice(sb, value, 1);
        string_buf_push_slice(sb, "'", 1);
    }
}

const type_info char_value_info = { trace_char_value, display_char_value, 0 };

struct char_value *allocate_char(uint32_t x) {
    struct char_value *v = malloc(sizeof(struct char_value));
    v->value = (uintptr_t)x;

    cons_new_alloc(AS_ALLOC(v), &char_value_info);
    return v;
}

void trace_closure(struct alloc_header *alloc) {
    struct closure *cl = CAST_CLOSURE(alloc);
    mark_gray(AS_ALLOC(cl->env));
}

void display_closure(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push_slice(sb, "<closure>", 9);
}

const type_info closure_info = { trace_closure, display_closure, 0 };

void trace_empty_env(struct alloc_header *alloc) {
    struct empty_env *env = CAST_EMPTY_ENV(alloc);
}

void display_env(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push_slice(sb, "<env>", 5);
}

const type_info empty_env_info = { trace_empty_env, display_env, 0 };
struct empty_env _the_empty_env = { { 0, NULL, &empty_env_info } };
struct empty_env *the_empty_env = &_the_empty_env;

struct closure *allocate_closure(
        struct alloc_header *env,
        void (*enter)(void)) {
    struct closure *cl = malloc(sizeof(struct closure));
    cl->env = env;
    cl->enter = enter;

    cons_new_alloc(AS_ALLOC(cl), &closure_info);
    return cl;
}

void trace_pair(struct alloc_header *alloc) {
    struct pair *p = CAST_PAIR(alloc);
    mark_gray(p->fst);
    mark_gray(p->snd);
}

void display_pair(struct alloc_header *alloc, struct string_buf *sb) {
    struct pair *p = CAST_PAIR(alloc);
    string_buf_push_slice(sb, "(", 1);
    p->fst->info->display(p->fst, sb);
    string_buf_push_slice(sb, ", ", 2);
    p->snd->info->display(p->snd, sb);
    string_buf_push_slice(sb, ")", 1);
}

const type_info pair_info = { trace_pair, display_pair, 0 };

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
    string_buf_push_slice(sb, "()", 2);
}

const type_info unit_info = { trace_unit, display_unit, 0 };

struct unit *allocate_unit(void) {
    struct unit *n = malloc(sizeof(struct unit));
    cons_new_alloc(AS_ALLOC(n), &unit_info);
    return n;
}

void trace_string(struct alloc_header *alloc) {
}

void display_string(struct alloc_header *alloc, struct string_buf *sb) {
    // Actually, this should probably do string escaping in addition to
    // surrounding with quotes.
    struct string_value *s = CAST_STRING(alloc);
    string_buf_push_slice(sb, "\"", 1);
    string_buf_push_slice(sb, s->contents, s->len);
    string_buf_push_slice(sb, "\"", 1);
}

const type_info string_info = { trace_string, display_string, 0 };

struct string_value *allocate_string(const char *src, size_t len) {
    struct string_value *s = malloc(sizeof(struct string_value) + (len + 1) * sizeof(char));
    memcpy(s->contents, src, len);
    s->contents[len] = '\0';
    s->len = len;
    cons_new_alloc(AS_ALLOC(s), &string_info);
    return s;
}

struct string_value *allocate_string_from_buf(struct string_buf *sb) {
    return allocate_string(sb->data, sb->len);
}

void trace_token(struct alloc_header *alloc) {
}

void display_token(struct alloc_header *alloc, struct string_buf *sb) {
    string_buf_push_slice(sb, "WORLD#", 6);
}

const type_info token_info = { trace_token, display_token, 0 };

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

struct bool_value *prim_eqint64(struct int64_value *x, struct int64_value *y) {
    return allocate_bool_value(x->value == y->value);
}

struct bool_value *prim_neint64(struct int64_value *x, struct int64_value *y) {
    return allocate_bool_value(x->value != y->value);
}

struct bool_value *prim_ltint64(struct int64_value *x, struct int64_value *y) {
    return allocate_bool_value(x->value < y->value);
}

struct bool_value *prim_leint64(struct int64_value *x, struct int64_value *y) {
    return allocate_bool_value(x->value <= y->value);
}

struct bool_value *prim_gtint64(struct int64_value *x, struct int64_value *y) {
    return allocate_bool_value(x->value > y->value);
}

struct bool_value *prim_geint64(struct int64_value *x, struct int64_value *y) {
    return allocate_bool_value(x->value >= y->value);
}

struct bool_value *prim_eqchar(struct char_value *x, struct char_value *y) {
    return allocate_bool_value(x->value == y->value);
}

struct string_value *prim_concatenate(struct string_value *x, struct string_value *y) {
    struct string_buf *sb = string_buf_with_capacity(x->len + y->len);
    string_buf_push_slice(sb, x->contents, x->len);
    string_buf_push_slice(sb, y->contents, y->len);
    struct string_value *s = allocate_string_from_buf(sb); // Copy contents into new string.
    string_buf_destroy(sb); // Destroy temporary buffer.
    return s;
}

struct int64_value *prim_strlen(struct string_value *x) {
    return allocate_int64(x->len);
}

struct char_value *prim_strindex(struct string_value *x, struct int64_value *idx) {
    int64_t i = idx->value;
    if (i < 0 || i >= x->len) {
        runtime_error("string index out of bounds");
    }
    char c = x->contents[i];
    return allocate_char((uint32_t)c);
}

void prim_getLine(struct token *x, struct token **out_x, struct string_value **out_y) {
    char *line_buf = NULL;
    size_t buf_size = 0;
    ssize_t chars_read = getline(&line_buf, &buf_size, stdin);
    if (chars_read == -1) {
        // Error or EOF: return ""
        // (I need better error handling for this. Still need to think about
        // API) (It gets annoying because streams are quite stateful, and
        // primops/RTS don't have great access to things like sum types)
        *out_x = x;
        *out_y = allocate_string("", 0);
        free(line_buf);
    } else {
        *out_x = x;
        // We pass 'chars_read - 1' here to omit the trailing '\n' read by
        // 'getline'.
        *out_y = allocate_string(line_buf, chars_read - 1);
        free(line_buf);
    }
}

void prim_putLine(struct token *x, struct string_value *msg, struct token **out_x, struct unit **out_y) {
    printf("%s\n", msg->contents);
    *out_x = x;
    *out_y = allocate_unit();
}

struct alloc_header *prim_runtime_error(struct string_value *msg) {
    // Note: requires null terminator on msg->contents
    runtime_error(msg->contents);
    return NULL; // unreachable
}
