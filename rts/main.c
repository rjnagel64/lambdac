
#include <stdio.h>
#include <string.h>

#include "alloc.h"
#include "control.h"
#include "panic.h"

struct string_buf {
    size_t len;
    size_t capacity;
    char *data;
};

struct string_buf *string_buf_new() {
    struct string_buf *sb = malloc(sizeof(struct string_buf));
    sb->len = 0;
    sb->capacity = 8;
    sb->data = malloc(sb->capacity * sizeof(char));
    return sb;
}

void string_buf_destroy(struct string_buf *sb) {
    free(sb->data);
    free(sb);
}

void string_buf_push(struct string_buf *sb, const char *s) {
    size_t len = strlen(s);
    size_t capacity = sb->capacity;
    while (sb->len + len + 1 > capacity) {
        capacity *= 2;
    }
    if (capacity != sb->capacity) {
        sb->data = realloc(sb->data, capacity);
        sb->capacity = capacity;
    }
    memcpy(sb->data + sb->len, s, len);
    sb->len += len;
    sb->data[sb->len] = '\0';
}

// Render any value as a string.
// Once I have a functioning IO system, this should probably be replaced with
// whatever->string primops.
void display_alloc(int prec, struct alloc_header *alloc, struct string_buf *sb) {
    switch (alloc->type) {
    case ALLOC_CLOSURE:
        string_buf_push(sb, "<closure>");
        break;
    case ALLOC_CONST:
        {
        struct value *v = AS_VALUE(alloc);
        char s[16];
        sprintf(s, "%d", int32_value(v));
        string_buf_push(sb, s);
        }
        break;
    case ALLOC_PROD:
        {
        struct value *v = AS_VALUE(alloc);
        string_buf_push(sb, "(");
        display_alloc(0, AS_ALLOC(v->words[0]), sb);
        string_buf_push(sb, ", ");
        display_alloc(0, AS_ALLOC(v->words[1]), sb);
        string_buf_push(sb, ")");
        }
        break;
    case ALLOC_SUM:
        {
        struct sum *v = AS_SUM(alloc);
        if (prec > 0) {
            string_buf_push(sb, "(");
        }
        // TODO: FIXME: use proper constructor names when printing sum types
        // Currently, I disambiguate by number of fields.
        // However, when I add general ADTs, this will not work *at all*.
        // (Arbitrary number of variants, each with unique names)
        // This is why Haskell has the 'Show' type class: so the runtime
        // doesn't need to keep track of this information.
        switch (v->discriminant) {
        case 0:
            string_buf_push(sb, (v->num_fields == 0) ? "false" : "inl");
            break;
        case 1:
            string_buf_push(sb, (v->num_fields == 0) ? "true" : "inr");
            break;
        };
        for (uint32_t i = 0; i < v->num_fields; i++) {
            string_buf_push(sb, " ");
            display_alloc(1, AS_ALLOC(v->words[i]), sb);
        }
        if (prec > 0) {
            string_buf_push(sb, ")");
        }
        }
        break;
    }
}

// Provided by user.
void program_entry(void);

int main(void) {
    // Initialize the locals vector.
    init_locals();

    // Prepare the main driver loop
    result_value = NULL;
    next_step = malloc(sizeof(struct thunk));

    // Prime the pump, so that we have a chain of thunks to enter.
    program_entry();

    // Main driver loop.
    // Repeatedly force/enter the current thunk until a final value is reached.
    while (result_value == NULL) {
        reset_locals();
        next_step->enter();
    }

    free(next_step);
    // Display the result value.
    // Once I have a functioning IO system, this can go away.
    struct string_buf *sb = string_buf_new();
    display_alloc(0, result_value, sb);
    printf("result = %s\n", sb->data);
    string_buf_destroy(sb);

    // Cleanup.
    destroy_locals();
    sweep_all_allocations();
}

// vim: set et sts=4 sw=4:
