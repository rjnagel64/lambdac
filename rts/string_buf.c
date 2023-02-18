
#include "string_buf.h"

#include <stdlib.h>
#include <string.h>

struct string_buf *string_buf_new(void) {
    struct string_buf *sb = malloc(sizeof(struct string_buf));
    sb->len = 0;
    sb->capacity = 8;
    sb->data = calloc(sb->capacity, sizeof(char));
    return sb;
}

void string_buf_destroy(struct string_buf *sb) {
    free(sb->data);
    free(sb);
}

char *string_buf_contents(struct string_buf *sb) {
    return sb->data;
}

void string_buf_push(struct string_buf *sb, const char *s) {
    size_t len = strlen(s);
    string_buf_push_slice(sb, s, len);
}

void string_buf_push_slice(struct string_buf *sb, const char *s, size_t len) {
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
