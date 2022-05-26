#ifndef __STRING_H__
#define __STRING_H__

#include <stdlib.h>

// A string_buf is basically a vector<char>.
// Or alternately, it's basically a StringBuilder? I can't seem to decide.
struct string_buf {
    size_t len;
    size_t capacity;
    char *data;
};

// Create a new string_buf with empty contents.
struct string_buf *string_buf_new(void);
// Destroy a string_buf and its contents.
void string_buf_destroy(struct string_buf *sb);

// Get a non-owning reference to the string.
char *string_buf_contents(struct string_buf *sb);
// Take ownership of the contents and reset the string_buf
// char *string_buf_consume(struct string_buf *sb);

void string_buf_push(struct string_buf *sb, const char *s);


// string value type?
// string value primops?

#endif
