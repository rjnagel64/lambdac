#ifndef __STRING_H__
#define __STRING_H__

#include <stddef.h>

// A string_buf is basically a vector<char>.
// Or alternately, it's basically a StringBuilder? I can't seem to decide.
// (Well, not all that much difference.)
//
// (Proposed) Invariants:
// * .capacity > 0         (zero-size allocations get weird, and I need a null terminator anyway.)
// * .data points to an allocation with space for exactly .capacity characters
// * the string_buf owns the allocation at .data
// * .len < .capacity
// * .data[.len] == '\0'   (might relax this requirement once string uses pointer+length)
struct string_buf {
    size_t len;
    size_t capacity;
    char *data;
};

// Create a new string_buf with empty contents.
struct string_buf *string_buf_new(void);
// Destroy a string_buf and its contents.
void string_buf_destroy(struct string_buf *sb);

// Append 'len' characters read from 's' to the buffer.
void string_buf_push_slice(struct string_buf *sb, const char *s, size_t len);

// Append a null-terminated string to the buffer.
// void string_buf_push_cstring(struct string_buf *sb, const char *s);
// Append a single character to the buffer.
// void string_buf_push_char(struct string_buf *sb, char c);


#endif
