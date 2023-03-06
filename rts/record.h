#ifndef __RECORD_H__
#define __RECORD_H__

#include <stdint.h>
#include <stdbool.h>

#include "alloc.h"

struct label {
    uint32_t offset;
};

struct label make_label(size_t len, const char *l);
bool compare_label_lt(struct label l1, struct label l2);

struct record_field {
    struct label l;
    uint32_t depth;
    struct alloc_header *value;
};

struct record_value {
    struct alloc_header header;
    uint32_t num_fields;
    struct record_field fields[];
};

#define AS_RECORD(v) ((struct record_value *)(v))

// empty/project/extend/restrict. Inefficient due to repeated copies. (O(N^2) in many cases.)
// Could/Should use more advanced API to construct entire value at once.
struct record_value *allocate_empty_record(void);
struct alloc_header *project_record_field(struct record_value *rec, struct label l);
struct record_value *extend_record(struct record_value *rec, struct label l, struct alloc_header *val);
struct record_value *restrict_record(struct record_value *rec, struct label l);

#endif
