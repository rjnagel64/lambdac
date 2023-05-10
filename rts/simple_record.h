#ifndef __SIMPLE_RECORD_H__
#define __SIMPLE_RECORD_H__

#include "alloc.h"
#include "prim.h"

struct record_field {
    // Because I do not have GC finalizers, each field label needs to be
    // independently collectable by the GC.
    // Therefore, I just reuse string values for the labels.
    struct string_value *label;
    struct alloc_header *value;
};

struct record {
    struct alloc_header header;
    size_t num_fields;
    struct record_field fields[];
};
#define CAST_RECORD(v) ((struct record *)(v))

struct record *allocate_record(size_t num_fields);

struct alloc_header *project_field(struct record *rec, char *name, size_t len);



#endif
