
#include "record.h"

#include <string.h>
#include <stdlib.h>

#include "panic.h"
#include "string_buf.h"


// Okay, I'm still very far from having functioning record values.
// I'm getting lost in the details. Shelve this for now, and come back later.


bool compare_label_lt(struct label l1, struct label l2) {
    return l1.offset < l2.offset;
}



struct label_entry {
    uint32_t offset;
    uint32_t len;
};

struct label_pool {
    // Dynamic buffer for storing label names
    char *names;
    size_t names_capacity;
    size_t names_len;

    // sorted array of (offset, length) into .names
    // do bsearch to update, insert.
    struct label_entry *labels;
    size_t labels_capacity;
    size_t labels_len;
};

struct label_pool *create_label_pool(void) {
    size_t names_cap = 64;
    char *names = malloc(names_cap * sizeof(char));

    size_t labels_cap = 8;
    struct label_entry *labels = malloc(labels_cap * sizeof(struct label_entry));

    struct label_pool *pool = malloc(sizeof(struct label_pool));
    pool->names = names;
    pool->names_capacity = names_cap;
    pool->names_len = 0;

    pool->labels = labels;
    pool->labels_capacity = labels_cap;
    pool->labels_len = 0;

    return pool;
}

void destroy_label_pool(struct label_pool *pool) {
    free(pool->names);
    free(pool->labels);

    free(pool);
}


struct label insert_label(struct label_pool *pool, size_t idx, const char *l, size_t len) {
    // push l[..len] onto '.label_names'.
    if (pool->names_len + len > pool->names_capacity) {
        size_t new_capacity = 2 * pool->names_capacity;
        pool->names = realloc(pool->names, new_capacity*sizeof(char));
        pool->names_capacity = new_capacity;
    }
    size_t offset = pool->names_len;
    memcpy(pool->names + offset, l, len);
    pool->names_len += len;

    // Make sure '.labels' is large enough for 1 more item.
    if (pool->labels_len + 1 > pool->labels_capacity) {
        size_t new_capacity = 2 * pool->labels_capacity;
        pool->labels = realloc(pool->labels, new_capacity * sizeof(struct label_entry));
        pool->labels_capacity = new_capacity;
    }
    size_t num_items_moved = pool->labels_len - idx;
    memmove(&pool->labels[idx+1], &pool->labels[idx], num_items_moved*sizeof(struct label_entry));
    pool->labels[idx].offset = offset;
    pool->labels[idx].len = len;

    pool->labels_len += 1;

    return (struct label){offset};
}

int compare_entry(struct label_pool *pool, struct label_entry *entry, const char *l, size_t len) {
    if (entry->len < len) {
        return -1;
    } else if (entry->len > len) {
        return 1;
    } else {
        return strncmp(pool->names + entry->offset, l, len);
    }
}

struct label get_label(struct label_pool *pool, const char *l, size_t len) {
    // Binary search pool->labels, from lo (inclusive) to hi (exclusive)
    size_t lo = 0;
    size_t hi = pool->labels_len;
    struct label_entry *target = NULL;
    while (lo < hi) {
        size_t mid = lo + (hi - lo)/2;
        struct label_entry *entry = &pool->labels[mid];
        int cmp = compare_entry(pool, entry, l, len);
        if (cmp > 0) {
            hi = mid;
            continue;
        } else if (cmp < 0) {
            lo = mid+1;
            continue;
        } else {
            // We found it?
            target = entry;
            break;
        }
    }

    if (target == NULL) {
        // didn't find the label. Insert it here, at lo == hi.
        return insert_label(pool, lo, l, len);
    } else {
        // We found it: return the label
        return (struct label){target->offset};
    }
}



size_t lookup_index(struct record_value *rec, struct label l) {
    size_t lo = 0;
    size_t hi = rec->num_fields;
    while (lo < hi) {
        size_t mid = lo + (hi - lo)/2;
        struct record_field *field = rec->fields + mid;
        if (compare_label_lt(l, field->l)) {
            hi = mid;
        } else if (compare_label_lt(field->l, l)) {
            lo = mid+1;
        } else {
            // Because we permit duplicate field labels, we need to use the
            // 'depth' field to jump to the outermost occurrence.
            return mid - field->depth;
        }
    }

    // Unreachable, type system guarantees that label 'l' exists in this record.
    panic("label not present in record");
}

void trace_record(struct alloc_header *alloc) {
    struct record_value *rec = AS_RECORD(alloc);
    for (uint32_t i = 0; i < rec->num_fields; i++) {
        mark_gray(rec->fields[i].value);
    }
}

void display_record(struct alloc_header *alloc, struct string_buf *sb) {
    struct record_value *rec = AS_RECORD(alloc);
    if (rec->num_fields == 0) {
        string_buf_push_slice(sb, "{}", 2);
    } else {
        string_buf_push_slice(sb, "{", 1);
        rec->fields[0].value->info->display(rec->fields[0].value, sb);
        for (uint32_t i = 1; i < rec->num_fields; i++) {
            string_buf_push_slice(sb, ", ", 2);
            rec->fields[i].value->info->display(rec->fields[i].value, sb);
        }
        string_buf_push_slice(sb, "}", 1);
    }
}

type_info record_info = { trace_record, display_record };

struct record_value *create_record(uint32_t num_fields) {
    size_t size = sizeof(struct record_value) + num_fields * sizeof(struct record_field);
    struct record_value *rec = malloc(size);
    rec->num_fields = num_fields;
    return rec;
}

void finalize_record(struct record_value *rec) {
    cons_new_alloc(AS_ALLOC(rec), &record_info);
}

struct record_value *allocate_empty_record(void) {
    struct record_value *rec = create_record(0);
    finalize_record(rec);
    return rec;
}

struct alloc_header *project_record_field(struct record_value *rec, struct label l) {
    size_t idx = lookup_index(rec, l);
    return rec->fields[idx].value;
}

struct record_value *extend_record(struct record_value *rec, struct label l, struct alloc_header *val) {
    // Compute index for 'l'
    // copy everything to left of 'l'
    // insert new field
    // copy everything to the right of 'l', possibly incrementing 'depth'.
    // (this is kind of subtle?)
    size_t idx = lookup_index(rec, l);
    panic("not implemented: record extension");
}

struct record_value *restrict_record(struct record_value *rec, struct label l) {
    size_t idx = lookup_index(rec, l);
    // Allocate new record with n-1 fields.
    // Because records are well-typed, 'l' must be a field of the record, and
    // therefore rec->num_fields >= 1. Underflow is therefore impossible.
    struct record_value *rec2 = create_record(rec->num_fields - 1);
    // copy fields[..idx]
    memcpy(rec2->fields, rec->fields, idx * sizeof(struct record_field));
    // copy fields[idx+1..]
    memcpy(rec->fields + idx, rec->fields + (idx + 1), (rec->num_fields - (idx + 1))*sizeof(struct record_field));

    finalize_record(rec2);
    return rec2;
}

