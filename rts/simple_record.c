
#include "simple_record.h"

#include <string.h>

#include "panic.h"



void trace_record(struct alloc_header *alloc) {
    struct record *rec = (struct record *)alloc;
    for (size_t i = 0; i < rec->num_fields; i++) {
        mark_gray(AS_ALLOC(rec->fields[i].label));
        mark_gray(rec->fields[i].value);
    }
}

void display_record(struct alloc_header *alloc, struct string_buf *sb) {
    struct record *rec = (struct record *)alloc;
    if (rec->num_fields == 0) {
        string_buf_push_slice(sb, "{}", 2);
    } else {
        // display first field, then display comma+field for rest, if any.
        struct record_field *first = &rec->fields[0];
        string_buf_push_slice(sb, "{ ", 2);
        string_buf_push_slice(sb, first->label->contents, first->label->len);
        string_buf_push_slice(sb, " = ", 3);
        first->value->info->display(first->value, sb);
        for (size_t i = 1; i < rec->num_fields; i++) {
            struct record_field *field = &rec->fields[i];
            string_buf_push_slice(sb, ", ", 2);
            string_buf_push_slice(sb, field->label->contents, field->label->len);
            string_buf_push_slice(sb, " = ", 3);
            field->value->info->display(field->value, sb);
        }
        string_buf_push_slice(sb, " }", 2);
    }
}

const type_info record_info = { trace_record, display_record };

struct record *allocate_record(size_t num_fields, struct field_init *fields) {
    struct record *rec = malloc(sizeof(struct record) + num_fields * sizeof(struct record_field));
    rec->num_fields = num_fields;
    for (size_t i = 0; i < num_fields; i++) {
        const struct field_init *field = &fields[i];
        rec->fields[i].label = allocate_string(field->label, field->len);
        rec->fields[i].value = field->value;
    }

    cons_new_alloc(AS_ALLOC(rec), &record_info);
    return rec;
}

struct alloc_header *project_field(struct record *rec, char *name, size_t len) {
    for (size_t i = 0; i < rec->num_fields; i++) {
        struct record_field *field = &rec->fields[i];
        struct string_value *lab = field->label;
        if (lab->len == len && strncmp(lab->contents, name, len) == 0) {
            return field->value;
        }
    }
    // unreachable, because the compiler emits well-formed code.
    unreachable("field not present in record");
}
