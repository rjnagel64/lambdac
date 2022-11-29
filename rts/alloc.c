
#include "alloc.h"
#include "panic.h"

#include <stdbool.h>

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



void collect(void) {
    // It might be better to malloc gray list at startup, realloc/resize when
    // collecting. After all, GC happens when there isn't much memory available
    // to allocate for the gray list.
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

// Set this constant to 'true' in order to GC on every allocation.
static const bool debug_stress_gc = false;
void cons_new_alloc(struct alloc_header *alloc, type_info info) {
    alloc->mark = 0;
    alloc->next = first_allocation;
    first_allocation = alloc;
    num_allocs++;
    push_local(first_allocation, info);
    if (debug_stress_gc || (num_allocs > gc_threshold)) {
        collect();
    }
}

