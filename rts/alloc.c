
#include "alloc.h"
#include "panic.h"

#include <stdbool.h>

// All allocations.
static struct alloc_header *first_allocation;
static struct alloc_stats gc_stats;
// static uint64_t num_allocs = 0; // number of currently live objects
static uint64_t gc_threshold = 256;

// The locals vector serves as an extra set of GC roots, for values allocated
// during the lifetime of a function.
//
// This is a consequence of the "straight-line code" thing.
// Because the continuation of a let-value or let-prim is implicitly the next
// statement, we do not call a 'suspend_*' method. Because we don't suspend,
// the freshly-allocated value is not saved as a thunk argument, and is
// therefore not added to the set of reachable values.
//
// To compensate for this, we maintain an auxiliary vector of roots, that is
// reset upon entry to a closure's code.
struct local_entry {
    struct alloc_header *alloc;
};
static struct local_entry *locals = NULL;
static size_t num_locals = 0;
static size_t locals_capacity = 0;

// Hmm. These are private, with only one use site. Consider inlining these
// definitions to init_gc and destroy_gc.
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

void push_local(struct alloc_header *local) {
    if (num_locals == locals_capacity) {
        locals_capacity *= 2;
        locals = realloc(locals, locals_capacity * sizeof(struct local_entry));
    }
    locals[num_locals].alloc = local;
    num_locals++;
}

// The gray list contains allocations in process of being traced. This avoids
// overflow when exploring deeply, and also can avoid cycles. 
struct gray_entry {
    struct alloc_header *alloc;
};
static struct gray_entry *gray_list = NULL;
static uint64_t num_gray = 0;
static uint64_t gray_capacity = 0;
void mark_gray(struct alloc_header *alloc) {
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
    num_gray++;
}



void collect(void) {
    // Clear the gray list. (It should be empty anyway after the last
    // collection, but be explicit.)
    num_gray = 0;

    // Add the roots to the gray list:
    // Each entry in 'locals' is a root.
    for (size_t i = 0; i < num_locals; i++) {
        mark_gray(locals[i].alloc);
    }
    // Mark any other roots. (Specifically, the argument data for the current
    // thunk is a set of roots.)
    trace_roots();

    while (num_gray > 0) {
        // Pick an item
        struct gray_entry gray = gray_list[--num_gray];
        if (gray.alloc->mark != 0) {
            // if marked already, continue to avoid cycles.
            continue;
        }
        // Mark this item as reachable.
        gray.alloc->mark = 1;
        // Push all subfields onto the gray list.
        gray.alloc->info->trace(gray.alloc);
    }

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
            gc_stats.num_live_objects--;
        } else {
            alloc->mark = 0;
            prev = alloc;
        }
        alloc = next;
    }

    // Set new threshold.
    // By using twice the current number of objects, the GC is sort of
    // "adaptive".
    gc_threshold = gc_stats.num_live_objects * 2;
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
void cons_new_alloc(struct alloc_header *alloc, const type_info *info) {
    alloc->mark = 0;
    alloc->next = first_allocation;
    alloc->info = info;
    first_allocation = alloc;
    gc_stats.num_live_objects++; gc_stats.lifetime_num_objects++;
    push_local(first_allocation);
    if (debug_stress_gc || (gc_stats.num_live_objects > gc_threshold)) {
        collect();
    }
}


// Hmm. I could pass trace_roots as a function parameter here. That would let
// me avoid an 'extern'.
void init_gc(void) {
    init_locals();

    gray_capacity = 8;
    num_gray = 0;
    gray_list = malloc(gray_capacity * sizeof(struct gray_entry));
}

void destroy_gc(void) {
    free(gray_list);
    gray_list = NULL;
    gray_capacity = 0;

    destroy_locals();

    sweep_all_allocations();
}

void get_alloc_stats(struct alloc_stats *out) {
    out->lifetime_num_objects = gc_stats.lifetime_num_objects;
    out->num_live_objects = gc_stats.num_live_objects;
}
