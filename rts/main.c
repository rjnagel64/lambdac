
#include <stdio.h>

#include "alloc.h"
#include "control.h"
#include "panic.h"
#include "string.h"

// Provided by user.
void program_entry(void);

int main(void) {
    // Initialize the GC: create the locals vector and the gray list.
    init_gc();

    // Prepare the calling convention by reserving space for a buffer of
    // arguments.
    init_args();

    // Prime the pump, so that we have a chain of thunks to enter.
    program_entry();

    // Main driver loop.
    // Repeatedly force/enter the current thunk until a final value is reached.
    while (!has_halted()) {
        reset_locals();
        next_entry_code();
    }

    // Display the result value.
    // Once I have a functioning IO system, this can go away.
    struct string_buf *sb = string_buf_new();
    struct alloc_header *result_value = get_result_value();
    result_value->info->display(result_value, sb);
    printf("result = ");
    fwrite(sb->data, sizeof(char), sb->len, stdout);
    printf("\n");
    string_buf_destroy(sb);

    // Cleanup.
    destroy_args();

    // Shut down the GC: release all memory and free the locals vector and gray
    // list.
    destroy_gc();
}

// vim: set et sts=4 sw=4:
