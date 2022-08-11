
#include <stdio.h>

#include "alloc.h"
#include "control.h"
#include "panic.h"
#include "string.h"

// Provided by user.
void program_entry(void);

int main(void) {
    // Initialize the locals vector.
    init_locals();
    
    // Prepare the main driver loop
    result_value = NULL;
    next_step = malloc(sizeof(struct thunk));
    next_step->args = NULL;

    // Prime the pump, so that we have a chain of thunks to enter.
    program_entry();

    // Main driver loop.
    // Repeatedly force/enter the current thunk until a final value is reached.
    while (result_value == NULL) {
        reset_locals();
        next_step->enter();
    }

    free(next_step);
    // Display the result value.
    // Once I have a functioning IO system, this can go away.
    struct string_buf *sb = string_buf_new();
    result_info.display(result_value, sb);
    printf("result = %s\n", string_buf_contents(sb));
    string_buf_destroy(sb);

    // Cleanup.
    destroy_locals();
    sweep_all_allocations();
}

// vim: set et sts=4 sw=4:
