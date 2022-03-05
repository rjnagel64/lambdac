
#include <stdio.h>
#include <string.h>

#include "alloc.h"
#include "control.h"
#include "panic.h"


// Provided by user.
void program_entry(void);

int main(void) {
    // Initialize the locals vector.
    init_locals();

    // Connect GC with control flow.
    trace_roots = &mark_root;

    // Prepare the main driver loop
    result_value = NULL;
    next_step = malloc(sizeof(struct thunk));

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
    if (result_value->type == ALLOC_CONST) {
        int32_t result = int32_value(AS_VALUE(result_value));
        printf("result = %d\n", result);
    } else {
        printf("FIXME: display values other than integers\n");
    }

    // Cleanup.
    destroy_locals();
    sweep_all_allocations();
}

// vim: set et sts=4 sw=4:
