
#include <stdio.h>
#include <string.h>

#include "alloc.h"
#include "control.h"
#include "panic.h"


// Provided by user.
void program_entry(void);

// TODO: Figure out how to properly allocate static closures.
// It's definitely possible, but I'm not sure why my previous attempt didn't work.

int main(void) {
    // Initialize the locals vector.
    init_locals();

    // Connect GC with control flow.
    trace_roots = &mark_root;

    // Push initial activation record on stack
    program_entry();

    // Main driver loop.
    int keep_running = 1;
    while (keep_running) {
        reset_locals();
        switch (next_step.type) {
        case JUMP_NEXT:
            next_step.kont->code(next_step.kont->env, next_step.arg);
            break;
        case TAILCALL_NEXT:
            next_step.fun->code(next_step.fun->env, next_step.arg, next_step.kont);
            break;
        case HALT_NEXT:
            printf("done.\n");
            if (next_step.arg->header.type == ALLOC_CONST) {
                int32_t result = int32_value(next_step.arg);
                printf("result = %d\n", result);
            } else {
                printf("FIXME: display values other than integers\n");
            }
            keep_running = 0;
            break;
        }
    }

    // Cleanup.
    destroy_locals();
    sweep_all_allocations();
}

// vim: set et sts=4 sw=4:
