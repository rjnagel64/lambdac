
#include "panic.h"

#include <stdio.h>
#include <stdlib.h>

void runtime_error(const char *msg) {
    printf("Runtime error: %s\n", msg);
    exit(1);
}

void unreachable(const char *msg) {
    printf("Entered unreachable code: %s\n", msg);
    exit(1);
}

void internal_error(const char *msg) {
    printf("Internal RTS error: %s\n", msg);
    exit(1);
}

