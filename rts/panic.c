
#include "panic.h"

#include <stdio.h>
#include <stdlib.h>

void panic(const char *msg) {
    printf("RTS error: %s\n", msg);
    exit(1);
}

