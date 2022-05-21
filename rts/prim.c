
#include "prim.h"

#include "alloc.h"

struct constant *prim_addint64(struct constant *x, struct constant *y) {
    return allocate_int64(int64_value(x) + int64_value(y));
}

struct constant *prim_subint64(struct constant *x, struct constant *y) {
    return allocate_int64(int64_value(x) - int64_value(y));
}

struct constant *prim_mulint64(struct constant *x, struct constant *y) {
    return allocate_int64(int64_value(x) * int64_value(y));
}

struct constant *prim_negint64(struct constant *x) {
    return allocate_int64(-int64_value(x));
}

struct bool_value *prim_eqint64(struct constant *x, struct constant *y) {
    if (int64_value(x) == int64_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_neint64(struct constant *x, struct constant *y) {
    if (int64_value(x) != int64_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_ltint64(struct constant *x, struct constant *y) {
    if (int64_value(x) < int64_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_leint64(struct constant *x, struct constant *y) {
    if (int64_value(x) <= int64_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_gtint64(struct constant *x, struct constant *y) {
    if (int64_value(x) > int64_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_geint64(struct constant *x, struct constant *y) {
    if (int64_value(x) >= int64_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

