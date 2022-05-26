
#include "prim.h"

#include "alloc.h"

struct int64_value *prim_addint64(struct int64_value *x, struct int64_value *y) {
    return allocate_int64(x->value + y->value);
}

struct int64_value *prim_subint64(struct int64_value *x, struct int64_value *y) {
    return allocate_int64(x->value - y->value);
}

struct int64_value *prim_mulint64(struct int64_value *x, struct int64_value *y) {
    return allocate_int64(x->value * y->value);
}

struct int64_value *prim_negint64(struct int64_value *x) {
    return allocate_int64(-x->value);
}

struct bool_value *prim_eqint64(struct int64_value *x, struct int64_value *y) {
    if (x->value == y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_neint64(struct int64_value *x, struct int64_value *y) {
    if (x->value != y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_ltint64(struct int64_value *x, struct int64_value *y) {
    if (x->value < y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_leint64(struct int64_value *x, struct int64_value *y) {
    if (x->value <= y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_gtint64(struct int64_value *x, struct int64_value *y) {
    if (x->value > y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct bool_value *prim_geint64(struct int64_value *x, struct int64_value *y) {
    if (x->value >= y->value) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

