
#include "prim.h"

#include "alloc.h"

struct value *prim_addint32(struct value *x, struct value *y) {
    return allocate_int32(int32_value(x) + int32_value(y));
}

struct value *prim_subint32(struct value *x, struct value *y) {
    return allocate_int32(int32_value(x) - int32_value(y));
}

struct value *prim_mulint32(struct value *x, struct value *y) {
    return allocate_int32(int32_value(x) * int32_value(y));
}

struct sum *prim_eqint32(struct value *x, struct value *y) {
    if (int32_value(x) == int32_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct sum *prim_neint32(struct value *x, struct value *y) {
    if (int32_value(x) != int32_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct sum *prim_ltint32(struct value *x, struct value *y) {
    if (int32_value(x) < int32_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct sum *prim_leint32(struct value *x, struct value *y) {
    if (int32_value(x) <= int32_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct sum *prim_gtint32(struct value *x, struct value *y) {
    if (int32_value(x) > int32_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

struct sum *prim_geint32(struct value *x, struct value *y) {
    if (int32_value(x) >= int32_value(y)) {
        return allocate_true();
    } else {
        return allocate_false();
    }
}

