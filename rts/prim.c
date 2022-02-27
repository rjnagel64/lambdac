
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

// TODO: Use booleans, not inl ()/inr ()
struct value *prim_iszero32(struct value *x) {
    if (int32_value(x) == 0) {
        return allocate_inl(allocate_nil());
    } else {
        return allocate_inr(allocate_nil());
    }
}

