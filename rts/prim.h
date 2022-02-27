#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct value *prim_addint32(struct value *x, struct value *y);
struct value *prim_subint32(struct value *x, struct value *y);
struct value *prim_mulint32(struct value *x, struct value *y);
struct value *prim_iszero32(struct value *x);


#endif
