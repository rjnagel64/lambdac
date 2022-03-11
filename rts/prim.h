#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct value *prim_addint32(struct value *x, struct value *y);
struct value *prim_subint32(struct value *x, struct value *y);
struct value *prim_mulint32(struct value *x, struct value *y);

struct value *prim_iszero32(struct value *x);

struct value *prim_eqint32(struct value *x, struct value *y);
struct value *prim_neint32(struct value *x, struct value *y);
struct value *prim_ltint32(struct value *x, struct value *y);
struct value *prim_leint32(struct value *x, struct value *y);
struct value *prim_gtint32(struct value *x, struct value *y);
struct value *prim_geint32(struct value *x, struct value *y);


#endif
