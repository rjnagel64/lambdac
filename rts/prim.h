#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct constant *prim_addint32(struct constant *x, struct constant *y);
struct constant *prim_subint32(struct constant *x, struct constant *y);
struct constant *prim_mulint32(struct constant *x, struct constant *y);

struct sum *prim_eqint32(struct constant *x, struct constant *y);
struct sum *prim_neint32(struct constant *x, struct constant *y);
struct sum *prim_ltint32(struct constant *x, struct constant *y);
struct sum *prim_leint32(struct constant *x, struct constant *y);
struct sum *prim_gtint32(struct constant *x, struct constant *y);
struct sum *prim_geint32(struct constant *x, struct constant *y);


#endif
