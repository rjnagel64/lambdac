#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct constant *prim_addint64(struct constant *x, struct constant *y);
struct constant *prim_subint64(struct constant *x, struct constant *y);
struct constant *prim_mulint64(struct constant *x, struct constant *y);

struct sum *prim_eqint64(struct constant *x, struct constant *y);
struct sum *prim_neint64(struct constant *x, struct constant *y);
struct sum *prim_ltint64(struct constant *x, struct constant *y);
struct sum *prim_leint64(struct constant *x, struct constant *y);
struct sum *prim_gtint64(struct constant *x, struct constant *y);
struct sum *prim_geint64(struct constant *x, struct constant *y);


#endif
