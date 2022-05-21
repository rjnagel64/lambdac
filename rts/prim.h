#ifndef __PRIM_H__
#define __PRIM_H__

#include "alloc.h"

struct constant *prim_addint64(struct constant *x, struct constant *y);
struct constant *prim_subint64(struct constant *x, struct constant *y);
struct constant *prim_mulint64(struct constant *x, struct constant *y);
struct constant *prim_negint64(struct constant *x);

struct bool_value *prim_eqint64(struct constant *x, struct constant *y);
struct bool_value *prim_neint64(struct constant *x, struct constant *y);
struct bool_value *prim_ltint64(struct constant *x, struct constant *y);
struct bool_value *prim_leint64(struct constant *x, struct constant *y);
struct bool_value *prim_gtint64(struct constant *x, struct constant *y);
struct bool_value *prim_geint64(struct constant *x, struct constant *y);


#endif
