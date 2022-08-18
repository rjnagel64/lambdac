
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

// An experiment with re-vamping the runtime to use separately-passed type
// information.
//
// All changes have been implemented into the RTS, and several have been
// superseded by subsequent improvements.

/// PROBLEM: GC
//* need to mark allocations
//* need access to all allocation
//
// => I *think* I can add a header back to each type? mark/sweep casts boxed to
// gc_header*, which I think is valid.

// Technically, this probably should be gc_header *, but it casts easier
typedef void* boxed;

struct gc_header {
    int mark;
    struct gc_header *next;
};

// 'type_info' should contain enough information to GC/trace a value
// of this type. (e.g., a trace method, or a data structure that specifies
// fields, etc.)
//
// 'type_info' is a value that (uniquely?) represents a type. It's honestly
// halfway to being a singleton, to keep a type around at runtime.
// This lets a closure's type environment be simply part of its value
// environment.
typedef struct {
    // I do like having a type_id field, though. I guess I could use it to
    // implement 'Typeable' or 'Dynamic' someday (and also do sanity checks on
    // types)
    uint64_t type_id;
    void (*trace)(boxed self);
    // Note: I'm starting to worry that type_info may have free variables, and
    // may therefore need to be boxed. Is this truly necessary or/and viable?
    // Possibly only existential types need this complication.
    // (something something stack of type info for existential bound variables,
    // deBruijn indexes to reference them?)
    // (Hmm. Closure types `∃a.a * ((a,...) -> 0)` theoretically could store
    // the type info for 'a' in the product type, because it's a polymorphic
    // product)
} type_info;

struct thunk {
    // Even though closures store their enter method, we still have the enter
    // field here, to avoid needing to the actual type of the boxed closure.
    void (*enter)(void);
    boxed closure;
    type_info closure_info;
    boxed args;
    type_info args_info;
};

static struct thunk current_thunk; // Note: GC root
static boxed result = NULL; // Note: GC root? irrelevant.
static type_info result_info;

static size_t num_allocs;
static struct gc_header *head_alloc;

struct gray_object {
    type_info info;
    boxed value;
};
static struct gray_object *gray_list = NULL;
static size_t gray_len = 0;
static size_t gray_capacity = 0;
void mark_gray(type_info info, boxed value) {
    if (gray_len == gray_capacity) {
        gray_capacity *= 2;
        gray_list = realloc(gray_list, gray_capacity * sizeof(struct gray_object));
    }
    gray_len++;
    gray_list[gray_len].info = info;
    gray_list[gray_len].value = value;
}

void mark(void) {
    // Init gray list
    // Add roots to gray list
    // until gray list empty:
    // pop first object
    // mark first object
    // use info of first to extend gray list
}

void sweep(void) {
    // For each object:
    // if object not marked, free it.
    // if object marked, unmark and continue.
    // Set new threshold based on number of live objects
}

void collect(void) {
    mark();
    sweep();
}

void cons_new_alloc(struct gc_header *alloc) {
    alloc->mark = 0;
    alloc->next = head_alloc;
    head_alloc = alloc;
    num_allocs++;
    // push_local(alloc);
}

// static size_t num_locals;
// static size_t locals_capacity;
// static boxed *locals; // Note: GC root
// static type_info *locals_info;

void halt_with(type_info val_info, boxed val) {
    result_info = val_info;
    result = val;
}

void driver(void) {
    while (result == NULL) {
        current_thunk.enter();
    }
}


struct _int64_box {
    struct gc_header header;
    int64_t value;
};
typedef struct _int64_box *int64_box;
void trace_int64_box(boxed _self) {
    int64_box self = _self;
}
static type_info int64_box_info = { 1, trace_int64_box };

int64_box box_int64(int64_t val) {
    int64_box x = malloc(sizeof(struct _int64_box));
    x->value = val;
    cons_new_alloc((struct gc_header *)x);
    return x;
}

int64_box boxed_int64_add(int64_box x, int64_box y) {
    return box_int64(x->value + y->value);
}


// Arguably, I should hoist the closure environment types up with the other
// product types.
// Each type declaration generates:
// * a struct for the type
// * a type info (and probably the corresponding trace method)
// * an 'alloc_$type' method
// * type-specific things (such as enter/tailcall for closures, probably
// projections for products, etc.)

// Each closure type ∃a.(a, s1, ..., sn) -> 0 generates the following declarations:
// * a closure type
// * info for the closure type
// * an arguments type for s1, ..., sn
// * info for the arguments type
// * allocation for the closure
// * allocation for the arguments
// * enter for the closure
// * tailcall/suspend for the closure
struct closure_1 {
    struct gc_header header;
    boxed env;
    type_info env_info;
    void (*code)(boxed env, int64_box z);
    void (*enter)(void);
};
void trace_closure_1(boxed _self) {
    struct closure_1 *self = _self;
    mark_gray(self->env_info, self->env);
}
static type_info closure_1_info = { 5, trace_closure_1 };
struct closure_1 *alloc_closure_1(boxed env, type_info env_info, void (*code)(boxed env, int64_box z), void (*enter)(void)) {
    struct closure_1 *closure = malloc(sizeof(struct closure_1));
    closure->env = env;
    closure->env_info = env_info;
    closure->code = code;
    closure->enter = enter;
    cons_new_alloc((struct gc_header *)closure);
    return closure;
}
struct args_1 {
    struct gc_header header;
    // A smarter scheme would just 'typedef int64_box args_1;'
    int64_box z;
};
void trace_args_1(boxed _self) {
    struct args_1 *self = _self;
    mark_gray(int64_box_info, self->z);
}
static type_info args_1_info = { 13, trace_args_1 };
struct args_1 *alloc_args_1(int64_box z) {
    struct args_1 *args = malloc(sizeof(struct args_1));
    args->z = z;
    cons_new_alloc((struct gc_header *)args);
    return args;
}
void enter_1(void) {
    // Sanity check: opening a closure with the correct method, avoid UB.
    // assert(current_thunk.closure_info.type_id == closure_1_info.type_id);
    struct closure_1 *closure = current_thunk.closure;
    // assert(current_thunk.args_info.type_id == args_1_info.type_id);
    struct args_1 *args = current_thunk.args;
    closure->code(closure->env, args->z);
}
void tailcall_1(struct closure_1 *closure, int64_box z) {
    current_thunk.enter = closure->enter;
    current_thunk.closure = closure;
    current_thunk.closure_info = closure_1_info;
    current_thunk.args = alloc_args_1(z);
    current_thunk.args_info = args_1_info;
}

struct closure_2 {
    struct gc_header header;
    boxed env;
    type_info env_info;
    void (*code)(boxed env, int64_box y, struct closure_1 *k1);
    void (*enter)(void);
};
void trace_closure_2(boxed _self) {
    struct closure_2 *self = _self;
    mark_gray(self->env_info, self->env);
}
static type_info closure_2_info = { 6, trace_closure_2 };
struct closure_2 *alloc_closure_2(boxed env, type_info env_info, void (*code)(boxed env, int64_box y, struct closure_1 *k1), void (*enter)(void)) {
    struct closure_2 *closure = malloc(sizeof(struct closure_2));
    closure->env = env;
    closure->env_info = env_info;
    closure->code = code;
    closure->enter = enter;
    cons_new_alloc((struct gc_header *)closure);
    return closure;
}
struct args_2 {
    struct gc_header header;
    int64_box y;
    struct closure_1 *k1;
};
void trace_args_2(boxed _self) {
    struct args_2 *self = _self;
    mark_gray(int64_box_info, self->y);
    mark_gray(closure_1_info, self->k1);
}
static type_info args_2_info = { 14, trace_args_2 };
struct args_2 *alloc_args_2(int64_box y, struct closure_1 *k1) {
    struct args_2 *args = malloc(sizeof(struct args_2));
    args->y = y;
    args->k1 = k1;
    cons_new_alloc((struct gc_header *)args);
    return args;
}
void enter_2(void) {
    struct closure_2 *closure = current_thunk.closure;
    struct args_2 *args = current_thunk.args;
    closure->code(closure->env, args->y, args->k1);
}
void tailcall_2(struct closure_2 *closure, int64_box y, struct closure_1 *k1) {
    current_thunk.enter = closure->enter;
    current_thunk.closure = closure;
    current_thunk.closure_info = closure_2_info;
    current_thunk.args = alloc_args_2(y, k1);
    current_thunk.args_info = args_2_info;
}

struct closure_3 {
    struct gc_header header;
    boxed env;
    type_info env_info;
    void (*code)(boxed env, struct closure_2 *add3);
    void (*enter)(void);
};
void trace_closure_3(boxed _self) {
    struct closure_3 *self = _self;
    mark_gray(self->env_info, self->env);
}
static type_info closure_3_info = { 7, trace_closure_3 };
struct closure_3 *alloc_closure_3(boxed env, type_info env_info, void (*code)(boxed env, struct closure_2 *add3), void (*enter)(void)) {
    struct closure_3 *closure = malloc(sizeof(struct closure_3));
    closure->env = env;
    closure->env_info = env_info;
    closure->code = code;
    closure->enter = enter;
    cons_new_alloc((struct gc_header *)closure);
    return closure;
}
struct args_3 {
    struct gc_header header;
    struct closure_2 *add3;
};
void trace_args_3(boxed _self) {
    struct args_3 *self = _self;
    mark_gray(closure_2_info, self->add3);
}
static type_info args_3_info = { 15, trace_args_3 };
struct args_3 *alloc_args_3(struct closure_2 *add3) {
    struct args_3 *args = malloc(sizeof(struct args_3));
    args->add3 = add3;
    cons_new_alloc((struct gc_header *)args);
    return args;
}
void enter_3(void) {
    struct closure_3 *closure = current_thunk.closure;
    struct args_3 *args = current_thunk.args;
    closure->code(closure->env, args->add3);
}
void tailcall_3(struct closure_3 *closure, struct closure_2 *add3) {
    current_thunk.enter = closure->enter;
    current_thunk.closure = closure;
    current_thunk.closure_info = closure_3_info;
    current_thunk.args = alloc_args_3(add3);
    current_thunk.args_info = args_3_info;
}

struct closure_4 {
    struct gc_header header;
    boxed env;
    type_info env_info;
    void (*code)(boxed env, int64_box x, struct closure_3 *k0);
    void (*enter)(void);
};
void trace_closure_4(boxed _self) {
    struct closure_4 *self = _self;
    mark_gray(self->env_info, self->env);
}
static type_info closure_4_info = { 8, trace_closure_4 };
struct closure_4 *alloc_closure_4(boxed env, type_info env_info, void (*code)(boxed env, int64_box x, struct closure_3 *k0), void (*enter)(void)) {
    struct closure_4 *closure = malloc(sizeof(struct closure_4));
    closure->env = env;
    closure->env_info = env_info;
    closure->code = code;
    closure->enter = enter;
    cons_new_alloc((struct gc_header *)closure);
    return closure;
}
struct args_4 {
    struct gc_header header;
    int64_box x;
    struct closure_3 *k0;
};
void trace_args_4(boxed _self) {
    struct args_4 *self = _self;
    mark_gray(int64_box_info, self->x);
    mark_gray(closure_3_info, self->k0);
}
static type_info args_4_info = { 16, trace_args_4 };
struct args_4 *alloc_args_4(int64_box x, struct closure_3 *k0) {
    struct args_4 *args = malloc(sizeof(struct args_4));
    args->x = x;
    args->k0 = k0;
    cons_new_alloc((struct gc_header *)args);
    return args;
}
void enter_4(void) {
    struct closure_4 *closure = current_thunk.closure;
    struct args_4 *args = current_thunk.args;
    closure->code(closure->env, args->x, args->k0);
}
void tailcall_4(struct closure_4 *closure, int64_box x, struct closure_3 *k0) {
    current_thunk.enter = closure->enter;
    current_thunk.closure = closure;
    current_thunk.closure_info = closure_4_info;
    current_thunk.args = alloc_args_4(x, k0);
    current_thunk.args_info = args_4_info;
}



// Each closure declaration generates:
// * an environment type
// * environment type info
// * code for that closure.
struct k1_env {
    struct gc_header header;
};
void trace_k1_env(boxed _self) {
    struct k1_env *self = _self;
}
static type_info k1_env_info = { 9, trace_k1_env };
struct k1_env *alloc_k1_env(void) {
    struct k1_env *env = malloc(sizeof(struct k1_env));
    cons_new_alloc((struct gc_header *)env);
    return env;
}
void k1_code(boxed env, int64_box z) {
    halt_with(int64_box_info, z);
}

struct k0_env {
    struct gc_header header;
};
void trace_k0_env(boxed _self) {
    struct k0_env *self = _self;
}
static type_info k0_env_info = { 10, trace_k0_env };
struct k0_env *alloc_k0_env(void) {
    struct k0_env *env = malloc(sizeof(struct k0_env));
    cons_new_alloc((struct gc_header *)env);
    return env;
}
void k0_code(boxed env, struct closure_2 *add3) {
    struct k1_env *k1_env_tmp = alloc_k1_env();
    struct closure_1 *k1 = alloc_closure_1(k1_env_tmp, k1_env_info, k1_code, enter_1);
    int64_box t0 = box_int64(5);
    tailcall_2(add3, t0, k1);
}

// a 1-tuple (int,)
// A smarter thing to do would be just have the environment type be
// 'int64_box'. That's kind of the whole point of having the environment be
// 'boxed': you can put any type in it.
struct inner_env {
    struct gc_header header;
    int64_box x;
};
void trace_inner_env(boxed _self) {
    struct inner_env *self = _self;
    mark_gray(int64_box_info, self->x);
}
static type_info inner_env_info = { 11, trace_inner_env };
struct inner_env *alloc_inner_env(int64_box x) {
    struct inner_env *env = malloc(sizeof(struct inner_env));
    env->x = x;
    cons_new_alloc((struct gc_header *)env);
    return env;
}
void inner_code(boxed env, int64_box y, struct closure_1 *k1) {
    struct inner_env *envp = env;
    int64_box z = boxed_int64_add(envp->x, y);
    tailcall_1(k1, z);
}

struct adder_env {
    struct gc_header header;
};
void trace_adder_env(boxed _self) {
    struct adder_env *self = _self;
}
static type_info adder_env_info = { 12, trace_adder_env };
struct adder_env *alloc_adder_env(void) {
    struct adder_env *env = malloc(sizeof(struct adder_env));
    cons_new_alloc((struct gc_header *)env);
    return env;
}
void adder_code(boxed env, int64_box x, struct closure_3 *k0) {
    struct closure_2 *inner = alloc_closure_2(alloc_inner_env(x), inner_env_info, inner_code, enter_2);
    tailcall_3(k0, inner);
}

void program_entry(void) {
    struct closure_4 *adder = alloc_closure_4(alloc_adder_env(), adder_env_info, adder_code, enter_4);
    struct closure_3 *k0 = alloc_closure_3(alloc_k0_env(), k0_env_info, k0_code, enter_3);
    int64_box t0 = box_int64(3);
    tailcall_4(adder, t0, k0);
}

int main(void) {
    /* init_gc(); */

    program_entry();
    driver();
    if (result_info.type_id != int64_box_info.type_id) {
        printf("error: incorrect result type %llu\n", result_info.type_id);
        return 1;
    }
    int64_box val = result;
    printf("result = %lld\n", val->value);

    /* destroy_gc(); */
    return 0;
}
