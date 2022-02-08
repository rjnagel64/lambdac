
#include "rts.h"

struct k0_env {
    struct value *n;
    struct cont *k;
};

struct k0_env *allocate_k0_env(struct value *n, struct cont *k) {
    struct k0_env *env = malloc(sizeof(struct k0_env));
    env->n = n;
    env->k = k;
    return env;
}

void trace_k0_env(void *env) {
    struct k0_env *env0 = env;
    trace_value(env0->n);
    trace_cont(env0->k);
}

void k0_code(void *env, struct value *arg) {
    struct k0_env *env0 = (struct k0_env *)env;
    allocate_locals(1);

    struct value *t1 = prim_mulint32(env0->n, arg);
    store_local(0, (struct alloc_header *)t1);
    JUMP(env0->k, t1);
}

struct fact_env {
    struct fun *fact;
};

struct fact_env *allocate_fact_env(struct fun *fact) {
    struct fact_env *env = malloc(sizeof(struct fact_env));
    env->fact = fact;
    return env;
}

void trace_fact_env(void *env) {
    struct fact_env *env0 = env;
    trace_fun(env0->fact);
}

void fact_code(void *env, struct value *n, struct cont *k) {
    struct fact_env *env0 = (struct fact_env *)env;
    allocate_locals(3);

    int32_t x = int32_value(n);
    if (x == 0) {
        struct value *t0 = allocate_int32(1);
        store_local(0, (struct alloc_header *)t0);
        JUMP(k, t0);
    } else {
        struct value *t1 = allocate_int32(1);
        store_local(0, (struct alloc_header *)t1);
        struct value *t2 = prim_subint32(n, t1);
        store_local(1, (struct alloc_header *)t2);
        struct k0_env *env1 = allocate_k0_env(n, k);
        struct cont *k0 = allocate_cont(env1, k0_code, trace_k0_env);
        store_local(2, (struct alloc_header *)k0);
        TAILCALL(env0->fact, t1, k0);
    }
}

void halt_code(void *env, struct value *arg) {
    allocate_locals(0);
    HALT(arg);
}

void trace_halt_env(void *env) {
}

void program_entry(void) {
    struct value *t0 = allocate_int32(16); // largest that fits in int32_t without wrapping.

    struct fact_env *fact_env = allocate_fact_env(NULL);
    struct fun *fact = allocate_fun(fact_env, fact_code, trace_fact_env);
    fact_env->fact = fact;

    struct cont *halt = allocate_cont(NULL, halt_code, trace_halt_env);

    TAILCALL(fact, t0, halt);
}
