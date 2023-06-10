#ifndef __PANIC_H__
#define __PANIC_H__

__attribute__((noreturn))
void runtime_error(const char *msg);

__attribute__((noreturn))
void unreachable(const char *msg);

__attribute__((noreturn))
void internal_error(const char *msg);

#endif
