#ifndef __PANIC_H__
#define __PANIC_H__

// Hmm. Consider splitting 'panic' into 'runtime_error' and 'internal_error'
__attribute__((noreturn))
void panic(const char *msg);

#endif
