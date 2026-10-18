/* Wiping scratch memory.
 *
 * This file is trusted, not verified.  It is the C half of Hacl.Mem.fst,
 * whose two `assume val`s say that after `Hacl_Mem_wipe(a, n)` the contents
 * of `a` are unknown, and that `Hacl_Mem_free(a, n)` releases an array that
 * Hacl.Mem.alloc returned.  Both are plainly true of the code below.
 *
 * What the F* side cannot state is that the zeroes actually reach memory.
 * A store to an object that is about to go out of scope is dead, and a
 * compiler is entitled to delete it.  The empty asm statement takes the
 * buffer as a memory input, so as far as the optimizer knows, something
 * reads all of it after the memset.  It emits no instructions.  glibc's
 * explicit_bzero clobbers "memory" instead, which would also make the
 * compiler reload every other value it holds from memory: in the curve
 * arithmetic that costs up to a third of the running time.
 *
 * `n` counts elements, not bytes.
 */

#ifndef HACL_MEM_H
#define HACL_MEM_H

#include <stdlib.h>
#include <string.h>

#if defined(__GNUC__) || defined(__clang__)

#define Hacl_Mem_wipe(a, n)                                             \
  do {                                                                  \
    void *hacl_mem_p_ = (void *)(a);                                    \
    memset(hacl_mem_p_, 0, (size_t)(n) * sizeof (a)[0]);                \
    __asm__ __volatile__("" : : "m"(*(char (*)[(size_t)(n) * sizeof (a)[0]])hacl_mem_p_));\
  } while (0)

#else

static inline void Hacl_Mem_wipe_bytes(void *p, size_t len) {
  volatile unsigned char *q = (volatile unsigned char *)p;
  while (len--) *q++ = 0;
}

#define Hacl_Mem_wipe(a, n) Hacl_Mem_wipe_bytes((void *)(a), (size_t)(n) * sizeof (a)[0])

#endif

#define Hacl_Mem_free(a, n)                                             \
  do {                                                                  \
    Hacl_Mem_wipe(a, n);                                                \
    free((void *)(a));                                                  \
  } while (0)

#endif
