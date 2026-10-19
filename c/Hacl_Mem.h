/* Wiping scratch memory.
 *
 * This file is trusted, not verified.  It is the C half of Hacl.Mem.fst,
 * whose two `assume val`s say that after `Hacl_Mem_wipe(a, n)` the contents
 * of `a` are unknown, and that `Hacl_Mem_free(a, n)` releases an array that
 * Hacl.Mem.alloc returned.  Both are plainly true of the code below.
 *
 * What the F* side cannot state is that the zeroes actually reach memory.
 * A store to an object that is about to go out of scope is dead, and a
 * compiler is entitled to delete it.  Two ways of preventing that:
 *
 *   - When the length is a compile-time constant multiple of eight, at
 *     most 512 bytes -- every field element and most scratch, once the
 *     extracted Hacl_Mem_wipe__t_N wrapper is inlined -- volatile
 *     eight-byte stores, through a type that may be unaligned and may alias
 *     anything.  gcc lowers a memset of 128 bytes or more, and any memset
 *     whose length it cannot see, to `rep stosq`, whose start-up cost
 *     dominates on buffers this small: on Ed25519 and secp256k1 signing that
 *     was 40% of the running time (bench/REPORT.md Part 70).
 *   - Otherwise memset, followed by an empty asm statement that takes the
 *     buffer as a memory input, so as far as the optimizer knows, something
 *     reads all of it after the memset.  It emits no instructions.  glibc's
 *     explicit_bzero clobbers "memory" instead, which would also make the
 *     compiler reload every other value it holds from memory: in the curve
 *     arithmetic that costs up to a third of the running time.
 *
 * Hacl_Mem_free always takes the second way: a heap length is never a
 * constant, and the smaller wrapper the first way's dead branch leaves out
 * changes gcc's inlining enough to trip a false -Wstringop-overflow in RSA.
 *
 * `n` counts elements, not bytes.
 */

#ifndef HACL_MEM_H
#define HACL_MEM_H

#include <stdlib.h>
#include <string.h>

#if defined(__GNUC__) || defined(__clang__)

typedef unsigned long long __attribute__((aligned(1), may_alias)) Hacl_Mem_word_;

#define Hacl_Mem_wipe_heap_(a, n)                                       \
  do {                                                                  \
    void *hacl_mem_p_ = (void *)(a);                                    \
    memset(hacl_mem_p_, 0, (size_t)(n) * sizeof (a)[0]);                \
    __asm__ __volatile__("" : : "m"(*(char (*)[(size_t)(n) * sizeof (a)[0]])hacl_mem_p_));\
  } while (0)

#define Hacl_Mem_wipe(a, n)                                             \
  do {                                                                  \
    void *hacl_mem_p_ = (void *)(a);                                    \
    size_t hacl_mem_len_ = (size_t)(n) * sizeof (a)[0];                 \
    if (__builtin_constant_p(hacl_mem_len_) && hacl_mem_len_ <= 512 &&  \
        hacl_mem_len_ % 8 == 0) {                                       \
      volatile Hacl_Mem_word_ *hacl_mem_q_ =                            \
        (volatile Hacl_Mem_word_ *)hacl_mem_p_;                         \
      for (size_t hacl_mem_i_ = 0; hacl_mem_i_ < hacl_mem_len_ / 8;     \
           hacl_mem_i_++)                                               \
        hacl_mem_q_[hacl_mem_i_] = 0;                                   \
    } else {                                                            \
      memset(hacl_mem_p_, 0, hacl_mem_len_);                            \
      __asm__ __volatile__("" : : "m"(*(char (*)[hacl_mem_len_])hacl_mem_p_));\
    }                                                                   \
  } while (0)

#else

static inline void Hacl_Mem_wipe_bytes(void *p, size_t len) {
  volatile unsigned char *q = (volatile unsigned char *)p;
  while (len--) *q++ = 0;
}

#define Hacl_Mem_wipe(a, n) Hacl_Mem_wipe_bytes((void *)(a), (size_t)(n) * sizeof (a)[0])
#define Hacl_Mem_wipe_heap_(a, n) Hacl_Mem_wipe(a, n)

#endif

#define Hacl_Mem_free(a, n)                                             \
  do {                                                                  \
    Hacl_Mem_wipe_heap_(a, n);                                          \
    free((void *)(a));                                                  \
  } while (0)

#endif
