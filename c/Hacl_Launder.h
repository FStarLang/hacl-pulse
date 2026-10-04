/* A value barrier.
 *
 * This file is trusted, not verified.  It is the C half of Hacl.Launder.fst,
 * whose single `assume val` says that `launder x` is `x`.  That postcondition
 * is plainly true of everything below -- the function returns its argument --
 * so unlike the axioms in Hacl_Vec128.h this one costs nothing to believe.
 *
 * What the file is *for* is the part the F* side cannot state.  A
 * constant-time table lookup computes sixteen masks, one per entry, fifteen
 * of which are zero, and folds every entry through its mask so that the time
 * taken and the addresses touched do not depend on which entry was wanted.
 * That argument assumes the compiler treats the mask as an unknown machine
 * word.  It need not: the masks come from comparing the secret index against
 * the constants zero through fifteen, and a compiler that notices this is
 * free to turn the fold into a sixteen-way branch on the secret, which is
 * exactly what clang -O3 did here.  See `tests/test_launder.c`.
 *
 * Passing the mask through `Hacl_Launder_u64` removes the information the
 * compiler was using.  After the barrier the mask is a value that arrived
 * from somewhere unknown, so there is nothing left to case-split on and the
 * fold has to be emitted as the arithmetic it was written as.
 *
 * The asm statement has no instructions in it and no clobbers; it costs
 * nothing at run time.  Its whole content is the constraint "+r", which says
 * that this value goes into a register, is read, and is written -- so the
 * value that comes out is, as far as the optimizer may assume, unrelated to
 * the one that went in.
 */

#ifndef HACL_LAUNDER_H
#define HACL_LAUNDER_H

#include <stdint.h>

#if defined(__GNUC__) || defined(__clang__)

static inline uint64_t Hacl_Launder_u64(uint64_t x) {
  __asm__("" : "+r"(x));
  return x;
}

#else

/* Without inline asm, a local volatile does the same job by forcing the
 * value through memory.  It costs a store and a load, and it is correct
 * under threads because the object is on the calling frame. */
static inline uint64_t Hacl_Launder_u64(uint64_t x) {
  volatile uint64_t v = x;
  return v;
}

#endif

#endif
