/* Add-with-carry and subtract-with-borrow on sixty-four-bit words.
 *
 * This file is trusted, not verified.  It is the C half of
 * lib/Hacl.Carry64.fst: each function here realizes one `assume val` there,
 * and the postcondition written on that `assume val` -- that `addc` returns
 * the carry out of `a + b + c` and stores the low word through `r` -- is an
 * axiom of the library.  `tests/test_carry64.c` checks both against
 * `unsigned __int128` arithmetic on edge cases and random inputs.
 *
 * Why it exists: a 4x64-bit field multiply is a few dozen carry chains, and
 * written portably (`(unsigned __int128)a + b + c`, then split) neither gcc
 * nor clang reliably turns the chain back into `adc`.  `__builtin_addcll`
 * (clang, gcc 14 and later) and `_addcarry_u64` both compile to one `adc`;
 * the builtin is preferred because clang schedules it better -- X25519 runs
 * 36 us with it against 40 us with the intrinsic, and gcc does not care.
 * Storing the sum through a pointer to a local is what lets the compiler
 * keep it in a register.  Returning the sum and carry packed in one
 * `__int128` instead was measured: clang does not mind, gcc runs X25519 2.4
 * times slower.
 *
 * `adc` and `sbb` are in the x86-64 baseline, so nothing here needs a
 * `target`.  The X25519 code that uses these is compiled for BMI2, for
 * `mulx`, and `Hacl_Carry64_supported` is the run-time check that picks it.
 * Elsewhere the bodies fall back to `__int128`, which is correct but is not
 * what anyone should be calling: `supported` is false there.
 *
 * The carry in `c` must be 0 or 1.  The verified callers guarantee it --
 * it is a precondition of the `assume val`s -- but the three bodies do not
 * agree outside that range: `_addcarry_u64` reads any nonzero `c` as 1,
 * while the builtin and the `__int128` fallback add `c` as a number.
 */

#ifndef HACL_CARRY64_H
#define HACL_CARRY64_H

#include <stdbool.h>
#include <stdint.h>

#if defined(__x86_64__)
#include <immintrin.h>
#endif

#define HACL_CARRY64_INLINE __attribute__((always_inline)) static inline

#if defined(__has_builtin)
#if __has_builtin(__builtin_addcll) && __has_builtin(__builtin_subcll)
#define HACL_CARRY64_BUILTIN 1
#endif
#endif

HACL_CARRY64_INLINE uint64_t Hacl_Carry64_addc(uint64_t c, uint64_t a,
                                               uint64_t b, uint64_t *r) {
#if defined(HACL_CARRY64_BUILTIN)
  unsigned long long co;
  *r = __builtin_addcll(a, b, c, &co);
  return co;
#elif defined(__x86_64__)
  unsigned long long s;
  unsigned char o = _addcarry_u64((unsigned char)c, a, b, &s);
  *r = (uint64_t)s;
  return (uint64_t)o;
#else
  unsigned __int128 t = (unsigned __int128)a + b + c;
  *r = (uint64_t)t;
  return (uint64_t)(t >> 64);
#endif
}

HACL_CARRY64_INLINE uint64_t Hacl_Carry64_subb(uint64_t c, uint64_t a,
                                               uint64_t b, uint64_t *r) {
#if defined(HACL_CARRY64_BUILTIN)
  unsigned long long co;
  *r = __builtin_subcll(a, b, c, &co);
  return co;
#elif defined(__x86_64__)
  unsigned long long s;
  unsigned char o = _subborrow_u64((unsigned char)c, a, b, &s);
  *r = (uint64_t)s;
  return (uint64_t)o;
#else
  unsigned __int128 t = (unsigned __int128)a - b - c;
  *r = (uint64_t)t;
  return (uint64_t)(t >> 64) & 1;
#endif
}

static inline bool Hacl_Carry64_supported(void) {
#if defined(__x86_64__) && defined(__GNUC__)
  __builtin_cpu_init();
  return __builtin_cpu_supports("bmi2");
#else
  return false;
#endif
}

#endif
