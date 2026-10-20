/* The 256-bit vector type and the AVX2 intrinsics.
 *
 * This file is trusted, not verified.  It is the C half of
 * lib/Hacl.Vec256.fst: every function here realizes one `assume val` there,
 * and the postcondition written on that `assume val` is an axiom of the
 * library.  `tests/test_vec256.c` checks each of them against a scalar
 * transcription on random inputs.
 *
 * Everything except `Hacl_Vec256_supported` carries `target("avx2")`, and so
 * does every generated function that reaches it, by way of the `CPrologue`
 * and `custard_c_closure_prologue` attributes on the F* side.  On a target
 * that is not x86, `Hacl_Vec256_supported` is false and the rest of this file
 * is unreachable; the bodies are there so that the program links.
 */

#ifndef HACL_VEC256_H
#define HACL_VEC256_H

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#if defined(__x86_64__) || defined(__i386__)

#include <immintrin.h>

typedef __m256i Hacl_Vec256_t;

#define HACL_VEC256 \
  __attribute__((target("avx2"), always_inline)) static inline

/* Unaligned, because an F* array carries no alignment. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_load(uint8_t *p) {
  return _mm256_loadu_si256((const __m256i *)(const void *)p);
}

HACL_VEC256 void Hacl_Vec256_store(uint8_t *p, Hacl_Vec256_t x) {
  _mm256_storeu_si256((__m256i *)(void *)p, x);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_zero(void) {
  return _mm256_setzero_si256();
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_bcast(uint32_t x) {
  return _mm256_set1_epi32((int)x);
}

/* `_mm256_setr_epi32` takes its arguments from lane zero up. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_iota(void) {
  return _mm256_setr_epi32(0, 1, 2, 3, 4, 5, 6, 7);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_add32(Hacl_Vec256_t a,
                                            Hacl_Vec256_t b) {
  return _mm256_add_epi32(a, b);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_xor(Hacl_Vec256_t a, Hacl_Vec256_t b) {
  return _mm256_xor_si256(a, b);
}

/* Every call site passes a literal, so after inlining exactly one branch
 * survives.  A rotation by a whole number of bytes is a byte shuffle within
 * each lane, which is one instruction instead of three. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_rotl(Hacl_Vec256_t a, uint32_t s) {
  if (s == 16)
    return _mm256_shuffle_epi8(
        a, _mm256_setr_epi8(2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12,
                            13, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15,
                            12, 13));
  if (s == 8)
    return _mm256_shuffle_epi8(
        a, _mm256_setr_epi8(3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12, 13,
                            14, 3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12,
                            13, 14));
  return _mm256_or_si256(
      _mm256_sll_epi32(a, _mm_cvtsi32_si128((int)s)),
      _mm256_srl_epi32(a, _mm_cvtsi32_si128((int)(32 - s))));
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_unpacklo32(Hacl_Vec256_t a,
                                                 Hacl_Vec256_t b) {
  return _mm256_unpacklo_epi32(a, b);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_unpackhi32(Hacl_Vec256_t a,
                                                 Hacl_Vec256_t b) {
  return _mm256_unpackhi_epi32(a, b);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_unpacklo64(Hacl_Vec256_t a,
                                                 Hacl_Vec256_t b) {
  return _mm256_unpacklo_epi64(a, b);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_unpackhi64(Hacl_Vec256_t a,
                                                 Hacl_Vec256_t b) {
  return _mm256_unpackhi_epi64(a, b);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_lo128(Hacl_Vec256_t a, Hacl_Vec256_t b) {
  return _mm256_permute2x128_si256(a, b, 0x20);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_hi128(Hacl_Vec256_t a, Hacl_Vec256_t b) {
  return _mm256_permute2x128_si256(a, b, 0x31);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_add64(Hacl_Vec256_t a,
                                            Hacl_Vec256_t b) {
  return _mm256_add_epi64(a, b);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_mul32(Hacl_Vec256_t a,
                                            Hacl_Vec256_t b) {
  return _mm256_mul_epu32(a, b);
}

/* The shift count is a register operand so that a non-constant argument
 * still compiles; every call site passes a literal, which the compiler
 * folds into the immediate form. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_shr64(Hacl_Vec256_t a, uint32_t s) {
  return _mm256_srl_epi64(a, _mm_cvtsi32_si128((int)s));
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_shl64(Hacl_Vec256_t a, uint32_t s) {
  return _mm256_sll_epi64(a, _mm_cvtsi32_si128((int)s));
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_mask26(Hacl_Vec256_t a) {
  return _mm256_and_si256(a, _mm256_set1_epi64x(0x3ffffff));
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_bcast64(uint64_t x) {
  return _mm256_set1_epi64x((long long)x);
}

/* `_mm256_set_epi64x` takes its arguments from the top lane down. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_set64(uint64_t x0, uint64_t x1,
                                            uint64_t x2, uint64_t x3) {
  return _mm256_set_epi64x((long long)x3, (long long)x2, (long long)x1,
                           (long long)x0);
}

HACL_VEC256 void Hacl_Vec256_store64(uint64_t *p, Hacl_Vec256_t x) {
  _mm256_storeu_si256((__m256i *)(void *)p, x);
}

HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_xor64(Hacl_Vec256_t a,
                                            Hacl_Vec256_t b) {
  return _mm256_xor_si256(a, b);
}

/* `_mm256_andnot_si256(a, b)` is `~a & b`. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_andnot64(Hacl_Vec256_t a,
                                               Hacl_Vec256_t b) {
  return _mm256_andnot_si256(a, b);
}

/* As for `Hacl_Vec256_rotl`: every call site passes a literal, and a
 * rotation by a whole number of bytes is one byte shuffle. */
HACL_VEC256 Hacl_Vec256_t Hacl_Vec256_rotl64(Hacl_Vec256_t a, uint32_t s) {
  if (s == 8)
    return _mm256_shuffle_epi8(
        a, _mm256_setr_epi8(7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13,
                            14, 7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12,
                            13, 14));
  if (s == 56)
    return _mm256_shuffle_epi8(
        a, _mm256_setr_epi8(1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15,
                            8, 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14,
                            15, 8));
  return _mm256_or_si256(
      _mm256_sll_epi64(a, _mm_cvtsi32_si128((int)s)),
      _mm256_srl_epi64(a, _mm_cvtsi32_si128((int)(64 - s))));
}

static inline bool Hacl_Vec256_supported(void) {
#if defined(__GNUC__)
  __builtin_cpu_init();
  return __builtin_cpu_supports("avx2");
#else
  return false;
#endif
}

#else /* not x86 */

typedef struct {
  uint32_t w[8];
} Hacl_Vec256_t;

/* Unreachable: every caller is guarded by Hacl_Vec256_supported.  They are
 * defined rather than merely declared so that the program links. */
static inline Hacl_Vec256_t Hacl_Vec256_zero(void) {
  Hacl_Vec256_t r;
  memset(&r, 0, sizeof r);
  return r;
}
static inline Hacl_Vec256_t Hacl_Vec256_load(uint8_t *p) {
  Hacl_Vec256_t r;
  memcpy(&r, p, 32);
  return r;
}
static inline void Hacl_Vec256_store(uint8_t *p, Hacl_Vec256_t x) {
  memcpy(p, &x, 32);
}
static inline Hacl_Vec256_t Hacl_Vec256_bcast(uint32_t x) {
  Hacl_Vec256_t r;
  for (int i = 0; i < 8; i++) r.w[i] = x;
  return r;
}
static inline Hacl_Vec256_t Hacl_Vec256_iota(void) {
  Hacl_Vec256_t r;
  for (int i = 0; i < 8; i++) r.w[i] = (uint32_t)i;
  return r;
}
static inline Hacl_Vec256_t Hacl_Vec256_rotl(Hacl_Vec256_t a, uint32_t s) {
  (void)s;
  return a;
}
#define HACL_VEC256_STUB2(name)                                              \
  static inline Hacl_Vec256_t name(Hacl_Vec256_t a, Hacl_Vec256_t b) {       \
    (void)b;                                                                 \
    return a;                                                                \
  }
HACL_VEC256_STUB2(Hacl_Vec256_add32)
HACL_VEC256_STUB2(Hacl_Vec256_xor)
HACL_VEC256_STUB2(Hacl_Vec256_unpacklo32)
HACL_VEC256_STUB2(Hacl_Vec256_unpackhi32)
HACL_VEC256_STUB2(Hacl_Vec256_unpacklo64)
HACL_VEC256_STUB2(Hacl_Vec256_unpackhi64)
HACL_VEC256_STUB2(Hacl_Vec256_lo128)
HACL_VEC256_STUB2(Hacl_Vec256_hi128)
HACL_VEC256_STUB2(Hacl_Vec256_add64)
HACL_VEC256_STUB2(Hacl_Vec256_mul32)
HACL_VEC256_STUB2(Hacl_Vec256_xor64)
HACL_VEC256_STUB2(Hacl_Vec256_andnot64)
#undef HACL_VEC256_STUB2
static inline Hacl_Vec256_t Hacl_Vec256_shr64(Hacl_Vec256_t a, uint32_t s) {
  (void)s;
  return a;
}
static inline Hacl_Vec256_t Hacl_Vec256_shl64(Hacl_Vec256_t a, uint32_t s) {
  (void)s;
  return a;
}
static inline Hacl_Vec256_t Hacl_Vec256_mask26(Hacl_Vec256_t a) { return a; }
static inline Hacl_Vec256_t Hacl_Vec256_rotl64(Hacl_Vec256_t a, uint32_t s) {
  (void)s;
  return a;
}
static inline Hacl_Vec256_t Hacl_Vec256_bcast64(uint64_t x) {
  Hacl_Vec256_t r;
  for (int i = 0; i < 4; i++) memcpy(&r.w[2 * i], &x, 8);
  return r;
}
static inline Hacl_Vec256_t Hacl_Vec256_set64(uint64_t x0, uint64_t x1,
                                            uint64_t x2, uint64_t x3) {
  Hacl_Vec256_t r;
  uint64_t x[4] = {x0, x1, x2, x3};
  memcpy(&r, x, 32);
  return r;
}
static inline void Hacl_Vec256_store64(uint64_t *p, Hacl_Vec256_t x) {
  memcpy(p, &x, 32);
}
static inline bool Hacl_Vec256_supported(void) { return false; }

#endif

#endif /* HACL_VEC256_H */
