/* The 128-bit vector type and the AES-NI / PCLMULQDQ intrinsics.
 *
 * This file is trusted, not verified.  It is the C half of Hacl.Vec128.fsti:
 * every function here realizes one `assume val` there, and the postcondition
 * written on that `assume val` -- for instance that `aesenc` computes
 * `Spec.AES.round` -- is an axiom of the library.  `tests/test_vec128.c`
 * checks each of those axioms against the portable implementation that the
 * rest of hacl-pulse verifies, on random inputs, which is the only way the
 * claim gets any evidence behind it.
 *
 * Every function that touches an instruction beyond the x86-64 baseline
 * carries `target(...)`, and so does every generated function that calls one:
 * `Hacl.Vec128.fsti` puts a `CPrologue` on the entry points and a
 * `custard_c_closure_prologue` on everything they reach.  That is what lets a
 * single translation unit hold both a baseline path and an AES-NI path and
 * pick between them at run time with `Hacl_Vec128_supported`.
 *
 * On a target that is not x86, `Hacl_Vec128_supported` is false and nothing
 * else in this file is ever reached; the bodies are there so the program
 * still compiles and links.
 */

#ifndef HACL_VEC128_H
#define HACL_VEC128_H

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#if defined(__x86_64__) || defined(__i386__)
#define HACL_VEC128_X86 1
#else
#define HACL_VEC128_X86 0
#endif

#if HACL_VEC128_X86

#include <immintrin.h>

typedef __m128i Hacl_Vec128_t;

/* `always_inline` is not an optimization request here: without it the
 * intrinsics become real calls, which is most of the instruction count. */
#define HACL_VEC128_NI \
  __attribute__((target("aes,pclmul,ssse3,sse4.1"), always_inline)) static inline

/* Unaligned, because an F* array carries no alignment. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_load(uint8_t *p) {
  return _mm_loadu_si128((const __m128i *)(const void *)p);
}

HACL_VEC128_NI void Hacl_Vec128_store(uint8_t *p, Hacl_Vec128_t x) {
  _mm_storeu_si128((__m128i *)(void *)p, x);
}

HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_zero(void) {
  return _mm_setzero_si128();
}

HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_xor(Hacl_Vec128_t a,
                                             Hacl_Vec128_t b) {
  return _mm_xor_si128(a, b);
}

/* One full AES round: SubBytes, ShiftRows, MixColumns, AddRoundKey. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_aesenc(Hacl_Vec128_t st,
                                                Hacl_Vec128_t k) {
  return _mm_aesenc_si128(st, k);
}

/* The last round: the same without MixColumns. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_aesenclast(Hacl_Vec128_t st,
                                                    Hacl_Vec128_t k) {
  return _mm_aesenclast_si128(st, k);
}

/* The four halves of a carry-less 64x64 -> 128 multiply.  The immediate has
 * to be a constant expression, so there is one wrapper per combination
 * rather than one taking the selector. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_clmul_ll(Hacl_Vec128_t a,
                                                  Hacl_Vec128_t b) {
  return _mm_clmulepi64_si128(a, b, 0x00);
}
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_clmul_lh(Hacl_Vec128_t a,
                                                  Hacl_Vec128_t b) {
  return _mm_clmulepi64_si128(a, b, 0x10);
}
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_clmul_hl(Hacl_Vec128_t a,
                                                  Hacl_Vec128_t b) {
  return _mm_clmulepi64_si128(a, b, 0x01);
}
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_clmul_hh(Hacl_Vec128_t a,
                                                  Hacl_Vec128_t b) {
  return _mm_clmulepi64_si128(a, b, 0x11);
}

/* Shifts of the whole register by whole bytes, and of each 64-bit lane by a
 * bit count; together these are the GF(2^128) reduction. */
#define HACL_VEC128_SHIFT(n)                                                 \
  HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_shift_left_bytes_##n(             \
      Hacl_Vec128_t a) {                                                     \
    return _mm_slli_si128(a, n);                                             \
  }                                                                          \
  HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_shift_right_bytes_##n(            \
      Hacl_Vec128_t a) {                                                     \
    return _mm_srli_si128(a, n);                                             \
  }
HACL_VEC128_SHIFT(4)
HACL_VEC128_SHIFT(8)
#undef HACL_VEC128_SHIFT

HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_shift_left_lanes64(Hacl_Vec128_t a,
                                                            uint32_t n) {
  return _mm_sll_epi64(a, _mm_cvtsi32_si128((int)n));
}

HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_shift_right_lanes64(Hacl_Vec128_t a,
                                                             uint32_t n) {
  return _mm_srl_epi64(a, _mm_cvtsi32_si128((int)n));
}

/* Reverse the sixteen bytes.  GHASH reads its operands big-endian and the
 * carry-less multiplier is little-endian, so every GHASH operand crosses
 * this once on the way in and once on the way out. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_bswap(Hacl_Vec128_t a) {
  const __m128i rev =
      _mm_set_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
  return _mm_shuffle_epi8(a, rev);
}

/* The GHASH reduction constant: byte zero is 0xe1 and the rest are zero.
 * `_mm_set_epi8` takes its arguments from the high byte down. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_reduction(void) {
  return _mm_set_epi8(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (char)0xe1);
}

static inline bool Hacl_Vec128_supported(void) {
#if defined(__GNUC__)
  __builtin_cpu_init();
  return __builtin_cpu_supports("aes") && __builtin_cpu_supports("pclmul") &&
         __builtin_cpu_supports("sse4.1") && __builtin_cpu_supports("ssse3");
#else
  return false;
#endif
}

#else /* not x86 */

typedef struct {
  uint8_t b[16];
} Hacl_Vec128_t;

/* Unreachable: every caller is guarded by Hacl_Vec128_supported.  They are
 * defined rather than merely declared so that the program links. */
static inline Hacl_Vec128_t Hacl_Vec128_zero(void) {
  Hacl_Vec128_t r;
  memset(&r, 0, sizeof r);
  return r;
}
static inline Hacl_Vec128_t Hacl_Vec128_load(uint8_t *p) {
  Hacl_Vec128_t r;
  memcpy(&r, p, 16);
  return r;
}
static inline void Hacl_Vec128_store(uint8_t *p, Hacl_Vec128_t x) {
  memcpy(p, &x, 16);
}
static inline Hacl_Vec128_t Hacl_Vec128_xor(Hacl_Vec128_t a, Hacl_Vec128_t b) {
  for (int i = 0; i < 16; i++) a.b[i] ^= b.b[i];
  return a;
}
#define HACL_VEC128_STUB2(name)                                              \
  static inline Hacl_Vec128_t name(Hacl_Vec128_t a, Hacl_Vec128_t b) {       \
    (void)b;                                                                 \
    return a;                                                                \
  }
HACL_VEC128_STUB2(Hacl_Vec128_aesenc)
HACL_VEC128_STUB2(Hacl_Vec128_aesenclast)
HACL_VEC128_STUB2(Hacl_Vec128_clmul_ll)
HACL_VEC128_STUB2(Hacl_Vec128_clmul_lh)
HACL_VEC128_STUB2(Hacl_Vec128_clmul_hl)
HACL_VEC128_STUB2(Hacl_Vec128_clmul_hh)
#undef HACL_VEC128_STUB2
#define HACL_VEC128_STUB1(name)                                              \
  static inline Hacl_Vec128_t name(Hacl_Vec128_t a) { return a; }
HACL_VEC128_STUB1(Hacl_Vec128_shift_left_bytes_4)
HACL_VEC128_STUB1(Hacl_Vec128_shift_right_bytes_4)
HACL_VEC128_STUB1(Hacl_Vec128_shift_left_bytes_8)
HACL_VEC128_STUB1(Hacl_Vec128_shift_right_bytes_8)
HACL_VEC128_STUB1(Hacl_Vec128_bswap)
#undef HACL_VEC128_STUB1
static inline Hacl_Vec128_t Hacl_Vec128_shift_left_lanes64(Hacl_Vec128_t a,
                                                           uint32_t n) {
  (void)n;
  return a;
}
static inline Hacl_Vec128_t Hacl_Vec128_shift_right_lanes64(Hacl_Vec128_t a,
                                                            uint32_t n) {
  (void)n;
  return a;
}
static inline Hacl_Vec128_t Hacl_Vec128_reduction(void) {
  Hacl_Vec128_t r;
  memset(&r, 0, sizeof r);
  r.b[0] = 0xe1;
  return r;
}
static inline bool Hacl_Vec128_supported(void) { return false; }

#endif

#endif /* HACL_VEC128_H */
