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
 * Everything here is x86-64 only, and so is every generated function that
 * uses it: those carry `custard_c_closure_guard "defined(__x86_64__)"` and
 * are printed inside `#if defined(__x86_64__)`, and their callers test the
 * `Hacl.X64.x86_64` flag, which is printed as the same `#if`.  On any other
 * target this header defines only the type, as sixteen opaque bytes: the
 * pair and triple structs Custard declares for the PCLMULQDQ code are types,
 * which a guard does not cover, so they are in `Hacl.h` everywhere.  Nothing
 * off x86-64 makes or reads one.
 */

#ifndef HACL_VEC128_H
#define HACL_VEC128_H

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#if defined(__x86_64__)

#include <immintrin.h>

typedef __m128i Hacl_Vec128_t;

/* {2 The baseline}
 *
 * SSE2 is part of the x86-64 baseline, so these two need no `target` and can
 * therefore be inlined into an AES-NI function and into a SHA function both.
 * `add32` is used by SHA-256's message schedule and by AES's counter; keeping
 * it here rather than under either target is what lets it serve both. */

#define HACL_VEC128_BASE __attribute__((always_inline)) static inline

HACL_VEC128_BASE Hacl_Vec128_t Hacl_Vec128_add32(Hacl_Vec128_t a,
                                                 Hacl_Vec128_t b) {
  return _mm_add_epi32(a, b);
}

/* One in lane zero, zero in the other three: the counter-mode increment.
 * `_mm_set_epi32` takes its arguments from the high lane down. */
HACL_VEC128_BASE Hacl_Vec128_t Hacl_Vec128_lane_one(void) {
  return _mm_set_epi32(0, 0, 0, 1);
}

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

/* AESKEYGENASSIST with a zero round constant.  Bytes 8..11 of the result are
 * the S-box applied to bytes 12..15 of the argument; the rest of the result
 * is the same for bytes 4..7 and two rotated copies, none of which is used.
 * This is the key schedule's SubWord. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_subword(Hacl_Vec128_t a) {
  return _mm_aeskeygenassist_si128(a, 0);
}

/* The key schedule's RotWord, broadcast.  Byte i of the result is byte
 * 8 + ((i + 1) % 4) of the argument, so applied to the result of
 * Hacl_Vec128_subword it is RotWord (SubWord w3) in all four words at once --
 * which is exactly the term the schedule adds to every word of a round key.
 * One PSHUFB against a constant mask. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_bcast_rot(Hacl_Vec128_t a) {
  return _mm_shuffle_epi8(
      a, _mm_setr_epi8(9, 10, 11, 8, 9, 10, 11, 8, 9, 10, 11, 8, 9, 10, 11, 8));
}

/* The same without the rotation, which is what AES-256 wants halfway between
 * its round-constant steps: byte i of the result is byte 8 + (i % 4). */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_bcast_sub(Hacl_Vec128_t a) {
  return _mm_shuffle_epi8(
      a, _mm_setr_epi8(8, 9, 10, 11, 8, 9, 10, 11, 8, 9, 10, 11, 8, 9, 10, 11));
}

/* One byte in the low end of each of the four words, zero elsewhere: the
 * round constant, as a register, without going through memory. */
HACL_VEC128_NI Hacl_Vec128_t Hacl_Vec128_word_bcast(uint8_t x) {
  return _mm_set1_epi32((int)(uint32_t)x);
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

/* {2 SHA-256}
 *
 * A separate target and a separate feature test: SHA and AES are separate
 * CPUID bits and a machine may have either without the other.  Nothing here
 * may be called from a function compiled for HACL_VEC128_NI or the other way
 * round; the two paths meet only in the dispatchers, which are plain. */

#define HACL_VEC128_SHA \
  __attribute__((target("ssse3,sse4.1,sha"), always_inline)) static inline

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_load32(uint32_t *p) {
  return _mm_loadu_si128((const __m128i *)(const void *)p);
}

HACL_VEC128_SHA void Hacl_Vec128_store32(uint32_t *p, Hacl_Vec128_t x) {
  _mm_storeu_si128((__m128i *)(void *)p, x);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_shuffle_swap_pairs(Hacl_Vec128_t a) {
  return _mm_shuffle_epi32(a, 0xB1);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_shuffle_reverse(Hacl_Vec128_t a) {
  return _mm_shuffle_epi32(a, 0x1B);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_shuffle_high_pair(Hacl_Vec128_t a) {
  return _mm_shuffle_epi32(a, 0x0E);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_align_right_4(Hacl_Vec128_t a,
                                                        Hacl_Vec128_t b) {
  return _mm_alignr_epi8(a, b, 4);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_align_right_8(Hacl_Vec128_t a,
                                                        Hacl_Vec128_t b) {
  return _mm_alignr_epi8(a, b, 8);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_blend_high(Hacl_Vec128_t a,
                                                     Hacl_Vec128_t b) {
  return _mm_blend_epi16(a, b, 0xF0);
}

/* Reverse the bytes within each 32-bit lane, not across the register: a
 * message block is read big-endian and the lanes are little-endian. */
HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_bswap32(Hacl_Vec128_t a) {
  const __m128i rev = _mm_set_epi8(12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0,
                                   1, 2, 3);
  return _mm_shuffle_epi8(a, rev);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_load_be32(uint8_t *p) {
  return Hacl_Vec128_bswap32(_mm_loadu_si128((const __m128i *)(const void *)p));
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_sha256rnds2(Hacl_Vec128_t cdgh,
                                                      Hacl_Vec128_t abef,
                                                      Hacl_Vec128_t k) {
  return _mm_sha256rnds2_epu32(cdgh, abef, k);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_sha256msg1(Hacl_Vec128_t a,
                                                     Hacl_Vec128_t b) {
  return _mm_sha256msg1_epu32(a, b);
}

HACL_VEC128_SHA Hacl_Vec128_t Hacl_Vec128_sha256msg2(Hacl_Vec128_t a,
                                                     Hacl_Vec128_t b) {
  return _mm_sha256msg2_epu32(a, b);
}

static inline bool Hacl_Vec128_sha_supported(void) {
#if defined(__GNUC__)
  __builtin_cpu_init();
  return __builtin_cpu_supports("sha") && __builtin_cpu_supports("sse4.1") &&
         __builtin_cpu_supports("ssse3");
#else
  return false;
#endif
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

#else

typedef struct {
  uint8_t opaque[16];
} Hacl_Vec128_t;

#endif

#endif /* HACL_VEC128_H */
