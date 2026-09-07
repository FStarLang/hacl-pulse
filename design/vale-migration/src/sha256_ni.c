/* SHA-256 via SHA-NI intrinsics. See header for scope. */

#include "sha256_ni.h"

#include <immintrin.h>

/* SHA-256 round constants. Loaded four at a time; note these are read at
 * fixed offsets, never indexed by message data, so there is no secret
 * dependent addressing here. */
static const uint32_t K256[64] = {
  0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,
  0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,
  0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,
  0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
  0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,
  0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
  0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,
  0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
  0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,
  0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,
  0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,
  0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
  0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,
  0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,
  0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,
  0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u
};

/* Loading K from a table rather than materialising 16 _mm_set_epi64x
 * immediates: an earlier version hand-transcribed the constants and got
 * several wrong while still benchmarking identically. Same instruction
 * count, no transcription risk. */
#define KV(i) _mm_loadu_si128((const __m128i *)&K256[(i)])

#define RNDS(m, i)                                        \
  MSG    = _mm_add_epi32(m, KV(i));                       \
  STATE1 = _mm_sha256rnds2_epu32(STATE1, STATE0, MSG);    \
  MSG    = _mm_shuffle_epi32(MSG, 0x0E);                  \
  STATE0 = _mm_sha256rnds2_epu32(STATE0, STATE1, MSG);

/* Full quad: two rounds plus message schedule for a and c. */
#define QUAD(a, b, c, d, i)                               \
  MSG    = _mm_add_epi32(a, KV(i));                       \
  STATE1 = _mm_sha256rnds2_epu32(STATE1, STATE0, MSG);    \
  TMP    = _mm_alignr_epi8(a, d, 4);                      \
  b      = _mm_add_epi32(b, TMP);                         \
  b      = _mm_sha256msg2_epu32(b, a);                    \
  MSG    = _mm_shuffle_epi32(MSG, 0x0E);                  \
  STATE0 = _mm_sha256rnds2_epu32(STATE0, STATE1, MSG);    \
  c      = _mm_sha256msg1_epu32(c, a);

__attribute__((target("sse4.1,sha")))
void sha256_ni_update(uint32_t *digest, const uint8_t *data, uint64_t num_blocks)
{
  __m128i STATE0, STATE1, MSG, TMP, MASK, T0, T1, T2, T3, ABEF, CDGH;

  TMP    = _mm_loadu_si128((const __m128i *)&digest[0]);
  STATE1 = _mm_loadu_si128((const __m128i *)&digest[4]);
  MASK   = _mm_set_epi64x(0x0c0d0e0f08090a0bULL, 0x0405060700010203ULL);

  TMP    = _mm_shuffle_epi32(TMP, 0xB1);        /* CDAB */
  STATE1 = _mm_shuffle_epi32(STATE1, 0x1B);     /* EFGH */
  STATE0 = _mm_alignr_epi8(TMP, STATE1, 8);     /* ABEF */
  STATE1 = _mm_blend_epi16(STATE1, TMP, 0xF0);  /* CDGH */

  while (num_blocks--) {
    ABEF = STATE0;
    CDGH = STATE1;

    T0 = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)(data +  0)), MASK);
    T1 = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)(data + 16)), MASK);
    T2 = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)(data + 32)), MASK);
    T3 = _mm_shuffle_epi8(_mm_loadu_si128((const __m128i *)(data + 48)), MASK);

    RNDS(T0, 0)
    RNDS(T1, 4)  T0 = _mm_sha256msg1_epu32(T0, T1);
    RNDS(T2, 8)  T1 = _mm_sha256msg1_epu32(T1, T2);
    QUAD(T3, T0, T2, T2, 12)
    QUAD(T0, T1, T3, T3, 16)
    QUAD(T1, T2, T0, T0, 20)
    QUAD(T2, T3, T1, T1, 24)
    QUAD(T3, T0, T2, T2, 28)
    QUAD(T0, T1, T3, T3, 32)
    QUAD(T1, T2, T0, T0, 36)
    QUAD(T2, T3, T1, T1, 40)
    QUAD(T3, T0, T2, T2, 44)
    QUAD(T0, T1, T3, T3, 48)
    QUAD(T1, T2, T0, T0, 52)

    /* rounds 56-59: msg2 only, no further msg1 needed */
    MSG    = _mm_add_epi32(T2, KV(56));
    STATE1 = _mm_sha256rnds2_epu32(STATE1, STATE0, MSG);
    TMP    = _mm_alignr_epi8(T2, T1, 4);
    T3     = _mm_add_epi32(T3, TMP);
    T3     = _mm_sha256msg2_epu32(T3, T2);
    MSG    = _mm_shuffle_epi32(MSG, 0x0E);
    STATE0 = _mm_sha256rnds2_epu32(STATE0, STATE1, MSG);

    RNDS(T3, 60)

    STATE0 = _mm_add_epi32(STATE0, ABEF);
    STATE1 = _mm_add_epi32(STATE1, CDGH);
    data += 64;
  }

  TMP    = _mm_shuffle_epi32(STATE0, 0x1B);
  STATE1 = _mm_shuffle_epi32(STATE1, 0xB1);
  STATE0 = _mm_blend_epi16(TMP, STATE1, 0xF0);
  STATE1 = _mm_alignr_epi8(STATE1, TMP, 8);

  _mm_storeu_si128((__m128i *)&digest[0], STATE0);
  _mm_storeu_si128((__m128i *)&digest[4], STATE1);
}
