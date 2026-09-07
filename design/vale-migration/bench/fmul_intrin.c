#include <stdint.h>
#include <immintrin.h>
#include <string.h>
/* ONLY the intrinsics version - no inline asm anywhere in this TU */
void fmul_intrin(uint64_t *out, const uint64_t *a, const uint64_t *b)
{
  uint64_t t[9]; memset(t, 0, sizeof t);
  for (int i = 0; i < 4; i++) {
    unsigned char cf = 0, of = 0;
    unsigned long long hi, lo;
    for (int j = 0; j < 4; j++) {
      lo = _mulx_u64(a[i], b[j], &hi);
      of = _addcarryx_u64(of, lo, t[i+j],   (unsigned long long*)&t[i+j]);
      cf = _addcarryx_u64(cf, hi, t[i+j+1], (unsigned long long*)&t[i+j+1]);
    }
    unsigned char c2 = _addcarryx_u64(0, (unsigned long long)of, t[i+4], (unsigned long long*)&t[i+4]);
    t[i+5] += (uint64_t)cf + (uint64_t)c2;
  }
  unsigned char cf = 0, of = 0;
  unsigned long long hi, lo, r[4], carry; uint64_t acc = 0;
  for (int i = 0; i < 4; i++) {
    lo = _mulx_u64(t[4+i], 38ULL, &hi);
    of = _addcarryx_u64(of, lo, t[i], (unsigned long long*)&r[i]);
    cf = _addcarryx_u64(cf, hi, (i<3)?t[i+1]:0, &carry);
    if (i<3) t[i+1]=carry; else acc=carry;
  }
  acc += (uint64_t)cf + (uint64_t)of;
  unsigned __int128 c = (unsigned __int128)acc * 38;
  unsigned char k = 0;
  k = _addcarry_u64(k, r[0], (uint64_t)c, (unsigned long long*)&r[0]);
  k = _addcarry_u64(k, r[1], 0, (unsigned long long*)&r[1]);
  k = _addcarry_u64(k, r[2], 0, (unsigned long long*)&r[2]);
  k = _addcarry_u64(k, r[3], 0, (unsigned long long*)&r[3]);
  uint64_t add = k ? 38 : 0;
  k = _addcarry_u64(0, r[0], add, (unsigned long long*)&r[0]);
  r[1] += k;
  out[0]=r[0]; out[1]=r[1]; out[2]=r[2]; out[3]=r[3];
}
