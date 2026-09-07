#include <stdint.h>
#include <string.h>
void fmul_plain(uint64_t *out, const uint64_t *a, const uint64_t *b)
{
  uint64_t w[8]; memset(w, 0, sizeof w);
  unsigned __int128 acc;
  for (int i = 0; i < 4; i++) {
    uint64_t carry = 0;
    for (int j = 0; j < 4; j++) {
      acc = (unsigned __int128)a[i] * b[j] + w[i+j] + carry;
      w[i+j] = (uint64_t)acc;
      carry = (uint64_t)(acc >> 64);
    }
    w[i+4] += carry;
  }
  /* reduce */
  uint64_t r[4]; uint64_t carry = 0;
  for (int i = 0; i < 4; i++) {
    acc = (unsigned __int128)w[4+i] * 38 + w[i] + carry;
    r[i] = (uint64_t)acc;
    carry = (uint64_t)(acc >> 64);
  }
  acc = (unsigned __int128)carry * 38 + r[0];
  r[0] = (uint64_t)acc; carry = (uint64_t)(acc >> 64);
  for (int i = 1; i < 4 && carry; i++) { acc = (unsigned __int128)r[i] + carry; r[i]=(uint64_t)acc; carry=(uint64_t)(acc>>64); }
  r[0] += carry * 38;
  memcpy(out, r, 32);
}
