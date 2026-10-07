#include <stdio.h>
#include "EverCrypt_AutoConfig2.h"
int main(void){ EverCrypt_AutoConfig2_init();
  printf("shaext=%d sse=%d avx=%d avx2=%d aesni=%d pclmul=%d bmi2=%d adx=%d\n",
    EverCrypt_AutoConfig2_has_shaext(), EverCrypt_AutoConfig2_has_sse(),
    EverCrypt_AutoConfig2_has_avx(), EverCrypt_AutoConfig2_has_avx2(),
    EverCrypt_AutoConfig2_has_aesni(), EverCrypt_AutoConfig2_has_pclmulqdq(),
    EverCrypt_AutoConfig2_has_bmi2(), EverCrypt_AutoConfig2_has_adx());
  return 0; }
