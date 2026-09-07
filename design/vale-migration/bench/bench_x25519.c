#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h>
#include "Hacl_Curve25519_51.h"
#include "Hacl_Curve25519_64.h"
int main(void){
  uint8_t sk[32], pk[32], o51[32], o64[32];
  for (int i=0;i<32;i++){ sk[i]=(uint8_t)(i*7+1); pk[i]=(uint8_t)(i*13+9); }
  pk[31]&=0x7f;
  Hacl_Curve25519_51_ecdh(o51, sk, pk);
  Hacl_Curve25519_64_ecdh(o64, sk, pk);
  printf("outputs identical: %s\n", memcmp(o51,o64,32)==0 ? "YES" : "NO");
  const int N=3000;
  double b51=1e30,b64=1e30;
  for(int r=0;r<5;r++){
    unsigned long long c0=__rdtsc();
    for(int k=0;k<N;k++){ sk[0]=(uint8_t)k; Hacl_Curve25519_51_ecdh(o51,sk,pk); }
    unsigned long long c1=__rdtsc();
    double v=(double)(c1-c0)/N; if(v<b51)b51=v;
    c0=__rdtsc();
    for(int k=0;k<N;k++){ sk[0]=(uint8_t)k; Hacl_Curve25519_64_ecdh(o64,sk,pk); }
    c1=__rdtsc();
    v=(double)(c1-c0)/N; if(v<b64)b64=v;
  }
  printf("X25519 pure C   (Curve25519_51, radix-51 __int128) : %9.0f cycles/op\n", b51);
  printf("X25519 Vale asm (Curve25519_64, mulx/adcx/adox)    : %9.0f cycles/op\n", b64);
  printf("\npure C is %.2fx SLOWER than Vale assembly\n", b51/b64);
  return 0;
}
