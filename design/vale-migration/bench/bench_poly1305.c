#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h>
#include "Hacl_MAC_Poly1305.h"
#include "Hacl_MAC_Poly1305_Simd128.h"
#include "Hacl_MAC_Poly1305_Simd256.h"
#include "EverCrypt_Poly1305.h"
#define LEN 16384
int main(void){
  static uint8_t msg[LEN]; uint8_t key[32], t1[16],t2[16],t3[16],t4[16];
  for(int i=0;i<LEN;i++) msg[i]=(uint8_t)(i*17+3);
  for(int i=0;i<32;i++) key[i]=(uint8_t)(i*5+1);
  EverCrypt_Poly1305_mac(t1,msg,LEN,key);
  Hacl_MAC_Poly1305_mac(t2,msg,LEN,key);
  Hacl_MAC_Poly1305_Simd128_mac(t3,msg,LEN,key);
  Hacl_MAC_Poly1305_Simd256_mac(t4,msg,LEN,key);
  printf("tags match: vale==C %s, vale==simd128 %s, vale==simd256 %s\n",
    memcmp(t1,t2,16)?"NO":"YES", memcmp(t1,t3,16)?"NO":"YES", memcmp(t1,t4,16)?"NO":"YES");
  double b[4]={1e30,1e30,1e30,1e30}; unsigned long long c0,c1; const int N=2000;
  for(int r=0;r<7;r++){
    for(int v=0;v<4;v++){
      c0=__rdtsc();
      for(int k=0;k<N;k++){
        if(v==0) EverCrypt_Poly1305_mac(t1,msg,LEN,key);
        else if(v==1) Hacl_MAC_Poly1305_mac(t2,msg,LEN,key);
        else if(v==2) Hacl_MAC_Poly1305_Simd128_mac(t3,msg,LEN,key);
        else Hacl_MAC_Poly1305_Simd256_mac(t4,msg,LEN,key);
      }
      c1=__rdtsc();
      double x=(double)(c1-c0)/((double)N*LEN); if(x<b[v])b[v]=x;
    }
  }
  const char*n[4]={"Vale asm (scalar mul/adc)   ","pure C   (scalar __int128)  ","C intrinsics SSE2  (Simd128)","C intrinsics AVX2  (Simd256)"};
  for(int v=0;v<4;v++) printf("Poly1305 %s : %5.3f cycles/byte  (%.2fx vs Vale)\n", n[v], b[v], b[v]/b[0]);
  return 0;
}
