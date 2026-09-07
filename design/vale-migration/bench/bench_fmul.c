#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h>
void fmul_vale(uint64_t*,uint64_t*,uint64_t*,uint64_t*);
void fmul_intrin(uint64_t*,const uint64_t*,const uint64_t*);
void fmul_plain(uint64_t*,const uint64_t*,const uint64_t*);
static uint64_t rnd(void){static uint64_t s=0x243F6A8885A308D3ULL;s^=s<<13;s^=s>>7;s^=s<<17;return s;}
#define N 2000000
int main(void){
  uint64_t f1[4],f2[4],o1[4],o2[4],o3[4],tmp[16];
  int bi=0,bp=0;
  for(int k=0;k<2000;k++){
    for(int i=0;i<4;i++){f1[i]=rnd();f2[i]=rnd();}
    f1[3]&=0x7fffffffffffffffULL; f2[3]&=0x7fffffffffffffffULL;
    fmul_vale(o1,f1,f2,tmp); fmul_intrin(o2,f1,f2); fmul_plain(o3,f1,f2);
    if(memcmp(o1,o2,32)) bi++;
    if(memcmp(o1,o3,32)) bp++;
  }
  printf("correctness: intrinsics_mismatch=%d plainC_mismatch=%d\n",bi,bp);
  for(int i=0;i<4;i++){f1[i]=rnd();f2[i]=rnd();}
  f1[3]&=0x7fffffffffffffffULL; f2[3]&=0x7fffffffffffffffULL;
  double best[3]={1e30,1e30,1e30};
  const char*nm[3]={"Vale inline asm ","Intrinsics(ADX) ","Plain C __int128"};
  for(int v=0;v<3;v++)for(int r=0;r<5;r++){
    memcpy(o1,f1,32);
    unsigned long long c0=__rdtsc();
    for(int k=0;k<N;k++){
      if(v==0)fmul_vale(o1,o1,f2,tmp); else if(v==1)fmul_intrin(o1,o1,f2); else fmul_plain(o1,o1,f2);
      __asm__ volatile("":::"memory");
    }
    unsigned long long c1=__rdtsc();
    double c=(double)(c1-c0)/N; if(c<best[v])best[v]=c;
    if(o1[0]==0xdeadbeef) printf("x");
  }
  for(int v=0;v<3;v++) printf("%s : %6.2f cyc/fmul  (%.2fx vs Vale)\n",nm[v],best[v],best[v]/best[0]);
  return 0;
}
