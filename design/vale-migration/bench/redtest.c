#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <immintrin.h>
__attribute__((target("pclmul,sse4.1,avx")))
static __m128i good(__m128i lo,__m128i hi,__m128i K){
  __m128i mid=_mm_xor_si128(K,_mm_xor_si128(lo,hi));
  __m128i t3=lo,t6=hi,t7,t8,t9,t2,t4,t5;
  t3=_mm_xor_si128(t3,_mm_slli_si128(mid,8));
  t6=_mm_xor_si128(t6,_mm_srli_si128(mid,8));
  t7=_mm_srli_epi32(t3,31);t8=_mm_srli_epi32(t6,31);
  t3=_mm_slli_epi32(t3,1);t6=_mm_slli_epi32(t6,1);
  t9=_mm_srli_si128(t7,12);t8=_mm_slli_si128(t8,4);t7=_mm_slli_si128(t7,4);
  t3=_mm_or_si128(t3,t7);t6=_mm_or_si128(t6,t8);t6=_mm_or_si128(t6,t9);
  t7=_mm_slli_epi32(t3,31);t8=_mm_slli_epi32(t3,30);t9=_mm_slli_epi32(t3,25);
  t7=_mm_xor_si128(t7,t8);t7=_mm_xor_si128(t7,t9);
  t8=_mm_srli_si128(t7,4);t7=_mm_slli_si128(t7,12);
  t3=_mm_xor_si128(t3,t7);
  t2=_mm_srli_epi32(t3,1);t4=_mm_srli_epi32(t3,2);t5=_mm_srli_epi32(t3,7);
  t2=_mm_xor_si128(t2,t4);t2=_mm_xor_si128(t2,t5);t2=_mm_xor_si128(t2,t8);
  t3=_mm_xor_si128(t3,t2);
  return _mm_xor_si128(t6,t3);
}
__attribute__((target("pclmul,sse4.1,avx")))
static __m128i fast(__m128i lo,__m128i hi,__m128i K,int i1,int i2){
  __m128i mid=_mm_xor_si128(K,_mm_xor_si128(lo,hi));
  lo=_mm_xor_si128(lo,_mm_slli_si128(mid,8));
  hi=_mm_xor_si128(hi,_mm_srli_si128(mid,8));
  __m128i c1=_mm_srli_epi64(lo,63),c2=_mm_srli_epi64(hi,63);
  lo=_mm_slli_epi64(lo,1);hi=_mm_slli_epi64(hi,1);
  lo=_mm_or_si128(lo,_mm_slli_si128(c1,8));
  hi=_mm_or_si128(hi,_mm_slli_si128(c2,8));
  hi=_mm_or_si128(hi,_mm_srli_si128(c1,8));
  const __m128i P=_mm_set_epi64x(0,(long long)0xc200000000000000ULL);
  __m128i T;
  if(i1==0x01) T=_mm_clmulepi64_si128(lo,P,0x01); else T=_mm_clmulepi64_si128(lo,P,0x10);
  lo=_mm_shuffle_epi32(lo,0x4E);lo=_mm_xor_si128(lo,T);
  if(i2==0x01) T=_mm_clmulepi64_si128(lo,P,0x01); else T=_mm_clmulepi64_si128(lo,P,0x10);
  lo=_mm_shuffle_epi32(lo,0x4E);lo=_mm_xor_si128(lo,T);
  return _mm_xor_si128(hi,lo);
}
static uint64_t rnd(void){static uint64_t s=12345;s^=s<<13;s^=s>>7;s^=s<<17;return s;}
int main(void){
  int combos[4][2]={{0x01,0x01},{0x01,0x10},{0x10,0x01},{0x10,0x10}};
  for(int c=0;c<4;c++){
    int bad=0;
    for(int t=0;t<5000;t++){
      __m128i lo=_mm_set_epi64x((long long)rnd(),(long long)rnd());
      __m128i hi=_mm_set_epi64x((long long)rnd(),(long long)rnd());
      __m128i K =_mm_set_epi64x((long long)rnd(),(long long)rnd());
      __m128i a=good(lo,hi,K), b=fast(lo,hi,K,combos[c][0],combos[c][1]);
      if(memcmp(&a,&b,16)) bad++;
    }
    printf("imm1=0x%02x imm2=0x%02x -> mismatches=%d %s\n",combos[c][0],combos[c][1],bad,bad?"":"<== MATCH");
  }
  return 0;
}
