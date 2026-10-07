#define _DEFAULT_SOURCE 1
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "Hacl_Chacha20_Vec256.h"
#include "Hacl_MAC_Poly1305_Simd256.h"
#include "Hacl_AEAD_Chacha20Poly1305_Simd256.h"
#include "Hacl_Hash_Blake2b_Simd256.h"
#include "Hacl_Hash_Blake2s_Simd128.h"
static volatile uint64_t sink;
static double now_sec(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec;}
static uint8_t msg[262144+64], ct[262144+64], out[256], key[32], nonce[12], tag[16];
#define TIME(nm,by,body) do{uint64_t it=1;double t=0;for(;;){t=now_sec();for(uint64_t i=0;i<it;i++){body;}t=now_sec()-t;if(t>0.05)break;it*=2;}double b=t/it;for(int r=0;r<4;r++){double s=now_sec();for(uint64_t i=0;i<it;i++){body;}s=(now_sec()-s)/it;if(s<b)b=s;}printf("hacl-avx2,%s,%zu,%.2f,%.2f\n",nm,(size_t)(by),b*1e9,(by)/b/1e6);fflush(stdout);}while(0)
int main(void){
  printf("impl,bench,bytes,ns_per_op,mb_per_s\n");
  size_t sizes[]={64,1024,16384,262144};
  for(int i=0;i<4;i++){size_t n=sizes[i];
    TIME("chacha20",n,{Hacl_Chacha20_Vec256_chacha20_encrypt_256((uint32_t)n,ct,msg,key,nonce,0);sink+=ct[0];});}
  for(int i=0;i<4;i++){size_t n=sizes[i];
    TIME("poly1305",n,{Hacl_MAC_Poly1305_Simd256_mac(out,msg,(uint32_t)n,key);sink+=out[0];});}
  for(int i=0;i<4;i++){size_t n=sizes[i];
    TIME("chacha20poly1305-enc",n,{Hacl_AEAD_Chacha20Poly1305_Simd256_encrypt(ct,tag,msg,(uint32_t)n,msg,16,key,nonce);sink+=ct[0];});}
  for(int i=0;i<4;i++){size_t n=sizes[i];
    TIME("blake2b",n,{Hacl_Hash_Blake2b_Simd256_hash_with_key(out,64,msg,(uint32_t)n,NULL,0);sink+=out[0];});}
  for(int i=0;i<4;i++){size_t n=sizes[i];
    TIME("blake2s",n,{Hacl_Hash_Blake2s_Simd128_hash_with_key(out,32,msg,(uint32_t)n,NULL,0);sink+=out[0];});}
  return 0;
}
