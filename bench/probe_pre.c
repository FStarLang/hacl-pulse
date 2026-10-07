#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "Hacl.h"
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec*1e9+t.tv_nsec;}
int main(void){
  size_t nn=32; uint64_t n[32], r2[32], t1a[32], t2a[32], wide[64];
  for(size_t i=0;i<nn;i++) n[i]=0x9e3779b97f4a7c15ULL^i;
  n[0]|=1; n[nn-1]|=1ULL<<63;
  uint64_t mu=Hacl_Bignum_Montgomery_mont_mu(n[0]);
  double t0=now(); volatile uint64_t s=0;
  int it=2000;
  for(int k=0;k<it;k++){ Hacl_Bignum_Montgomery_precomp(r2,t1a,t2a,wide,n,nn,mu); s+=r2[0]; }
  double t1=now();
  printf("precomp: %.2f us\n",(t1-t0)/it/1000.0);
  (void)s; return 0;
}
