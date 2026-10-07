#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include "Hacl.h"
static double now_sec(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec+ts.tv_nsec*1e-9;}
static uint8_t out[256], sk[32];
volatile uint8_t sink; volatile uint64_t csink;
static double canary(void){ /* 200M dependent adds = 200M cycles */
  double t=now_sec(); uint64_t x=1; for(uint64_t i=0;i<200000000ULL;i++) x+=x>>3|1; csink=x;
  return (now_sec()-t); }
int main(void){
  for(int i=0;i<32;i++) sk[i]=(uint8_t)(i*7+1);
  double c1=canary();
  double best=1e9; uint64_t iters=200;
  for(int r=0;r<7;r++){ double t=now_sec();
    for(uint64_t i=0;i<iters;i++){Hacl_Ed25519_secret_to_public(out,sk);sink+=out[0];}
    t=(now_sec()-t)/(double)iters; if(t<best)best=t; }
  double c2=canary();
  printf("ed25519 %8.1f ns   canary %.3f/%.3f s  (~%.2f GHz)\n", best*1e9, c1, c2, 0.2/((c1+c2)/2));
  return 0; }
