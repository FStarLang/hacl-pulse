/* ctgrind-style constant-time audit.
 *
 * Marks secrets as "undefined" for valgrind memcheck, then runs the target.
 * Memcheck reports any conditional branch or memory address that depends on
 * undefined data -- i.e. any branch-on-secret or table-lookup-on-secret.
 *
 * Two rules learned the hard way, both encoded in the Makefile `ct` target:
 *
 *  1. ALWAYS run the `knownbad_fmul` positive control. It is a deliberately
 *     leaky plain-C fmul (bench/fmul_plain.c, the `carry`-conditioned loop).
 *     If the control does not report an error, the harness is broken and a
 *     clean result from any other target means nothing.
 *
 *  2. ALWAYS check the target printed its "done" line. valgrind 3.26 does not
 *     implement sha256rnds2, so `sha256ni` SIGILLs -- and an aborted run
 *     otherwise looks indistinguishable from a clean one. sha256ni was
 *     audited by disassembly instead; see ../README.md.
 *
 * Caveat: memcheck tracks value dependence, not time. It cannot see
 * variable-latency instructions. None of the targets here use any.
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <valgrind/memcheck.h>
#include "Hacl_MAC_Poly1305_Simd256.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Ed25519.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#include "sha256_ni.h"
#include "aesgcm_x86_intrin.h"

void fmul_plain(uint64_t*,const uint64_t*,const uint64_t*);


#define SECRET(p,n) VALGRIND_MAKE_MEM_UNDEFINED(p,n)
#define PUBLIC(p,n) VALGRIND_MAKE_MEM_DEFINED(p,n)

int main(int argc,char**argv){
  if(argc<2){printf("usage: ct <target>\n");return 1;}
  const char*t=argv[1];
  EverCrypt_AutoConfig2_init();

  if(!strcmp(t,"sha256ni")){
    static uint8_t msg[640]; uint32_t st[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    for(int i=0;i<640;i++) msg[i]=(uint8_t)i;
    SECRET(msg,sizeof msg);                 /* message is secret (HMAC case) */
    sha256_ni_update(st,msg,10);
    PUBLIC(st,sizeof st);
    printf("%s done %08x\n",t,st[0]);
  }
  else if(!strcmp(t,"sha256purec")){
    static uint8_t msg[640]; uint32_t st[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    for(int i=0;i<640;i++) msg[i]=(uint8_t)i;
    SECRET(msg,sizeof msg);
    Hacl_Hash_SHA2_sha256_update_nblocks(640,msg,st);
    PUBLIC(st,sizeof st);
    printf("%s done %08x\n",t,st[0]);
  }
  else if(!strcmp(t,"poly1305simd256")){
    static uint8_t msg[1024]; uint8_t key[32],tag[16];
    for(int i=0;i<1024;i++) msg[i]=(uint8_t)i;
    for(int i=0;i<32;i++) key[i]=(uint8_t)(i*3+1);
    SECRET(key,32); SECRET(msg,sizeof msg);   /* one-time key + msg secret */
    Hacl_MAC_Poly1305_Simd256_mac(tag,msg,1024,key);
    PUBLIC(tag,16);
    printf("%s done %02x\n",t,tag[0]);
  }
  else if(!strcmp(t,"curve25519_51")){
    uint8_t sk[32],pk[32],out[32];
    for(int i=0;i<32;i++){sk[i]=(uint8_t)(i*7+1);pk[i]=(uint8_t)(i*13+9);}
    pk[31]&=0x7f;
    SECRET(sk,32);                             /* private scalar is secret */
    Hacl_Curve25519_51_ecdh(out,sk,pk);
    PUBLIC(out,32);
    printf("%s done %02x\n",t,out[0]);
  }
  else if(!strcmp(t,"ed25519")){
    uint8_t sk[32],sig[64],msg[64];
    for(int i=0;i<32;i++) sk[i]=(uint8_t)(i*11+3);
    for(int i=0;i<64;i++) msg[i]=(uint8_t)(i*7+1);
    SECRET(sk,32);                             /* private key is secret */
    Hacl_Ed25519_sign(sig,sk,64,msg);
    PUBLIC(sig,64);
    printf("%s done %02x\n",t,sig[0]);
  }
  else if(!strcmp(t,"gcm_intrin")){
    static uint8_t pt[1024],ct[1024]; uint8_t key[16],iv[16],aad[20],tag[16];
    for(int i=0;i<1024;i++) pt[i]=(uint8_t)i;
    for(int i=0;i<16;i++) key[i]=(uint8_t)(i*3+1);
    for(int i=0;i<12;i++) iv[i]=(uint8_t)(i*7+2);
    iv[12]=0;iv[13]=0;iv[14]=0;iv[15]=1;
    for(int i=0;i<20;i++) aad[i]=(uint8_t)(i+5);
    static aesgcm_ctx G;
    aesgcm128_init(&G,key);
    SECRET(key,16); SECRET(pt,sizeof pt);      /* key + plaintext secret */
    aesgcm128_encrypt(&G,iv,aad,20,pt,1024,ct,tag);
    PUBLIC(ct,sizeof ct); PUBLIC(tag,16);
    printf("%s done %02x\n",t,tag[0]);
  }
  else if(!strcmp(t,"gcm_vale")){
    static uint8_t pt[1024],ct[1024]; uint8_t key[16],iv[16],aad[20],tag[16];
    for(int i=0;i<1024;i++) pt[i]=(uint8_t)i;
    for(int i=0;i<16;i++) key[i]=(uint8_t)(i*3+1);
    for(int i=0;i<12;i++) iv[i]=(uint8_t)(i*7+2);
    for(int i=0;i<20;i++) aad[i]=(uint8_t)(i+5);
    EverCrypt_AEAD_state_s*s=NULL;
    if(EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES128_GCM,&s,key)!=EverCrypt_Error_Success){printf("nokey\n");return 1;}
    SECRET(pt,sizeof pt);
    EverCrypt_AEAD_encrypt(s,iv,12,aad,20,pt,1024,ct,tag);
    PUBLIC(ct,sizeof ct); PUBLIC(tag,16);
    printf("%s done %02x\n",t,tag[0]);
  }
  else if(!strcmp(t,"knownbad_fmul")){
    uint64_t a[4],b[4],o[4];
    for(int i=0;i<4;i++){a[i]=0xffffffffffffffffULL-i;b[i]=0xfffffffffffffff0ULL+i;}
    a[3]&=0x7fffffffffffffffULL; b[3]&=0x7fffffffffffffffULL;
    SECRET(a,32); SECRET(b,32);
    fmul_plain(o,a,b);
    PUBLIC(o,32);
    printf("%s done %llx\n",t,(unsigned long long)o[0]);
  }
  else { printf("unknown\n"); return 1; }
  return 0;
}
