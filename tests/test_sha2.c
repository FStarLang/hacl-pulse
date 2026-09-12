/* SHA-2 against the published test vectors.
 *
 * The vectors are the four from FIPS 180-4's own examples ("abc", the
 * 448-bit and 896-bit strings, and a million 'a's) plus the empty string,
 * which between them exercise every path in the padding: a message shorter
 * than a block, one whose remainder leaves room for the length, one whose
 * remainder does not and so needs a second padding block, and one long
 * enough to run the block loop many times. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl.h"

typedef void (*hash_fn)(uint8_t *out, uint8_t *input, size_t input_len);

static int failures = 0;

static void hex(char *dst, const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    sprintf(dst + 2 * i, "%02x", src[i]);
}

static void check(const char *name, hash_fn f, size_t digest_len,
                  const uint8_t *msg, size_t msg_len, const char *expected) {
  uint8_t out[64];
  char got[129];

  memset(out, 0, sizeof out);
  f(out, (uint8_t *)msg, msg_len);
  hex(got, out, digest_len);

  if (strcmp(got, expected) != 0) {
    printf("  FAIL %s\n    got      %s\n    expected %s\n", name, got, expected);
    failures++;
  } else {
    printf("  ok   %s\n", name);
  }
}

static void check_str(const char *name, hash_fn f, size_t digest_len,
                      const char *msg, const char *expected) {
  check(name, f, digest_len, (const uint8_t *)msg, strlen(msg), expected);
}

#define ABC "abc"
#define S448 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
#define S896                                                                   \
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk" \
  "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

int main(void) {
  printf("SHA-224\n");
  check_str("empty", Hacl_Hash_SHA2_Ptr_sha224, 28, "",
            "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f");
  check_str("abc", Hacl_Hash_SHA2_Ptr_sha224, 28, ABC,
            "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7");
  check_str("448", Hacl_Hash_SHA2_Ptr_sha224, 28, S448,
            "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525");

  printf("SHA-256\n");
  check_str("empty", Hacl_Hash_SHA2_Ptr_sha256, 32, "",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
  check_str("abc", Hacl_Hash_SHA2_Ptr_sha256, 32, ABC,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  check_str("448", Hacl_Hash_SHA2_Ptr_sha256, 32, S448,
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
  check_str("896", Hacl_Hash_SHA2_Ptr_sha256, 32, S896,
            "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1");

  printf("SHA-384\n");
  check_str("empty", Hacl_Hash_SHA2_Ptr_sha384, 48, "",
            "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da"
            "274edebfe76f65fbd51ad2f14898b95b");
  check_str("abc", Hacl_Hash_SHA2_Ptr_sha384, 48, ABC,
            "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed"
            "8086072ba1e7cc2358baeca134c825a7");
  check_str("896", Hacl_Hash_SHA2_Ptr_sha384, 48, S896,
            "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712"
            "fcc7c71a557e2db966c3e9fa91746039");

  printf("SHA-512\n");
  check_str("empty", Hacl_Hash_SHA2_Ptr_sha512, 64, "",
            "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
            "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e");
  check_str("abc", Hacl_Hash_SHA2_Ptr_sha512, 64, ABC,
            "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
            "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f");
  check_str("896", Hacl_Hash_SHA2_Ptr_sha512, 64, S896,
            "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018"
            "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909");

  printf("a million 'a'\n");
  {
    size_t n = 1000000;
    uint8_t *big = malloc(n);
    if (big == NULL) {
      printf("  FAIL out of memory\n");
      return 1;
    }
    memset(big, 'a', n);
    check("sha224", Hacl_Hash_SHA2_Ptr_sha224, 28, big, n,
          "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67");
    check("sha256", Hacl_Hash_SHA2_Ptr_sha256, 32, big, n,
          "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
    check("sha384", Hacl_Hash_SHA2_Ptr_sha384, 48, big, n,
          "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b"
          "07b8b3dc38ecc4ebae97ddd87f3d8985");
    check("sha512", Hacl_Hash_SHA2_Ptr_sha512, 64, big, n,
          "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973eb"
          "de0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b");
    free(big);
  }

  if (failures != 0) {
    printf("%d failure(s)\n", failures);
    return 1;
  }
  printf("all SHA-2 vectors pass\n");
  return 0;
}
