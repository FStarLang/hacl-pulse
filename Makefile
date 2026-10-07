# hacl-pulse
#
#   make            verify everything, extract C, compile it, run the tests
#   make verify     verify everything
#   make extract    (re)generate dist/
#   make test       build and run the C test suite
#   make clean

include mk/common.mk

# ---------------------------------------------------------------------------
# What gets extracted to C
# ---------------------------------------------------------------------------
#
# The library is one whole program: one root module, one dist/Hacl.c, one
# dist/Hacl.h.  See mk/extract.mk.  C_ROOT names the root; CUSTARD_ENTRIES
# lists, fully qualified, every function the library exports.  Nothing else
# survives extraction, so this list *is* the public API.

C_ROOT := Hacl

CUSTARD_ENTRIES += $(addprefix Hacl.Hash.MD5., md5)

CUSTARD_ENTRIES += $(addprefix Hacl.Streaming.MD5., \
  md5_init md5_update md5_digest)

CUSTARD_ENTRIES += $(addprefix Hacl.Hash.SHA1., sha1)

CUSTARD_ENTRIES += $(addprefix Hacl.Streaming.SHA1., \
  sha1_init sha1_update sha1_digest)

CUSTARD_ENTRIES += $(addprefix Hacl.Hash.SHA2., \
  sha224 sha256 sha384 sha512)

CUSTARD_ENTRIES += $(addprefix Hacl.Streaming.SHA2., \
  sha224_init sha224_update sha224_digest \
  sha256_init sha256_update sha256_digest \
  sha384_init sha384_update sha384_digest \
  sha512_init sha512_update sha512_digest)

CUSTARD_ENTRIES += $(addprefix Hacl.Hash.SHA3., \
  sha3_224 sha3_256 sha3_384 sha3_512 shake128 shake256)

CUSTARD_ENTRIES += $(addprefix Hacl.Streaming.SHA3., \
  sha3_224_init sha3_224_update sha3_224_digest \
  sha3_256_init sha3_256_update sha3_256_digest \
  sha3_384_init sha3_384_update sha3_384_digest \
  sha3_512_init sha3_512_update sha3_512_digest \
  shake128_init shake128_update shake128_digest \
  shake256_init shake256_update shake256_digest)

CUSTARD_ENTRIES += $(addprefix Hacl.Hash.Blake2.Named., \
  blake2b_512 blake2b_384 blake2b_256 blake2b_160 \
  blake2s_256 blake2s_224 blake2s_160 blake2s_128)

CUSTARD_ENTRIES += $(addprefix Hacl.Streaming.Blake2., \
  blake2b_512_init blake2b_512_update blake2b_512_digest \
  blake2b_384_init blake2b_384_update blake2b_384_digest \
  blake2b_256_init blake2b_256_update blake2b_256_digest \
  blake2b_160_init blake2b_160_update blake2b_160_digest \
  blake2s_256_init blake2s_256_update blake2s_256_digest \
  blake2s_224_init blake2s_224_update blake2s_224_digest \
  blake2s_160_init blake2s_160_update blake2s_160_digest \
  blake2s_128_init blake2s_128_update blake2s_128_digest)

CUSTARD_ENTRIES += $(addprefix Hacl.Chacha20., encrypt decrypt)

CUSTARD_ENTRIES += $(addprefix Hacl.Poly1305., mac)

CUSTARD_ENTRIES += $(addprefix Hacl.Chacha20Poly1305., encrypt decrypt)

CUSTARD_ENTRIES += $(addprefix Hacl.Salsa20., encrypt decrypt key_block0 hsalsa20)

CUSTARD_ENTRIES += $(addprefix Hacl.NaCl.crypto_secretbox_, \
                     detached open_detached easy open_easy)
CUSTARD_ENTRIES += $(addprefix Hacl.NaCl.crypto_box_, \
                     beforenm detached open_detached easy open_easy \
                     detached_afternm open_detached_afternm \
                     easy_afternm open_easy_afternm)

CUSTARD_ENTRIES += $(addprefix Hacl.HMAC.SHA1., hmac_sha1)

CUSTARD_ENTRIES += $(addprefix Hacl.HMAC., \
  hmac_sha224 hmac_sha256 hmac_sha384 hmac_sha512)

CUSTARD_ENTRIES += $(addprefix Hacl.Streaming.HMAC., \
  hmac_sha224_init hmac_sha224_update hmac_sha224_digest \
  hmac_sha256_init hmac_sha256_update hmac_sha256_digest \
  hmac_sha384_init hmac_sha384_update hmac_sha384_digest \
  hmac_sha512_init hmac_sha512_update hmac_sha512_digest)

CUSTARD_ENTRIES += $(addprefix Hacl.HKDF., \
  extract_sha224 extract_sha256 extract_sha384 extract_sha512 \
  expand_sha224 expand_sha256 expand_sha384 expand_sha512)

CUSTARD_ENTRIES += $(addprefix Hacl.RSAPSS., \
  sign_sha256 sign_sha384 sign_sha512 \
  verify_sha256 verify_sha384 verify_sha512)

CUSTARD_ENTRIES += $(addprefix Hacl.Curve25519., \
  scalarmult secret_to_public ecdh)

CUSTARD_ENTRIES += $(addprefix Hacl.Ed25519., \
  secret_to_public expand_keys sign sign_expanded verify)

CUSTARD_ENTRIES += $(addprefix Hacl.P256., \
  ecdsa_sign_sha256 ecdsa_sign_sha384 ecdsa_sign_sha512 \
  ecdsa_sign_without_hash \
  ecdsa_verify_sha256 ecdsa_verify_sha384 ecdsa_verify_sha512 \
  ecdsa_verify_without_hash)

CUSTARD_ENTRIES += Hacl.P256.Key.validate_private_key \
                   Hacl.P256.Key.Public.validate_public_key

CUSTARD_ENTRIES += $(addprefix Hacl.P256.Sec1., \
  raw_to_uncompressed raw_to_compressed \
  uncompressed_to_raw compressed_to_raw)

CUSTARD_ENTRIES += $(addprefix Hacl.P256.Ecdh., dh_initiator dh_responder)

CUSTARD_ENTRIES += $(addprefix Hacl.K256., \
  ecdsa_sign_hashed_msg ecdsa_sign_sha256 \
  ecdsa_verify_hashed_msg ecdsa_verify_sha256 \
  secp256k1_ecdsa_sign_hashed_msg secp256k1_ecdsa_sign_sha256 \
  secp256k1_ecdsa_verify_hashed_msg secp256k1_ecdsa_verify_sha256)

CUSTARD_ENTRIES += Hacl.K256.Key.validate_private_key \
                   Hacl.K256.Key.Public.validate_public_key

CUSTARD_ENTRIES += $(addprefix Hacl.K256.LowS., \
  is_signature_normalized signature_normalize)

CUSTARD_ENTRIES += $(addprefix Hacl.K256.Sec1., \
  raw_to_uncompressed raw_to_compressed \
  uncompressed_to_raw compressed_to_raw)

CUSTARD_ENTRIES += $(addprefix Hacl.K256.Ecdh., dh_initiator dh_responder)

CUSTARD_ENTRIES += $(addprefix Hacl.HMAC.DRBG., \
  instantiate_sha256 reseed_sha256 generate_sha256 \
  instantiate_sha384 reseed_sha384 generate_sha384 \
  instantiate_sha512 reseed_sha512 generate_sha512)

CUSTARD_ENTRIES += $(addprefix Hacl.AES.GCM., \
  aes128_expand aes128_encrypt_expanded aes128_decrypt_expanded \
  aes256_expand aes256_encrypt_expanded aes256_decrypt_expanded \
  aes128_encrypt aes128_decrypt aes256_encrypt aes256_decrypt)

CUSTARD_ENTRIES += $(addprefix Hacl.Bignum.Base., \
  zero add sub add_mod sub_mod mul sqr lt_mask eq_mask table_select)

# Exported for tests/test_consttime.c, which times each of them once per
# value of the secret they branch on.  See "The compiler is allowed to undo
# a constant-time algorithm" in README.md.
CUSTARD_ENTRIES += Hacl.Impl.Select.eq_mask_bytes
CUSTARD_ENTRIES += Hacl.AES.Core.sbox_impl

CUSTARD_ENTRIES += $(addprefix Hacl.Bignum.Convert., \
  from_bytes_be from_bytes_le to_bytes_be to_bytes_le)

CUSTARD_ENTRIES += $(addprefix Hacl.Bignum.Montgomery., \
  mont_mu precomp reduction mont_mul from_mont modulo)

CUSTARD_ENTRIES += $(addprefix Hacl.Bignum.Exponentiation., \
  mod_exp_consttime mod_exp_vartime mod_inv_prime_vartime)

CUSTARD_ENTRIES += $(addprefix Hacl.FFDHE., \
  ffdhe2048_secret_to_public ffdhe2048_shared_secret \
  ffdhe3072_secret_to_public ffdhe3072_shared_secret \
  ffdhe4096_secret_to_public ffdhe4096_shared_secret \
  ffdhe6144_secret_to_public ffdhe6144_shared_secret \
  ffdhe8192_secret_to_public ffdhe8192_shared_secret)

CUSTARD_ENTRIES += $(addprefix Hacl.Frodo64., keypair enc dec)
CUSTARD_ENTRIES += $(addprefix Hacl.Frodo640., keypair enc dec)
CUSTARD_ENTRIES += $(addprefix Hacl.Frodo976., keypair enc dec)
CUSTARD_ENTRIES += $(addprefix Hacl.Frodo1344., keypair enc dec)

CUSTARD_ENTRIES += $(addprefix Hacl.MLKEM512., keypair enc dec ek_valid dk_valid)
CUSTARD_ENTRIES += $(addprefix Hacl.MLKEM768., keypair enc dec ek_valid dk_valid)
CUSTARD_ENTRIES += $(addprefix Hacl.MLKEM1024., keypair enc dec ek_valid dk_valid)

CUSTARD_ENTRIES += $(addprefix Hacl.HPKE.Suites., \
  x25519_sha256_chachapoly_setup_base_s x25519_sha256_chachapoly_setup_base_r \
  x25519_sha256_chachapoly_seal x25519_sha256_chachapoly_open \
  x25519_sha512_chachapoly_setup_base_s x25519_sha512_chachapoly_setup_base_r \
  x25519_sha512_chachapoly_seal x25519_sha512_chachapoly_open \
  p256_sha256_chachapoly_setup_base_s p256_sha256_chachapoly_setup_base_r \
  p256_sha256_chachapoly_seal p256_sha256_chachapoly_open \
  x25519_sha256_aes128gcm_setup_base_s x25519_sha256_aes128gcm_setup_base_r \
  x25519_sha256_aes128gcm_seal x25519_sha256_aes128gcm_open)

include mk/extract.mk

.DEFAULT_GOAL := all
.PHONY: all
all: verify extract compile test

include mk/verify.mk
include mk/test.mk
include mk/clones.mk

.PHONY: clean
clean:
	rm -rf obj .depend

.PHONY: distclean
distclean: clean
	rm -rf $(DIST_DIR)
