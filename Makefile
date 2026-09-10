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
# One line per public translation unit.  See mk/extract.mk for what a unit is.

C_UNITS += Hacl.Hash.SHA2.Ptr
CUSTARD_ENTRIES_Hacl.Hash.SHA2.Ptr := sha224 sha256 sha384 sha512

C_UNITS += Hacl.Streaming.SHA2.Ptr
CUSTARD_ENTRIES_Hacl.Streaming.SHA2.Ptr := \
  sha224_init sha224_update sha224_digest \
  sha256_init sha256_update sha256_digest \
  sha384_init sha384_update sha384_digest \
  sha512_init sha512_update sha512_digest

C_UNITS += Hacl.Hash.SHA3.Ptr
CUSTARD_ENTRIES_Hacl.Hash.SHA3.Ptr := \
  sha3_224 sha3_256 sha3_384 sha3_512 shake128 shake256

C_UNITS += Hacl.Streaming.SHA3.Ptr
CUSTARD_ENTRIES_Hacl.Streaming.SHA3.Ptr := \
  sha3_224_init sha3_224_update sha3_224_digest \
  sha3_256_init sha3_256_update sha3_256_digest \
  sha3_384_init sha3_384_update sha3_384_digest \
  sha3_512_init sha3_512_update sha3_512_digest \
  shake128_init shake128_update shake128_digest \
  shake256_init shake256_update shake256_digest

C_UNITS += Hacl.Hash.Blake2.Ptr
CUSTARD_ENTRIES_Hacl.Hash.Blake2.Ptr := \
  blake2b_512 blake2b_384 blake2b_256 blake2b_160 \
  blake2s_256 blake2s_224 blake2s_160 blake2s_128

C_UNITS += Hacl.Streaming.Blake2.Ptr
CUSTARD_ENTRIES_Hacl.Streaming.Blake2.Ptr := \
  blake2b_512_init blake2b_512_update blake2b_512_digest \
  blake2b_384_init blake2b_384_update blake2b_384_digest \
  blake2b_256_init blake2b_256_update blake2b_256_digest \
  blake2b_160_init blake2b_160_update blake2b_160_digest \
  blake2s_256_init blake2s_256_update blake2s_256_digest \
  blake2s_224_init blake2s_224_update blake2s_224_digest \
  blake2s_160_init blake2s_160_update blake2s_160_digest \
  blake2s_128_init blake2s_128_update blake2s_128_digest

C_UNITS += Hacl.Chacha20.Ptr
CUSTARD_ENTRIES_Hacl.Chacha20.Ptr := encrypt decrypt

C_UNITS += Hacl.Poly1305.Ptr
CUSTARD_ENTRIES_Hacl.Poly1305.Ptr := mac

C_UNITS += Hacl.Chacha20Poly1305.Ptr
CUSTARD_ENTRIES_Hacl.Chacha20Poly1305.Ptr := encrypt decrypt

C_UNITS += Hacl.HMAC.Ptr
CUSTARD_ENTRIES_Hacl.HMAC.Ptr := hmac_sha224 hmac_sha256 hmac_sha384 hmac_sha512

C_UNITS += Hacl.HKDF.Ptr
CUSTARD_ENTRIES_Hacl.HKDF.Ptr := \
  extract_sha224 extract_sha256 extract_sha384 extract_sha512 \
  expand_sha224 expand_sha256 expand_sha384 expand_sha512

C_UNITS += Hacl.Curve25519.Ptr
CUSTARD_ENTRIES_Hacl.Curve25519.Ptr := scalarmult secret_to_public ecdh

# Which unit each C test links against; see mk/test.mk.
TEST_UNITS_test_sha2 := Hacl.Hash.SHA2.Ptr
TEST_UNITS_test_streaming := Hacl.Streaming.SHA2.Ptr
TEST_UNITS_test_sha3 := Hacl.Hash.SHA3.Ptr
TEST_UNITS_test_sha3_streaming := Hacl.Streaming.SHA3.Ptr
TEST_UNITS_test_blake2 := Hacl.Hash.Blake2.Ptr
TEST_UNITS_test_blake2_streaming := Hacl.Streaming.Blake2.Ptr
TEST_UNITS_test_chacha20 := Hacl.Chacha20.Ptr
TEST_UNITS_test_poly1305 := Hacl.Poly1305.Ptr
TEST_UNITS_test_chacha20poly1305 := Hacl.Chacha20Poly1305.Ptr
TEST_UNITS_test_hmac := Hacl.HMAC.Ptr
TEST_UNITS_test_hkdf := Hacl.HKDF.Ptr
TEST_UNITS_test_curve25519 := Hacl.Curve25519.Ptr

include mk/extract.mk

.DEFAULT_GOAL := all
.PHONY: all
all: verify extract compile test

include mk/verify.mk
include mk/test.mk

.PHONY: clean
clean:
	rm -rf obj .depend

.PHONY: distclean
distclean: clean
	rm -rf $(DIST_DIR)
