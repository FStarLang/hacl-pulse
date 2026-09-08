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

C_UNITS += Hacl.HMAC.Ptr
CUSTARD_ENTRIES_Hacl.HMAC.Ptr := hmac_sha224 hmac_sha256 hmac_sha384 hmac_sha512

C_UNITS += Hacl.HKDF.Ptr
CUSTARD_ENTRIES_Hacl.HKDF.Ptr := \
  extract_sha224 extract_sha256 extract_sha384 extract_sha512 \
  expand_sha224 expand_sha256 expand_sha384 expand_sha512

# Which unit each C test links against; see mk/test.mk.
TEST_UNITS_test_sha2 := Hacl.Hash.SHA2.Ptr
TEST_UNITS_test_streaming := Hacl.Streaming.SHA2.Ptr
TEST_UNITS_test_hmac := Hacl.HMAC.Ptr
TEST_UNITS_test_hkdf := Hacl.HKDF.Ptr

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
