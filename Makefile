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
