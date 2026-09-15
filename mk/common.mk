# Common definitions for the hacl-pulse build.
#
# The build has three kinds of artifact:
#
#   * .checked files   -- the result of verifying an F*/Pulse module, in
#                         $(CACHE_DIR).
#   * .c / .h files    -- the result of running Custard on a *unit* (see
#                         mk/extract.mk), in $(DIST_DIR).
#   * .o / binaries    -- the result of compiling those, in $(BUILD_DIR).
#
# Nothing is ever written outside those three directories, so `make clean` is
# three `rm -rf`s.

HACL_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/..)

CACHE_DIR ?= $(HACL_ROOT)/obj/cache
BUILD_DIR ?= $(HACL_ROOT)/obj/build
DIST_DIR  ?= $(HACL_ROOT)/dist

# ---------------------------------------------------------------------------
# Locating the compiler
# ---------------------------------------------------------------------------
#
# hacl-pulse needs a stage3 F* -- that is, one with the Pulse plugin and the
# Pulse libraries installed -- built from the `gebner_custard` branch, which is
# where the Custard extraction pipeline lives.  Point FSTAR_EXE at it, or set
# FSTAR_ROOT to a checkout whose stage3 has been built.

ifneq ($(FSTAR_ROOT),)
FSTAR_EXE ?= $(FSTAR_ROOT)/stage3/out/bin/fstar.exe
endif
FSTAR_EXE ?= $(shell which fstar.exe 2>/dev/null)

ifeq ($(FSTAR_EXE),)
$(error No F* found. Set FSTAR_EXE to a stage3 fstar.exe from the gebner_custard branch, or FSTAR_ROOT to its checkout.)
endif

FSTAR_EXE := $(abspath $(FSTAR_EXE))

CC ?= cc

# ---------------------------------------------------------------------------
# Pretty printing
# ---------------------------------------------------------------------------

Q ?= @
ifeq ($(V),1)
  Q :=
  SIL :=
else
  SIL := --silent
endif

msg = @printf "  %-14s %s\n" $(1) $(2)

# ---------------------------------------------------------------------------
# Source layout
# ---------------------------------------------------------------------------
#
# Every directory listed here is both a source directory and an --include
# directory; there is no distinction between the two and no per-directory
# makefile.  A new algorithm is a new directory added to this list.

SOURCE_DIRS += lib
SOURCE_DIRS += spec
SOURCE_DIRS += code/hash
SOURCE_DIRS += code/chacha
SOURCE_DIRS += code/poly1305
SOURCE_DIRS += code/aead
SOURCE_DIRS += code/curve25519
SOURCE_DIRS += code/ed25519
SOURCE_DIRS += code/field256
SOURCE_DIRS += code/p256
SOURCE_DIRS += code/drbg
SOURCE_DIRS += code/aes
SOURCE_DIRS += code/bignum
SOURCE_DIRS += code/ffdhe
SOURCE_DIRS += code/rsapss
SOURCE_DIRS += code
SOURCE_DIRS += tests

INCLUDE_DIRS := $(addprefix $(HACL_ROOT)/,$(SOURCE_DIRS))

FSTAR_FILES := $(wildcard $(addsuffix /*.fst,$(INCLUDE_DIRS)) $(addsuffix /*.fsti,$(INCLUDE_DIRS)))

# ---------------------------------------------------------------------------
# F* invocation
# ---------------------------------------------------------------------------

# Set ADMIT=1 to skip all SMT queries.  Useful when iterating on extraction.
ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

OTHERFLAGS += --ext optimize_let_vc
OTHERFLAGS += --ext fly_deps
OTHERFLAGS += --warn_error -321   # "unused open" -- too noisy to be useful
OTHERFLAGS += --warn_error @247   # could not write a .checked file: fail now

FSTAR = $(FSTAR_EXE) $(SIL)                                     \
	  --cache_checked_modules                               \
	  --cache_dir $(CACHE_DIR)                              \
	  --odir $(BUILD_DIR)                                   \
	  --already_cached 'Prims,FStar,Pulse,PulseCore'        \
	  $(addprefix --include ,$(INCLUDE_DIRS))               \
	  $(OTHERFLAGS) $(MAYBE_ADMIT)
