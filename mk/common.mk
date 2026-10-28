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
# hacl-pulse needs an F* with the Pulse plugin and the Pulse libraries
# installed, new enough to have Custard, where the extraction pipeline lives.
# A nightly tarball from FStarLang/FStar-nightly is one -- it ships Pulse --
# and so is a checkout of master built through stage3.  The tree tracks
# master; past releases are not supported.  CI uses the nightly named in
# .fstar-nightly.
#
# Point FSTAR_EXE at the binary, or FSTAR_ROOT at either kind of tree:
#
#   make FSTAR_ROOT=$HOME/tools/fstar-nightly   # unpacked nightly
#   make FSTAR_ROOT=$HOME/tools/fstar           # source checkout
#
# A nightly has bin/fstar.exe; a checkout has stage3/out/bin/fstar.exe, and
# the stage3 one wins if somehow both are there, because a checkout being
# built is the case where the two disagree.

ifneq ($(FSTAR_ROOT),)
  ifneq ($(wildcard $(FSTAR_ROOT)/stage3/out/bin/fstar.exe),)
FSTAR_EXE ?= $(FSTAR_ROOT)/stage3/out/bin/fstar.exe
  else
FSTAR_EXE ?= $(FSTAR_ROOT)/bin/fstar.exe
  endif
endif
FSTAR_EXE ?= $(shell which fstar.exe 2>/dev/null)

# `make clean` should not need a compiler to delete a directory.
NEEDS_FSTAR := $(filter-out clean distclean,$(or $(MAKECMDGOALS),all))

# DIST_ONLY=1 builds and tests the C already in $(DIST_DIR) without F*:
# dist/Hacl.c becomes a source file rather than a target, so nothing is
# verified or re-extracted.  For compilers and machines F* does not run on,
# such as CI's clang and arm64 jobs, which test the dist/ the verify job
# produced.  Only the C targets (compile, stack, test, cross) make sense.
ifneq ($(DIST_ONLY),)
NEEDS_FSTAR :=
endif

ifneq ($(NEEDS_FSTAR),)
  ifeq ($(FSTAR_EXE),)
$(error No F* found. Set FSTAR_EXE to an fstar.exe with Pulse and Custard, or FSTAR_ROOT to a release tree or a stage3 checkout.)
  endif
  ifeq ($(wildcard $(FSTAR_EXE)),)
$(error No fstar.exe at $(FSTAR_EXE). Set FSTAR_EXE, or FSTAR_ROOT to a release tree or a stage3 checkout.)
  endif
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
SOURCE_DIRS += code/salsa20
SOURCE_DIRS += code/poly1305
SOURCE_DIRS += code/aead
SOURCE_DIRS += code/curve25519
SOURCE_DIRS += code/nacl
SOURCE_DIRS += code/ed25519
SOURCE_DIRS += code/field256
SOURCE_DIRS += code/p256
SOURCE_DIRS += code/p384
SOURCE_DIRS += code/k256
SOURCE_DIRS += code/drbg
SOURCE_DIRS += code/aes
SOURCE_DIRS += code/bignum
SOURCE_DIRS += code/ffdhe
SOURCE_DIRS += code/rsapss
SOURCE_DIRS += code/frodo
SOURCE_DIRS += code/hpke
SOURCE_DIRS += code/mlkem
SOURCE_DIRS += code/mldsa
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
