# The C test suite.
#
# The tests are plain C: they link against the extracted units and check them
# against published vectors.  Property-based differential testing against the
# specifications happens on the F* side instead, where the specification is
# available; see tests/.
#
# One binary per test source.  There is a single extracted translation unit,
# so every test just includes "Hacl.h" and links dist/Hacl.c; no test has to
# say which part of the library it exercises, and a test is free to use two
# algorithms at once.

TEST_SRCS  := $(wildcard $(HACL_ROOT)/tests/*.c)
TEST_NAMES := $(notdir $(basename $(TEST_SRCS)))

define hacl_test
$(BUILD_DIR)/tests/$(1).o: $(HACL_ROOT)/tests/$(1).c $$(C_HEADERS)
	$$(call msg, "CC", "$(1).c")
	$$(Q)mkdir -p $$(dir $$@)
	$$(Q)$$(CC) $$(HACL_CFLAGS) -I $$(DIST_DIR) -I $$(HACL_ROOT)/c \
	  -I $$(HACL_ROOT)/tests -c $$< -o $$@

$(BUILD_DIR)/tests/$(1): $(BUILD_DIR)/tests/$(1).o $$(C_OBJECTS) $$(HAND_OBJS)
	$$(call msg, "LD", "$(1)")
	$$(Q)$$(CC) $$(HACL_CFLAGS) $$^ -o $$@

TEST_BINS += $(BUILD_DIR)/tests/$(1)
endef

$(foreach t,$(TEST_NAMES),$(eval $(call hacl_test,$(t))))

# Tests built but not run by `make test`, e.g. TEST_NORUN=test_consttime on
# a shared machine whose timing noise the constant-time audit would flag.
TEST_NORUN ?=

.PHONY: test
test: $(TEST_BINS)
	$(Q)for t in $(filter-out $(addprefix $(BUILD_DIR)/tests/,$(TEST_NORUN)),$(TEST_BINS)); do                                          \
	  printf '  %-14s %s\n' RUN "$$(basename $$t)";                        \
	  $$t || exit 1;                                                       \
	done

# ---------------------------------------------------------------------------
# Another architecture
# ---------------------------------------------------------------------------
#
# `make cross` compiles the library and the test suite with CROSS_CC, by
# default for aarch64, and runs the tests with CROSS_RUN if that is set or
# qemu-aarch64 is on the PATH.  It checks that every function compiled for an
# x86 extension is guarded by `#if defined(__x86_64__)` and every call to one
# is under the matching `Hacl.X64.x86_64` test; see lib/Hacl.X64.fst.  A
# miss shows up here as an unknown `target` attribute or an undeclared
# function.  It is not part of `make` because it needs a cross compiler
# (on Debian and Ubuntu, gcc-aarch64-linux-gnu and qemu-user).  The
# constant-time audit is compiled but not run: under an emulator its timings
# measure qemu, not the code.

CROSS_CC    ?= aarch64-linux-gnu-gcc
CROSS_QEMU  ?= qemu-aarch64 -L /usr/aarch64-linux-gnu
CROSS_RUN   ?= $(if $(shell command -v $(firstword $(CROSS_QEMU)) 2>/dev/null),$(CROSS_QEMU))
CROSS_DIR   := $(BUILD_DIR)/cross
CROSS_NORUN ?= test_consttime

.PHONY: cross
cross: $(C_FILES) $(C_HEADERS)
	$(Q)mkdir -p $(CROSS_DIR)/tests
	$(call msg, "CROSS-CC", "Hacl")
	$(Q)$(CROSS_CC) $(HACL_CFLAGS) $(GENERATED_CFLAGS) -I $(DIST_DIR)         \
	  -I $(HACL_ROOT)/c -c $(DIST_DIR)/Hacl.c -o $(CROSS_DIR)/Hacl.o
	$(Q)for f in $(HAND_SRCS); do                                          \
	  printf '  %-14s %s\n' CROSS-CC "c/$$(basename $$f)";                 \
	  $(CROSS_CC) $(HACL_CFLAGS) -I $(HACL_ROOT)/c -c $$f                  \
	    -o $(CROSS_DIR)/$$(basename $$f .c).o || exit 1;                   \
	done
	$(Q)for t in $(TEST_NAMES); do                                         \
	  printf '  %-14s %s\n' CROSS-CC "$$t.c";                              \
	  $(CROSS_CC) $(HACL_CFLAGS) -I $(DIST_DIR) -I $(HACL_ROOT)/c          \
	    -I $(HACL_ROOT)/tests $(HACL_ROOT)/tests/$$t.c $(CROSS_DIR)/*.o    \
	    -o $(CROSS_DIR)/tests/$$t || exit 1;                               \
	done
ifneq ($(strip $(CROSS_RUN)),)
	$(Q)for t in $(filter-out $(CROSS_NORUN),$(TEST_NAMES)); do            \
	  printf '  %-14s %s\n' CROSS-RUN "$$t";                               \
	  $(CROSS_RUN) $(CROSS_DIR)/tests/$$t || exit 1;                       \
	done
else
	@echo "  (no $(firstword $(CROSS_QEMU)); the cross-compiled tests were not run)"
endif
