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

.PHONY: test
test: $(TEST_BINS)
	$(Q)for t in $(TEST_BINS); do                                          \
	  printf '  %-14s %s\n' RUN "$$(basename $$t)";                        \
	  $$t || exit 1;                                                       \
	done
