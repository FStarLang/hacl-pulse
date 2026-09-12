# The C test suite.
#
# The tests are plain C: they link against the extracted units and check them
# against published vectors.  Property-based differential testing against the
# specifications happens on the F* side instead, where the specification is
# available; see tests/.
#
# One binary per test source.  A unit is a *whole-program* translation unit --
# everything its entry points reach is emitted into it -- so two units share
# code and each carries its own `custard_init_globals`; they cannot be linked
# together.  Each test therefore names the unit it exercises:
#
#     TEST_UNITS_test_hmac := Hacl.HMAC.Ptr
#
# and gets its own `main`, which calls `custard_init_globals` first.

TEST_SRCS  := $(wildcard $(HACL_ROOT)/tests/*.c)
TEST_NAMES := $(notdir $(basename $(TEST_SRCS)))

define hacl_test
$(BUILD_DIR)/tests/$(1).o: $(HACL_ROOT)/tests/$(1).c $$(C_HEADERS)
	$$(call msg, "CC", "$(1).c")
	$$(Q)mkdir -p $$(dir $$@)
	$$(Q)$$(CC) $$(HACL_CFLAGS) -I $$(DIST_DIR) -I $$(HACL_ROOT)/c \
	  -I $$(HACL_ROOT)/tests -c $$< -o $$@

$(BUILD_DIR)/tests/$(1): $(BUILD_DIR)/tests/$(1).o \
    $$(foreach u,$$(TEST_UNITS_$(1)),$$(BUILD_DIR)/$$(call c_name,$$(u)).o) \
    $$(HAND_OBJS)
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
