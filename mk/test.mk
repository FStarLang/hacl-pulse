# The C test suite.
#
# The tests are plain C: they link against the extracted units and check them
# against published vectors.  Property-based differential testing against the
# specifications happens on the F* side instead, where the specification is
# available; see tests/.

TEST_SRCS := $(wildcard $(HACL_ROOT)/tests/*.c)
TEST_OBJS := $(patsubst $(HACL_ROOT)/tests/%.c,$(BUILD_DIR)/tests/%.o,$(TEST_SRCS))

$(BUILD_DIR)/tests/%.o: $(HACL_ROOT)/tests/%.c $(C_HEADERS)
	$(call msg, "CC", $(notdir $<))
	$(Q)mkdir -p $(dir $@)
	$(Q)$(CC) $(HACL_CFLAGS) -I $(DIST_DIR) -I $(HACL_ROOT)/c -I $(HACL_ROOT)/tests -c $< -o $@

$(BUILD_DIR)/test-runner: $(TEST_OBJS) $(C_OBJECTS)
	$(call msg, "LD", "test-runner")
	$(Q)$(CC) $(HACL_CFLAGS) $^ -o $@

.PHONY: test
test: $(BUILD_DIR)/test-runner
	$(call msg, "RUN", "test-runner")
	$(Q)$<
