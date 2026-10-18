# Checks that every array this library allocates is wiped when it is done
# with, and that no caller can choose how much stack we use.  See
# lib/Hacl.Mem.fsti and issue #1.
#
#   make lint    the source rules in mk/memlint.pl
#   make stack   per-function stack frames of the generated C
#
# Both run as part of `make`.

LINT_SRCS := $(shell find $(HACL_ROOT)/code $(HACL_ROOT)/lib $(HACL_ROOT)/tests \
                       -name '*.fst' -o -name '*.fsti' 2>/dev/null)

.PHONY: lint
lint:
	$(call msg, "LINT", "memory")
	$(Q)perl $(HACL_ROOT)/mk/memlint.pl $(LINT_SRCS)

# gcc's -fstack-usage reports, per function, the frame size and whether it is
# "static", "dynamic,bounded" (a VLA whose size gcc can bound -- here, always
# one sized by a constant that monomorphization has bound to a variable) or
# "dynamic": a frame whose size depends on a run time value.  The last is a
# caller choosing our stack usage, and is an error.  Anything that big belongs
# on the heap, via Hacl.Mem.alloc.  STACK_MAX is the largest frame we accept;
# the largest today is ML-KEM-1024 encryption, at about 25 KB.
STACK_MAX ?= 32768
STACK_OBJ := $(BUILD_DIR)/stack/Hacl.o
STACK_SU  := $(BUILD_DIR)/stack/Hacl.su

$(STACK_SU): $(DIST_DIR)/Hacl.c $(C_HEADERS)
	$(call msg, "CC", "Hacl (stack usage)")
	$(Q)mkdir -p $(dir $@)
	$(Q)$(CC) $(HACL_CFLAGS) $(GENERATED_CFLAGS) -fstack-usage -I $(DIST_DIR) \
	  -I $(HACL_ROOT)/c -c $< -o $(STACK_OBJ)

.PHONY: stack
stack: $(STACK_SU)
	$(call msg, "LINT", "stack")
	$(Q)awk -F'\t' -v max=$(STACK_MAX) '                                 \
	  $$3 == "dynamic" { print "unbounded stack frame: " $$1; bad = 1 }   \
	  $$2 + 0 > max    { print "stack frame of " $$2 " bytes (> " max "): " $$1; bad = 1 } \
	  END { exit bad }' $<
