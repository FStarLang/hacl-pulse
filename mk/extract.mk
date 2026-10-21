# Extraction rules.
#
# hacl-pulse extracts with Custard, F*'s whole-program extraction pipeline,
# straight to C -- there is no karamel in the loop and no `-bundle` flags.
#
# Custard extracts a *whole program*: one root module plus a list of entry
# points, and everything those entry points reach is inlined or emitted
# alongside them.  The library is one such program.  Its root is code/Hacl.fst,
# which names every entry module; its entry points are listed in CUSTARD_ENTRIES
# in the Makefile; and the result is a single self-contained dist/Hacl.c over
# the C standard headers, plus dist/Hacl.h declaring exactly the entry points.
#
# It used to be sixteen programs, one per algorithm family.  That gave each
# family its own copy of everything it reached -- sixteen secret-integer
# layers, three SHA-2s -- and, since two whole programs define the same static
# helpers, made it impossible to link any two of them into one binary.  One
# program shares what is shared and links with itself.
#
# Entry points are named one at a time rather than with
# --custard_entry_module, which makes *every* definition in the module a root:
# a root cannot be specialized, so a module that contains anything polymorphic
# -- and an entry module usually does, since it is where the type-class
# instances get pinned down -- is rejected.  Naming the functions that are
# meant to be callable from C says what we mean anyway.

CUSTARD_FLAGS += --codegen C
CUSTARD_FLAGS += --custard_monomorphize_types true

# Custard normalizes each monomorphized argument and each specialized
# signature to a normal form.  The signatures here are Pulse separation-logic
# assertions mentioning the whole SHA-2 specification, which is a large term
# even though none of it survives into C, so the default budget of ten million
# reduction steps is not enough.
CUSTARD_FLAGS += --custard_norm_budget 100000000

# Whole-program extraction reads far more than the root module's own .checked
# file, and the dependency graph of a target Custard invented is not in
# .depend, so the library depends on every .checked file.  Re-extracting the
# world when any module changes is cheap next to verifying it.
$(DIST_DIR)/Hacl.c: $(CACHE_DIR)/$(C_ROOT).fst.checked $(ALL_CHECKED_FILES)
	$(call msg, "EXTRACT", "$(C_ROOT)")
	$(Q)mkdir -p $(DIST_DIR)
	$(Q)$(FSTAR) $< $(CUSTARD_FLAGS)                                       \
	  $(foreach e,$(CUSTARD_ENTRIES),--custard_entry $(e)) -o $@

# Custard writes the header from the same invocation that writes the source.
$(DIST_DIR)/Hacl.h: $(DIST_DIR)/Hacl.c
	@true

$(BUILD_DIR)/Hacl.o: $(DIST_DIR)/Hacl.c
	$(call msg, "CC", "Hacl")
	$(Q)mkdir -p $(BUILD_DIR)
	$(Q)$(CC) $(HACL_CFLAGS) $(GENERATED_CFLAGS) -I $(DIST_DIR)             \
	  -I $(HACL_ROOT)/c -c $< -o $@

# A translation unit is compiled with warnings on and warnings fatal: an unused
# variable or a missing cast in generated code is a bug in the pipeline, not a
# style question.
HACL_CFLAGS ?= -std=c11 -O3 -Wall -Wextra -Werror

# Extra flags for the generated translation unit only.  There are none: it
# used to need -Wno-dangling-pointer, for stack arrays sized by a run time
# parameter, but those now live on the heap (see lib/Hacl.Mem.fsti).
GENERATED_CFLAGS ?=

# Handwritten C.  Everything in c/ is trusted computing base -- currently just
# the platform entropy shim -- and is compiled with the same flags and linked
# into every binary that needs it.
HAND_SRCS := $(wildcard $(HACL_ROOT)/c/*.c)
HAND_OBJS := $(patsubst $(HACL_ROOT)/c/%.c,$(BUILD_DIR)/c/%.o,$(HAND_SRCS))

$(BUILD_DIR)/c/%.o: $(HACL_ROOT)/c/%.c $(HACL_ROOT)/c/%.h
	$(call msg, "CC", "c/$*.c")
	$(Q)mkdir -p $(dir $@)
	$(Q)$(CC) $(HACL_CFLAGS) -I $(HACL_ROOT)/c -c $< -o $@

C_FILES   = $(DIST_DIR)/Hacl.c
C_HEADERS = $(DIST_DIR)/Hacl.h
C_OBJECTS = $(BUILD_DIR)/Hacl.o

.PHONY: extract compile
extract: $(C_FILES)
compile: $(C_OBJECTS) $(HAND_OBJS)
