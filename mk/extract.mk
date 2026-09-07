# Extraction rules.
#
# hacl-pulse extracts with Custard, F*'s whole-program extraction pipeline,
# straight to C -- there is no karamel in the loop and no `-bundle` flags.
#
# The unit of extraction is a *unit*: one entry module, one .c file, one .h
# file.  Everything the entry module reaches is pulled in and inlined or
# emitted alongside it, so a unit is a self-contained translation unit over the
# C standard headers.  That is precisely the "one instance per translation
# unit, compiled with its own flags" discipline that HACL* got from the
# specialize tactic plus a pile of `-bundle` arguments; here it falls out of
# naming an entry point.
#
# A client makefile declares units by adding to C_UNITS, and names the entry
# points of each one:
#
#     C_UNITS += Hacl.Hash.SHA2.Ptr
#     CUSTARD_ENTRIES_Hacl.Hash.SHA2.Ptr := sha224 sha256 sha384 sha512
#
# and may set per-unit flags in CUSTARD_FLAGS_<dotted module name>, e.g. to
# pass --custard_c_no_prefix.
#
# Entry points are named one at a time rather than with
# --custard_entry_module, which makes *every* definition in the module a root:
# a root cannot be specialized, so a module that contains anything polymorphic
# -- and an entry module usually does, since it is where the type-class
# instances get pinned down -- is rejected.  Naming the four functions that
# are meant to be callable from C says what we mean anyway.

# The C name of a unit is its module name with dots replaced by underscores,
# which is also the name HACL* gave it.
c_name = $(subst .,_,$(1))

CUSTARD_FLAGS += --codegen Custard
CUSTARD_FLAGS += --custard_backend C
CUSTARD_FLAGS += --custard_monomorphize_types true

# Custard normalizes each monomorphized argument and each specialized
# signature to a normal form.  The signatures here are Pulse separation-logic
# assertions mentioning the whole SHA-2 specification, which is a large term
# even though none of it survives into C, so the default budget of ten million
# reduction steps is not enough.
CUSTARD_FLAGS += --custard_norm_budget 100000000

# Whole-program extraction reads far more than the entry module's own .checked
# file, and the dependency graph of a target Custard invented is not in
# .depend, so every unit depends on every .checked file.  Re-extracting the
# world when any module changes is cheap next to verifying it.
define hacl_c_unit
$(DIST_DIR)/$(call c_name,$(1)).c: $(CACHE_DIR)/$(1).fst.checked $$(ALL_CHECKED_FILES)
	$$(call msg, "EXTRACT", "$(1)")
	$$(Q)mkdir -p $$(DIST_DIR)
	$$(Q)$$(FSTAR) $$< $$(CUSTARD_FLAGS)                     \
	  $$(foreach e,$$(CUSTARD_ENTRIES_$(1)),--custard_entry $(1).$$(e)) \
	  $$(CUSTARD_FLAGS_$(1)) -o $$@

# Custard writes the header from the same invocation that writes the source.
$(DIST_DIR)/$(call c_name,$(1)).h: $(DIST_DIR)/$(call c_name,$(1)).c
	@true

$(BUILD_DIR)/$(call c_name,$(1)).o: $(DIST_DIR)/$(call c_name,$(1)).c
	$$(call msg, "CC", "$(call c_name,$(1))")
	$$(Q)mkdir -p $$(BUILD_DIR)
	$$(Q)$$(CC) $$(HACL_CFLAGS) -I $$(DIST_DIR) -I $$(HACL_ROOT)/c -c $$< -o $$@
endef

# A translation unit is compiled with warnings on and warnings fatal: an unused
# variable or a missing cast in generated code is a bug in the pipeline, not a
# style question.
HACL_CFLAGS ?= -std=c11 -O3 -Wall -Wextra -Werror

$(foreach u,$(C_UNITS),$(eval $(call hacl_c_unit,$(u))))

C_FILES   = $(foreach u,$(C_UNITS),$(DIST_DIR)/$(call c_name,$(u)).c)
C_HEADERS = $(foreach u,$(C_UNITS),$(DIST_DIR)/$(call c_name,$(u)).h)
C_OBJECTS = $(foreach u,$(C_UNITS),$(BUILD_DIR)/$(call c_name,$(u)).o)

.PHONY: extract compile
extract: $(C_FILES)
compile: $(C_OBJECTS)
