# Verification rules.
#
# There is one dependency graph for the whole library, computed once by
# `fstar.exe --dep full`, rather than a makefile per directory.  Pulse modules
# and plain F* modules are checked by exactly the same rule; `#lang-pulse` is a
# property of the file, not of the build.

.depend: $(FSTAR_FILES) $(HACL_ROOT)/mk/common.mk
	$(call msg, "DEPEND", "$(HACL_ROOT)")
	$(Q)mkdir -p $(CACHE_DIR) $(BUILD_DIR)
	$(Q)$(FSTAR) --dep full $(FSTAR_FILES) --output_deps_to $@

ifeq ($(filter clean distclean,$(MAKECMDGOALS)),)
include .depend
endif

# The .depend places these in $(CACHE_DIR); the % here is a full path.
%.fst.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(Q)$(FSTAR) $<
	$(Q)touch -c $@

%.fsti.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(Q)$(FSTAR) $<
	$(Q)touch -c $@

.PHONY: verify
verify: $(ALL_CHECKED_FILES)
