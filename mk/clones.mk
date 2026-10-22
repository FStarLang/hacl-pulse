# Where the C compiler is doing specialisation we should have done ourselves.
#
# gcc's interprocedural constant propagation clones a function when a caller
# passes it a constant worth specialising on: the four moduli of P-256 and
# secp256k1, the rate of a Keccak permutation, the block length of a hash.
# Each clone is a measurable speedup, and every one of them is a speedup we
# are *not* in control of:
#
#   * It is spent against a budget for the translation unit as a whole
#     (--param ipa-cp-large-unit-insns, default sixteen thousand).  Adding an
#     unrelated primitive can exhaust it, at which point the clones silently
#     disappear and code that did not change gets slower.  This happened:
#     merging FrodoKEM and HPKE cost every elliptic curve operation a factor
#     of two and a half.
#
#   * clang does not do it at all -- LLVM's function specialisation pass is
#     off by default -- so anything we get this way is a gcc-only speedup and
#     shows up as a gcc/clang gap.
#
# So a clone is a message: here is a specialisation you left on the table.
# The answer is usually `inline_for_extraction` on the F* side, which makes
# the decision ours and gives both compilers the same code.
#
# This target lists the clones and diffs them against a baseline.  The
# baseline is a record of what we have not got to yet, and it is meant to
# shrink.  Growing it should be a deliberate act with a reason in the commit
# message.
#
# Requires gcc and nm; does nothing if gcc is absent.

CLONES_BASELINE := $(HACL_ROOT)/mk/clones.baseline
CLONES_OBJ      := $(BUILD_DIR)/clones/Hacl.o

# The suffixes gcc gives a clone.  .constprop is interprocedural constant
# propagation, .isra is the related "scalar replacement of aggregates" pass
# that drops or splits arguments, .part is partial inlining.  All three mean
# the same thing here: the compiler found a specialisation.
CLONES_SUFFIXES := constprop|isra|part

$(CLONES_OBJ): $(DIST_DIR)/Hacl.c $(C_HEADERS)
	$(call msg, "CC", "Hacl.c (clone survey)")
	$(Q)mkdir -p $(dir $@)
	$(Q)gcc -std=c11 -O3 -I $(DIST_DIR) -I $(HACL_ROOT)/c -c $< -o $@

.PHONY: clones
clones: $(CLONES_OBJ)
	$(Q)nm $(CLONES_OBJ) \
	  | awk '{ print $$NF }' \
	  | grep -E '\.($(CLONES_SUFFIXES))' \
	  | sed -E 's/\..*$$//' \
	  | sort -u > $(BUILD_DIR)/clones/now
	$(Q)if diff -u $(CLONES_BASELINE) $(BUILD_DIR)/clones/now > \
	      $(BUILD_DIR)/clones/diff; then                                    \
	  printf '  %-14s %s\n' OK                                              \
	    "$$(wc -l < $(CLONES_BASELINE)) known compiler specialisations";    \
	else                                                                    \
	  echo;                                                                 \
	  echo "The set of functions gcc specialises for us has changed:";      \
	  echo;                                                                 \
	  sed -n '/^+++/d;/^---/d;/^@@/d;/^[-+]/p' $(BUILD_DIR)/clones/diff;    \
	  echo;                                                                 \
	  echo "A '+' is a new specialisation the C compiler found and we did"; \
	  echo "not.  Specialise it in F* (inline_for_extraction), or add it";  \
	  echo "to mk/clones.baseline and say why.  A '-' is one we have taken"; \
	  echo "over, or lost: if you did not mean it, check that the IPA-CP";  \
	  echo "budget has not been exhausted by unrelated growth --";          \
	  echo "  gcc ... --param ipa-cp-large-unit-insns=1000000";             \
	  echo "will show what it would have cloned with room to spare.";       \
	  echo;                                                                 \
	  echo "Then: make clones-update";                                      \
	  exit 1;                                                               \
	fi

# Rewrite the baseline.  Deliberate: run it, read the diff, explain it.
.PHONY: clones-update
clones-update: $(CLONES_OBJ)
	$(Q)nm $(CLONES_OBJ) \
	  | awk '{ print $$NF }' \
	  | grep -E '\.($(CLONES_SUFFIXES))' \
	  | sed -E 's/\..*$$//' \
	  | sort -u > $(CLONES_BASELINE)
	$(call msg, "UPDATE", "mk/clones.baseline")

# What gcc *would* specialise if the unit were small enough.  Everything here
# that is not in the baseline is a speedup we are currently losing to the
# size of the translation unit; see design/notes.md, "inline is a global resource".
.PHONY: clones-available
clones-available: $(DIST_DIR)/Hacl.c
	$(Q)mkdir -p $(BUILD_DIR)/clones
	$(Q)gcc -std=c11 -O3 --param ipa-cp-large-unit-insns=1000000 \
	  --param ipa-cp-unit-growth=100 -I $(DIST_DIR) -I $(HACL_ROOT)/c \
	  -c $(DIST_DIR)/Hacl.c -o $(BUILD_DIR)/clones/Hacl-big.o
	$(Q)nm $(BUILD_DIR)/clones/Hacl-big.o \
	  | awk '{ print $$NF }' \
	  | grep -E '\.($(CLONES_SUFFIXES))' \
	  | sed -E 's/\..*$$//' \
	  | sort -u > $(BUILD_DIR)/clones/available
	$(Q)echo "Specialisations lost to the size of the translation unit:"
	$(Q)comm -13 $(CLONES_BASELINE) $(BUILD_DIR)/clones/available \
	  | sed 's/^/  /'
