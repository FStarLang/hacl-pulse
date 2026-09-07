# Benchmarks and constant-time audit for the Vale -> C migration evaluation.
# See README.md.
#
#   make            build everything with $(CC) (default gcc)
#   make run        build + run every benchmark
#   make ct         run the valgrind constant-time audit
#   make CC=clang run
#   make gcm-sweep  AES-GCM across message sizes

DIST    := $(abspath ..)/dist
CC      ?= gcc
VG      ?= valgrind

INC := -I. -Isrc \
       -I$(DIST)/gcc-compatible \
       -I$(DIST)/gcc-compatible/internal \
       -I$(DIST)/karamel/include \
       -I$(DIST)/karamel/krmllib/dist/minimal

CFLAGS  ?= -O3 -march=native
CFLAGS  += $(INC) -Wall -Wno-unused-function

G := $(DIST)/gcc-compatible
V := $(DIST)/vale

# EverCrypt_AEAD pulls in the whole Chacha20Poly1305 chain whether you use it
# or not, so all of these have to be linked to resolve the AES-GCM entry point.
EVERCRYPT_SRC := \
  $(G)/EverCrypt_AEAD.c \
  $(G)/EverCrypt_AutoConfig2.c \
  $(G)/EverCrypt_Chacha20Poly1305.c \
  $(G)/Hacl_AEAD_Chacha20Poly1305.c \
  $(G)/Hacl_AEAD_Chacha20Poly1305_Simd128.c \
  $(G)/Hacl_AEAD_Chacha20Poly1305_Simd256.c \
  $(G)/Hacl_Chacha20.c \
  $(G)/Hacl_Chacha20_Vec128.c \
  $(G)/Hacl_Chacha20_Vec256.c \
  $(G)/Hacl_MAC_Poly1305.c \
  $(G)/Hacl_MAC_Poly1305_Simd128.c \
  $(G)/Hacl_MAC_Poly1305_Simd256.c

VALE_ASM := $(wildcard $(V)/*-x86_64-linux.S)

BINS := bin/bench_fmul bin/bench_sha256 bin/bench_aesgcm \
        bin/bench_poly1305 bin/bench_x25519 bin/redtest bin/ct_audit

all: $(BINS)

bin:
	@mkdir -p bin

# ---------------------------------------------------------------- curve25519
# Three separate translation units on purpose. Putting the intrinsics version
# in the same file as Vale's inline asm makes it impossible to attribute
# adcx/adox in the generated .s -- that mistake is documented in README.md.
bin/bench_fmul: bin bench/bench_fmul.c bench/fmul_vale.c bench/fmul_intrin.c bench/fmul_plain.c
	$(CC) $(CFLAGS) -o $@ bench/bench_fmul.c bench/fmul_vale.c bench/fmul_intrin.c bench/fmul_plain.c

# Inspect what the compiler actually emits for the ADX intrinsics.
# Expect 0 adcx and 0 adox from both gcc and clang.
adx-check: bin
	@$(CC) $(CFLAGS) -S -o bin/fmul_intrin.s bench/fmul_intrin.c
	@echo "$(CC): adcx=$$(grep -c adcx bin/fmul_intrin.s) adox=$$(grep -c adox bin/fmul_intrin.s) adc=$$(grep -cw adcq bin/fmul_intrin.s) mulx=$$(grep -c mulx bin/fmul_intrin.s)"

# ------------------------------------------------------------------ sha256
bin/bench_sha256: bin bench/bench_sha256.c src/sha256_ni.c
	$(CC) $(CFLAGS) -o $@ bench/bench_sha256.c src/sha256_ni.c \
	  $(G)/Hacl_Hash_SHA2.c $(V)/sha256-x86_64-linux.S

# ------------------------------------------------------------------ aes-gcm
bin/bench_aesgcm: bin bench/bench_aesgcm.c src/aesgcm_x86_intrin.c
	$(CC) $(CFLAGS) -o $@ bench/bench_aesgcm.c src/aesgcm_x86_intrin.c \
	  $(EVERCRYPT_SRC) $(VALE_ASM)

gcm-sweep: bin src/aesgcm_x86_intrin.c bench/bench_aesgcm.c
	@for n in 256 1024 1420 4096 16384; do \
	  $(CC) $(CFLAGS) -DLEN=$$n -o bin/gcm_$$n bench/bench_aesgcm.c \
	    src/aesgcm_x86_intrin.c $(EVERCRYPT_SRC) $(VALE_ASM) && ./bin/gcm_$$n; \
	done

# ---------------------------------------------------------------- poly1305
bin/bench_poly1305: bin bench/bench_poly1305.c
	$(CC) $(CFLAGS) -o $@ bench/bench_poly1305.c $(EVERCRYPT_SRC) $(G)/EverCrypt_Poly1305.c $(VALE_ASM)

# ----------------------------------------------------------------- x25519
bin/bench_x25519: bin bench/bench_x25519.c
	$(CC) $(CFLAGS) -o $@ bench/bench_x25519.c \
	  $(G)/Hacl_Curve25519_51.c $(G)/Hacl_Curve25519_64.c $(VALE_ASM)

# Unit test for the 2-clmul GHASH reduction that did NOT work out.
bin/redtest: bin bench/redtest.c
	$(CC) $(CFLAGS) -o $@ bench/redtest.c

# ------------------------------------------------------------- ct audit
# -O1: enough optimisation to be representative, low enough that valgrind can
# still attribute errors to source lines.
bin/ct_audit: bin ct/ct_audit.c src/sha256_ni.c src/aesgcm_x86_intrin.c bench/fmul_plain.c
	$(CC) -O1 -g -march=native $(INC) -o $@ ct/ct_audit.c src/sha256_ni.c \
	  src/aesgcm_x86_intrin.c bench/fmul_plain.c \
	  $(G)/Hacl_Curve25519_51.c $(G)/Hacl_Ed25519.c $(G)/Hacl_Hash_SHA2.c \
	  $(EVERCRYPT_SRC) $(VALE_ASM)

CT_TARGETS := knownbad_fmul sha256purec poly1305simd256 curve25519_51 ed25519 \
              gcm_intrin gcm_vale

# knownbad_fmul MUST report an error. If it does not, the harness is broken
# and every other result here is worthless.
ct: bin/ct_audit
	@for t in $(CT_TARGETS); do \
	  printf '%-18s ' $$t; \
	  out=$$($(VG) -q --error-exitcode=9 ./bin/ct_audit $$t 2>&1); rc=$$?; \
	  if echo "$$out" | grep -q "$$t done"; then done_=yes; else done_=NO-ABORTED; fi; \
	  errs=$$(echo "$$out" | grep -c "Conditional jump\|uninitialised value"); \
	  echo "exit=$$rc completed=$$done_ leak-reports=$$errs"; \
	done
	@echo
	@echo "Expected: knownbad_fmul exit=9 with leak-reports>0 (positive control);"
	@echo "          every other target exit=0, completed=yes, leak-reports=0."
	@echo "sha256ni is omitted: valgrind cannot execute sha256rnds2. Audited"
	@echo "statically instead -- see README.md."

run: $(BINS)
	@for b in bin/bench_fmul bin/bench_sha256 bin/bench_poly1305 \
	          bin/bench_x25519 bin/bench_aesgcm; do \
	  echo "=== $$b ($(CC)) ==="; ./$$b; echo; \
	done

clean:
	rm -rf bin

.PHONY: all run ct clean adx-check gcm-sweep

# LTO variant. Cross-TU inlining of aesgcm128_encrypt is worth ~15% here.
# Verified NOT to be an artifact of constant-folding the key schedule or the
# message length: the ratio is unchanged when both are made opaque via
# volatile. See README.md.
gcm-sweep-lto: bin
	@for n in 256 1024 1420 4096 16384; do \
	  $(CC) $(CFLAGS) -flto -DLEN=$$n -o bin/gcmlto_$$n bench/bench_aesgcm.c \
	    src/aesgcm_x86_intrin.c $(EVERCRYPT_SRC) $(G)/EverCrypt_Poly1305.c \
	    $(VALE_ASM) && ./bin/gcmlto_$$n; \
	done

.PHONY: gcm-sweep-lto
