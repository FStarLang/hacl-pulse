# Replacing Vale-generated assembly with C

An empirical evaluation of whether `dist/vale/*.S` can be replaced by C —
with intrinsics, or plain — at comparable performance.

Every number below was measured on the machine described under
[Test environment](#test-environment), and every C implementation was
validated bit-for-bit against the Vale output it replaces before being timed.
Reproduce with `make run`.

---

## Summary

| Primitive | Best C replacement | vs Vale | Recommendation |
|---|---|---|---|
| **Poly1305** | `Hacl_MAC_Poly1305_Simd256` (already in tree) | **0.99×** | **Delete the Vale path now.** No work required. |
| **SHA-256** | C + SHA-NI intrinsics (`src/sha256_ni.c`) | **1.00×** | **Port.** Exact parity, ~110 lines. |
| **AES-GCM** | C + AES-NI/PCLMULQDQ (`src/aesgcm_x86_intrin.c`) | **0.76–1.15×** | **Port.** Faster than Vale on short messages; within ~10% on long ones, and faster than Vale everywhere under clang+LTO. |
| **Curve25519** | plain C `Curve25519_51` (already in tree) | 1.34–1.39× | **The only hard case.** See [below](#curve25519-the-only-hard-case). |
| **CPUID** | trivial | n/a | Replaceable with `__get_cpuid`. |

**Three of the four primitives are solved.** Poly1305 needs no work at all —
the AVX2 C already in the tree matches the assembly. SHA-256 and AES-GCM reach
parity or better with a few hundred lines of intrinsics.

Curve25519 is the exception, and the reason is specific and well understood:
**no production C compiler emits `adcx`/`adox`**, so the two-independent-carry-chain
trick that makes Vale's radix-64 field arithmetic fast is unavailable from C.

Note that **Ed25519 does not use Vale at all** — it is already pure C via
`Curve25519_51`/`Bignum25519_51`. Verified by linking `Hacl_Ed25519` with zero
Vale symbols. So the "HACL* Ed25519 is fast because of Vale" framing is not
right; its speed comes from the C implementation. X25519 (`Curve25519_64`) is
the primitive that actually depends on Vale.

---

## Results

### Poly1305 — already solved, delete the Vale path

```
tags match: vale==C YES, vale==simd128 YES, vale==simd256 YES
                                          gcc      clang
Poly1305 Vale asm (scalar mul/adc)      1.00×      1.00×      0.447 / 0.420 c/B
Poly1305 pure C   (scalar __int128)     3.24×      3.70×
Poly1305 C intrinsics SSE2  (Simd128)   1.95×      1.82×
Poly1305 C intrinsics AVX2  (Simd256)   0.99×      0.99×   <-- already in tree
```

`Hacl_MAC_Poly1305_Simd256.c` ships today and matches the assembly on both
compilers. Vale's Poly1305 is scalar; the C is vectorised. This one is free.

### SHA-256 — exact parity with intrinsics

```
digests match -- Vale==intrinsics: YES   Vale==pureC: YES
                                          gcc      clang
SHA-256 Vale asm     (SHA-NI)           1.00×      1.00×      1.24 / 1.23 c/B
SHA-256 C intrinsics (SHA-NI)           1.00×      1.01×
SHA-256 HACL* pure C (scalar)           5.98×      5.77×
```

Unsurprising once you look at what the assembly does: SHA-256 on SHA-NI is a
serial dependency chain through `sha256rnds2`. There is no scheduling freedom
to exploit, so hand-written assembly has nothing to win. The intrinsics
version (`src/sha256_ni.c`, ~110 lines) compiles to essentially the same
instruction sequence.

Note the 5.8–6.0× penalty for dropping to portable C — **the intrinsics are
doing all the work here, not the assembly.** This is the general shape of the
result: what matters is access to the instruction, not who schedules it.

### AES-GCM — C beats the assembly

`src/aesgcm_x86_intrin.c`, validated against `EverCrypt_AEAD_encrypt`
(ciphertext *and* tag) at every size.

Ratio vs Vale (lower is better):

| message bytes | 256 | 1024 | 1420 | 4096 | 16384 |
|---|---|---|---|---|---|
| clang, `-flto` | **0.76×** | **0.91×** | **0.88×** | **0.90×** | **0.95×** |
| clang, no LTO | **0.82×** | 1.01× | 1.07× | 1.10× | 1.11× |
| gcc, `-flto` | **0.78×** | 1.01× | 1.07× | 1.10× | 1.15× |
| gcc, no LTO | **0.77×** | 1.00× | 1.08× | 1.10× | 1.15× |

Two things got this from an initial 1.30× to competitive:

1. **Karatsuba GHASH** (1.24× → 0.96×). Three `pclmulqdq` per block instead of
   four. The aggregated loop is `pclmulqdq`-throughput-bound, not AES-bound, so
   removing 25% of the multiplies is close to a 25% win on the GHASH half.
   Products are accumulated unreduced across the whole aggregation group and
   reduced once, which is valid because carry-less multiply-then-reduce is
   linear over GF(2).

2. **Hoisting the key schedule and H-powers into a context.** This was
   originally a *benchmarking* bug on my side, not an optimisation: I was
   recomputing the AES key expansion and eight GHASH key powers on every call
   while EverCrypt keeps them in `EverCrypt_AEAD_state_s`. Fixing the
   comparison to be fair moved it 0.96× → 0.93×.

**On the LTO row.** Cross-TU inlining of `aesgcm128_encrypt` is worth ~15% under
clang. I checked that this is not a benchmark artifact: the ratio is unchanged
(0.93×→0.94×) when the message length is made opaque with `volatile`, and
unchanged when the key is made opaque so the key schedule cannot be
constant-folded. It is genuine — but it does mean the number you get depends on
how the library is built. `make gcm-sweep` and `make gcm-sweep-lto` show both.

The C version wins decisively on **short messages** (0.76–0.82× at 256 bytes),
which is the case that actually matters for TLS record traffic. Vale's fixed
prologue/epilogue cost dominates there.

### Curve25519 — the only hard case

```
outputs identical: YES
                                                       gcc      clang
X25519 pure C   (Curve25519_51, radix-51 __int128)   1.34×      1.39×
X25519 Vale asm (Curve25519_64, mulx/adcx/adox)      1.00×      1.00×   ~73k cycles/op
```

Field multiply in isolation (`make bench_fmul`, three separate translation
units, dependent chain, barriers):

| | gcc | clang |
|---|---|---|
| Vale inline asm | ~33 cyc (1.00×) | ~33 cyc (1.00×) |
| `_addcarryx_u64` intrinsics | 57 (1.73–1.76×) | **36.7 (1.12×)** |
| Plain C `__int128` | 51 (1.54–1.57×) | **38.5 (1.18×)** |

(Ranges are across repeated runs. This benchmark is the most contention-
sensitive of the set — a run competing with a compile showed 1.99× — so treat
single readings on a shared machine with suspicion.)

---

## Why the ADX intrinsics don't help: `make adx-check`

```
clang: adcx=0 adox=0 adc=34 mulx=20
gcc:   adcx=0 adox=0 adc=36 mulx=21
```

**Neither compiler emits a single `adcx` or `adox`** from `_addcarryx_u64`.
Both collapse the two independent carry chains into one chain of plain `adc`,
which is precisely the serialisation ADX exists to avoid.

The root cause is structural, not a missing optimisation: `EFLAGS` cannot be
kept live across basic blocks before register allocation, so a compiler cannot
maintain two separate carry flags (CF and OF) across a loop. GCC PR 79173 has
been open since 2017 (still ASSIGNED); the maintainer's position is explicit —
*"they all generate add/adc. There is no use case to maintain two interleaved
carry chains."* LLVM has #33640, #40891 and #74493, and a 2024
`X86CarryChainLoops` RFC that remains unmerged. MSVC emits `adcx` but has **no
`adox` intrinsic at all**. As far as I can establish, no production compiler
has ever emitted `ADCX`/`ADOX` from portable source.

> **Methodology correction, recorded because it changes the conclusion.** My
> first measurement appeared to show clang emitting 132 `adcx` and 126 `adox`.
> That was wrong: I was counting Vale's *inline-asm text*, which sits in the
> same `.s` file. `bench/fmul_intrin.c` is deliberately a separate translation
> unit containing no inline assembly anywhere, which is what makes the
> `adx-check` count meaningful. **Always isolate the TU when counting codegen.**

The interesting part is what happens anyway: **clang still reaches 1.12× with
nothing but plain `adc`.** On Zen 2 the field multiply is bound by `mulx`
latency, not by carry-chain serialisation, so ADX buys much less than its
reputation suggests. The ~1.75× gcc figure is a *gcc* code-generation penalty,
not a fundamental cost of writing this in C. That distinction matters: it means
the gap is a compiler-quality problem that can improve, not an inherent limit.

---

## Constant-time analysis

Short answer to the question "do any of the best-C functions branch on
secrets?": **no.** None of the recommended implementations has a
secret-dependent branch or a secret-dependent memory address.

`make ct` runs a ctgrind-style audit: secrets are marked undefined for valgrind
memcheck, which then reports any conditional branch or address derived from
them.

```
knownbad_fmul      exit=9 completed=yes leak-reports=1   <-- positive control
sha256purec        exit=0 completed=yes leak-reports=0
poly1305simd256    exit=0 completed=yes leak-reports=0
curve25519_51      exit=0 completed=yes leak-reports=0
ed25519            exit=0 completed=yes leak-reports=0
gcm_intrin         exit=0 completed=yes leak-reports=0
gcm_vale           exit=0 completed=yes leak-reports=0
```

Identical under gcc and clang.

Two methodological points, both of which caught real problems here and are
enforced by the `ct` target:

1. **Always run a positive control.** `knownbad_fmul` is a deliberately leaky
   plain-C field multiply (`bench/fmul_plain.c`, the `carry`-conditioned
   normalisation loop). Valgrind pinpoints it correctly. Without a control
   firing, "0 errors" only tells you the harness ran.

2. **Always confirm the target actually completed.** valgrind 3.26 does not
   implement `sha256rnds2`, so the SHA-NI target SIGILLs — and an aborted run
   is otherwise indistinguishable from a clean one. An earlier version of this
   harness silently reported three targets as clean when its own completion
   check was broken.

`sha256_ni` was therefore audited by disassembly instead: 2 conditional jumps,
both `test %rdx,%rdx` on the public block count, 0 `cmov`, and the K-table is
read at fixed RIP-relative offsets, never indexed by message data.

Other observations:

- `Curve25519_51`'s ladder compiles to 2 conditional jumps under gcc (loop
  counter, stack canary) and 1 under clang (loop counter). The mask-based
  `cswap2` in `internal/Hacl_Bignum25519_51.h:659` survives both compilers
  without being turned into a branch.
- **Ed25519 is constant-time.** `precomp_get_consttime`
  (`dist/gcc-compatible/Hacl_Ed25519.c:1288`) reads all 16 table entries and
  mask-selects with `FStar_UInt64_eq_mask` rather than indexing by a secret.
- There is no `memcmp` on secret data anywhere in the generated C.

**One real gap to close before porting AES-GCM.** The decrypt-side tag
comparison currently lives *inside* the Vale assembly
(`EverCrypt_AEAD.c:~1288`, `uint64_t r = c;` from `gcm128_decrypt_opt`). A C
port must reimplement it as a constant-time comparison — the
`FStar_UInt8_eq_mask` idiom already used in `Hacl_RSAPSS.c` is the right
pattern. This is easy to get wrong and easy to miss, since the encrypt-only
prototype here never exercises it.

**Caveats.** Memcheck tracks value dependence, not time: it cannot see
variable-latency instructions (none of these use any). And the result is a
property of one compiler at one optimisation level — a compiler is free to
introduce a branch on a value that was branchless in source. That argues for
running this audit **in CI**, not once. But note that this exposure is not new:
Ed25519, Curve25519_51 and Poly1305 are already pure C in the shipped tree, so
constant-time behaviour already depends on the compiler today.

---

## What this means for a migration

**Do now, no cost:** delete the Vale Poly1305 path. `Simd256` already matches
it. This is pure win.

**Port to intrinsics:** SHA-256 (parity) and AES-GCM (faster on short
messages, within 10% on long ones, faster everywhere under clang+LTO). Together
these are ~85% of the volume of `dist/vale/` — the AES-GCM assembly alone is
196–208 KB per platform, times four platforms.

**Curve25519 is the decision point.** Two options:

1. **Accept `Curve25519_51`** — pure C, already in the tree, already
   constant-time, 1.34–1.39× slower on X25519. Zero new code. Note this affects
   X25519 only; Ed25519 already uses this path.

2. **Write radix-64 field arithmetic in Low\* over `Lib.IntTypes.Intrinsics`**,
   which should land near clang's 1.12×.

Option 2 deserves emphasis because it **satisfies the constraint that the
result must be generated, not vendored**. The mechanism already exists and is
already used:

- `lib/Lib.IntTypes.Intrinsics.fsti` is a verified Low\* interface for
  add-with-carry / sub-with-borrow.
- `lib/c/lib_intrinsics.h:20-75` maps `Lib_IntTypes_Intrinsics_add_carry_u64`
  to `_addcarry_u64` when `HACL_CAN_COMPILE_INTRINSICS` is set, and falls back
  to `__int128` otherwise.
- `Hacl_Bignum*.c` already extracts through it.

So this is not a new mechanism to invent — it is an existing, verified path
that produces C with intrinsics from F\*. That is exactly the property Vale
loses when it stops being maintainable.

**A structural argument that favours C independently of these numbers:** this
machine has no VAES or VPCLMULQDQ, so both Vale and my code are capped at
128-bit AES. On a CPU that has them, the C version gets wider codegen from the
compiler, whereas the assembly would need a new hand-written path. Over time
the C tracks new hardware and the assembly does not. (Asserted from the
structure of the problem — not measured here, as this CPU cannot.)

---

## Honest limitations

- **One machine, one microarchitecture** (Zen 2). No Intel measurements. The
  ADX result in particular could differ on Intel, where `adcx`/`adox` have
  different port behaviour and the carry chain may matter more than it does
  here.
- **No VAES / VPCLMULQDQ / AVX-512** available to test.
- **gcc trails clang by 10–20% on carry-heavy code**, and gcc gets no LTO
  benefit on AES-GCM. If consumers build with gcc, the AES-GCM and Curve25519
  numbers are the worse ones. This is a real decision input, not a footnote.
- **The AES-GCM prototype is encrypt-only, AES-128, 96-bit IV.** EverCrypt
  handles general IVs, decryption, and AES-256. Some of the short-message
  advantage may be reduced generality rather than better code.
- Benchmarks report the **minimum** of repeated runs, which is the right
  estimator for comparing code but understates real-world variance.

### One optimisation that did not work

A 2-`pclmulqdq` Montgomery GHASH reduction should be cheaper than the
shift-based one in `src/aesgcm_x86_intrin.c`. My transcription of it did not
validate. `bench/redtest.c` unit-tests all four immediate encodings against the
known-good reduction:

```
imm1=0x01 imm2=0x01 -> mismatches=5000
imm1=0x01 imm2=0x10 -> mismatches=5000
imm1=0x10 imm2=0x01 -> mismatches=5000
imm1=0x10 imm2=0x10 -> mismatches=5000
```

5000/5000 on every combination means the problem is a structural mismatch in
the expected operand convention, not a wrong immediate. Recorded so the next
person doesn't burn time re-deriving the same dead end by guessing immediates.
The payoff is small in any case — one reduction per 8 blocks.

---

## Layout

```
src/aesgcm_x86_intrin.{c,h}   AES-128-GCM, AES-NI + PCLMULQDQ + Karatsuba
src/sha256_ni.{c,h}           SHA-256 via SHA-NI intrinsics
bench/bench_fmul.c            curve25519 fmul: Vale vs intrinsics vs plain C
bench/fmul_vale.c             Vale inline asm (from dist/vale/curve25519-inline.h)
bench/fmul_intrin.c           _addcarryx_u64 version -- isolated TU, no asm
bench/fmul_plain.c            plain __int128 -- also the CT positive control
bench/bench_sha256.c          SHA-256 three ways
bench/bench_aesgcm.c          AES-GCM vs EverCrypt, -DLEN to sweep
bench/bench_poly1305.c        Poly1305 four ways
bench/bench_x25519.c          end-to-end X25519
bench/redtest.c               the GHASH reduction that didn't work
ct/ct_audit.c                 ctgrind-style constant-time harness
config.h                      stub normally produced by ./configure
```

### Building

```sh
make run                # all benchmarks, gcc
make CC=clang run       # all benchmarks, clang
make ct                 # constant-time audit (needs valgrind)
make adx-check          # count adcx/adox the compiler emits
make gcm-sweep          # AES-GCM across message sizes
make gcm-sweep-lto      # ... with -flto
```

Links directly against `../dist`, so no HACL* build is needed. `config.h` here
is a stub standing in for the one `./configure` generates.

### Test environment

- AMD EPYC 7662 (Zen 2); `adx bmi2 sha_ni aes pclmulqdq avx2`; no `vaes`, no
  `vpclmulqdq`, no AVX-512
- gcc 15.2.0, clang 21.1.8, valgrind 3.26.0
- `-O3 -march=native`
- Cycle counts via `rdtsc`, minimum of 7 runs

Benchmark loops need `__asm__ volatile("":::"memory")`: without it clang hoists
the SHA-256 loop entirely and reports 0.00 c/B.

## Status

This is **evaluation code, not production code**. It exists to answer a
feasibility question. The implementations here are prototypes: unverified,
narrower than the EverCrypt API, and x86-64/Linux only. A real migration would
write them in Low\* and verify them, not adopt these files.
