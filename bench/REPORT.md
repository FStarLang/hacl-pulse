# hacl-pulse vs. HACL\* — C benchmark

**Machine** AMD EPYC 7662 (Zen 2), pinned to one core, gcc 15.2.0, `-std=c11 -O3`.
**hacl-pulse** `dist/Hacl.c` at HEAD + `c/Hacl_Vec128.h`.
**HACL\*** `dist/gcc-compatible` @ 504c298 (2026-04-10), built with its own
`config.h` (Vale asm, inline asm, uint128 enabled), Vale `.S` linked in.

Method: one driver compiled twice against a per-library shim, so both sides run
identical loops and timing code. Each measurement auto-scales to ~50 ms, best of
5 rounds, three alternating whole-program runs, per-benchmark minimum.
Public-key/RSA/FFDHE entries use each library's *byte-level* API on both sides,
so key loading is inside the unit on both.

`ratio` = pulse / HACL\*; below 1.00 means hacl-pulse is faster.

## Where hacl-pulse wins

| benchmark | size | pulse | HACL\* | ratio |
|---|---|---|---|---|
| sha2-256 | 256 KiB | 1156 MB/s | 235 MB/s | **0.20** |
| sha2-512 | 256 KiB | 335 MB/s | 195 MB/s | **0.58** |
| hmac-sha2-512 | 256 KiB | 333 MB/s | 189 MB/s | **0.57** |
| chacha20 | 256 KiB | 522 MB/s | 303 MB/s | **0.58** |
| chacha20poly1305 enc | 256 KiB | 318 MB/s | 244 MB/s | **0.77** |
| chacha20poly1305 dec | 16 KiB | 317 MB/s | 246 MB/s | **0.78** |

SHA-256 is the standout: 5x. HACL\*'s scalar SHA-2 is a known weak spot (it is
normally multiplexed to SHA-EXT/AVX2 through EverCrypt, which is not in this
comparison), but hacl-pulse's 1.1 GB/s is genuinely good scalar code.

## Roughly at parity (1.0–1.9x)

sha1 1.02, md5 1.37, blake2s 1.51, blake2b 1.84, poly1305 1.38, salsa20 1.21,
nacl-secretbox 1.26, hmac-sha2-256 1.04, hkdf 1.4, streaming sha2-256 1.3,
hmac-drbg 1.35.

## Where hacl-pulse loses badly

| benchmark | pulse | HACL\* | ratio |
|---|---|---|---|
| sha3-256 / shake128 / sha3-512 | 21 / 26 / 11 MB/s | 142 / 174 / 75 MB/s | **5.6–6.7** (12.6 at 64 B) |
| aes128-gcm enc, 256 KiB | 295 MB/s | 3713 MB/s | **12.6** |
| aes256-gcm enc, 256 KiB | 271 MB/s | 3440 MB/s | **12.7** |
| x25519 scalarmult | 471 µs | 44.8 µs (36.9 µs asm) | **10.5** (12.8) |
| ed25519 sign / verify | 1.74 / 1.80 ms | 64.6 / 74.8 µs | **26.9 / 24.0** |
| p256 ecdsa sign / verify | 3.10 / 5.96 ms | 171 / 433 µs | **18.1 / 13.8** |
| k256 ecdsa sign / verify | 2.58 / 4.85 ms | 66.9 / 91.1 µs | **38.7 / 53.2** |
| rsapss-2048 sign / verify | 31.1 / 0.96 ms | 4.77 / 0.146 ms | **6.5 / 6.6** |
| ffdhe2048 | 31.1 ms | 4.71 ms | **6.6** |
| bn2048 modexp (ct) | 30.2 ms | 13.1 ms (32-bit limbs) / 4.59 ms (64-bit) | **2.3 / 6.6** |

## Three causes explain almost all of the losses

1. **No wide multiply in the secret-integer layer.** `Hacl.Secret.UInt64.fsti`
   exposes `mul_mod` (low 64 bits) and no 64x64 -> 128 primitive, and there is no
   `uint128` in the generated C (`grep -c 'unsigned __int128' dist/Hacl.c` = 0).
   So `Hacl.Curve25519.Field` works in **16-bit limbs** (16 limbs, 31 schoolbook
   columns) where HACL\* uses 5x51-bit limbs with `mul_wide`; `Hacl.Bignum` is on
   **32-bit limbs** where HACL\* is on 64. That is the whole story for
   Curve25519/Ed25519/P-256/K-256 (10-50x) and most of RSA/FFDHE/bignum (6.6x;
   2.3x of it survives even against HACL\*'s own 32-bit-limb bignum).
2. **Keccak is memory-resident and index-computed.** In
   `Hacl_Hash_SHA3_Core_*`, theta/rho-pi/chi are `while` loops over the 25-word
   state array with runtime `% 5` and `/ 5` index arithmetic and rotation counts
   read from `rotc_tbl`, i.e. variable-count rotates. HACL\* unrolls with
   constant rotations and keeps lanes in registers. 5.6-6.7x, and 12.6x on short
   inputs where the fixed per-permutation cost dominates.
3. **AES-GCM uses AES-NI one block at a time.** `Hacl_AES_GF128_NI_gmul_ni` does
   4 `pclmulqdq` plus *two* further clmul reduction passes per 16-byte block,
   and `Hacl_AES_Block_cipher_impl__Mkparams` re-tests `Hacl_Vec128_supported()`
   per block. Vale aggregates GHASH over 6 blocks and interleaves it with the
   AES rounds. 12.6x. (Note this is verified-C vs. verified-assembly.)

Smaller, shared contributors: hacl-pulse's per-call fixed cost is higher at 64
bytes across the board (e.g. md5 1.41x at 64 B vs 1.37x at 256 KiB, sha3 12.6x
vs 6.7x), and the `Hacl_Secret_*` wrappers are real `static` functions that gcc
inlines but does not always fold as well as HACL\*'s macros.

## Context: what HACL\* actually ships

The table above is scalar C vs. scalar C, which is the fair comparison for a
single portable translation unit. HACL\*'s default build multiplexes to
vectorized and assembly code, which widens some gaps further (256 KiB, same
machine):

| | pulse | HACL\* scalar | HACL\* AVX2 |
|---|---|---|---|
| chacha20 | 522 MB/s | 303 | 2777 |
| poly1305 | 913 MB/s | 1259 | 4487 |
| chacha20poly1305 | 318 MB/s | 244 | 1744 |
| blake2b | 454 MB/s | 834 | 592 (AVX2 is a regression here) |

hacl-pulse already has the AES-NI/PCLMUL escape hatch, so the same door is open
for the rest.

## Reproducing

Artifacts are in the session workspace under `files/bench/`: `bench.c` (driver),
`shim_pulse.h` / `shim_ref.h` (the two bindings), `bench_vec.c`, `cmp2.py`
(comparison), the raw CSVs, and `table.txt` (the full 98-row table).


---

# Part 2 — clang

**clang 21.1.8**, same machine/core/method. Three configurations, all four
binaries re-run interleaved in the same session so every number below is
directly comparable:

| tag | flags |
|---|---|
| `gcc` | gcc 15.2.0 `-std=c11 -O3` |
| `clang` | clang 21.1.8 `-std=c11 -O3` |
| `clangU` | clang 21.1.8 `-std=c11 -O3 -mllvm -unroll-threshold=1000` |

Both libraries are built with the identical flags in each configuration.
Full data: `table6.txt` (all three configs side by side), `tablebest.txt`
(each side's best configuration per benchmark), `table4.txt` (gcc vs clang).

## Headline: the compiler moves these numbers more than the source does

Neither library is "the fast one" independent of the toolchain. Ratios move by
3x in both directions purely on compiler choice.

| benchmark (256 KiB) | gcc ratio | clang ratio | clangU ratio |
|---|---|---|---|
| sha2-256 | **0.21** | 0.62 | 0.40 |
| sha2-512 | **0.58** | 1.25 | 1.25 |
| hmac-sha2-512 | **0.57** | 1.25 | 1.22 |
| chacha20 | **0.58** | 1.24 | 1.07 |
| chacha20poly1305 | **0.77** | 1.29 | 1.19 |
| salsa20 | 1.21 | **0.90** | **0.89** |
| sha1 | 1.02 | 1.06 | **0.85** |
| sha3-256 | 6.80 | 7.62 | **1.32** |
| shake128 | 6.67 | 7.60 | **1.32** |
| p256-ecdsa-sign | **18.20** | 50.72 | 50.02 |
| x25519 | 10.46 | **7.13** | **7.00** |
| ed25519-sign | 26.98 | **17.59** | 17.27 |

## The big one: SHA-3 was never an algorithmic problem

`-mllvm -unroll-threshold=1000` takes hacl-pulse's Keccak from **6.7–7.6x
slower to 1.32x**: sha3-256 at 256 KiB goes 8.20 ms -> 1.43 ms (183 MB/s),
shake128 6.60 ms -> 1.15 ms. This confirms cause (2) from Part 1: the loops in
`Hacl_Hash_SHA3_Core_*` are small and fully-bounded (`while (i < 25)`), and once
LLVM unrolls them the `% 5` / `/ 5` index arithmetic and the `rotc_tbl` lookups
all fold to constants and the state lands in registers. **gcc will not do this
at any `-funroll-loops` / `--param max-unrolled-insns` setting I tried** (it
stays at ~750 µs for 16 KiB).

That is a concrete, cheap fix: either ship the unroll pragma/attribute on those
loops, or unroll them in the Pulse source. It closes the single largest
non-arithmetic gap in the library.

## The other big one: hacl-pulse's SHA-256 win is gcc-only

gcc gives hacl-pulse 1156 MB/s on SHA-256. Plain clang gives 393 MB/s — a **2.9x
regression from changing compiler alone**, while HACL\*'s SHA-256 is flat
(±2%) across all three. `clangU` recovers it to 610 MB/s. So the 5x headline
from Part 1 is really "gcc unrolls hacl-pulse's SHA-2 compression function and
clang does not". Best-of-both-compilers, the honest SHA-256 number is still a
**4.7x win** (227 µs vs 1070 µs), but the source is fragile in a way HACL\*'s
is not.

## HACL\* is the more compiler-sensitive one elsewhere

clang speeds HACL\* up a lot on: sha2-512 **1.9x**, hmac-sha2-512 **1.9x**,
chacha20 **1.8x**, chacha20poly1305 **1.6x**, and p256 **2.8x** (p256-ecdsa-sign
168 µs -> 67 µs). Every one of hacl-pulse's Part-1 wins outside SHA-256
disappears as a result.

clang slows HACL\* down on: salsa20 **1.4x** (so hacl-pulse now wins there),
nacl-secretbox 1.26x, ed25519 1.3x, x25519\_51 1.2x.

## Compiler-insensitive (±2%, all three configs)

AES-GCM (both sides are intrinsics/assembly), RSA-PSS, FFDHE, bn2048-modexp,
K-256, MD5, BLAKE2b/2s. The 6.2–6.7x RSA/FFDHE gap and the 12.6x AES-GCM gap are
properties of the code, not the toolchain — consistent with Part 1's diagnosis
(limb width; per-block GHASH).

## Best-of-both-compilers summary

Each side allowed its best of the three configurations, 256 KiB where bulk:

| | pulse | HACL\* | ratio |
|---|---|---|---|
| sha2-256 | 227 µs (gcc) | 1070 µs (clangU) | **0.21** |
| sha1 | 804 µs (clangU) | 925 µs (clang) | **0.87** |
| sha2-512 | 773 µs (gcc) | 700 µs (clang) | 1.10 |
| chacha20 | 494 µs (gcc) | 468 µs (clang) | 1.05 |
| chacha20poly1305 | 808 µs (clangU) | 679 µs (clang) | 1.19 |
| salsa20 | 529 µs (gcc) | 438 µs (gcc) | 1.21 |
| sha3-256 | 1.43 ms (clangU) | 1.08 ms (clang) | 1.33 |
| poly1305 | 283 µs (gcc) | 202 µs (clangU) | 1.40 |
| blake2b | 578 µs (gcc) | 310 µs (gcc) | 1.86 |
| aes128-gcm | 875 µs (gcc) | 69.5 µs (clangU) | 12.6 |
| x25519 | 376 µs (clangU) | 44.1 µs (gcc) | 8.5 |
| ed25519 sign | 1.43 ms (clangU) | 63.7 µs (gcc) | 22.4 |
| p256 ecdsa sign | 3.06 ms (gcc) | 67.4 µs (clangU) | **45.5** |
| k256 ecdsa verify | 4.80 ms (gcc) | 90.4 µs (gcc) | 53.1 |
| rsapss-2048 sign | 29.1 ms (clangU) | 4.69 ms (gcc) | 6.2 |

P-256 is now the single worst result in the suite at 45–57x, having been 8–19x
under gcc, because HACL\*'s P-256 is the thing clang helps most.

## What this changes about Part 1's conclusions

The three root causes stand, but their weights change:

1. **No wide multiply** — unchanged and compiler-proof. Still the dominant cost
   for every EC and bignum primitive (6x to 57x). This is the one thing worth
   fixing at the design level.
2. **Keccak codegen** — *downgraded from a 6.7x algorithmic gap to a 1.32x gap
   that one unroll setting closes.* Fix in the source, not the design.
3. **Per-block AES-GCM** — unchanged, compiler-proof, 12.6x.

And a new one: **hacl-pulse's scalar hash code depends on gcc's unroller in a
way HACL\*'s does not.** Whatever is done about Keccak should probably be done
for the SHA-2 compression function too, so the library performs the same on
both compilers.

---

# Part 3: after the uint128 fix (root cause #1, bignum half)

Custard's `gebner_custard` branch now emits `unsigned __int128`, so root cause
#1 is fixable. This part reports the first instalment: a secret 128-bit
integer type, a 64-bit machine layer, and the arbitrary-precision bignum
moved from radix 2^32 to radix 2^64. The two 16-bit-limb cores (Curve25519 and
field256/P-256/K-256) are untouched and unchanged in these numbers.

## What was done

- `lib/Hacl.Secret.UInt128.fsti/.fst` — a secret `FStar.UInt128` exposing
  `mul_wide : S64.t -> S64.t -> t` plus add/sub/shift/logic. No `classify`,
  no comparison masks, no 128-bit `mul`/`div`.
- `lib/Hacl.Impl.Limb64.fst` replaces `Hacl.Impl.Limb32.fst`: the same
  `mac`/`sum`/`diff` machine layer one notch wider. Every proof carried over
  unchanged — the `(2^w-1)^2 + 2*(2^w-1) = 2^2w - 1` tightness argument is
  structurally identical at w = 64.
- `Spec.Bignum.rad` 32 -> 64. **Zero lemma bodies changed**: the spec was
  already generic in `rad`.
- `Hacl.Bignum.{Base,Montgomery,Convert,Exponentiation}`, `Hacl.RSAPSS`,
  `Hacl.FFDHE` ported. The RFC 7919 moduli in `Spec.FFDHE` were regenerated as
  64-bit limbs; the RFC test vectors pass, which is the real check on them.
- Montgomery's Hensel lifting needed a sixth Newton step to reach 64 bits.
- `tests/test_bignum.c` and `tests/test_montgomery.c` re-vectored for 64-bit
  limbs.

The whole library verifies, extracts, compiles under
`-std=c11 -O3 -Wall -Wextra -Werror` on gcc and clang, and all 1021 test cases
pass.

The inner loop is now exactly what it should be:

```c
unsigned __int128 t = mul_wide(aj, bi) + (unsigned __int128)rj + (unsigned __int128)vc;
res[pos] = (uint64_t)t;
c = (uint64_t)(t >> 64);
```

## Results

Best-of-3 interleaved runs, `taskset -c 6`, same protocol as Parts 1 and 2.
Times in µs. `ratio` is pulse/HACL\*; `bn2048` is compared against HACL\*'s
own 64-bit-limb bignum, which is the like-for-like target.

### gcc 15.2.0

| benchmark | pulse before | pulse after | speedup | HACL\* | ratio before | ratio after |
|---|---|---|---|---|---|---|
| rsapss-2048-sign | 30 953 | 9 450 | **3.28x** | 4 750 | 6.60x | **1.99x** |
| rsapss-2048-verify | 961 | 524 | 1.83x | 147 | 6.61x | 3.56x |
| ffdhe2048-secret-to-public | 30 912 | 9 481 | **3.26x** | 4 709 | 6.65x | **2.01x** |
| ffdhe2048-shared-secret | 30 526 | 9 488 | **3.22x** | 4 691 | 6.54x | **2.02x** |
| bn2048-modexp-consttime | 30 068 | 9 128 | **3.29x** | 4 611 | 6.62x | **1.98x** |

### clang 21.1.8

| benchmark | pulse before | pulse after | speedup | HACL\* | ratio before | ratio after |
|---|---|---|---|---|---|---|
| rsapss-2048-sign | 29 523 | 9 914 | 2.98x | 4 696 | 6.29x | 2.11x |
| rsapss-2048-verify | 915 | 498 | 1.84x | 139 | 6.65x | 3.59x |
| ffdhe2048-secret-to-public | 29 136 | 9 924 | 2.94x | 4 668 | 6.21x | 2.13x |
| ffdhe2048-shared-secret | 29 412 | 9 860 | 2.98x | 4 668 | 6.32x | 2.11x |
| bn2048-modexp-consttime | 28 644 | 9 575 | 2.99x | 4 621 | 6.25x | 2.07x |

Across the other 93 benchmarks nothing moved by more than 2.3%, which is inside
the noise floor of this machine.

## Why 3.3x and not 4x

Halving the limb count quarters the number of limb-by-limb products in a
schoolbook multiply, so the naive expectation is 4x. The measured 3.3x is the
difference between a 32-bit `mac` (one 32x32->64 multiply, two adds, all in
64-bit registers) and a 64-bit one (one 64x64->128 multiply plus a 128-bit
carry chain, which on Zen 2 is `mulx` + `adc` + `adc`). Per-limb cost rises
about 20%, and 4 / 1.2 = 3.3.

## Why still 2x behind HACL\*

This is **not** root cause #1 any more. Reading the extracted C:

```c
while (i > 0) {
  mont_mul(res, acc, acc, ...);        /* square       */
  mont_mul(t, acc, aM, ...);           /* multiply     */
  cselect(acc, t, nn, get_bit(bb, j)); /* keep one     */
}
```

hacl-pulse does plain binary square-and-multiply: **2 Montgomery
multiplications per exponent bit**, the second thrown away half the time to stay
constant-time. HACL\* uses a 4-bit fixed window with a 16-entry precomputed
table: one squaring per bit plus one table multiply per 4 bits, i.e. **1.25
multiplications per bit**. 2.0 / 1.25 = 1.6x, and the rest is HACL\*'s slightly
leaner `bn_almost_mont_mul` (it skips the final conditional subtraction).

So the remaining RSA/FFDHE gap is an *algorithmic* one in the ladder, fixable
entirely inside `Hacl.Bignum.Exponentiation` with no new machine primitives.

`rsapss-2048-verify` is the outlier at 3.56x because its exponent is 65537:
only 17 ladder steps, so the fixed `precomp` cost of R^2 mod n dominates, and
that is `2*rad*nn` = 4096 Montgomery doublings either way.

## Remaining work on root cause #1

| core | limbs today | clients | current gap |
|---|---|---|---|
| bignum | **2^64 (done)** | RSA-PSS, FFDHE | 2.0x (now a ladder problem) |
| curve25519 | 2^16 | X25519, Ed25519 | 7.0x / 16–22x |
| field256 | 2^16 | P-256, K-256 | 45–57x / 27–56x |

The two field cores are the larger prizes: radix-51 for Curve25519 and 64-bit
limbs for `Spec.Bignum256`. Both now have the `Hacl.Secret.UInt128.mul_wide`
they were waiting on; `Hacl.Impl.Limb`'s own header says the premise was "with
no hundred-and-twenty-eight-bit type there is no room for a radix-2^51
product", and that premise is now false.

---

# Part 4: the 256-bit field core on `unsigned __int128`

Commit `3c26fba`, "Field256 and Curve25519: radix 2^32, on a secret 128-bit
integer". The second half of root cause #1.

## What changed

Both field representations had been chosen so a whole schoolbook column stayed
inside a 64-bit word, because that was the widest integer the extraction could
emit. A column is a sum of `nl` limb products, so with `nl * (2^rad - 1)^2 <
2^64` the only workable point was **sixteen limbs of sixteen bits** -- for the
shared 256-bit Montgomery core (`Spec.Bignum256`, used by P-256, K-256 and, via
`Spec.Curve25519.Field`, by X25519 and Ed25519 too).

With `Hacl.Secret.UInt128` the constraint moves up by sixty-four bits, and the
natural point is **eight limbs of thirty-two bits**:

| quantity | old (`rad = 16`) | new (`rad = 32`) |
|---|---|---|
| limb product | `< 2^32` | `< 2^64` |
| Montgomery column | `< 2^36` | `< 2^69` |
| accumulator ceiling | `2^40` | `2^72` |
| carry into neighbour | `< 2^25` | `< 2^41` |
| limb products per multiply | 256 | **64** |

The whole Montgomery accumulator now lives in `Hacl.Secret.UInt128`, which
forced one genuine design change: `redc_op` used to copy the reduction's top
half into the 64-bit output array and carry there. Columns no longer fit a word,
so the carry pass happens in 128 bits through a fresh nine-column scratch and
narrows on the way out.

Also regenerated: the P-256, K-256 and Ed25519 constant tables as eight
thirty-two-bit literals, and the two Montgomery constants `mu`, which are
`-p^-1 mod 2^rad` and therefore change with the radix.

One proof had to be spelled out that Z3 used to guess. `Spec.Field256`'s
`limbs_n_eval` needs `rad * n == rad + rad * (n - 1)`, which is nonlinear in
`n`. At `rad = 16` Z3 found it; at `rad = 32` the query stopped returning at all,
even at rlimit 400. An explicit `Math.distributivity_add_right` takes it from
over ten minutes to **8.9 seconds**.

## Results

Best-of-3 interleaved runs across all three compiler configurations (`gcc`,
`clang`, `clangU`), `taskset -c 6`, same protocol as Parts 1-3. Times in µs.

| benchmark | pulse before | pulse after | speedup | HACL\* | gap before | gap after |
|---|---|---|---|---|---|---|
| x25519-base | 378 | 251 | **1.51x** | 45 | 8.5x | **5.6x** |
| x25519-scalarmult | 376 | 250 | **1.51x** | 44 | 8.5x | **5.7x** |
| ed25519-keygen | 665 | 429 | **1.55x** | 31 | 21.2x | **13.7x** |
| ed25519-sign-64B | 1 428 | 897 | **1.59x** | 65 | 22.4x | **13.9x** |
| ed25519-verify-64B | 1 450 | 931 | **1.56x** | 74 | 19.7x | **12.5x** |
| p256-dh-initiator | 2 923 | 1 160 | **2.52x** | 56 | 52.0x | **20.8x** |
| p256-dh-responder | 2 922 | 1 161 | **2.52x** | 119 | 24.6x | **9.8x** |
| p256-ecdsa-sign | 3 064 | 1 232 | **2.49x** | 67 | 45.5x | **18.3x** |
| p256-ecdsa-verify | 5 841 | 2 363 | **2.47x** | 145 | 39.8x | **16.3x** |
| k256-secret-to-public | 2 396 | 979 | **2.45x** | 49 | 48.9x | **19.9x** |
| k256-ecdh | 2 404 | 979 | **2.45x** | 91 | 26.7x | **10.8x** |
| k256-ecdsa-sign | 2 545 | 1 045 | **2.43x** | 66 | 38.8x | **15.8x** |
| k256-ecdsa-verify | 4 799 | 1 958 | **2.45x** | 91 | 53.1x | **21.5x** |

Across the other 90 benchmarks nothing moved by more than 2%.

The P-256/K-256 speedup is 2.5x rather than the naive 4x for the same reason as
Part 3: a 64-bit `mac` costs about 20% more per limb than a 32-bit one on
Zen 2, and Montgomery reduction has a serial carry chain that does not shrink
as fast as the product does. X25519 and Ed25519 get only 1.5x because
Curve25519's field was already only moderately multiply-bound; its inversion
and ladder overheads are unchanged.

## An unexpected gcc result

The 2.5x on P-256/K-256 is entirely a **clang** result. Broken out by compiler
(`p256-ecdsa-sign`, µs):

| compiler | before | after | speedup |
|---|---|---|---|
| gcc 15.2.0 | 3 064 | 3 090 | **0.99x** |
| clang 21.1.8 | 3 421 | 1 273 | 2.69x |
| clangU | 3 371 | 1 232 | 2.74x |

gcc gets *nothing*. The generated C is the same, and gcc's inner product loop is
not obviously wrong -- it fully unrolls into straight-line `mulq`/`adcq`, which
is what one wants. The problem is that it unrolls too much: `-O3` completely
peels the eight-iteration Montgomery loops (and the loops around them) into a
block large enough that the 128-bit accumulator spills. Capping the peeler
recovers most of it:

| gcc flags | p256-ecdsa-sign | x25519-base | sha2-256 256 KiB |
|---|---|---|---|
| `-O3` (default) | 3 090 | 242 | 225 |
| `-O3 --param max-completely-peel-times=1` | **1 794** | 307 | 430 |
| `-O3 --param max-completely-peel-times=4` | **1 795** | 302 | 391 |
| `-O3 -fno-peel-loops` | 3 117 | 242 | 225 |

So it is specifically *complete* peeling, and the fix is not free: it costs 27%
on X25519 and 74% on SHA-2. This is a whole-translation-unit flag, which is the
wrong granularity -- the right fix is a `#pragma GCC unroll` (or a
`__attribute__((optimize))`) on the two or three Montgomery loops, i.e. the same
kind of targeted unrolling hint Part 2 already recommended for Keccak, just
pushing in the opposite direction. Both are instances of the same underlying
issue: **the extracted C gives the compiler counted loops with no unrolling
guidance, and the two compilers' default heuristics land in very different
places.**

## Where root cause #1 stands

| core | limbs | clients | gap before | gap now |
|---|---|---|---|---|
| bignum | 2^64 | RSA-PSS, FFDHE | 6.6x | **2.0x** |
| curve25519 | 2^32 | X25519, Ed25519 | 8.5x / 22x | **5.6x / 13.9x** |
| field256 | 2^32 | P-256, K-256 | 45x / 53x | **18x / 21x** |

Root cause #1 as originally stated -- "the extraction cannot emit a 64x64->128
multiply" -- is **fixed**. What is left in the asymmetric primitives is no
longer about integer width:

1. **Curve25519 should be radix 2^51, not 2^32.** Five limbs of 51 bits is what
   HACL\* uses, and it is available now: `5 * (2^51 - 1)^2 < 2^115` fits a
   `__int128` with room for the carry. That is 25 limb products instead of 64,
   and lazy reduction on top. Worth roughly another 2x on X25519.
2. **P-256 and K-256 should use their special prime shapes.** Both are pseudo-
   Mersenne-ish and HACL\* reduces with shifts and adds rather than a general
   Montgomery step. That is the bulk of the remaining 18x.
3. **The exponentiation ladder** (Part 3) is still binary square-and-multiply:
   worth 1.6x on RSA-PSS and FFDHE.
4. **Windowed scalar multiplication.** hacl-pulse's P-256/K-256 point
   multiplication is a double-and-add over 256 bits; HACL\* uses a 4-bit window
   with a precomputed table, and a larger one for the fixed base point. That
   accounts for most of the difference between the 20.8x on `p256-dh-initiator`
   (fixed base) and the 9.8x on `p256-dh-responder` (variable base).

---

# Part 5: Root cause #2 -- unrolling the Keccak permutation

Root cause #2 was Keccak. On a 256 KiB message SHA3-256 took 12.24 ms against
HACL\*'s 1.07 ms, a factor of 11.4, and SHA3-512 was 23.04 ms against 2.02 ms.
Part 2 had already shown this was not an algorithmic gap: rebuilding the *same*
C with `clang -O3 -mllvm -unroll-threshold=1000` took SHA3-256 on 256 KiB from
8.28 ms to 1.43 ms, a 5.7x swing from a compiler flag alone. So the algorithm
was right and the emitted loop structure was wrong.

## Why the lane loops are so expensive

Each of the three sub-steps of a Keccak round -- theta, rho-pi, chi -- was a
`while` loop over the twenty-five lanes of the state. A loop over lanes pays
for three things a straight-line version does not:

1. **Coordinate recovery.** A lane's (x, y) position has to be recovered from
   its index at runtime, so every iteration contains a `div` and a `mod` by 5.
2. **A table load.** The rho rotation offset for the lane is fetched from
   `rotc_tbl`, a load the hardware cannot fold away and which the compiler must
   assume could alias the state.
3. **A variable-count rotate.** This is the worst of the three. `rol %cl, %rax`
   has a serialising dependency on the flags register and costs about three
   instructions' worth of latency, where `rol $44, %rax` is a single uop.

Multiply that by 25 lanes x 3 sub-steps x 24 rounds and the permutation is
mostly bookkeeping. Neither gcc nor clang unrolls these loops at `-O3` by
default -- the trip count is 25, above both compilers' default thresholds.

## The fix: unroll in the source, prove one lane

Rather than hope a compiler discovers the unrolling (and it clearly does not,
unless told to at a granularity that hurts everything else -- see Part 4), the
three sub-steps are unrolled in the Pulse source.

The proof cost is kept to a single lane. Each sub-step gets an
`inline_for_extraction` helper carrying exactly the invariant the `while` loop
carried, indexed by its lane argument:

```
requires ... (forall (k: nat). k < SZ.v i     ==> Seq.index vst  k == Seq.index (theta vst0) k)
ensures  ... (forall (k: nat). k < SZ.v i + 1 ==> Seq.index vst' k == Seq.index (theta vst0) k)
```

The helper is verified once against a symbolic `i` and then applied twenty-five
times to literal ones. Each call site discharges exactly what one loop
iteration used to, the twenty-five calls chain without the solver ever seeing a
nested `Seq.upd`, and the wrapper closes with a `Seq.equal` against the spec.
Custard inlines `inline_for_extraction fn` completely, so what comes out the
other side is straight-line C with literal indices and literal rotation counts.

The twenty-four rounds themselves are deliberately still a loop. Unrolling
those too would be roughly 20 KB of instruction cache for no further gain.

Three things were worth learning along the way:

- **An `ensures` needs its own well-typedness facts.** `Seq.index (theta vst0) k`
  in an `ensures` requires `Seq.length vst0 == 25` stated *in that same ensures*,
  because `theta : state -> state` and `state` is length-refined. Having it in
  the `requires` is not enough.
- **An implicit that occurs only under `pure` cannot be inferred.** `#vst0` had
  to become an explicit `erased` argument; erased arguments extract away anyway.
- **Long straight-line Pulse bodies need intermediate anchors.** `theta_impl`
  has 25 reads, 5 parities, 5 `d` values and 25 lane calls. Without anchors the
  VC ran for six minutes and then failed on a fact that is true by unfolding.
  One `assert (pure (dN == theta_d vst0 N))` after each `let dN` brought the
  whole file to 2m25s.

`rotc` is a twenty-five way `match`, and `Spec.SHA3.Constants` already carried a
comment warning that a Pulse VC cannot case-split on it. A new `rotc_lit`
lemma, modelled on the existing `rotc_ok`, has the conjunction of all
twenty-five ground equalities as its conclusion; calling it once at the top of
`rho_pi_impl` puts them in the context as ground terms.

## A structural bonus

Unrolling theta made it possible to restructure it. It now reads all
twenty-five lanes into locals *before* writing any of them, computes the five
column parities and the five `d` values in registers, and writes back. So the
five-word `c` scratch buffer is gone entirely -- and with it an aliasing
barrier, since the C compiler no longer has to assume a store through `c` might
hit `st`. `rotc_tbl` is gone for the same reason on the rho side. Both were
threaded out of the sponge, the streaming layer and the two top-level modules.

## Results

256 KiB message, gcc -O3, minimum of three interleaved rounds:

| benchmark | before | after | speedup | vs HACL\* before | vs HACL\* after |
|---|---|---|---|---|---|
| sha3-256 | 12.24 ms | 1.13 ms | **10.8x** | 11.4x | **1.05x** |
| sha3-512 | 23.04 ms | 1.95 ms | **11.8x** | 11.3x | **0.97x** |
| shake128 | 9.97 ms | 0.90 ms | **11.1x** | 11.5x | **1.04x** |

At 16 KiB the picture is the same (10.6x, 11.8x, 10.9x). At 1 KiB it is 10.1x,
11.1x, 10.2x. Only the 64-byte case still lags at 2.4x, which is per-call
setup, not the permutation.

SHA3-512 is now **faster than HACL\***, and the other two are within five
percent. This is the first primitive where hacl-pulse has drawn level with
hand-written HACL\* C on a hot loop.

Two further observations:

- **The gain is the same under clang, without the flag.** `clangU` no longer has
  any advantage over plain `clang` on SHA-3, because there is nothing left for
  the raised unroll threshold to unroll. The 5.7x that the flag used to buy is
  now in the source, where it is checked.
- **The object file got 19 KB *smaller*** (448118 -> 429062 bytes of text).
  Removing 25 divisions, 25 remainders and a table lookup per sub-step more than
  pays for writing the lanes out longhand. This is the opposite of what one
  expects from unrolling, and it is a good argument for doing it at the source
  level where the index arithmetic disappears rather than at the IR level where
  it merely gets constant-folded.

## Part 9 -- Curve25519 at radix 2^51

The first item on the list, and the one that had been sitting there since
Part 1. X25519 was 243 microseconds against HACL\*'s 44, and the reason was
entirely the field representation: eight limbs of thirty-two bits, sixty-four
32x32 partial products per `fmul`, where HACL\*'s `_51` does twenty-five
64x64->128.

### What changes, besides the multiply count

The obvious win is 64 products down to 25. The less obvious one is that the
reduction gets simpler. At radix 2^32 the number occupies `8 * 32 == 256`
bits, one more than the field needs, so the top bit has to be folded back
against `2^256 == 2 * prime + 38` and a whole apparatus exists to do it:
`freeze_b`, `red255`, `fold255`, `hi255`, `mask255`, `mask_top`. At radix
2^51 the number occupies `5 * 51 == 255` bits exactly, `2^255 == prime + 19`,
and all of that vanishes. The final reduction is `add19`, one carry pass, and
a select on the carry out. Six lemmas and their implementations deleted.

The bound arithmetic, all `assert_norm`-checked, with a limb bound of
`lim = 2^52 - 1`:

| operation | limb bound in | `d` | bound out |
|---|---|---|---|
| `fadd` | `2*lim` | 4 | `<= lim` |
| `fsub` | `lim + 8*(base-1)` | 10 | `<= lim` |
| `fscale` (m <= 121665) | `2^69` | `2^18 + 2^6` | `<= lim` |
| `fmul` pass 1 | `2^111` | `2^60 + 2^10` | `<= 2^65` |
| `fmul` pass 2 | `2^65` | `2^14 + 2^2` | `<= lim` |
| `freeze` pass 1 | `lim` | 2 | `base + 37` |

`fmul` is 25 `mul_wide`s into nine 128-bit columns, a four-iteration fold of
the top half against 19, two 128-bit carry passes, then a narrow to 64 bits.
No final 64-bit pass at all.

`fscale` is the one operation that needed a new signature. `121665 * lim` is
about `2^69`, past a word, so it takes a nine-element 128-bit scratch array.

### The proof work was all about context, not mathematics

Three separate times the same lesson came back.

**A quantified postcondition assembled from N concrete facts is the standard
timeout.** `load_windows` says "for every `k < 5`, limb `k` is this window of
the 32-bit representation". Written flat -- five lemma calls and an
`assert_norm` -- it does not close. Written as an inner
`aux (k: nat { k < 5 })` that case-splits `k` with `if`/`else if`, plus
`Classical.forall_intro aux`, it closes in seconds. Same facts, same lemmas;
the difference is whether Z3 sees the case split.

**A generic lemma costs far more than N concrete copies.** `store_windows`
originally called one combinator `sw s j j51 off` with a precondition
`32 * j == 51 * j51 + off`. Every one of its eight call sites timed out, even
in an otherwise empty module -- eleven minutes and no progress. Replaced by
eight lemmas `sw0`--`sw7`, each with literal indices and `assert_norm` for the
arithmetic: forty seconds for all eight.

**Moving a hard block into its own module is almost always the fix.** Even
the concrete version would not close inside the 1300-line implementation at
rlimit 300. `Spec.Curve25519.Repack` exists for no other reason than to hold
these eighteen lemmas somewhere with a small ambient context. It verifies in
three and a half minutes; the implementation then verifies in two and a half,
down from a forty-minute failing run.

A smaller one: `assert (pure (rad * nl == 255))` inside a Pulse `fn` can burn
the entire rlimit, where `assert_norm (rad * nl == 255)` is instant.
`assert_norm` works directly in Pulse bodies.

### Two structural consequences in Ed25519

**The scalar had to be untangled from the field.** Ed25519's arithmetic mod
the group order `q` is eight limbs of thirty-two bits, and always was -- but
it had been written against `Hacl.Curve25519.Field`'s names, because the field
happened to use the same radix. Changing the field changed the meaning of
every one of those names. `Hacl.Ed25519.Scalar` now opens `Hacl.Impl.Limb`
and `Spec.Bignum256` and owns `copy`, `load_le`, `store_le`, `limbs_eq`,
`reduce32`; `Hacl.Ed25519` mixes the two deliberately, and the auditing job
was deciding, array by array, which of `8sz` and `5sz` each of about forty
declarations wanted. Three of them -- `SZ.div bi 8sz`, the SHA-512 state, the
scalar temporaries -- are `8` for reasons that have nothing to do with the
field.

**The compressed sign bit moved from the top limb to the top byte.** At radix
2^32, `point_compress` set bit 255 by OR-ing into limb 7, which had room. At
radix 2^51 limb 4 ends exactly at bit 255, so adding `b * 2^51` to it would
push it to `2^52` and break `store`'s precondition. The bit now goes into
byte 31 of the encoded output, after `store`. The justification is pure
arithmetic and turned out to be four lines: `b * 2^255` is a multiple of
`2^(8i+8)` for every `i < 31`, so no other byte moves; and `v / 2^248 < 2^7`
for `v < 2^255`, so byte 31 does not carry.

### Numbers

gcc 15.2.0 `-std=c11 -O3`, Zen 2, `taskset -c 6`, minimum of three rounds,
microseconds per operation:

| benchmark | radix 2^32 | radix 2^51 | gain | vs HACL\* |
|---|---:|---:|---:|---:|
| x25519-scalarmult | 242.9 | **145.3** | 1.67x | 3.27x |
| x25519-base | 243.7 | **143.7** | 1.70x | 3.20x |
| ed25519-keygen | 433.2 | **255.3** | 1.70x | 8.22x |
| ed25519-sign-64B | 890.3 | **541.7** | 1.64x | 8.41x |
| ed25519-verify-64B | 929.5 | **559.0** | 1.66x | 7.46x |

No other benchmark in the suite moves by more than one percent.

With `-march=native` the same change is worth almost exactly 2x -- 124.9
against 242.9 on `x25519-scalarmult` -- because the 128-bit multiply is the
part that benefits from a better instruction selection, and the baseline
32-bit code has nothing to gain. The `-O3` figure is the honest one for the
table, since that is the configuration everything else in this report used.

### What is left in Curve25519 and Ed25519

X25519 at 3.3x and Ed25519 signing at 8.4x are now *different* problems. The
field is the same shape as HACL\*'s, so what remains in X25519 is lazy
reduction across ladder steps and the usual scheduling; but Ed25519 is much
further behind because it multiplies the base point one bit at a time where
HACL\* uses a precomputed window. That is now the largest single gap in the
library and moves to the head of the queue.

## Part 10 -- A straight-line `fmul` for Curve25519

The queue said windowed scalar multiplication for Ed25519 next. Before
committing to that proof, one arithmetic check: 145.3 microseconds over 255
ladder steps is about 57 nanoseconds per `fmul`, and HACL\*'s `_51` does the
same work in about 17. The two ladders have the same shape, so the ratio
should have been near one. It was not, so the field got measured instead of
the algorithm.

A microbenchmark of the two `fmul`s alone, same inputs, identical outputs,
twenty million iterations pinned to one core:

| build | ns/op |
|---|---:|
| HACL\* `Field51_fmul` (a `static inline` in a header) | 12.8 |
| hacl-pulse `Hacl_Curve25519_Field_fmul` | 52.8 |

That is the entire remaining gap in X25519 and most of the one in Ed25519.
Nothing else in a scalar multiplication matters next to 255 field
multiplications.

### Why it was slow

The radix-2^51 port had made every field operation five limbs wide, but it
had left `fmul` shaped the way the *specification* is shaped: nine schoolbook
columns accumulated into a scratch array of 128-bit words, a second pass
folding the top four columns down against nineteen, and then two full 128-bit
carry passes. That is the right structure for the proof -- both halves are
inductions over the limb index, which is what made them provable at all --
and the wrong structure for the machine. Nine 128-bit values live in memory,
the fold is a second traversal, and each carry pass is another.

Three C variants, hand-written and measured outside F*:

| variant | ns/op |
|---|---:|
| A: as extracted | 53.0 |
| B: five columns, 19 folded into `b`, one carry chain, still array-based | 40.2 |
| C: fully straight-line, everything in locals | 24.1 |
| all three, plus HACL\*, under `-flto` | ~12.5 |

So two separable costs: the nine-column-plus-two-passes algorithm, and the
array traffic. `-flto` collapses the difference entirely, which says the
remaining factor of two between C and HACL\* is inlining, not arithmetic.
Patching variant C into `dist/Hacl.c` by hand and rerunning the whole suite
gave a clean 2x end-to-end -- more than windowing's projected 1.5x -- so the
work moved here.

### The design

Two observations make the fast form fit.

**Fold the reduction constant into `b` up front.** Nineteen times a limb is
under `19 * (2^52 - 1) < 2^57`, so it still fits a word. Four scalar
multiplications produce `r_j = 19 * b_j`, and then the nine columns collapse
to five, each a sum of five limb products:

```
c0 = a0*b0 + a1*r4 + a2*r3 + a3*r2 + a4*r1
c1 = a0*b1 + a1*b0 + a2*r4 + a3*r3 + a4*r2
c2 = a0*b2 + a1*b1 + a2*b0 + a3*r4 + a4*r3
c3 = a0*b3 + a1*b2 + a2*b1 + a3*b0 + a4*r4
c4 = a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0
```

Five 128-bit locals, no array. Putting the nineteen in the *right* operand
costs four multiplications in total rather than four shifts per column, and
is exactly HACL\*'s layout.

**Carry in a word.** A column is bounded by `5 * 19 * lim^2`, about
`2^110.57`, so its quotient by `2^51` is under `2^60`. Nineteen times that is
about `1.63e19`, still under `2^64`. So the chain

```
o0 = c0 % base;  k0 = c0 / base
l1 = c1 + k0;  o1 = l1 % base;  k1 = l1 / base
...
l4 = c4 + k3;  o4 = l4 % base;  k4 = l4 / base
t0 = o0 + 19 * k4           (a word)
w0 = t0 % base;  w1 = o1 + t0 / base
```

does in one pass what two 128-bit passes did, and the wrap happens in a
register.

This only closes with the *tight* bound. The old proof rounded the product up
to `2^111` before handing off to the generic carry chain; at that bound
`19 * (2^111 / 2^51) = 19 * 2^60` is about `2.19e19`, past `2^64`, and the
whole scheme fails. So `fmul_spec_ok` now carries `20 * (nl * (lim * lim))`
unrounded the entire way through `carry_pass_shaped`. And `fmul_spec` ends in
`carry_fix` -- a single `carry_step` on limb zero -- rather than a second full
pass, because `carry_pass_shaped` already proves that after one pass every
limb but the lowest is a proper base-2^51 digit.

### The bridge

`Spec.Curve25519.Columns` is a new module whose only job is to connect the two
shapes. `psucc`/`pzero` take one step of the `repeati` that defines `part`;
`p0` to `p8` apply it five times each to give the nine columns as explicit
sums; `m19` moves the nineteen across a product; `col0` to `col4` distribute
`fold19` over them, producing the five columns as five-term sums in exactly
the association the implementation evaluates; and `chain` unfolds
`carry_fix (carry_pass s)` into the straight line of quotients and remainders,
at `--fuel 8 --ifuel 8`. There is no new mathematics in any of it, which is the
point: the fast `fmul` computes the same nine columns as the slow one, folded
the same way.

Two proof-engineering notes. The lemmas are stated with `vat` rather than
`Seq.index`, because `Seq.index (part a b i) k` needs a length precondition
that only `part_len` supplies and a lemma statement cannot depend on its own
body. And the final extensionality step -- five limbs agreeing one by one
means the same sequence -- had to be pulled out into a lemma of its own
(`five_eq`). Inside the Pulse function, with forty-odd equations about
`mulw19` and `col5` in scope, the quantifier that `Seq.equal` unfolds to
would not close in any rlimit; in a two-line lemma it is `Seq.lemma_eq_intro`.
That is the same move as `Spec.Curve25519.Repack` and the ladder body: when a
goal will not close, the problem is usually the context, not the goal.

Everything else in the function verifies at rlimit 40.

### Result

Custard emits ten reads, four scalar multiplications, twenty-five
`mul_wide`s, a chain of shifts and masks, and five writes. The scratch array
argument is gone from `fmul` and from all thirty-odd call sites. gcc `-O3`,
three rounds, per-benchmark minimum:

| benchmark | radix 2^51 | straight-line `fmul` | speedup | HACL\* | ratio |
|---|---:|---:|---:|---:|---:|
| x25519-scalarmult | 145.3 us | **68.2 us** | 2.13x | 44.4 us | 1.54x |
| x25519-base | 143.7 us | **67.9 us** | 2.12x | 44.9 us | 1.51x |
| ed25519-keygen | 255.3 us | **114.7 us** | 2.23x | 31.0 us | 3.69x |
| ed25519-sign-64B | 541.7 us | **263.0 us** | 2.06x | 64.4 us | 4.08x |
| ed25519-verify-64B | 559.0 us | **262.2 us** | 2.13x | 74.9 us | 3.50x |

Nothing else moved by more than a percent. X25519 is now within 1.5x of
HACL\*'s portable C, and on the microbenchmark evidence essentially all of
that residue is inlining: HACL\*'s `fmul` is a `static inline` in a header and
disappears into the ladder body, while Custard emits a `static` function that
gcc declines to inline at this size.

## Part 11 -- `CInline`, and why forcing an inline is worse than asking

Part 10 ended on the observation that the last 1.5x in X25519 looked like
inlining: under `-flto` the pulse and HACL\* `fmul`s are both about 12.5 ns,
without it they are 24 and 12.8. HACL\*'s `_51` field is a set of
`static inline` functions in a header, so each of them disappears into the
ladder body. Custard emits plain `static` functions in one translation unit,
which gcc is free to inline but declines to: `fmul` is forty lines with thirty
call sites.

Three variants of the *generated C*, no F* involved, gcc `-O3`:

| x25519-scalarmult | us |
|---|---:|
| as emitted | 68.2 |
| `__attribute__((always_inline))` on `fmul` | 78.0 |
| `static inline` on `fmul` | 57.1 |

Forcing the inline is worse than not inlining at all. A ladder step has five
`fmul`s, each holding ten limbs and five 128-bit columns; inlining all of them
into one body spills. `static inline` is a *hint*, and gcc's answer -- inline
at some sites, call at others -- beats either fixed choice by twenty percent.

This is precisely what Custard's `FStar.Attributes.CInline` does. The
compiler source is explicit about the distinction:

> Custard's own `Inline` means "substitute this and emit nothing", which is a
> decision; this one is a request to the C compiler and leaves the definition
> where it is.

So the fix is not `inline_for_extraction` -- that is F*-level substitution,
the moral equivalent of `always_inline`, and on this evidence it would have
made things worse. It is one attribute on each of the eight field operations:
`fmul`, `fadd`, `fsub`, `fscale`, `carry_chain`, `carry_chain128`, `cswap`
and `copy`.

| benchmark | Part 10 | `CInline` | speedup | HACL\* | ratio |
|---|---:|---:|---:|---:|---:|
| x25519-scalarmult | 68.2 us | **56.2 us** | 1.21x | 44.4 us | 1.27x |
| x25519-base | 67.9 us | **55.8 us** | 1.22x | 44.9 us | 1.24x |
| ed25519-keygen | 114.7 us | **110.8 us** | 1.03x | 31.0 us | 3.57x |
| ed25519-sign-64B | 263.0 us | **255.0 us** | 1.03x | 64.4 us | 3.96x |
| ed25519-verify-64B | 262.2 us | **256.0 us** | 1.02x | 74.9 us | 3.42x |

Ed25519 barely moves, which is consistent: its cost is dominated by point
additions, which are already large bodies where the call overhead is a
smaller fraction.

clang is unaffected in either direction -- 68.4 us with or without the
attribute. It was already making its own decision and arrives at a worse one
than gcc's, which reverses the usual ordering in this report.

Two lessons worth keeping. First, an extraction-level hint can be worth as
much as an algorithmic change and costs one line. Second, `inline` in C is a
request for a reason: the compiler has the register-pressure information and
the programmer does not. The temptation to reach for `always_inline`, or for
F*-level `inline_for_extraction`, would have cost fifteen percent here.

The remaining 1.27x in X25519 is now the ladder itself -- no lazy reduction
across steps, and a `cswap` on every bit -- rather than anything about the
field.

## Part 12 -- Where else does `inline` pay, and what does it cost?

Part 11 left two questions. Does `CInline` help anywhere but Curve25519's
field? And should the `Hacl.Secret` arithmetic -- `mul_mod`, `add_mod`,
`logand`, 168 emitted functions, each a single expression -- be marked too?

Both were answered by patching the generated C and rebuilding, which costs a
build and a benchmark run rather than a twenty-minute re-verification.

### The `Hacl.Secret` layer: nothing

Marking all 168 of them changed no benchmark by more than one percent in
either direction. They are one-liners; gcc was already inlining every one.
They were never the problem, and F*-level `inline_for_extraction` on them
would have been equally invisible.

### `Hacl.Impl.Bignum256`: 1.9x on both 256-bit curves

Twelve `fn`s, twenty-four emitted functions -- the Montgomery step, the
reduction, the 4x4 product, the conditional subtract, the modular add and
subtract. Every P-256 and secp256k1 operation is dozens of calls into this
layer and almost nothing else, and none of them were being inlined: each is
thirty to eighty lines with ten or more call sites, exactly where gcc's
default heuristics say "call".

| benchmark | Part 11 | `CInline` | speedup | HACL\* | ratio |
|---|---:|---:|---:|---:|---:|
| p256-ecdsa-sign | 2487 us | **1288 us** | 1.93x | 169 us | 7.6x |
| p256-ecdsa-verify | 4749 us | **2490 us** | 1.91x | 432 us | 5.8x |
| p256-dh-initiator | 2369 us | **1240 us** | 1.91x | 157 us | 7.9x |
| p256-dh-responder | 2367 us | **1235 us** | 1.92x | 352 us | 3.5x |
| k256-ecdsa-sign | 2089 us | **1114 us** | 1.88x | 66 us | 17.0x |
| k256-ecdsa-verify | 3920 us | **2053 us** | 1.91x | 91 us | 22.6x |
| k256-ecdh | 1957 us | **987 us** | 1.98x | 91 us | 10.8x |
| k256-secret-to-public | 1958 us | **990 us** | 1.98x | 49 us | 20.2x |

Nothing else in the library moves by more than one percent. This is the
largest single change in the report by ratio-times-scope, and it is twelve
lines of attribute.

### And then it stops working

The obvious next step was to mark the layers above it -- `Hacl.Impl.Mont256`
and the two `Field` wrappers -- and Poly1305 alongside. P-256 and secp256k1
do get a little more (0.40 rather than 0.50 of baseline). But:

| marked | p256-sign | blake2s 256K | salsa20 256K | ed25519-sign | poly1305 256K |
|---|---:|---:|---:|---:|---:|
| nothing | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 |
| Bignum256 | **0.52** | 1.00 | 0.99 | 0.99 | 1.00 |
| + Mont256, Field | 0.46 | **1.52** | 1.00 | 0.98 | **1.50** |
| + Poly1305 | 0.40 | **1.53** | 1.00 | 1.01 | 0.92 |
| + all P-256/K-256 | 0.39 | **1.51** | **1.38** | **1.55** | 0.91 |
| everything | 0.40 | **1.26** | 0.96 | 1.00 | 1.04 |

BLAKE2, Salsa20 and Ed25519 share no code with any of what was marked. The
whole library is one translation unit, and `inline` is spent against gcc's
`--param inline-unit-growth`, which is a budget for the *unit*: asking for
more inlining in one place means gcc declines to inline somewhere else.
Recompiling the same file with `--param inline-unit-growth=200` restores
BLAKE2b to 582 us and BLAKE2s to 869 us against baselines of 575 and 877 --
exactly -- which confirms the mechanism.

A library cannot dictate its consumers' compiler flags, so the conclusion is
to spend the budget only where it is paid for: Curve25519's field (Part 11)
and the 256-bit bignum core. Both were chosen by measurement, not by looking
at the code.

Three lessons, all of them about the same thing:

1. An inline hint is a *request*, and the compiler's answer is better than
   any fixed one -- Part 11's `always_inline` was 15% slower than asking.
2. An inline hint is *global* in a single-TU library. There is no such thing
   as a local inlining decision here.
3. The place to look is not the small function. It is the middle layer:
   thirty to eighty lines, called from everywhere, just over the threshold.
   `Hacl.Secret` was invisible; `Hacl.Impl.Bignum256` was worth 1.9x.

## Score after two root causes

| primitive | gap at Part 1 | gap now |
|---|---|---|
| SHA-3 / SHAKE | 11.4x | **1.0x** |
| RSA-PSS, FFDHE | 6.6x | 2.0x |
| X25519 / Ed25519 | 8.5x / 22x | **1.27x / 4.0x** |
| P-256 / K-256 | 45x / 53x | **5.8-7.9x / 11-23x** |
| AES-GCM | 12-85x | 12-85x |

AES-GCM (root cause #3) is untouched and is now the largest remaining gap by a
wide margin -- though it is the one comparison that is verified C against
verified *assembly*, so parity is not the expected outcome there.

---

# Part 6: Root cause #3 -- AES-GCM

AES-GCM was the last of the three root causes and by far the largest gap: 12x
behind HACL\* on long messages and 85x on short ones. It is also the one
comparison that is not like for like, because HACL\*'s AES-GCM is Vale
assembly. Parity was never the goal; the goal was to find out how much of the
gap was algorithmic and how much was the generated C getting in its own way.

## Profiling first

There was no obvious culprit in the source, so rather than guess I built an
rdtsc-instrumented copy of `dist/Hacl.c` -- a Python patch that inserts
`PR_x -= __rdtsc();` at a function's opening brace and `PR_x += __rdtsc();`
before its closing brace -- and linked it against a driver calling the exported
`Hacl_AES_GCM_aes128_encrypt`. Neither `perf` nor `valgrind` is available on
this machine, so function stubbing plus rdtsc was the substitute.

The answer for aes128-gcm-enc on 256 KiB, at roughly **108 cycles per block**
against HACL\*'s 8.5:

| component | cycles/block | share |
|---|---|---|
| `gmul` (the GF(2^128) multiply) | 34 | 31% |
| GHash glue (byte-at-a-time xor, accumulator via memory) | 28 | 26% |
| AES-NI cipher (a latency-bound chain of `AESENC`) | 23 | 21% |
| CTR glue (`copy_exact`, byte xor, `inc32`) | 23 | 21% |

There is no single dominant cost. Closing the gap needs all four addressed,
which is why this took two commits rather than one.

**A warning for anyone repeating this.** Custard emits *two* monomorphic copies
of every function that takes a `params` argument: `__Mkparams` is AES-256 and
`__Mkparams_1` is AES-128. The `aes128-gcm-enc` benchmark uses the `_1` copy.
Stubbing the wrong one produces a confident, completely wrong "this costs
nothing" reading. That cost four wasted probe cycles here.

## The glue: half the cost, and none of it computing anything

Half the time was going not into arithmetic but into moving sixteen-byte values
into and out of memory one byte at a time. The reason it was so expensive is
worth spelling out, because it is easy to misdiagnose.

Both the GHash accumulator and the CTR keystream block were produced by a single
sixteen-byte *vector store* and then immediately consumed by a *byte-at-a-time
loop*. On every block that is a store-forwarding stall of roughly fifteen
cycles -- the narrow loads overlap a wide store that has not yet retired -- on
top of the byte traffic itself.

The diagnostic value of this is that several probes which merely *vectorised
those loops in place* showed **no measurable gain at all**: replacing the CTR
inner byte-xor with a sixteen-byte loop moved 884 us to 861 us, and vectorising
`Hacl_AES_GF128_gadd_at_impl` and `Hacl_Impl_Copy_copy_range` did nothing
whatsoever. What helps is removing the *round trip*, so that the value travels
from producer to consumer in a register and never reaches memory.

So, in commit `2e8b01e`:

- `Hacl.AES.GF128.NI` gained **`gmul_add_ni`**, which loads the next message
  block, exclusive-ors it into the accumulator, and multiplies, all without
  writing the intermediate sum down. The pure lemmas in `Hacl.AES.GHash` were
  already in exactly the right shape and needed no change.
- `Hacl.AES.NI.cipher_ni` was split into **`cipher_vec`** (`Vec.t -> Vec.t`,
  `inline_for_extraction`) plus a thin load/call/store wrapper, and a new
  **`ctr_block_ni`** builds the counter block, ciphers it, and exclusive-ors the
  result straight into the message. Custard inlines `inline_for_extraction`
  completely, so this extracts to one flat sequence of intrinsics.
- The CTR driver's inner loop was guarded by `(t < 16) && (t < rem)`, a
  conjunction that defeats vectorisation in both gcc and clang and that no
  amount of hinting will fix. It became **two loops**: a whole-block loop and a
  tail loop for the at most one partial block.

That took 256 KiB of aes128-gcm-enc from **884 to 647 us**.

## The cipher: four blocks at once

Re-profiling put the cipher at 27 cycles a block. `AESENC` has a latency of four
cycles on this machine and there are ten of them in a chain, so one block is 40
cycles of pure latency; measuring 27 means the out-of-order window was already
overlapping about one and a half blocks by itself. That is as far as hardware
will get on its own.

Counter mode's blocks are independent, so commit `84ba813` hands the machine
four at a time. `Hacl.AES.NI.ctr_block4_ni` produces four consecutive counter
blocks in registers, runs all four through **one shared round-key loop** -- one
key load and four `AESENC` per round -- and exclusive-ors the four results into
the message. The generated C is exactly the intended shape:

```c
while (i < 10) {
  Hacl_Vec128_t kv = Hacl_Vec128_load(kb);
  s0 = Hacl_Vec128_aesenc(u0, kv);
  s1 = Hacl_Vec128_aesenc(u1, kv);
  s2 = Hacl_Vec128_aesenc(u2, kv);
  s3 = Hacl_Vec128_aesenc(u3, kv);
  ...
}
```

Three things had to move:

- **The counter had to be advanced inside the vectorised step**, since all four
  counter blocks must exist before any is encrypted. `inc32_impl` moved out of
  `Hacl.AES.CTR` into a new `Hacl.AES.Counter` below `Hacl.AES.NI`.
- **`Hacl.Secret.UInt8.zero` had to go.** Once `inc32_impl` is reached from a
  function carrying a target attribute, Custard refuses to emit a global that is
  reached from both the attributed and unattributed parts of the program --
  correctly, since no portable qualifier means "reachable from both" for a
  variable. It now classifies its own zero.
- **The driver became three loops**: four blocks, then whole blocks, then the
  partial tail. Its guard is a *precomputed limit* rather than `j + 64 <= n`,
  because `n` may be within sixty-four of the largest representable size and the
  sum is then not a size at all.

### A Pulse lesson worth recording

Composing the four blocks' postconditions back into the loop invariant, written
as assertions inside the loop, **timed out at `--z3rlimit 600` after six
minutes**. Pulled out as a pure lemma over a single byte index -- `ctr4_step`,
with the whole separation-logic context left outside -- the same fact is a
five-way case split that goes through in seconds.

When a pointwise fact about an array is expensive to establish inside Pulse, the
problem is usually the *size of the ambient context*, not the fact. This is the
same lesson as the `assert (pure ...)` anchors in Part 5, in a stronger form:
there, anchoring inside the proof was enough; here, the proof had to leave.

## Results

256 KiB, gcc -O3, minimum of three interleaved rounds:

| benchmark | size | before | after | speedup | vs HACL\* before | vs HACL\* after |
|---|---|---|---|---|---|---|
| aes128-gcm-enc | 256 KiB | 876 us | **445 us** | **1.97x** | 12.5x | **6.3x** |
| aes256-gcm-enc | 256 KiB | 964 us | **471 us** | **2.05x** | 12.6x | **6.2x** |
| aes128-gcm-enc | 16 KiB | 58.5 us | **32.4 us** | 1.81x | 13.3x | 7.3x |
| aes128-gcm-dec | 16 KiB | 58.9 us | **31.9 us** | 1.85x | 13.2x | 7.1x |
| aes128-gcm-enc | 1 KiB | 8.00 us | **6.38 us** | 1.25x | 24.6x | 19.6x |
| aes128-gcm-enc | 64 B | 4.83 us | **4.72 us** | 1.02x | 79x | 77x |

clang is within five percent of gcc throughout (1.85x and 1.93x at 256 KiB).
Nothing else in the suite moved. The 64-byte case is untouched, as expected:
it is one block of message against a key expansion and a `j0` computation, so
none of this work is on its critical path.

AES-256 and AES-128 are now within five percent of each other on long messages,
which is itself a result: it means the cipher has stopped being the bottleneck.

## Where it stands, and what is left

Stubbing the pieces out one at a time puts the remaining 449 us at:

| component | before all this | now |
|---|---|---|
| `gmul` (field multiply) | 245 us | **245 us** (55%) |
| CTR (cipher + glue) | 442 us | **112 us** (25%) |
| GHash glue | 197 us | **91 us** (20%) |

**The field multiply is now more than half the total and is untouched.** It
issues twelve `pclmulqdq` per block where four would do. The reason is that the
reduction is written as a general `shifted_product` run three times, which is an
elegant formulation -- `Spec.GF128.Poly.gmul_three` says exactly that the three
low halves added together are the answer -- but the second and third runs
multiply by the reduction constant, and

> `Spec.GF128.Poly.r_block` is `x^7 + x^2 + x + 1`: only bits {0, 1, 2, 7}.

Multiplying by it is a shift and an exclusive-or. Written that way,
`pcoef a r_block k == a_k ^ a_{k-1} ^ a_{k-2} ^ a_{k-7}`, the multiply goes from
twelve `pclmulqdq` to four and from about 34 cycles a block to about 15. The
spec is already factored for it (`gmul_split`, `halves`, `mul_r_high`,
`mul_r_zero`), but it needs a new bit-level lemma and so was not attempted here.

Disassembly of the current `gmul_add_ni` also shows **26 `movdqa`
register-to-register moves** out of 95 instructions, which is the two-operand
SSE encoding. Adding `avx` to the target attribute would give the three-operand
VEX form and remove most of them -- at the cost of requiring a 2011 processor
rather than a 2010 one. That is a policy question, not a technical one.

## Score after three root causes

| primitive | gap at Part 1 | gap now |
|---|---|---|
| SHA-3 / SHAKE | 11.4x | **1.0x** |
| RSA-PSS, FFDHE | 6.6x | 2.0x |
| X25519 / Ed25519 | 8.5x / 22x | **1.27x / 4.0x** |
| P-256 / K-256 | 45x / 53x | **5.8-7.9x / 11-23x** |
| AES-GCM | 12-85x | **6.2-77x** |

All three root causes from Part 1 have now been addressed. What remains is a
list of ordinary optimisations rather than structural problems with the
extraction:

1. **GF(2^128) reduction by shifts** -- 12 to 4 `pclmulqdq`; about 1.4x more on
   AES-GCM, and the single largest remaining item.
2. **Curve25519 at radix 2^51** -- five limbs fit an `__int128`; about 2x on
   X25519 and Ed25519.
3. **Special-prime reduction for P-256 and K-256** instead of general
   Montgomery; the bulk of what is left after Part 12's 1.9x.
4. **Windowed exponentiation** (4-bit) in `Hacl.Bignum.Exponentiation` -- about
   1.6x on RSA-PSS and FFDHE.
5. **Windowed scalar multiplication** for P-256 and K-256, which is what the
   21x fixed-base versus 9.9x variable-base split is pointing at.

---

# Part 7: the GF(2^128) reduction without a multiplier

Item 1 of the list above, done. The estimate of 1.4x was wrong; the measured
figure is 1.11x, and the reason it is wrong is the interesting part.

## The change

Gueron's GHASH reduction is written as two further 128x128 carry-less
products, both by the constant `R = x^7 + x^2 + x + 1`, which is how a GHASH
multiply comes to cost twelve `pclmulqdq`. But `R` has four set bits, so

```
pcoef a R k == bit a k ^ bit a (k-1) ^ bit a (k-2) ^ bit a (k-7)
```

and a product by it is four shifted copies of the other operand added
together. `Spec.GF128.Poly.mul_r_coef` proves this by splitting the
convolution's 128-term sum at the four points where `R` is nonzero; the two
special cases the old proof used, `mul_r_high` and `mul_r_zero`, are
instances.

The awkwardness is that SSE has no 128-bit shift by a bit count: the shift
units work one 64-bit lane at a time and carry nothing between lanes. A full
right shift by `n` is therefore two instructions, the lane-wise shift plus a
lane-wise left shift by `64 - n` of the value with its lanes moved down one,
to bring in what fell out of the high lane. A full left shift by `64 + m` is
one, because moving the lanes up has already zeroed the low lane and there is
nothing left to carry. `Spec.CLMUL.shr_gen` and `shl_gen` are those two
recipes; `mul_r_halves` assembles them into the pair of halves that
`Poly.gmul_three` consumes.

Stage one now stops before its byte reversals and hands back the raw
little-endian pair, because the reduction works in the multiplier's bit order
and never leaves it. Three `bswap` at the end replace twelve spread over the
three stages.

`gmul_add_ni` comes out at **4 `pclmulqdq` and 5 `pshufb`**, down from 12 and
10.

## What it bought

gcc -O3 on Zen 2, minimum of three runs:

| benchmark | before | after | speedup |
|---|---|---|---|
| aes128-gcm-enc 256 KiB | 445,447 ns | **402,400 ns** | 1.11x |
| aes256-gcm-enc 256 KiB | 471,221 ns | **427,491 ns** | 1.10x |
| aes128-gcm-enc 16 KiB | 32,360 ns | 29,009 ns | 1.12x |
| aes128-gcm-dec 16 KiB | 31,894 ns | 29,022 ns | 1.10x |

The 1.4x estimate came from the dependency chain: eight `pclmulqdq` at about
five cycles of latency each, on a chain that the serial GHASH accumulator
cannot hide, replaced by shifts at one. The chain really did get about that
much shorter. The function did not get 1.4x faster, so the chain is no longer
what is binding.

## What is binding

The disassembly is 95 instructions, of which **26 are register-to-register
`movdqa`**: the two-operand SSE encoding, which cannot write its result
anywhere but over one of its inputs. The obvious next move is to add `avx` to
the target attribute and get the three-operand VEX forms. Measured, by
compiling the whole library `-mavx`:

| benchmark | SSE | AVX | speedup |
|---|---|---|---|
| aes128-gcm-enc 256 KiB | 402,400 ns | 391,212 ns | 1.03x |
| aes256-gcm-enc 256 KiB | 427,491 ns | 423,822 ns | 1.01x |
| aes128-gcm-enc 16 KiB | 29,009 ns | 28,323 ns | 1.02x |

23 of the 26 `movdqa` disappear and 1 to 3% comes back, which is not worth
raising the hardware floor from 2010 to 2011. So the moves were not binding
either: they are register-renamed away, as they have been on every
out-of-order core since Ivy Bridge.

That leaves the one thing the single-block formulation cannot avoid: GHASH is
a Horner evaluation, `acc = (acc ^ block) * H`, and every multiply waits on
the previous one. The fix is not to make the multiply cheaper but to stop
serialising it -- accumulate four blocks against `H^4, H^3, H^2, H` and reduce
once per four -- which is the same trick as the four-way counter loop in
Part 6 and would need the same kind of work. That is now the top remaining
AES-GCM item, ahead of anything else in the function.

## The proof lesson, again

The first attempt put all six shifts in one function. It left fifteen
quantified refinements in scope at the point where the halves had to be
assembled, and timed out. Splitting each shift into its own
`inline_for_extraction` helper with a tight specification, and each four-term
sum into a pure lemma over bare `int -> bool` bit functions, brings the module
back to sixteen seconds.

This is the third time in this report that the cure for a slow proof has been
to move reasoning out of the context rather than to raise the rlimit --
Part 5 anchored the Keccak indices, Part 6 lifted the four-block composition
into `ctr4_step`, and here the shifts had to leave the function entirely. The
file's own existing comment said so already: "Keeping the polynomials out of
these two queries is the difference between seconds and hours."

## Score

| primitive | gap at Part 1 | gap now |
|---|---|---|
| SHA-3 / SHAKE | 11.4x | **1.0x** |
| RSA-PSS, FFDHE | 6.6x | 2.0x |
| X25519 / Ed25519 | 8.5x / 22x | **1.27x / 4.0x** |
| P-256 / K-256 | 45x / 53x | **5.8-7.9x / 11-23x** |
| AES-GCM | 12-85x | **5.6-77x** |

Remaining list, reordered:

1. **Four-way GHASH** with `H^2, H^3, H^4` -- breaks the Horner chain; the
   largest remaining AES-GCM item by a wide margin.
2. **Curve25519 at radix 2^51** -- five limbs fit an `__int128`; about 2x on
   X25519 and Ed25519.
3. **Special-prime reduction for P-256 and K-256** instead of general
   Montgomery; the bulk of what is left after Part 12's 1.9x.
4. **Windowed exponentiation** (4-bit) in `Hacl.Bignum.Exponentiation` -- about
   1.6x on RSA-PSS and FFDHE.
5. **Windowed scalar multiplication** for P-256 and K-256.

---

# Part 8 -- Four-way GHASH

## The identity, and the algebra it needs

GHASH is Horner's rule. The loop of Part 7 xored a block into the
accumulator, multiplied by the hash key `H`, and went round again, so every
multiply waited on the one before it. Part 7 measured that chain and found it
was the entire cost: thirty cycles a block against a dependency chain of about
twenty-two, with no overhead left anywhere to remove.

The standard cure is to take four blocks at a time:

```
acc' = (acc + b0) * H^4 + b1 * H^3 + b2 * H^2 + b3 * H
```

The four products no longer depend on one another. Turning the first form into
the second is associativity, commutativity and distributivity of GF(2^128)
multiplication -- and not one of those three was anywhere in the
specification, because a one-at-a-time GHASH had never needed them.

`spec/Spec.GF128.Algebra.fst` supplies them, in about three hundred and fifty
lines. The obvious route -- show that reduction modulo the Galois polynomial
is a ring homomorphism out of `F_2[x]` -- is a lot of work. The route taken
exploits a normal form `Spec.GF128.Poly` already proves:

```
gmul x y == bsum (fun k -> if pget (pbits x) k then xti y k else zero) 128
```

that is, a sum over the set bits of the *first* operand of the second operand
shifted and reduced. In that shape multiplication is visibly linear in its
first argument, so distributivity and "a multiplication can be pushed through
a sum" are nearly free, and the whole file reduces to three facts:

- `gmul_xt_right : gmul u (xt c j) == xt (gmul u c) j`, true term by term
  from `xt_add`, `xt_gadd` and `xt_zero`;
- `gmul_comm`, which is the convolution being symmetric -- the existing
  `xsum_rev` and `xsum_shift` from `Spec.CarryLess`, plus a local
  `xsum_window` that trims two differently placed ranges down to their common
  support;
- `gmul_assoc`, which is then just expanding the left product as a sum and
  pushing the third factor through it.

No new reasoning about the reduction polynomial appears anywhere. `xt` carries
all of it and the proofs never look inside. The module ends with `horner4`,
the rearrangement above stated directly in terms of four turns of the GHASH
recurrence, so that the implementation can appeal to it without doing any
algebra of its own.

Two things went wrong on the way. The module needs `--fuel 1`, not the `--fuel
0` the rest of the code uses, because `xt`, `bsum` and `accum` all need one
unfolding; and the reversed summand in `conv_comm` has to be written `fun i ->
pget b i && pget a (k - i)`, matching `conv b a k` syntactically down to the
argument order of `&&`. With the operands swapped the proof fails even though
every fact needed is in context: functions under `xsum` are opaque and the
solver will not commute `&&` inside a lambda.

## The loop

`ghash_step4` glues four applications of Part 7's `ghash_step` together with
the index arithmetic that turns them into one statement about `ghash_from`
four blocks on, and then calls `horner4`. `ghash_loop4_ni` is the loop itself:
four loads, four independent `gmul_vec`s against `H^4, H^3, H^2, H`, three
xors, accumulator in a register throughout. The powers are computed once on
entry, in registers, and only when there are at least four blocks to do, so
short messages pay nothing.

## The proof lesson, a fourth time

The first version put the four-way loop and the branch guarding it inside
`ghash_loop_ni`, next to the one-block loop that handles the tail. The branch
did not go through at an rlimit of four hundred, and one attempt that did go
through took nine minutes for the module.

Splitting it up -- the loop into `ghash_loop4_ni`, the branch into
`ghash_start`, the fact that a multiple of sixty-four is a multiple of sixteen
into `step4_bounds`, the fact that a partial block cannot fit into
`step1_bounds` -- brings the module to twenty-five seconds. Nothing about the
mathematics changed; only how many hypotheses each query has to look at.

That is the fourth time in this report. It is no longer a lesson, it is the
method: **when a Pulse proof is slow, take the reasoning out of the context.
Do not raise the rlimit.**

## Result

gcc -O3, Zen 2, `taskset -c 6`, minimum of three interleaved rounds:

| benchmark | Part 7 | Part 8 | speedup |
|---|---|---|---|
| aes128-gcm-enc 256 KiB | 390,706 | **318,749** | 1.23x |
| aes256-gcm-enc 256 KiB | 414,053 | **343,421** | 1.21x |
| aes128-gcm-enc 16 KiB | 28,402 | **24,137** | 1.18x |
| aes128-gcm-dec 16 KiB | 28,777 | **24,094** | 1.19x |
| aes128-gcm-enc 1 KiB | 6,084 | **5,918** | 1.03x |
| aes128-gcm-enc 64 B | 4,692 | 4,748 | 0.99x |

All 450 CAVP GCM vectors still pass. Nothing else in the suite moved.

## Why it is 1.23x and not 3x

This is the predicted outcome, not a disappointment. Stubbing the loops out
puts GHASH at 172 microseconds of the 319 -- 54 percent, down from 244 of 391
-- which is 21 cycles per block against a dependency chain that is now
irrelevant.

What binds now is issue throughput, not latency. One reduced product costs
about seventy vector operations that Zen 2 cannot eliminate at rename, and
thirty-two of them are shift-class operations that issue on only two ports.
Four independent products therefore cannot retire faster than roughly seventy
cycles however well they interleave. Breaking the latency chain was still the
right thing to do, and the thing that binds is now a different thing, which is
progress.

The next step for GHASH is clear and is not more parallelism: accumulate the
four 256-bit carry-less products *before* reducing, and reduce once per four
blocks instead of four times. That removes three quarters of the shift-class
work, which is most of the remaining cost. It needs one new specification
fact -- additivity of `Poly.halves`, the sum of four half-pairs being the
half-pair of the sum -- which is not yet proved.

The other half of AES-GCM is now the counter mode, at 147 microseconds, or
nine cycles per block for ten AES rounds. The reference does the whole of
AES-GCM in 4.25 cycles per block, so both halves still have a long way to go.

## Score

| primitive | gap at Part 1 | gap now |
|---|---|---|
| SHA-3 / SHAKE | 11.4x | **1.0x** |
| RSA-PSS, FFDHE | 6.6x | 2.0x |
| X25519 / Ed25519 | 8.5x / 22x | **1.27x / 4.0x** |
| P-256 / K-256 | 45x / 53x | **5.8-7.9x / 11-23x** |
| AES-GCM | 12-85x | **4.6-78x** |

Remaining list, reordered:

1. **Windowed scalar multiplication for Ed25519** -- a precomputed base-point
   window in place of bit-at-a-time double-and-add; now essentially all of the
   remaining 4.1x, since the field is at parity with HACL\*'s.
2. **One GF(2^128) reduction per four blocks** -- the rest of the GHASH cost.
3. **Special-prime reduction for P-256 and K-256** instead of general
   Montgomery; the bulk of what is left after Part 12's 1.9x.
4. **Windowed exponentiation** (4-bit) in `Hacl.Bignum.Exponentiation` -- about
   1.6x on RSA-PSS and FFDHE.
5. **Windowed scalar multiplication** for P-256 and K-256.
6. **Straight-line `fscale`** -- the same treatment as `fmul`. It is the only
   thing still using a nine-element 128-bit scratch array, and doing it would
   let every such allocation in Curve25519 and Ed25519 disappear. Worth a few
   percent at most, but it retires `carry_chain128` and `mul19` as well.
7. **Splitting the distribution into several translation units**, so that
   `inline` stops being one global budget. Part 12 shows real speedups
   available in Poly1305 and the Montgomery layer that cannot be taken today
   because claiming them costs 1.5x elsewhere. This is an extraction and
   packaging question, not a proof one.

---

# Part 13: F* master, and the clones that disappeared

## The toolchain move

Upstream `hacl-pulse` master had already merged the performance branch
(`6e1ed94`) and added FrodoKEM and HPKE, so the local branch fast-forwarded
onto `a643682` with no conflicts. F* moved from the `gebner_custard` branch to
`master` (`d57a6d9ae3`, "Merge pull request #4395"), 257 commits.

Rebuilding F* stage3 failed twice on this machine, both times in ulib, both
times for the same reason: commit `022e275299` removed 190 of 222 `z3rlimit`
pragmas from ulib on the assumption that the new per-goal SMT encoding made
them unnecessary, and on a shared, loaded box two of them are still needed.
`FStar.Math.Lemmas` and `FStar.Matrix` both fail at the default rlimit.

`--z3rlimit_factor` on the command line does *not* fix this: the modules
contain `#reset-options`, which discards it. The flag that does is
`--proof_recovery`, which F*'s own `check-friends` CI job uses -- it retries a
failed query at successively higher rlimits and warns. One warning for the
whole build:

```
* Warning 359 at ulib/FStar.Matrix.fst(1135,82-1163,43):
  - This query succeeded after increasing its rlimit by 2x
```

So: `make -j8 stage3 OTHERFLAGS="--proof_recovery"`. No local edits to F*.

## hacl-pulse against the new F*

A clean `make -j8 verify` of all 220-odd modules -- including FrodoKEM and
HPKE, which this branch had never checked -- passed with no errors on the
first attempt, across 257 commits of F* that included the removal of
`FStar.Mul`, the per-goal SMT encoding and a reworked Custard. `make extract`
then produced a `dist/Hacl.c` **byte-identical** to the committed one, and
`make test` returned zero.

That would have been the end of it. But the benchmark said otherwise.

## A 2.5x regression with no code change

| benchmark | Part 12 | after the merge |
| --- | ---: | ---: |
| p256-ecdsa-sign | 1,288 us | 3,302 us |
| p256-ecdsa-verify | 2,490 us | 6,329 us |
| p256-dh-initiator | 1,240 us | 3,154 us |
| k256-ecdsa-sign | 1,114 us | 2,747 us |
| k256-ecdsa-verify | 2,053 us | 5,108 us |
| k256-ecdh | 987 us | 2,587 us |
| k256-secret-to-public | 990 us | 2,560 us |

Nothing else moved. Splitting `dist/Hacl.c` into functions and comparing the
147 with `P256`, `K256`, `Bignum256`, `Mont256` or `Field256` in their names
against the pre-merge file: **all 147 byte for byte identical**. Rebuilding
the pre-merge `dist` on the same machine at the same moment gave the old
numbers, so it was not drift.

`nm --size-sort` found it. The old object had

```
Hacl_Impl_Mont256_amul.constprop.0    0xc68
Hacl_Impl_Mont256_amul.constprop.1    0xa83
Hacl_Impl_Mont256_amul.constprop.2    0xb13
Hacl_Impl_Mont256_amul.constprop.3    0xbe2
```

and the new one had a single generic `Hacl_Impl_Mont256_amul`. gcc's
interprocedural constant propagation had been cloning the Montgomery
multiplier once for each of the four moduli -- P-256 field, P-256 scalar,
secp256k1 field, secp256k1 scalar -- specialising on the modulus arrays and on
`mu`. The comment at the top of `Hacl.Impl.Mont256` asserted that this
specialisation "would buy the multiplier nothing". It was worth 2.5x, and we
had been getting it for free without knowing.

IPA-CP has its own size budget, separate from the inliner's:
`--param ipa-cp-large-unit-insns`, default 16,000. The whole distribution is
one translation unit; FrodoKEM and HPKE pushed it past. Recompiling the
*unchanged* new `dist/Hacl.c` with

```
--param ipa-cp-large-unit-insns=1000000 --param ipa-cp-unit-growth=100
```

brings back all four clones and all seven timings, to within one percent.
That is the proof. (`--param inline-unit-growth` and `large-unit-insns`, the
knobs from Part 12, do nothing here -- different pass, different budget.)

Removing every Frodo function from the file by hand was not enough to get the
clones back either: the unit is simply over the line now, and HPKE alone keeps
it there.

## The fix

Marking Mont256 `static inline` did nothing -- `amul` is three kilobytes and
gcc declines. `always_inline` on `amul` alone recovered nearly all of it, so
the F*-level equivalent is `inline_for_extraction`, which is what went in:

```
inline_for_extraction
fn amul (out a b ms nm: A.array S64.t) (mu: S64.t) (d: erased modulus)
```

Custard then emits a copy of the body at each of the 19 call sites, each with
its modulus and Montgomery constant in place. Verify, extract and test all
clean.

| benchmark | Part 12 | regressed | Part 13 | vs Part 12 |
| --- | ---: | ---: | ---: | ---: |
| p256-ecdsa-sign | 1,288 | 3,302 | 1,373 | 1.07x |
| p256-ecdsa-verify | 2,490 | 6,329 | 2,572 | 1.03x |
| k256-ecdsa-sign | 1,114 | 2,747 | 1,139 | 1.02x |
| k256-ecdh | 987 | 2,587 | 1,036 | 1.05x |
| k256-secret-to-public | 990 | 2,560 | 1,035 | 1.05x |

85 of 97 benchmarks are within 4% of Part 12; the rest are SHA-3 on large
inputs, +6%, a layout effect from the merge that is present with and without
this change. The 2-7% the curves do not get back is the difference between
19 copies and gcc's 4: more code, worse instruction cache. Object grew from
501 KB to 628 KB.

## What this is really about

This is the second time the same thing has happened, and the first time was
Part 12's discovery that `CInline` hints do not compose. Both are the single
translation unit. Every interprocedural optimisation gcc performs -- inlining,
constant propagation, cloning -- is allocated against a budget computed from
the size of the whole unit, and *any* new primitive can exhaust one and slow
down code it shares nothing with. FrodoKEM made P-256 2.5x slower and never
touched it.

A library cannot ask its consumers for `--param`. What it can do is stop
relying on decisions it does not control: say `inline_for_extraction` where
the specialisation matters, and split the distribution so the budgets are
smaller and local. The latter has moved up the queue.

The general lesson for this project: **benchmark after every toolchain or
dependency change, even when the generated code is byte-identical.** A diff of
`dist/` would have shown nothing at all.

## Score

| | vs HACL\* before | now |
| --- | --- | --- |
| P-256 / K-256 | 45x / 53x | **6.0-8.2x / 11-24x** |

Everything else is unchanged from Part 12.

Remaining list: unchanged, except that item 7 (splitting the distribution into
several translation units) is now the fix for two measured regressions rather
than an opportunity, and belongs above item 5.

---

# Part 14: taking the specialisations back

Part 13 fixed `amul` but left two residuals unexplained: SHA-3 about 6% slow
on large inputs, and the curves still 2-7% off. Both had the same cause.

`gcc -fdump-ipa-cp-details` on the distribution says, 523 times:

```
Ignoring candidate value because maximum unit size would be reached with 36556.
```

The unit is 36,223 "insns"; the inliner then grows it 31%. Recompiling with
`--param ipa-cp-large-unit-insns=1000000` and diffing `nm` output names the
specialisations we are losing: `Hacl_Impl_Exp256_mexp`,
`Hacl_Hash_SHA3_keccak_impl`, `Hacl_Hash_SHA3_Sponge_squeeze_impl`,
`Hacl_Bignum_Montgomery_precomp`, `Hacl_AES_Core_fmul_impl`,
`Hacl_Frodo_Pack_pack_byte`. Benchmarking that build: 5-9% on exactly the
SHA-3 and elliptic curve rows that were off.

## Two questions worth having asked

**Does IPA-CP propagate the arrays we pass as pointers?** Yes, and the dump
says so in as many words:

```
Creating a specialized node of Hacl_Impl_Mont256_amul/7645.
  replacing param #3 ms with const &Hacl_P256_Tables_qms_arr
  replacing param #4 nm with const &Hacl_P256_Tables_qnm_arr
  replacing param #5 mu with const 3993025615
```

It propagates the *address* as a scalar constant; the arrays are `static
const`, so later passes fold loads through it into literals. Both halves
matter -- the constant `mu` and the folded limbs.

**Do the `Hacl_Secret_*` wrappers count against the budget?** No. gcc's
*early* inliner disposes of functions whose body is smaller than the call
sequence, and it runs before the IPA passes compute `overall_size`. Of 102
`Hacl_Secret_*` definitions in `dist/Hacl.c`, zero appear as callgraph nodes
in the IPA-CP dump; the only `Hacl_Secret_*` symbols left are globals like
`Hacl_Secret_UInt64_zero`, referenced as data. Which also explains Part 12:
marking them `static inline` did nothing because they were already gone.

So the 36,223 insns are real loop bodies -- Frodo, HPKE, SHA-3 -- not
abstraction overhead. Trimming layers would buy no headroom.

## The policy

Do it ourselves. Two independent reasons:

1. It is a budget for the whole unit, so any new primitive can take a speedup
   away from code it shares nothing with. Demonstrated twice now.
2. **clang makes zero clones** -- LLVM's function specialisation pass is off
   by default. `nm` on the clang object: 0 specialised symbols against gcc's
   91. Everything we get this way is a gcc-only speedup, and reads as a
   gcc/clang gap rather than as a gap in the library.

Splitting the distribution into several files fixes neither: it moves the
budget and loses inlining across the new boundaries. It came off the queue.

## mexp

`Hacl.Impl.Exp256.mexp`, 67 lines of C, six call sites -- each curve's field
inversion, square root and scalar inversion, each with its own modulus,
Montgomery constant and exponent. `inline_for_extraction`:

| benchmark | Part 12 (pre-merge) | Part 13 | Part 14 |
| --- | ---: | ---: | ---: |
| p256-ecdsa-sign | 1,288 | 1,373 | **1,266** |
| p256-ecdsa-verify | 2,490 | 2,572 | **2,488** |
| k256-ecdsa-sign | 1,114 | 1,139 | **1,078** |
| k256-ecdh | 987 | 1,036 | **977** |
| k256-secret-to-public | 990 | 1,035 | **969** |

At or slightly ahead of where they were before FrodoKEM arrived, and no
longer contingent on gcc having room.

## `make clones`

A survey target, so this cannot quietly regress. It compiles the distribution
with gcc, lists every `.constprop`/`.isra`/`.part` symbol and diffs against
`mk/clones.baseline` -- 78 today. A `+` is a specialisation the compiler found
and we did not; a `-` is one we took over, or lost to unrelated growth.
`make clones-available` raises the budget and prints what gcc would have done
with room to spare.

The baseline is a to-do list: the generic bignum's Montgomery reduction and
exponentiation, Blake2's compress, HMAC, the SHA-2 cores.
`Hacl.Hash.SHA3.keccak_impl` is next -- already being lost, worth ~7%.

**The lesson, again and more generally: a diff of `dist/` is not a diff of
what the machine will run.** Twice now the generated C was identical or
irrelevant and the performance was not.

---

# Part 15: SHA-3, and what a clone is actually worth

First item off the `make clones` list.

## The rate

`Hacl.Hash.SHA3.Sponge` took the rate as a runtime `size_t` so that one copy
served SHA3-224 through SHA3-512 and both SHAKEs. Six call sites, six
literals: 72, 104, 136, 144, 168. Sharing cost the absorb loop two integer
divisions by a variable (`len msg / r`, `len msg % r`) and a variable length
on every block copy.

`inline_for_extraction` on the sponge -- `keccak_impl`, `absorb_impl`,
`absorb_full`, `last_block`, `squeeze_impl`, `squeeze_block`, `xor_block_at`.
Bulk improved 1.14x. **Short messages got 6% *slower*.**

The C-level probe had predicted 1.7x faster there, so something was missing.
It was the permutation: with the sponge inlined, `permute_impl` was still a
call, and for a 64-byte message one permutation *is* the work. A second probe
-- `always_inline` on `permute_impl`, `round_impl`, `theta_impl`,
`rho_pi_impl`, `chi_impl`, `lane_at`, `zero_state_impl` -- got 619 ns where
the first had got 772. So both halves went in.

| benchmark | before | after | |
| --- | ---: | ---: | ---: |
| sha3-512 64 B | 1,367 ns | **562** | 2.43x |
| sha3-256 64 B | 1,389 | **624** | 2.23x |
| sha3-256 1 KiB | 5,426 | **4,211** | 1.29x |
| sha3-512 1 KiB | 8,603 | **7,258** | 1.19x |
| shake128 64 B | 1,311 | **1,123** | 1.17x |
| sha3-256 256 KiB | 1,118 us | **986** | 1.13x |
| sha3-512 256 KiB | 1,874 | **1,737** | 1.08x |

SHA3-256 at 64 bytes was 1.31x the reference; it is now 1.6x faster than it.
Ed25519 picked up 5% as a side effect of code layout. Nothing regressed.

**Method note.** The first probe measured the ceiling of one idea and the F*
change fell short of it. That gap was the signal, not noise -- chasing it
found the permutation. When an F* change underperforms its C-level probe,
the difference is a fact about the code, and it is worth the twenty minutes.

## What `make clones` caught

The distribution went from 22,089 lines to 26,527, and the check immediately
reported five specialisations lost to that growth:

```
-Hacl_Bignum_Exponentiation_mod_exp_consttime
-Hacl_Bignum_Montgomery_precomp
-Hacl_Bignum_Montgomery_reduction
-Hacl_Frodo_Sample_sample_matrix__Mkparams_2
-Hacl_HPKE_Labeled_labeled_expand_impl__t
```

Three of those are the RSA and FFDHE hot path. Exactly the FrodoKEM trap
again -- except this time we knew to look, and this time it did not matter:

| | before | after |
| --- | ---: | ---: |
| bn2048-modexp-consttime | 8,929 us | 8,928 |
| rsapss-2048-sign | 9,277 | 9,315 |
| rsapss-2048-verify | 512 | 514 |
| ffdhe2048-secret-to-public | 9,477 | 9,312 |

Unchanged to within a quarter of a percent, and FFDHE slightly better. So the
baseline was updated rather than the code.

**This is the other half of the lesson.** A clone is evidence that the
compiler *found* a specialisation, not evidence that the specialisation pays.
`amul` was worth 2.5x and `mexp` 8%; these five are worth nothing. The check
is a prompt to measure, not a defect report -- which is why it diffs against
a baseline that can be updated with a reason, rather than simply failing.

Seventy-two left: Blake2's compress, HMAC, the SHA-2 cores.

## Score

| | vs HACL\* before | now |
| --- | --- | --- |
| SHA-3 bulk | 0.62x | **0.54x** |
| SHA-3 short | 1.31x | **0.63x** |

Remaining list: item 6 is now "take over the seventy-two remaining compiler
specialisations", and splitting the distribution into translation units has
come off it -- it moves the budget rather than removing the dependency, and
loses inlining across the new boundaries.

---

# Part 16 — BLAKE2: taking over the compression function, and the first place the two compilers disagree

## The setup

Part 15 ended with a survey: build `dist/Hacl.c` with `-fno-ipa-cp-clone` and
measure everything, to price all seventy-two remaining clones at once.  Two
families came back non-zero.  BLAKE2 was worth 1.13–1.15x, SHA-2 1.04–1.05x,
and the other sixty-odd were worth nothing measurable.  BLAKE2 first.

gcc's IPA-CP dump said what it was specialising:

```
Hacl_Hash_Blake2_Core_compress_impl__t   replacing param #3 ivs  with const &...ivs_arr
                                         replacing param #4 sg   with const &...sigma_arr
                                         replacing param #6 last with const 0
```

`ivs` is the initialisation vector, `sg` the message schedule table, both
`static const`; `last` is the final-block flag, a literal at every call site
(false in the block loop, true in the digest).  Custard already monomorphises
BLAKE2 eight ways, so this was six clones — compress and both half-rounds,
once per width.

clang cloned none of them.  LLVM's function-specialisation pass is off by
default.  That was the whole of a 13% gcc lead on BLAKE2b.

## Step one: `compress_impl`

`inline_for_extraction` on `compress_impl` alone.  Verify (38 min), extract,
test — all clean.  The extracted C grew by eight lines, because `compress_impl`
was three calls and nothing else.

| | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| blake2b 256 KiB | 566 us | 566 us | 640 us | 598 us |
| blake2s 256 KiB | 867 us | 847 us | 1,016 us | 1,003 us |

gcc parity, clang 1.07x on BLAKE2b.  As predicted.  `make clones` then said
something more interesting than the benchmark did:

```
-Hacl_Hash_Blake2_Core_compress_impl__t{,_4}
-Hacl_Hash_Blake2_Core_mix_columns__t{,_4}
-Hacl_Hash_Blake2_Core_mix_diagonals__t{,_4}
+Hacl_Hash_Blake2_Core_round_impl__t{,_4}
```

gcc had not given up.  It moved its clone one level down.  Taking over a
specialisation does not remove the compiler's interest in the chain; it just
changes where the compiler expresses it.

## Step two: the probe that split in half

So probe the rest of the chain at the C level — `always_inline` on `g_impl`,
`mix_columns`, `mix_diagonals`, `round_impl`, `rounds_impl`, `load_vector`,
`init_vector_impl`, `mix_state_impl`, across all eight monomorphisations
(104 functions, one regex).

```
                gcc              clang
blake2b 256K    566 -> 628 us    598 -> 441 us
blake2s 256K    847 -> 957 us  1,003 -> 713 us
```

clang 1.35x.  gcc *minus* 10%.  This is the first change in sixteen parts
where the two compilers wanted opposite things, so it was worth bisecting
rather than picking a side.  One function at a time, 256 KiB, against the
current baseline:

| inlined | gcc b | gcc s | clang b | clang s |
| --- | ---: | ---: | ---: | ---: |
| *(baseline)* | 566 | 847 | 598 | 1,003 |
| `g_impl` | 566 | 850 | **793** | **1,810** |
| `mix_columns`+`mix_diagonals` | 572 | 846 | 608 | 996 |
| `round_impl` | **663** | **1,007** | 597 | 995 |
| `rounds_impl` | 571 | 848 | 566 | 932 |

Two clean results and one surprise.  gcc's entire loss is `round_impl`.
clang's 1.8x blowup on `g_impl` *alone* is an artefact of inlining a leaf
without its parents — sixteen copies of the mixing function inside a call
that is still a call — and it disappears as soon as the enclosing functions
are inlined too.  Neither effect is visible in the all-at-once number.

Then the combinations:

| inlined | gcc b | gcc s | clang b | clang s |
| --- | ---: | ---: | ---: | ---: |
| all but `g_impl` | 655 | 972 | 444 | 714 |
| all but `round_impl` | 568 | 849 | 566 | 929 |
| all | 636 | 951 | 445 | 718 |

`round_impl` is the whole story, in both directions.  Inlining it is worth a
further 1.35x to clang and costs gcc 15%; everything else is free to gcc and
worth 6–8% to clang.

## What is actually happening

clang, with the round body inlined into the round loop, SROAs the sixteen-word
working vector into registers and the compression function never touches
memory.  gcc, given the same code, spills it.  Neither is wrong about its own
register allocator; the reason they can disagree at all is that the schedule
indices are *not* constants — `sg[base + i]` with `base` a loop-carried
variable — so the round body is sixteen indirect loads that alias analysis has
to reason about rather than sixteen known message words.

That makes the disagreement a fact about the code.  The annotation cannot
satisfy both because the code is asking the compiler to guess, and the two
compilers guess differently.

## What was committed

`inline_for_extraction` on `g_impl`, `mix_columns`, `mix_diagonals`,
`load_vector`, `init_vector_impl`, `rounds_impl`, `mix_state_impl` and
`compress_impl`.  Not `round_impl`, with a doc comment saying why.

Verify clean, extract clean, `make test` 0.  `dist/Hacl.c` 26,535 -> 28,685
lines.

| | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| blake2b 64 B | 352 ns | 353 ns | 342 ns | **312 ns** (1.10x) |
| blake2b 1 KiB | 2,301 ns | 2,289 ns | 2,538 ns | **2,237 ns** (1.14x) |
| blake2b 256 KiB | 566 us | 567 us | 640 us | **562 us** (1.14x) |
| blake2s 64 B | 256 ns | 258 ns | 260 ns | **242 ns** (1.07x) |
| blake2s 1 KiB | 3,432 ns | 3,370 ns | 3,986 ns | **3,661 ns** (1.09x) |
| blake2s 256 KiB | 867 us | **849 us** | 1,016 us | **932 us** (1.09x) |

gcc unchanged to within 2%, which is the point: it was already getting this.
clang gains 7–14%.  On BLAKE2b the two compilers now agree to within 1% where
they differed by 13%.

Collateral: nothing outside BLAKE2 moves more than 1.1% under gcc.  Under
clang the SHA-2 family reads about 2% slower, consistently across ten
benchmarks; its clones are all still present per `make clones`, so this is
code layout in a TU that grew 8%, not a lost specialisation.

`make clones`: the six BLAKE2 entries gone, `round_impl` added in their place,
and — despite 2,150 lines of growth — nothing else lost to the IPA-CP budget.
Baseline updated, 72 -> 68.

Commits `649def8` (blake2), `de2bd0b` (README).

## Score

BLAKE2b against HACL\*'s portable scalar C: 1.86x -> **1.81x** under gcc.  The
clang column, which nobody had been looking at, moves from 2.04x to 1.79x —
slightly ahead of gcc.

## Remaining list

A new item goes in at 6, ahead of the clones tidy-up, because the probe
measured its value precisely:

6. **An unrolled BLAKE2 round.**  Twelve straight-line bodies with literal
   schedule indices instead of a loop over a table.  Worth 441 us vs 562 on
   clang — a further 1.35x — and it is the only way to get that without
   costing gcc 15%, because it removes the thing the two compilers disagree
   about rather than choosing between them.  Same shape as the straight-line
   `fmul` in Part 15 of the curve work.
7. **The remaining sixty-eight clones**, now known (via `-fno-ipa-cp-clone`)
   to be collectively worth nothing measurable — a tidying exercise.

---

# Interlude — merging the `speed` branch

`origin/speed` = `origin/master` + one commit, `26bb0e1`, "Cut the
verification time from fifty minutes to seventeen".  It also carries master's
ML-KEM work (uniform sampler, centred binomial sampler, SHAKE128 squeeze
opened up for rejection sampling).

What it does: twelve modules that had no interface now have one, so clients
typecheck against a signature instead of waiting for a proof — the critical
path through the dependency graph was the entire wall clock, with fewer than
eight solvers busy on a 256-core box.  Plus per-module fuel reduction (most
expensive proofs ran at `--fuel 1 --ifuel 1` without needing either) and
native linear-arithmetic encoding in eight arithmetic-heavy modules.  Total
work 16,859 s -> 10,962 s; critical path 3,001 s -> 1,036 s.

Merged into `perf` with **no conflicts**.  Two things needed checking:

1. **`dist/Hacl.c` was auto-merged**, which is never trustworthy, so it was
   regenerated from scratch.  It came out **byte-identical** to the
   pre-merge extraction, as did `dist/Hacl.h` — so no re-benchmark was
   needed.  (Master's ML-KEM additions are not yet on the extraction
   surface.)
2. **The new `Hacl.Hash.SHA3.Core.fsti` exports `permute_impl` as a plain
   `val`**, and Part 15 had made that `inline_for_extraction` — worth 2.4x on
   a short SHA-3 digest.  An interface hiding the definition would have
   silently undone it.  It does not: `Hacl_Hash_SHA3_Core_permute_impl`
   appears zero times in the extracted C, so F* still inlines through the
   interface.  Worth knowing, because the same question will come up for
   every future interface placed over a specialised function.

Checked the other direction too — of the six modules carrying our
`inline_for_extraction` work (`Hacl.Impl.Mont256`, `Hacl.Impl.Exp256`,
`Hacl.Hash.SHA3`, `.Sponge`, `.Core`, `Hacl.Hash.Blake2.Core`), only
`SHA3.Core` acquired an interface at all.

`make -j16 verify` clean, `make test` 0, `make clones` OK at 68.  Merge
commit `0467a4b`, pushed.

---

# Part 17 — The unrolled BLAKE2 round

Part 16 ended by saying that `round_impl` was deliberately left un-inlined
because gcc and clang disagreed about it, and that the disagreement was the
honest signal that the *code* needed changing rather than the annotation.
This is that change.

## What the loop was

```c
size_t nr = 12;               /* 10 for BLAKE2s */
size_t base = 0;
size_t i = 0;
while (i < nr) {
  round_impl(vv, m, sg, base);
  base = (base + 16) % 160;
  i++;
}
```

`sg` is the hundred-and-sixty-entry sigma table; `base` is `16 * (i % 10)`,
and the modulus is there because BLAKE2b's eleventh and twelfth rounds reuse
the first and second permutations.  Each round reads sixteen message words
through `m[sg[base + k]]` — a load to get the index, then a load to get the
word.  A hundred and ninety-two of those per compression, none of them
foldable.

## Choosing the shape, at the C level first

The naive version — inline the round at all thirty-two call sites (eight
monomorphisations × four sites) — is 122 lines of C per round body, so
32 × 12 × 122 ≈ **47,000 lines**.  That is not acceptable for a generated
distribution of 28,685.  So four variants were probed on `dist/Hacl.c`
directly, with `always_inline` and regex-generated unrolling, before writing
any F*.

| variant | gcc | clang | object size gcc/clang |
| --- | ---: | ---: | ---: |
| baseline | — | — | 712k / 502k |
| unroll only, `round_impl` still a call | **1.00x** | **1.00x** | 717k / 502k |
| unroll + inline round, 32 copies | 1.06x | 1.67x | 909k / 654k |
| unroll + inline round, `vv` by pointer, 8 copies | 1.14x | 1.22x | 794k / 538k |
| unroll + inline round, **`vv` local**, 8 copies | **1.25–1.31x** | **1.48–1.62x** | 795k / 527k |

Three findings, and each of them changed the design:

1. **Unrolling alone is worth exactly nothing.**  1.00x on both compilers.
   With `round_impl` still a call, a literal `base` is just an argument that
   arrives in a register.  The win only exists once the body is inlined and
   the index folds — which means the two changes are a package, and either
   one measured alone would have looked like a failure.

2. **Where the working vector lives is worth as much as the unrolling
   itself.**  Passing `vv` as a pointer gets 1.14x/1.22x; making it a local
   array in the same function as the unrolled rounds gets 1.25x/1.62x.  The
   reason is aliasing: a pointer parameter might alias `m`, so the sixteen
   words have to stay in memory and every round does 32 loads and 16 stores.
   A local array that never escapes is SROA'd into registers.  That single
   fact dictated the F* signature change — `compress_impl` had to allocate
   the vector itself and lose its `vv` parameter, which rippled through four
   other modules.

3. **Thirty-two copies is worse than eight, for gcc.**  1.06x against 1.25x.
   The i-cache and gcc's own unit-growth budget eat the win.  Keeping
   `compress_impl` *not* `inline_for_extraction` is what bounds it at eight.

Note that the probe's best variant was *paying* for two sixteen-word copy
loops (copy-in and copy-out of the local vector) that the real version does
not need, so 1.25/1.62 was a floor.

## The F\* side

- `round_impl` becomes `inline_for_extraction`.
- A new `round_step` helper takes `(base: SZ.t) (n: G.erased nat) (vinit:
  G.erased (Seq.seq t))` with pre `v == rounds_upto p vm vinit n` and post
  `… (n+1)`, so each of the twelve steps is one unfolding of `rounds_upto`
  rather than one query carrying the whole chain.  Only `base` survives
  erasure into the C.
- `rounds_impl` is ten `round_step` calls at bases 0, 16, …, 144, then
  `if (SZ.gt nr 10sz) { round_step … 0sz 10; round_step … 16sz 11; }`.
  `nr` is `p.nrounds`, a literal after monomorphization, so the C compiler
  folds the test and exactly one arm survives in the object.
- `compress_impl` loses `inline_for_extraction` and its `vv` parameter, and
  does `let mut vv = [| z0; 16sz |]` itself.
- `Hacl.Hash.Blake2`, `.Streaming{,.fsti}` and `Hacl.Streaming.Blake2` lose
  the `vv`/`varr` threading — 95 substitutions and two stack allocations
  deleted.

## The proof failure, which was the interesting part

`rounds_impl` needs to know that the round count is ten or twelve; otherwise
the `else` branch cannot conclude `rounds p == 10` (it only has `0 < nr` and
`nr <= 10`).  Stated the obvious way:

```fstar
nrounds: n: SZ.t { SZ.v n == 10 \/ SZ.v n == 12 };
```

…and `make verify` failed in **`mix_columns`**, which does not care how many
rounds there are.  A forced single-module recheck took **18 minutes** and
still timed out at `--z3rlimit 600`, three times what the function had needed.

A single-variable experiment confirmed it: with the unrolling reverted and
*only* the refinement in place, `mix_columns` still times out (2m09s to
fail).  A refinement on a record field is a hypothesis in every query that
mentions a value of that type, and a disjunction is a case split.
`mix_columns` runs at `--fuel 0 --ifuel 0` and mentions `p` only for the
rotation distances, and it still paid.

The fix is to make the fact opaque and ask for it exactly once:

```fstar
[@@"opaque_to_smt"]
let nrounds_ok (n: SZ.t) : prop = SZ.v n == 10 \/ SZ.v n == 12

let nrounds_ok_intro (n: SZ.t)
  : Lemma (requires SZ.v n == 10 \/ SZ.v n == 12) (ensures nrounds_ok n) = …
let nrounds_cases (n: SZ.t { nrounds_ok n })
  : Lemma (SZ.v n == 10 \/ SZ.v n == 12) = …

nrounds: n: SZ.t { 0 < SZ.v n /\ nrounds_ok n };
```

The `0 < SZ.v n` is spelled out separately because that is the only part the
specifications themselves use (`rounds p : pos`), so nothing else changes.
`blake2b_with`/`blake2s_with` call `nrounds_ok_intro`; `rounds_impl` calls
`nrounds_cases`.  Result: `mix_columns` back to `--z3rlimit 200`, and the
whole module checks in **25 seconds**, down from 18 minutes and failing.

General rule, and it is worth writing down: **a refinement on a field should
be as close to atomic as the proofs that do not use it can bear.**

## Results

256 KiB, min of three rounds, `-std=c11 -O3`, pinned to one core.

| | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| BLAKE2b | 567 us | **396** | 562 us | **347** |
| BLAKE2s | 849 us | **598** | 932 us | **571** |

gcc 1.43x, clang 1.62x — both above the probe's floor, as expected.  Short
inputs move by the same factor (BLAKE2b at 64 bytes: 0.35 -> 0.27 gcc,
0.31 -> 0.20 clang).

Against HACL\*'s portable scalar C:

| | ref | gcc | clang |
| --- | ---: | ---: | ---: |
| BLAKE2b 256 KiB | 313 us | 396 (1.26x) | 347 (**1.11x**) |
| BLAKE2b 1 KiB | 1.28 us | 1.61 (1.26x) | 1.39 (1.08x) |
| BLAKE2s 256 KiB | 581 us | 598 (**1.03x**) | 571 (**0.98x**) |
| BLAKE2s 64 B | 0.18 us | 0.19 (1.10x) | 0.15 (**0.86x**) |

**BLAKE2s is at parity with the reference on both compilers**, and ahead of
it under clang.

Collateral: `dist/Hacl.c` 28,685 -> **41,301** lines.  clang loses 2% on
SHA-1 and gcc 2% on `x25519-base`; nothing else moves outside noise.
`make clones` 68 -> 64 (two `round_impl` and four `blake2_impl` clones gone,
gcc now clones `compress_impl` twice instead).  `make test` 0.

Commit `8689cbe`.

## Score

BLAKE2b against the reference: **1.81x -> 1.26x** under gcc, **1.79x ->
1.11x** under clang.  BLAKE2s: 1.46x -> 1.03x and 1.60x -> 0.98x.  The row
moves from eleventh-worst in the table to sixth-best.

## Remaining list

Item 6 is done, so the list is back to five real items plus the tidy-up:

1. **Windowed scalar multiplication for Ed25519** — signing is 4.0x where
   X25519 is 1.27x, and the whole difference is the precomputed base-point
   window.
2. **One GF(2^128) reduction per four GHASH blocks.**
3. **Special-prime reduction for P-256 and secp256k1.**
4. **Windowed modular exponentiation** (4-bit) — the whole RSA-PSS/FFDHE gap.
5. **Windowed scalar multiplication** for P-256 and secp256k1.
6. **The remaining sixty-four clones**, known to be collectively worth
   nothing measurable — a tidying exercise.

---

# Part 18 — Merging master, and taking the table pointer back from gcc

## The merge

`origin/master` had already merged our `8689cbe` (the unrolled round), so
`git merge origin/master` was a **fast-forward** to `ff16637`.  What came
with it is master's ML-KEM: specification, modular arithmetic, NTT and
twiddle tables, serialisation, both samplers, the vector layer, K-PKE, and
ML-KEM-512/768/1024 against the NIST vectors.  `dist/Hacl.c` 41,301 ->
43,989 lines.

Priced it, because the IPA-CP budget makes every merge a performance event:

| | gcc | clang |
| --- | --- | --- |
| ffdhe2048 | **+2%** | — |
| md5 | — | **+3%** |
| everything else | noise | noise |

Cheap.  `make clones` went 64 -> 69 (ML-KEM added five), no losses.

## The problem

The user's observation, and it is the right one: the unrolled round made the
*indices* literals, but the table itself was still a **parameter**.

```
blake2_impl / update_gen / digest_gen
  -> blake2_blocks / update_impl / digest_impl
    -> update_full -> absorb_blocks
      -> compress_impl
        -> rounds_impl -> round_step -> round_impl -> mix_columns
```

Sixteen signatures carrying `(sg: A.array SZ.t)`, a permission `#psg`, a
ghost sequence `#vsg`, and a `sigma_ok vsg` refinement — and **nothing ever
passed anything but `sigma_arr`**.  There is one sigma table in BLAKE2 and
both widths share it.  The parameter existed only so that a C compiler could
propagate it away.

## Measuring it, the right way

First measurement: shadow `sg` with the global inside all eight
`compress_impl` bodies in `dist/Hacl.c` and re-benchmark.

**Worth exactly nothing.**  Not 1%, nothing, on either compiler.  Both were
already getting it — gcc by cloning `compress_impl` (it is in
`clones.baseline`), clang by interprocedural constant propagation into a
`static` function.

That is the wrong measurement.  The question is not what it is worth today,
it is what it is worth *when the compiler stops doing it*.  gcc's clones come
out of `--param ipa-cp-large-unit-insns`, default sixteen thousand, spent
across the whole translation unit — and this project has already watched that
budget run out once, when FrodoKEM and HPKE cost every elliptic curve
operation 2.5x without a line of curve code changing.

So: `-fno-ipa-cp`, which is what an exhausted budget looks like.

| | `-O3` | `-O3 -fno-ipa-cp` | |
| --- | ---: | ---: | ---: |
| **before**, blake2b 256 KiB | 395 us | 450 us | **+14%** |
| before, blake2s 256 KiB | 597 us | 674 us | **+13%** |
| before, blake2b 16 KiB | 24.7 us | 28.4 us | +15% |
| **after**, blake2b 256 KiB | 397 us | 396 us | **0%** |
| after, blake2s 256 KiB | 605 us | 589 us | **0%** |

Thirteen to fifteen percent of BLAKE2, granted at gcc's discretion, out of a
budget any unrelated commit could spend.

## The fix

A helper in `Hacl.Hash.Blake2.Core` that packages the three steps every call
site was repeating:

```fstar
inline_for_extraction
fn sigma_table (_: unit)
requires emp
returns sg: A.array SZ.t
ensures exists* (ps: perm) (vs: Seq.seq SZ.t). A.pts_to sg #ps vs ** pure (sigma_ok vs)
{ sigma_len (); let sg = table sigma_arr 160sz; sigma_seq_ok (); sg }
```

`compress_impl` calls it and `drop_table`s at the end; `sg`, `#psg`, `#vsg`
and `sigma_ok vsg` come out of every signature above it.  Below it the chain
still threads `sg`, but everything there is `inline_for_extraction`, so the
generated C is one `size_t *sg = Hacl_Hash_Blake2_Core_sigma_arr;` per
instantiation and the literal subscripts fold at `-O1`.

Cost: 8 `A.array` parameters, 8 permissions, 8 ghost sequences and 10
refinement conjuncts deleted; `dist/Hacl.c` *shrinks* slightly.  Verification
unchanged (`Blake2.Core` still 25 s).

## What is left

Pricing the whole library with `-fno-ipa-cp` on the new code:

| still owes gcc's IPA-CP | |
| --- | ---: |
| nacl-secretbox-easy 64 B | 8% |
| sha2-256 256 KiB | 6% |
| md5 | 3% |
| **blake2b / blake2s** | **0%** |
| everything else | noise |

BLAKE2 was much the largest, and the only one where the table never varies —
which is exactly what made it a two-line fix.  The remaining table parameters
are harder for a reason worth recording:

- **BLAKE2's `ivs`** genuinely differs between the two widths (`iv64_arr` vs
  `iv32_arr`), and the word type `t` is abstract at the point where the
  choice would have to be made.  `p.iv` is the spec value and is erased.
- **SHA-2's `k256`/`k512`** and the initial states: same shape.
- **MD5's `k_arr`/`s_arr`** and **ML-KEM's `zeta_arr`** never vary and are
  mechanical, but are worth 3% and nothing respectively.

Getting `ivs` needs either a `[@@@monomorphize]` binder that Custard honours
for *array* arguments, or a type class carrying the table with an instance
per width.  Neither exists yet; noted on the roadmap.

## Score

No benchmark moves.  `make clones` 69 -> 67.  `make verify` clean, `make
test` 0.  Commit `d8eae39`.

The honest summary is that this bought zero microseconds and removed a 14%
cliff.  That is the second time in this project that the interesting number
came from deliberately *disabling* a compiler pass rather than from the
default configuration — the first was `-fno-ipa-cp-clone` pricing the whole
clone list at once — and it is becoming the standard way to ask "is this ours
or is it on loan?"

# Part 19 — A table that is not a pointer, and a benchmark that was lying

Part 18 ended with a note that BLAKE2's initialization vector could not be
taken back from gcc the way the sigma schedule had been, because the IV
genuinely varies between the 32-bit and the 64-bit instantiation and there
was no way to hand Custard an *array* as a monomorphization key.  There is
one.  It took three failures to find.

## `static_array` as a `Mono` binder

The mechanism the user proposed — take a `Pulse.Lib.GlobalArray.static_array`
and mark the binder `[@@@FStar.Attributes.monomorphize]` — works, despite
`static_array` being an `assume val` with no decidable equality.  Custard
names the emitted specialization after the table it was given:

    static void Hacl_Hash_Blake2_blake2_impl__t_iv32_arr(uint8_t *out, ...)

and the first line of the body is

    uint32_t *ivs = (uint32_t *)Hacl_Hash_Blake2_Named_iv32_arr;

which is exactly what was wanted: the constant is *inside* the function, not
an argument to it, and no interprocedural pass has to notice anything.

The edit, per table:

- binder `(x: A.array t)` becomes
  `([@@@FStar.Attributes.monomorphize] xa: GA.static_array t)`
- the `#p` / `#v` implicits and every `A.pts_to x #p v` conjunct come out of
  both `requires` and `ensures`
- the pure precondition now speaks of `GA.static_array_elems xa`
- the body opens with `let x = table xa 8sz;` and closes with `drop_table x;`
  before the last stateful statement — a Pulse `fn` may not end on a ghost
  statement
- call sites pass the global directly and lose their `table` / `drop_table`
  pair, so they get *shorter*

## Three failures

**Error 76, subtyping.** The `.fsti` still declared the old signature. Obvious
in hindsight; the error did not say so.

**Error 376, "binder 1 (w) of `block_len_sz` is monomorphized, but ... is
external".** A red herring, and an expensive one. `make extract` does not
re-check a modified `.fst` when the module has an `.fsti`; Custard was reading
a stale interface, saw a bodyless definition, called it external, and reported
it against an unrelated function. The rule is now: **always `make verify`
before `make extract`** after touching an `.fst` that has an `.fsti`.

**Error 393, "uses a static array where C needs an expression".** This is the
real one and the message is actively unhelpful — it advises binding the array
to a top-level definition, which is precisely what had been done. Custard's
specialization key is a *normal form*, and the reduction it runs includes
`UnfoldUntil delta_constant`, so a top-level `let iv64_arr = mk_static_array
iv64_list` gets unfolded to its braced initializer, which then lands in
expression position.

The fix is `[@@FStar.Custard.no_specialize]` on the global. That attribute is
named in a `DontUnfoldAttr` step in every reduction Custard performs, so the
key stops at the name. It says nothing to the SMT solver, so the lemmas
relating the array to its spec are untouched. `Spec.Blake2.Constants.fst`
already used it on `iv64`/`iv32`, which is how it was found; `custard.md` §M9g
documents it.

## MD5, the easy case

Not every table varies. MD5's `update_block_tbl` was `inline_for_extraction`
and `update_block_impl` was not, so the function that actually got compiled
was the one that took two table pointers, and gcc cloned it. Two attribute
moves — make `update_block_impl` `inline_for_extraction`, take it off
`update_block_tbl` — put the tables inside the compiled function. One call
site, so no code-size cost. `make clones` reported exactly
`-Hacl_Hash_MD5_Core_update_block_impl`.

## Score

No benchmark moves on either change, which is the point: both remove a
dependence on gcc's IPA-CP budget without asking for anything in return.
`make clones` 67 → 66. Commits `8ad284f`, `9408f24`.

# Part 20 — The benchmark was lying, twice

## First lie: a 75% regression that was not there

Benchmarking the MD5 change showed BLAKE2b 400 → 650 us and, under
`-falign-functions=32`, Ed25519 105 → 184 us. Stable. Repeatable across
alternating A/B runs. Nothing in the diff went anywhere near either.

Ruled out in order: the IPA-CP budget (clone symbol sets identical bar the
intended MD5 entry); function sizes (`nm -S` diff empty for every BLAKE2,
Ed25519 and SHA-2 symbol); `--param ipa-cp-large-unit-insns=1000000`, which
"recovered" it; `-falign-functions=32` and `64`, which also "recovered" it.
Those last two are how one talks oneself into a code-layout story.

What settled it: **every text and every data symbol in the fast and the slow
binary was at an identical address.** Then a byte-identical copy under a
different name ran fast; `rm` plus `cp` of the same bytes into the same name
ran fast; and the same two byte-identical binaries were 65% slower on cpu40
than on cpu6 with both cores idle, with cpu40 fast again 20 minutes later.

The box is an AMD EPYC 7662, two sockets, four NUMA nodes, 256 threads,
shared with other tenants, no `perf` (`perf_event_paranoid=4`), no `numactl`,
and `/proc/cpuinfo` reporting per-core clocks between 2.0 and 3.26 GHz. An
individual core can be most of a factor of two slow for tens of minutes,
invisibly.

**The canary.** The harness now runs a fixed 200,000,000-iteration serially
dependent integer loop — `x += (x >> 3) | 1` — once before the suite and once
after, and emits the minimum and the before/after spread as an ordinary CSV
row. About 188 ms on a healthy core here; spread typically 1.004. `cmp.py`
discards any run whose canary is more than 2% above the best canary seen
anywhere in the comparison: that run measured a different machine. `ab.sh`
runs A-B-B-A inside one window at two link-time code offsets.

The general rule, now in the README: a difference that is large, localized in
a subsystem the change did not touch, and *not accompanied by any difference
in the generated code* is a measurement artifact until proven otherwise, and
the cheapest proof is `nm -S`.

## Second lie: a reference with no assembly in it

The user asked for HACL* in its best available configuration, with vector
instructions enabled. Building it turned up a failure mode that is worse than
the first, because it flatters us rather than confusing us.

HACL*'s `./configure` **must be run with no arguments**. Given the
`--enable-vale --enable-inline-asm` flags one would naturally reach for, it
prints its help text and silently leaves `config.h` and `Makefile.config`
empty. Everything then compiles, links, and produces a `libevercrypt.a` with
no assembly in it whatsoever — and the objects from such a run are not
rebuilt by a later, correct `configure`, because their sources have not
changed.

The tell is a three-line program:

    EverCrypt_AutoConfig2_init();
    printf("shaext=%d ...", EverCrypt_AutoConfig2_has_shaext(), ...);

which printed `shaext=0 sse=0 avx=0 avx2=0 aesni=0 pclmul=0 bmi2=0 adx=0` on
a CPU that has all of them. After `rm *.o` and a rebuild: all 1, and the
archive went from 19.5 MB to 29.7 MB. AES-GCM in the reference went from
several hundred microseconds to 71. Had this gone unnoticed, the table would
have claimed hacl-pulse *beats* HACL* at AES-GCM, which it loses by 4.5x.

## The table, taken again

Three contenders — hacl-pulse, HACL* portable scalar, HACL* best — built at
two code offsets and run interleaved `pulse ref best best ref pulse` inside
each of three rounds, 36 runs, 10 discarded by the canary.

The scalar column barely moved from the previously published numbers, which
is the reassuring outcome: Ed25519 sign 255 → 238 us (a real improvement from
the intervening work), everything else within noise of where it was. The
pre-canary numbers were not wrong; they just had no warrant.

The new column is the interesting one:

| primitive | pulse | HACL* scalar | HACL* best | best / pulse |
| --- | ---: | ---: | ---: | ---: |
| ChaCha20 256K | 494 us | 854 us | 93 us | 5.30x |
| ChaCha20-Poly1305 256K | 808 us | 1,059 us | 148 us | 5.46x |
| Poly1305 256K | 281 us | 208 us | 57 us | 4.93x |
| HMAC-SHA-256 256K | 1,131 us | 1,102 us | 163 us | 6.94x |
| SHA-256 256K | 227 us | 1,098 us | 164 us | 1.39x |
| X25519 | 55 us | 44 us | 36 us | 1.52x |
| BLAKE2b 256K | 395 us | 312 us | 438 us | 0.90x |

Four observations.

**Vector code is worth five to seven times**, and that is the ceiling on what
a portable scalar implementation can reach however cleanly it extracts. Worth
stating plainly rather than leaving to be inferred.

**SHA-256 is the narrowest margin at 1.39x, and for a different reason.** Both
sides already issue `sha256rnds2`; that row is this repository's intrinsics
against Vale's hand-written assembly, not scalar against vector.

**HACL*'s AVX2 BLAKE2b is slower than its own scalar C here** — 438 us
against 312. Vectorization is not free and not always positive.

**Every vectorized primitive loses at 64 bytes.** ChaCha20 at 64 B is 264
MB/s vectorized against 293 scalar; Poly1305 513 against 736. Setup outweighs
the body.

## Score

No code changed. `README.md` gains the two reference columns, a paragraph on
what they mean and do not mean, and a new section on building the reference
honestly. Commit `f47c6bc`. CSVs in `r20/`; the runner is `table.sh` and the
aggregator `table.py` / `head.py`.

# Part 21 — The 4-bit window, and three lessons about the solver

Roadmap item 1, and the last purely algorithmic gap in the table.

## What was wrong

`Hacl.Bignum.Exponentiation.mod_exp_consttime` was square-and-multiply:
for each bit of the exponent, one squaring and one masked multiply, so
two `mont_mul`s per bit. HACL\* uses a 4-bit window and spends five per
four bits. For a 2048-bit exponent that is 4,096 against 2,560 — a ratio
of 1.60 — and it accounted for essentially the whole of the 1.98x gap on
the three rows that go through this function.

## What it is now

A *rung* is four squarings, then a constant-time lookup of `T[d]` for the
next four bits of the exponent, then one multiply. `T` is sixteen entries
of `nn` limbs, `T[d] = a^d · R mod n`, built once at the top of
`mod_exp_consttime` and held on its own stack — 4 KiB for RSA-2048,
16 KiB for FFDHE-8192. The lookup is `table_select` (new, in
`Hacl.Bignum.Base`): it reads *all sixteen* entries and folds them under a
mask derived from the digit, so the memory trace carries no information
about the exponent. `get_digit` extracts four bits and, because the
counter is always a multiple of four, never straddles a limb boundary.

`mod_exp_vartime` and `mod_inv_prime_vartime` are untouched — public
exponents, cold paths.

## Numbers

A/B against `be1b026`, two code offsets, two rounds, pinned to core 6,
canary-filtered.

gcc:

| benchmark | base | head | ratio |
| --- | ---: | ---: | ---: |
| bn2048-modexp-consttime | 8,932 us | 5,715 us | **0.640x** |
| ffdhe2048-secret-to-public | 9,453 us | 6,108 us | **0.646x** |
| ffdhe2048-shared-secret | 9,413 us | 6,111 us | **0.649x** |
| rsapss-2048-sign | 9,309 us | 6,046 us | **0.650x** |
| rsapss-2048-verify | 498 us | 515 us | 1.033x |

clang:

| benchmark | base | head | ratio |
| --- | ---: | ---: | ---: |
| bn2048-modexp-consttime | 9,495 us | 5,978 us | **0.630x** |
| rsapss-2048-sign | 9,800 us | 6,275 us | **0.640x** |
| ffdhe2048-shared-secret | 9,743 us | 6,253 us | **0.642x** |
| ffdhe2048-secret-to-public | 9,744 us | 6,259 us | **0.642x** |
| rsapss-2048-verify | 475 us | 487 us | 1.024x |

1.56x on gcc, 1.58x on clang, against a theoretical 1.60x — the window is
doing all of what it should. `rsapss-2048-verify` goes through
`mod_exp_vartime`, which did not change; its 2–3% is layout noise.

Against the reference, the three rows move from 1.98x / 1.98x / 2.04x to
**1.27x / 1.29x / 1.33x**.

## The honest caveat

This is not parity. From here both sides issue very nearly the same number
of `mont_mul`s; ours cost about 2.19 us each against HACL\*'s 1.77, and
the residual 1.27x *is* that multiply. The next win on this stack is the
inner multiply-and-reduce loop, not the exponent. The README says this in
the same paragraph as the improvement, deliberately.

## Three lessons, each of which cost hours

**1. Conditional congruence lemmas are poison.** A lemma

    pw_cong (a x y: nat) : Lemma (requires x == y) (ensures pw a x == pw a y)

makes the *caller* discharge `x == y`, and the caller's context is full of
nonlinear facts like `pw anum e * wt nn % num vn`. z3 could not prove
`e + e == 2 * e` there in forty-five minutes at rlimit 400. The
precondition-free forms — `pw_dbl`, `pw_q4`, `pw_q8`, `pw_q16`,
`pw_digit`, `tbl_get`, `mul64_mod4` — are proved in an *empty* context and
are instantaneous. The region went from >45 min to 90 s. Expect to need
exactly this for the Ed25519 and P-256 windows.

**2. Layer the contracts so arithmetic and effects never share a query.**
The final shape is three functions:

- `mont_win_mul` — lookup and multiply. Exponent and digit are opaque
  naturals. No divisions, no `pow2`, nothing about the exponent's bits.
- `mont_rung_core` — four squarings plus `mont_win_mul`. Still no
  divisions.
- `mont_rung` — the index arithmetic, and nothing else. Returns the next
  counter `j` with `SZ.v j == SZ.v i - 4` in its `ensures`, so the ladder
  never has to prove `i - 4 + 4 == i` in the big context either.

Also: asserting a function's own postcondition explicitly, just before the
closing brace, converts one enormous final VC into a small dedicated query
plus a congruence. That alone fixed `mont_win_mul`.

**3. An SMT timeout usually means a fact is genuinely absent.** Two were,
and both presented as timeouts rather than as failures:

- `Seq.length vtbl == 16 * SZ.v nn` had been dropped from `mont_rung`'s
  `requires` during a refactor. z3 span on it for an hour. Raising the
  rlimit from 100 to 300 made the run take 24m44s and did not fix it.
- `let mut tbl = [| S64.zero; ... |]` — `S64.zero` has the refined type
  `r: t { v r == 0 }`, and every other array-literal site in the tree
  binds it to a plain `let z64 = S64.zero;` first. The error was
  `Ill-typed term ... l_True == (S64.v r == 0)`, sixteen minutes in.

The technique that found both: `#push-options "--admit_smt_queries true"`
after the module's opens, `--admit_smt_queries false` around *one*
definition, and a deliberately **small** rlimit (30) so failure is fast.
That turns a 25-minute round trip into 30 seconds. Copy the reported
conjunction verbatim into an `assert (pure (...))` immediately before the
failing call; if the assert fails too, the fact is missing, not slow.

## Cost

`Hacl.Bignum.Exponentiation.fst` grew by about 600 lines, most of it
lemmas. Full `make verify` 13m49; the module alone 5m53. `extract`,
`test` and `clones` all clean; the clone count is unchanged at 66.

Callers pay two new preconditions, `SZ.fits (16 * SZ.v nn)` and
`SZ.v bbits % 4 == 0`. All three call sites pass `bbits = 64 * nn`, so
both are free — but both have to be handed to the solver explicitly
(`SZ.fits_lte` and the new `mul64_mod4`), or it will spend an hour not
finding them.

Commit `328575d`. CSVs in `r21/`; the runner is `ab.sh` (gcc) and
`abclang.sh` (clang, `sed`-derived), the aggregator `cmp.py`.

## Part 22 --- An exponent ladder for the Montgomery constant

`Hacl_Bignum_Montgomery_precomp` computes `R^2 mod n`, the constant that
takes a number into Montgomery form.  It was `128 * n` modular doublings
-- 4,096 of them for RSA-2048 -- and it cost **361 us** against HACL\*'s
**95**.  For signing that vanishes inside a 5.7 ms exponentiation.  For
*verification* it does not: RSA-PSS verify raises to 65537, seventeen
bits, so the ladder is 155 us and the setup was more than twice that.
It was essentially the whole of the `rsapss-2048-verify` gap.

### Two independent factors of two, and then a factor of eleven

Profiling the old chain showed two separate 2x gaps against HACL\*.  We
did `128 * n` doublings where they do `2 * 64n - bitlen(n)`, about 2,049
-- they start at a power of two just below the modulus, we started at
one.  And our per-doubling cost was 88 ns against their 46, because they
unroll four at a time.  Fixing both would have been 4x, to about 90 us.

The ladder is better than that, because doubling is not the only move
available.  Write the accumulator as the representative of `2^m`:

- `mont_mul acc acc` sends `m` to `2m`.  A Montgomery product of two
  representatives leaves a spare factor of `R`, and the reduction
  removes exactly one -- so squaring the representative of `2^m` is the
  representative of `2^(2m)`, with no correction.
- `double_mod acc n` sends `m` to `m + 1`.

Those are the two moves of binary exponentiation.  And `m == 64n` is
*definitionally* the existing postcondition `num res == (wt nn * wt nn)
% num vn`.  So the whole function is: get onto the ladder, then walk
`m` from 1 to `64n` in `floor(log2 64n)` squarings and as many
doublings.  Eleven multiplications for RSA-2048 instead of 4,096
doublings.

### The seed is the only part that stays linear

Reaching `m = 1` at all means having `2^(64n + 1)` already reduced.  We
checked whether any cheaper route existed and there is none: `mont_mul`
raises the exponent only in the squaring shape, and `reduction` and
`from_mont` only ever *lower* it.  Doubling is the sole operation that
raises the exponent by a fixed amount, so a linear phase is unavoidable
and the only question is where it starts.

It starts as high as it can for free.  Scan for the topmost limb index
`k` with `wt k <= num vn`; then `2^(64k)` is already its own residue and
can be written down as a single `1` in limb `k`.  The argument that it
is *strictly* below the modulus, which is what makes it its own residue,
runs: `mu`'s defining equation `mu * n[0] + 1 == 0 mod 2^64` forces
`n[0]` odd, hence `n` odd; an odd number greater than one is never a
power of the radix; so `wt k != num vn` and `wt k < num vn`.  That is
why `precomp` now takes `mu`.  Sixty-five doublings remain for a modulus
that fills its limbs, against 4,096.

The scan reads the modulus.  That is public in every caller -- an RSA
modulus travels with the public key, the FFDHE primes are literals in
the source -- so `top_limb` declassifies one `S64.eq_mask` per limb.
The doubling count that follows depends on the modulus's length and on
nothing secret.  This is a deliberate choice and is documented as one.

### Splitting the proof, again

The first attempt was one Pulse `fn` with three loops.  The file check
went 1m55 -> 9m41 -> still running at 13 minutes as each successive
obligation was discharged.  Splitting into `seed` / `ladder_step` /
`precomp` brought the whole file to **7m18** with no errors.  This is
the same lesson as the modexp window in Part 21, and it is now the
default assumption: a Pulse `fn` with more than one loop should be
split *before* the timings get bad, not after.

The contract that made it work is `ladder_step`'s, which mentions **no
division**:

    requires num vres == (pw 2 e * wt nn) % num vn
    ensures  num v == (pw 2 (2 * e + SZ.v bit) * wt nn) % num vn

The caller passes `e = mm / vp` and uses a separate `half_split` lemma
to see `mm / q == 2 * (mm / vp) + d`.  Putting the division inside the
step's contract had z3 reasoning about `/` and about effects in the
same query, and it did not come back.

Other proof notes from this part:

- `pw a 1 == a` needs `--fuel 2`, not `--fuel 1`.
- `SZ.add x 1sz` needs `SZ.fits (SZ.v x + 1)` in the invariant; for a
  bit index that comes from `e < pow2 e`.
- `SZ.sub vb 1sz` needs `1 <= SZ.v vb`, and z3 will *not* get it from
  `pow2 vb > 1` in a large context.  Extract `pow2_one`, proved by
  `assert_norm (pow2 0 == 1)`.
- **Adding a lemma can break an unrelated proof a thousand lines away.**
  `num_ge_at` in `Hacl.Bignum.Base.fst` broke `assert (rad * q + r == i)`
  in `num_bits_at`, with no `SMTPat` anywhere.  Confirmed against a
  stashed baseline before concluding.  Fix: put new lemmas in the module
  that uses them, as late in the file as possible.
- Shadowing an `open`ed module's definitions is legal, so `mul_expand`,
  `exp_mul`, `exp_sq_step`, `pw_dbl` and `modulus_low` were duplicated
  into `Montgomery.fst` rather than hoisted out of the already-fragile
  `Exponentiation.fst`.

### Measurements

Probe, RSA-2048, gcc `-O3`:

| | old | new |
| --- | ---: | ---: |
| `precomp` | 361 us | **32.5 us** |
| HACL\* `precomp` | 95 us | 95 us |

11.1x against ourselves, and 2.9x *ahead* of the reference.

A/B against `328575d`, three rounds, two link offsets:

| benchmark | gcc | clang |
| --- | ---: | ---: |
| rsapss-2048-verify | 516 -> 198 us, **0.387x** | 478 -> 190 us, **0.398x** |
| rsapss-2048-sign | 0.951x | 0.951x |
| ffdhe2048-secret-to-public | 0.947x | 0.959x |
| ffdhe2048-shared-secret | 0.947x | 0.960x |

Full three-way table, gcc, 31/36 runs kept:

| benchmark | hacl-pulse | HACL\* | ratio |
| --- | ---: | ---: | ---: |
| rsapss-2048-verify | 197.9 us | 143.6 us | 1.38x |
| rsapss-2048-sign | 5,740 us | 4,673 us | 1.23x |
| ffdhe2048-secret-to-public | 5,770 us | 4,623 us | 1.25x |
| ffdhe2048-shared-secret | 5,767 us | 4,616 us | 1.25x |
| bn2048-modexp-consttime | 5,696 us | 4,528 us | 1.26x |

The three bignum rows move from 1.27x / 1.29x / 1.33x to 1.26x / 1.23x /
1.25x, and the verify row -- measured for several parts but never shown
-- joins the README table at 1.38x.

### A harness bug worth recording

`/tmp/bench/Hacl.h` was a stale copy from an earlier part.  Because
`#include "Hacl.h"` searches the *including file's* directory first, it
silently shadowed `-I $R/dist` and handed every probe the old
three-argument prototype.  Deleted, and replaced by per-side header
directories (`base21/`, `head21/`) so that an A/B across a signature
change is expressible at all.  `ab.sh` cannot do that; the new `ab2.sh`
takes per-side include dirs and extra flags.

### Left open

`Hacl.Bignum.Montgomery.fst` now checks in 7m18 where it used to take
about 2, which is likely the critical path of `make verify`.  The
`--z3rlimit 300` region covers all four `fn`s and could probably be
narrowed; which one dominates has not been measured.

Commit `6da114f`.  CSVs in `r22/` (A/B) and `r22/table_gcc.md` (folded
three-way table); the runner is `ab2.sh`, the table `table.sh`.

## Part 23 --- The shared 256-bit core at four limbs of sixty-four bits

P-256 and secp256k1 were the two worst rows in the table, and the reason was
not either curve's scalar multiplication.  It was the core underneath both:
eight limbs of thirty-two bits, so a field multiply did sixty-four schoolbook
products and sixty-four reduction products where four limbs of sixty-four
would do sixteen and sixteen.  Measured directly before any of this work, our
secp256k1 `fmul` was 53.4 ns against HACL\*'s 7.0 and our P-256 `fmul` 42.2 ns
against HACL\*'s 16.8 --- and HACL\*'s two are four-limb and five-limb.

### What had to be rebuilt

The whole stack, because the limb width is not a parameter of it.  Six new
spec modules and four new implementation modules, in six commits:

| module | lines | verifies in |
| --- | ---: | ---: |
| `Spec.Bignum4` | 690 | 40 s |
| `Spec.Montgomery4` | 320 | 17 s |
| `Spec.Field4` | 784 | 3 m 39 |
| `Spec.Mont4` | 333 | seconds |
| `Hacl.Impl.Limb4` | 545 | 2 m 40 |
| `Hacl.Impl.Bignum4` | 920 | **30 min** |
| `Hacl.Impl.Mont4` / `Exp4` / `Lit4` | 811 | minutes |

`Hacl.Impl.Bignum4` is now the critical path of `make verify`; the previous
worst was `Hacl.Bignum.Montgomery` at 7 m 18.

### The one design decision

At radix 2^32 a product `a_i * b_j` fits in a 64-bit column and the
schoolbook accumulator can hold a whole column in a word.  At radix 2^64 one
product already fills 128 bits, so a product does not go in one column:

> `a_i * b_j` contributes `plo` of it to column `i + j` and `phi` of it to
> column `i + j + 1`.

Since `plo x + base * phi x == x` the number is unchanged, and a finished
column is under `2^67`.  Factoring this into a single `srow n u b i j` let
`Spec.Montgomery4` inherit it whole, and it made `mul_columns`'s interface
*simpler* rather than harder: the `lim` argument disappeared, because the
column bound `nl * (2 * (base - 1))` now holds unconditionally.

The bound chain moves up with it --- Montgomery headroom `pow2 66` where it
was `pow2 65`, carry bound `pow2 9` where it was `pow2 41` --- and one
consequence is not cosmetic.  At the old width `base < pow2 64` was a fact
the top carry could be narrowed with.  At this width it is false, so
`redc_op` narrows its top carry using `redc_ok`'s conclusion that the carry
is at most one.  Every addition in the core now builds its sum in an array of
128-bit words and narrows on the way out, which is the only change visible in
the interface: the scratch buffer callers pass is `A.array S128.t`.

### The switch-over

Mechanical, mostly: the module renames, and `8sz -> 4sz` at every stack
allocation and every table read.  The constant tables were regenerated by
script from the `assert_norm (leval ... == N)` lines already in the file ---
the values are stated there, so nothing had to be recomputed from the curve
parameters --- and the surrounding assertions, which are about the value and
not about the limbs, did not change at all.

`mu = -m^-1 mod 2^64` was recomputed for three of the four moduli.  P-256's
prime keeps `mu == 1`: its low limb is `2^64 - 1`, so its inverse is still
`-1`.  A small gift from its Solinas shape, and the only one this
representation collects.

### Seventy-eight minutes on a goal that takes no time at all

Worth recording because it cost most of a day and left no diagnostic.

`Hacl.Secret.UInt128.zero` has the refined type `r: t { v r == 0 }`.  The
four decoders that now need a wide scratch array were written as

```
let mut asv = [| S128.zero; 4sz |];
```

which asks Pulse to discharge that refinement in whatever context the
surrounding proof has built up.  Z3 then spun for over an hour on
`S128.v x == 0` --- with the rlimit set to 200, and no rlimit exhaustion,
because the search never reached an operation that counts against it.  Four
modules that used to check in seconds took seventy-eight minutes each and
`make verify` never finished.

The rest of the repository already writes

```
let z128 : S128.t = S128.zero;
let mut asv = [| z128; 4sz |];
```

which erases the refinement at the binding site, where the context is empty.
With that, `Hacl.P256.Field` checks in five seconds.  The lesson generalises:
**a refined constant should be bound at a point where its refinement is
cheap, not used at a point where it is not.**

### Results

`fmul`, gcc `-O3`, `taskset` to one core, probed directly:

| | before | after | HACL\* |
| --- | ---: | ---: | ---: |
| P-256 `fmul` | 42.2 ns | **19.7 ns** | 16.8 ns |
| secp256k1 `fmul` | 53.4 ns | **21.5 ns** | 7.0 ns |

P-256's field multiply is now within 1.17x of the reference.  secp256k1's is
not, and will not be from a width change: HACL\*'s secp256k1 is five limbs of
fifty-two bits, lazy, with no Montgomery factor at all.

The whole benchmarks, gcc, 34/36 runs kept, against the Part 14 baseline:

| benchmark | before | after | speedup | HACL\* | ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| p256-ecdsa-sign | 1,266 us | **418 us** | 3.03x | 168 us | 2.48x |
| p256-ecdsa-verify | 2,488 us | **811 us** | 3.07x | 425 us | 1.91x |
| p256-dh-initiator | 1,240 us | **403 us** | 3.08x | 156 us | 2.59x |
| p256-dh-responder | -- | **404 us** | -- | 352 us | 1.15x |
| k256-ecdsa-sign | 1,078 us | **313 us** | 3.44x | 65 us | 4.79x |
| k256-ecdsa-verify | -- | **594 us** | -- | 90 us | 6.60x |
| k256-ecdh | 977 us | **296 us** | 3.30x | 89 us | 3.34x |
| k256-secret-to-public | 969 us | **295 us** | 3.29x | 48 us | 6.09x |

Three times, uniformly, on eight benchmarks, from a change that touches no
curve code.  Two rows leave the bottom of the README table: P-256 ECDSA
verification goes from 5.74x the reference to **1.91x**, and secp256k1 ECDSA
signing from 16.16x to **4.79x**.

clang agrees and is slightly kinder to the new code on P-256 --- 724 us on
verification against gcc's 811, 359 against 403 on DH --- and slightly less
kind on secp256k1.  Both compilers see the same three-times improvement, which
is the point: it came from doing four times less arithmetic, not from a
heuristic.

No other row moved.  X25519 stays at 1.26x, SHA-256 at 0.21x, and
`make clones` reports one change beyond the renames: gcc, with the elliptic
curve code now four times smaller, found enough IPA-CP budget to start
specialising `Hacl_HPKE_Labeled_labeled_expand_impl__t`.  Sixty-seven known
specialisations, up from sixty-six.

### What is left on these two curves

The general Montgomery core where the primes admit special-prime reduction
--- which is all of secp256k1's remaining gap --- and bit-at-a-time scalar
multiplication where HACL\* uses a window.  Neither needs new proof
technique.  `Hacl.Impl.Bignum256`, `Mont256`, `Exp256` and `Lit256` are now
dead except for Ed25519's use of `Spec.Bignum256` for its scalar field, which
is eight limbs of thirty-two bits and correctly stays that way.

---

# Part 24 --- secp256k1 gets its own field

Roadmap item 3 said that P-256 and secp256k1 were behind for two reasons
once their limb width was fixed: the shared general Montgomery core, and
bit-at-a-time scalar multiplication.  This part removes the first of the two
for secp256k1.

## What was built

`code/k256` no longer uses `code/field256`'s Montgomery layer for the base
field.  It has its own: five limbs of fifty-two bits, lazily reduced, with
the fold `2^256 = p + 2^32 + 977` in place of a Montgomery reduction.  This
is the representation libsecp256k1 uses and the one HACL\* copied.

The spec stack, bottom to top:

| file | contents |
| --- | --- |
| `spec/Spec.Bignum52.fst` | prime-free radix-52 core: `nl = 5`, `base = 2^52`, `lim = 2^53 - 1`, `eval`, `bnd`, carries |
| `spec/Spec.K256.Field52.fst` | `felem`, `fev`, `fadd_spec`, `fmul` as `carry_pass (carry_pass (fold (prep (part a b nl))))` |
| `spec/Spec.K256.Columns.fst` | the bridge: the nine-column schoolbook product and its fold, restated as the straight line the code runs |
| `spec/Spec.K256.Freeze.fst` | canonical form: two carry runs, a 48-bit top fold, one branch-free conditional subtraction |
| `spec/Spec.K256.Repack.fst` | bit repacking between five 52-bit limbs and the four 64-bit ones whose byte layer was already proved |

and the code:

| file | contents |
| --- | --- |
| `code/k256/Hacl.K256.Field52.fst` | `fadd`, `fsub`, `fneg`, `fmul`, `fsqr`, `freeze`, `load`/`store`/`fload`/`fstore`, `fcopy`/`fzero`/`fone`/`feq`/`fis_zero`, `asel`, the four curve constants |
| `code/k256/Hacl.K256.Exp52.fst` | square-and-multiply with the Montgomery apparatus removed |
| `code/k256/Hacl.Impl.Lit52.fst`, `Hacl.K256.Tables52.fst` | radix-52 literals and `b`, `3b`, `g_x`, `g_y` |

`code/k256/Hacl.K256.Field.fst` is deleted, and with it the Montgomery-only
entries of `Hacl.K256.Tables` --- `fms`, `fr1`, `fr2`, and the Montgomery
forms of the curve constants.  `fnm` survives because `fload` still uses
`abelow` against the modulus to reject an out-of-range byte string.

## The caller migration

Nine modules allocate field elements.  Each needed three mechanical changes:
`[| z; 4sz |]` to `5sz` for the arrays that hold field elements (not the ones
that hold scalars), `open Spec.Bignum4` to `open Spec.Bignum52` so that `nl`
and `eval` resolve at the new radix, and `felem vx` to `felem (vals vx)`,
since the radix-52 specs are stated over the ghost `vals` view rather than
over machine words.

Two things made this less mechanical than it sounds.

**Mixed modules.**  Ecdh, Sign, Verify, PointStep, PointMul and PointMulD
handle a field element and a scalar in the same function, and the scalar
field is still four 64-bit limbs.  Those modules keep `Spec.Bignum4` and
`Hacl.Impl.Limb4` under abbreviations `B4` and `L4` and write `B4.nl`,
`B4.bnd (L4.vals vk) B4.base`, `B4.eval (L4.vals vk)` wherever a scalar is
meant.  Allocation sites had to be rewritten per variable: in `Hacl.K256.Sign`
the thirteen scratch arrays `c0`..`cc` are eight scalars followed by five
field elements, on one line.

**`4sz` is a substring of `64sz`.**  A blanket replacement silently turned
two `Sub.sub b 32sz 64sz` into `65sz` and two `copy_at out 1sz pk 64sz` the
same way.  Caught by reading the diff; worth remembering that this particular
sed is never safe without a negative lookbehind.

**`felem` confined to two definitions.**  In `Hacl.K256.Point` the only uses
of `felem` and `fev` are inside `pt` and `pt_ok`, which every other point
predicate in the tree is phrased through.  Changing those two definitions
carried the whole change; the other modules needed between one and five
rewrites each.

## Results

gcc 12, `-std=c11 -O3`, one core, three rounds at two link offsets,
interleaved palindromically as always.

| benchmark | before | after | HACL\* | ratio before | ratio after |
| --- | ---: | ---: | ---: | ---: | ---: |
| k256-ecdsa-sign | 313 us | 227 us | 65 us | 4.79x | 3.49x |
| k256-ecdsa-verify | 505 us | 428 us | 90 us | 5.6x | 4.76x |
| k256-ecdh | 291 us | 213 us | 89 us | 3.3x | 2.40x |
| k256-secret-to-public | 291 us | 213 us | 49 us | 6.0x | 4.37x |

clang 14 is consistently worse on this curve than gcc --- sign 261 us, verify
479, ecdh 239 --- which is the usual pattern for code Custard emits as many
small functions.

## The field is done; the ladder is not

The interesting measurement is the field multiply on its own.  Both `fmul`s
--- ours and HACL\*'s --- were put behind a `noinline` call and fed their own
previous output, so the loop measures latency rather than throughput:

| | gcc | clang |
| --- | ---: | ---: |
| hacl-pulse `Hacl_K256_Field52_fmul` | 29.4 ns | 33.0 ns |
| HACL\* `Hacl_K256_Field_fmul` | 25.9 ns | 27.1 ns |

Within 14%.  The 7.0 ns figure quoted in earlier parts of this report was a
throughput number from a different harness and is not comparable to these;
against the same harness the two implementations of the same representation
land within a few percent of each other, which is what one would expect since
the emitted C is nearly the same straight line.

So the remaining 2.4x on variable-base ECDH is not the field.  It is that
this tree still walks the scalar one bit at a time --- 256 iterations of
double, add, constant-time select --- where HACL\* uses a fixed window with
precomputed tables.  At roughly 830 ns per step against HACL\*'s effective
346, and with about twenty field multiplies per step, the arithmetic accounts
for essentially all of our per-step cost; the difference is the number of
steps.  That is roadmap item 4, and it is blocked on the group-law lemmas
being proved in parallel.

Two smaller things the generated C suggests and this part did not do:
`fsqr` is `fcopy` followed by `fmul`, which both wastes a five-word copy and
gives up the ten products a real squaring saves; and multiplication by the
small curve constant `3b = 21` goes through the full nine-column `fmul` where
HACL\* has a `fmul_small_num` that multiplies five limbs by a word.  Between
them they are worth a few percent of the group law, not a factor.

## Verification cost

`Hacl.K256.Field52` alone is about eight and a half minutes, which dominates
`make verify` for this directory.  The lesson from Part 23 held throughout:
what costs time is the size of a single Pulse verification condition, not the
number of facts in scope.  `load` --- nine index equations relating five
52-bit limbs to four 64-bit ones --- did not return in twenty-four minutes
with the three supporting lemmas applied inside the Pulse body, and returned
in seconds once they were folded into one spec-side `load_all` whose
conclusion is exactly the postcondition.  The same fold had already been
needed for `fmul`'s nine columns.  A corollary discovered the hard way: a
Pulse `fn` whose last statement is a ghost call does not thread that call's
postcondition into the final VC, so such a body must end with a bare `()`.

# Part 25 --- A window for secp256k1, and an abstract group to prove it with

## What was done

secp256k1's variable-base scalar multiplication walked the scalar one bit at
a time: 256 rungs, each a doubling, an addition, and a constant-time select
between the two.  512 point operations.  It now walks four bits at a time
against a table of the sixteen small multiples `[0]P … [15]P` of the input
point, built at run time: 64 rungs of four doublings and one addition, plus
sixteen additions to build the table.  336.

The table is three flat arrays of eighty limbs --- sixteen five-limb entries
each --- and a rung reads its digit with three calls to
`Hacl.Bignum.Base.table_select`, the constant-time lookup already written for
the modexp window in Part 21.  The digit itself comes from a new
`Hacl.Impl.Mont4.adigit` and its specification `Spec.Mont4.enib`, the nibble
analogues of `abit`/`ebit`; a nibble never straddles a limb because four
divides sixty-four.  The table is built by sixteen additions walking up from
the point at infinity, which wastes exactly one addition --- entry zero ---
and buys a loop with a single case.

There is no windowed *specification* function, and that was deliberate.  The
accumulated scalar is a ghost natural `e`; the loop invariant says the
accumulator represents `k / 2^j`, and a rung justifies `e := 16e + d` from a
division identity.  The specification `Spec.K256.point_mul` is untouched.

## Measurements

gcc 12, `-std=c11 -O3`, one core, interleaved with the reference at two
link-time code offsets, three rounds, palindromic order, canary-filtered ---
the standing protocol since Part 20.

| benchmark | before | after | HACL\* | ratio before | ratio after |
| --- | ---: | ---: | ---: | ---: | ---: |
| k256-ecdh | 213 us | **154 us** | 89 us | 2.40x | **1.73x** |
| k256-secret-to-public | 213 us | **153 us** | 49 us | 4.38x | **3.15x** |
| k256-ecdsa-sign | 227 us | **169 us** | 65 us | 3.49x | **2.58x** |
| k256-ecdsa-verify | 428 us | **313 us** | 90 us | 4.76x | **3.48x** |

clang 16 agrees within 3%: ECDH 149.4 us, sign 171.0, verify 301.5,
secret-to-public 150.1.  Nothing else in the table moved.

26% off, against a predicted 34% from the operation count (336 vs 512).  The
shortfall is the doubling-in-place copies and the fact that a rung's four
doublings cannot overlap with anything.

## The three timeouts, and what each one taught

This is the part worth keeping, because P-256 and Ed25519 will meet it again.

`Spec.K256.Group.on_curve` and `peq` are transparent `let` definitions that
unfold into field equations modulo a seventy-eight digit prime.  Any SMT goal
that merely has them *in scope* pays for the field.  Three separate disasters
followed, each with a different remedy.

**One: an induction that mentions `peq`.**  The bridge from the ladder to
scalar multiplication is a `repeati` induction, and stating it over projective
equality made the inductive step run eight minutes and time out.  The remedy
was not a bigger rlimit but an abstraction: `spec/Spec.Group.Smul.fst` is a
commutative group as an abstract `noeq` record whose operation, membership
predicate and equivalence are *opaque function fields*.  Scalar
multiplication, all its congruences, the double-and-add ladder, and the
theorem that the ladder computes scalar multiplication are all proved there,
over the record projections, in **2.5 seconds**.  `spec/Spec.K256.Smul.fst`
then instantiates it with the eighteen lemmas of `Spec.K256.Group` and
connects `Spec.K256.point_mul` by a *definitional* equality of step functions
--- a proof of `()` --- plus `Loops.repeati_g_ext`.  That equality mentions no
equivalence at all, so it is free: **0.9 seconds** for the whole module.  An
eight-minute timeout became a second, and the abstract module is
curve-independent.

**Two: a bookkeeping predicate that exposes `peq`.**  The table lemma
"entries 0..n are correct" took five and a half minutes and timed out on a
goal as trivial as `dd == e`, because the predicate it quantified over
unfolded to the field.  `[@@"opaque_to_smt"]` on the predicate: thirty
seconds.

**Three, the expensive one: a Pulse *precondition* that mentions `peq`.**  The
four-doubling rung timed out on `2 * (4 * e) == 8 * e`.  Splitting the
function in two did not help.  Hoisting the arithmetic to the very first
statement of the body did not help either --- and that is the lesson: a Pulse
precondition is in scope for the *entire* body, so every goal in the function,
however arithmetic, carries it.  The remedy is to make the contract itself
opaque.  `rep a n p` --- "`a` is on the curve and is projectively equal to `n`
times `p`" --- and `oc p` are single `opaque_to_smt` predicates, and every
Pulse contract in `Hacl.K256.PointWin` mentions only `rep`, `oc`, and the
cheap limb bound `pt_ok`.  The field appears in six small pure lemmas and
nowhere else.  The module verifies in about seven minutes.

The general rule, stated once: **the expensive definitions must appear in
pure lemmas and never in a contract.**  Bundle whatever a contract needs to
say about them into one opaque predicate, and give that predicate an
introduction and an elimination lemma.

## Changes at the caller

A window does not produce the same representative the ladder did, so
`point_mul` and `point_mul_g` moved from concluding `pt … == K.point_mul …`
to concluding `on_curve … /\ peq … (K.point_mul …)`, and gained `on_curve` on
the input.  Three callers discharge the difference with the two escape
hatches already in `Spec.K256.Group`: `peq_to_aff_point` where the result is
about to be encoded, `peq_is_point_at_infinity` where it is about to be
tested.  `Hacl.K256.Encode` gained `lpt_on_curve`, which says a decoded point
is on the curve --- the one thing `load_point` checks anyway.  The old
bit-at-a-time step is deleted; `Hacl.K256.PointStep` keeps only
`set_infinity`.

## What is next

The gap that remains on secp256k1 is fixed-base.  Signing, verification and
secret-to-public all begin with a multiplication by the generator, where
HACL\* has a table compiled in and this does not, and that is exactly why
those three rows sit between 2.6x and 3.5x while variable-base ECDH is at
1.73x.  A compiled-in table of multiples of `g` is the single largest
remaining win on this curve.

---

## Part 26 — The P-256 window, and the fourth face of the transparency problem

### What was done

P-256's variable-base scalar multiplication now uses the same 4-bit window
secp256k1 got in Part 25: a sixteen-entry table of small multiples of the
input point, built at run time, read with the constant-time
`Hacl.Bignum.Base.table_select`, and consumed sixty-four rungs of four
doublings and one addition. 336 point operations where the bit-at-a-time
ladder needed 512.

Commits `b043ef3` (code) and `cd692df` (README), pushed to `origin/perf`.

### Measured

gcc, `-std=c11 -O3`, one core, the standing protocol:

| benchmark | before | after | HACL* | ratio before | ratio after |
|---|---|---|---|---|---|
| p256-dh-initiator | 401.4 us | 270.6 | 158.1 | 2.58x | **1.71x** |
| p256-dh-responder | 402.1 | 271.2 | 356.7 | 1.14x | **0.76x** |
| p256-ecdsa-sign | 416.8 | 286.6 | 170.6 | 2.47x | **1.68x** |
| p256-ecdsa-verify | 812.2 | 544.5 | 427.4 | 1.91x | **1.27x** |

clang agrees and is slightly kinder: 238.5 / 239.0 / 258.9 / 480.3, giving
1.53x / **0.67x** / 1.52x / 1.12x. Nothing else in either table moved; the
k256 rows reproduce Part 25 within noise (gcc 155.8 / 171.1 / 318.9 / 155.0)
and Ed25519 is untouched.

About a third off each operation, against the 26% the same change bought on
secp256k1. The difference is real and has a cause: P-256's addition formula
is Renes–Costello–Batina for `a = -3`, which is more expensive than the
`a = 0` pair secp256k1 uses, so the 176 operations the window saves were
worth more per operation.

**The responder row is the headline.** Variable-base ECDH on P-256 was 1.14x
HACL*'s portable C and is now 0.76x it. That is the first asymmetric
primitive in this repository that is *ahead* of the reference. It is ahead
for an unglamorous reason — HACL*'s P-256 has no window on the variable-base
side either, and our field multiply is now competitive — but it is ahead.

### What the port cost, and why

The spec side was free, exactly as designed. `Spec.Group.Smul` is the
abstract commutative group with the ladder theorem; `Spec.P256.Smul` is
`Spec.K256.Smul` with the eighteen lemmas of `Spec.P256.Group` substituted
in. **It verified in 1.0 seconds on the first attempt.** That is the whole
return on having written Part 25's spec abstractly, and it should repeat for
Ed25519.

The implementation side did not transfer so cleanly. The mechanically
narrowed `Hacl.P256.PointWin` — five limbs to four, `80sz` to `64sz` — ran
**thirty-eight minutes and failed**, where the k256 original takes seven and
passes. Three rounds of diagnosis:

1. **`pt_ok` is not free on a Montgomery field.** k256's is a limb bound.
   P-256's `felem v` unfolds to `Seq.length v == nl /\ bnd (vals v) base /\
   eval (vals v) < fmod.m`, and `fmod` is `mk P.prime 1 0xfffffffe0000...`.
   Wrapped it in an opaque `pok` with intro/elim. 38m31 → 22m49, error moved
   earlier.

2. **`ent`, the table bookkeeping predicate, was the runaway.** Same shape as
   Part 25's, but P-256 pays more for it: about twenty minutes on the goal
   `dd == e`. Made it `opaque_to_smt` and added an explicit `ent_same` lemma
   so the `else` branch is a lemma call rather than a bare `()`. A trimmed
   prefix went from **22 minutes to 5.6 seconds**.

3. **The real one: `rep` took a point.** `pt x y z = (fev x, fev y, fev z)`
   and `fev v = eval (vals v) * fmod.ri % fmod.m` — two seventy-eight-digit
   literals per coordinate, six per point. `win_dbl4` has five points in
   flight, so thirty such literals entered a query that needs none of them.
   Restating `rep` over the three limb *sequences* rather than over the
   point, and rewriting `rep_elim`, `ent`, `tok_get`, `rep_cong`, `dbl_ok`,
   `add_ok`, `succ_ok`, `zero_ok` and `win_done` to match, leaves `fev` named
   in exactly one small lemma (`rep_fcopy`, whose hypothesis is precisely
   what `fcopy` guarantees).

After (3): `win_dbl4` prefix **19m06 → 1m06**, and the whole module
**1m27** — faster now than secp256k1's seven and a half minutes, because
four limbs beat five once the field is out of the way.

### The lesson, in its fourth form

Parts 23–25 recorded three shapes of the same failure: an induction that
mentions `peq`; a bookkeeping predicate that exposes the field; a Pulse
precondition that mentions the field (fatal because a precondition is in
scope for the *entire body*, so hoisting does not help).

P-256 adds a fourth, and it is the subtlest because nothing in the *contract*
looks expensive. **On a Montgomery field, the coordinate projection itself is
expensive.** `pt` looks like a harmless tuple constructor. It is two
seventy-eight-digit literals per coordinate. The rule that falls out is: an
invariant should be stated over the *representation* the code manipulates —
limb sequences — and the translation to the mathematical object should happen
in one named lemma, not in the invariant.

### The technique: `--query_stats`

Worth writing down separately, because it is general. The symptom was a
module that ran twenty minutes with **every reported query at 0.00 seconds**.
That is the signature of a single *failing* query burning its entire rlimit:
successful queries are reported with their times, the failing one is reported
in the error, and the error's tail reads `unknown because canceled
(rlimit=...)`. A separate probe confirmed that loading all dependencies costs
0.4 seconds, so none of the time was startup.

Having localized it to "one query somewhere", bisection by **truncated
copies** found which: write prefixes of the file to scratch modules
(`Hacl.P256.PwA`, `PwB`, renaming the `module` line), run them in parallel
with `&` and `wait`. One 19-minute round instead of several 40-minute ones.

### Where the curves stand now

Every variable-base scalar multiplication on a prime curve has had its
window. What is left on the elliptic curves is:

- **Ed25519**, which has had neither half and is the largest absolute gap
  (sign 3.82x under gcc, 4.21x under clang). Its spec side should be nearly
  free from `Spec.Group.Smul`.
- **The fixed-base windows** for secp256k1 and Ed25519. secp256k1's
  secret-to-public (3.16x), signing (2.59x) and verification (3.48x) all
  begin with a multiplication by the generator against HACL*'s compiled-in
  table. This is the largest remaining win and also the hardest proof
  problem: `smul (d * 2^(64i)) g` cannot be unfolded, so it needs either a
  few compiled-in base points with run-time additions, or normalization of a
  256-step `repeati` over concrete field arithmetic. Not yet scoped.
- **P-256's special-prime field.** `p = 2^256 - 2^224 + 2^192 + 2^96 - 1`
  reduces by shifted subtractions rather than a multiply, the way secp256k1's
  radix-52 field now does. P-256 still uses the shared Montgomery core, and
  as Part 26 showed, the Montgomery representation costs proof time as well
  as run time.

---

## Part 27 — The Ed25519 window

Ed25519 was the last of the three curves still multiplying one bit at a time.
Its ladder ran 256 doublings and 256 additions per scalar and threw half the
additions away with a constant-time select.  The window here walks the scalar
four bits at a time against a sixteen-entry table of small multiples of the
input point, built at run time: 256 doublings, 64 additions, 15 additions to
build the table, and 64 constant-time table lookups over 16 x 20 limbs.

### Measured

gcc 13, clang 17, `-std=c11 -O3`, pinned to one core, three runs, 36/36 kept
in both tables.  Nothing outside Ed25519 moved.

| benchmark | gcc before | gcc after | HACL\* | ratio before | ratio after |
| --- | ---: | ---: | ---: | ---: | ---: |
| ed25519-keygen | 108.2 us | **84.8** | 31.7 | 3.40x | **2.67x** |
| ed25519-sign-64B | 248.3 | **200.0** | 64.4 | 3.82x | **3.11x** |
| ed25519-verify-64B | 248.5 | **202.7** | 77.3 | 3.24x | **2.62x** |

| benchmark | clang before | clang after | HACL\* | ratio before | ratio after |
| --- | ---: | ---: | ---: | ---: | ---: |
| ed25519-keygen | -- | **77.8** | 31.8 | -- | **2.45x** |
| ed25519-sign-64B | 270.5 | **191.3** | 65.1 | 4.21x | **2.94x** |
| ed25519-verify-64B | -- | **188.6** | 77.0 | -- | **2.45x** |

22% off key generation, 19% off signing and 18% off verification under gcc;
29% off signing under clang.  Less than secp256k1's 26% and P-256's 33%, and
the arithmetic says why.  The ladder costs 256 x (8 + 9) = 4352 field
multiplications; the window costs 256 x 8 + 79 x 9 = 2759, a 37% saving.  But
the ladder's per-step `point_select` moves 4 x 5 limbs 256 times, 5120 limb
copies, while the window's `table_select` moves 16 x 20 limbs 64 times, 20480.
The extra 15k conditional copies are most of the difference between 37% and
19%.  Ed25519's doubling is also relatively cheaper than the prime curves'
(8 multiplications against 9 for addition, where P-256's ratio is wider), so
replacing additions by doublings buys less.

### The spec side, third time

`spec/Spec.Ed25519.Smul.fst`, five seconds, clean on the first attempt.  This
is now the third instance of `Spec.Group.Smul` and the pattern has paid for
itself three times over: everything inductive -- scalar multiplication, its
congruences, the double-and-add ladder, and the theorem that the ladder
computes it -- lives once in the abstract commutative group, and an instance
is a record of eighteen fields plus a bridge.

Ed25519 needed one thing the prime curves did not.  Their `point_mul` is
indexed by a *number* and reads bit `i` by dividing by `2^i`, which is
literally the abstract `gbit`, so the bridge was a definitional equality.
Ed25519's is indexed by thirty-two *bytes* and reads bit `i` with
`Spec.Curve25519.ith_bit k i = (v k.[i / 8] / 2^(i % 8)) % 2`.  So the module
proves

    ith_bit k i == gbit (le_nat k) i

from `le_nat_split`, `le_nat_bound`, `lemma_div_plus` and `small_div`: the
bytes above `i / 8` contribute a multiple of 256 to `le_nat k / 2^(8j)`, and
`256 = 2^r * 2^(8-r)` is an even multiple for every `r < 8`, so they do not
reach bit `r`.  `nibble_of_bytes` is the same proof modulo 16, and needs
`i % 4 == 0` so that `r` is 0 or 4 and `8 - r >= 4`.  Both are arithmetic
about byte strings, mention no curve, and are therefore cheap -- which is the
entire point of having done the expensive half abstractly.

### The implementation, and a lesson applied rather than learned

`code/ed25519/Hacl.Ed25519.PointWin.fst`, ~700 lines, **1m21 on its first
complete run**.  It is `Hacl.P256.PointWin` widened from three coordinates to
four and from four limbs to five, with a byte-based nibble reader.

Part 26 ended with a rule: state the invariant over the *representation the
code manipulates* -- the limb sequences -- not over the mathematical object
they denote, and translate in one named lemma.  P-256 discovered that rule
halfway through, after a thirty-eight-minute timeout.  Ed25519 started with
it.  `rep` and `pok` are opaque from the first line, `entry` is
`opaque_to_smt`, and no Pulse precondition anywhere mentions a field element.
The module never once timed out.  That is the return on writing the lesson
down.

One new gotcha: `Hacl.Bignum.Base` exports a `copy` that shadows
`Hacl.Curve25519.Field.copy` at a different arity, and the error is
`Error 228 ... partially applied`.  A `module CF = Hacl.Curve25519.Field`
alias fixes it.  Opens are not transitive and shadowing order matters; this
is the third time that has cost time in this session.

### The genuinely new obligation

A windowed multiplication returns a point only *equivalent* to the one the
specification names, so every consumer of a multiple must be shown blind to
the difference.  `Spec.Ed25519.Group` anticipated two of the three:
`point_compress_congr` exists with a comment explaining that it is there for
a future windowed implementation, and `point_add_congr` exists for the table.

The third is new.  Verification ends in `point_equal sb (point_add rp ka)`,
and to know the boolean is the one the specification computes one needs
`point_equal_congr` -- derivable from reflexivity, symmetry and transitivity,
four applications -- which wants `on_curve` of the *specification's* points
as well as the computed ones.  For `[k]A` that means `on_curve A`, and `A` is
the public key, which arrives as thirty-two bytes and is decompressed.
Nothing in the library had ever needed to know that decompression lands on
the curve, and `Spec.Ed25519` does not say it.

So `Spec.Ed25519.Group.decompress_on_curve` now proves it.  `recover_x`
returns a square root of `(y^2 - 1)/(d y^2 + 1)`, which is the affine curve
equation solved for `x`; multiplying the extended equation through by the
denominator `v = d y^2 + 1` makes both sides `d y^4 + 1`, and `v` cancels
because it is nonzero by the guard in `recover_x`.  The sign flip at the end
of `recover_x` is invisible because `(-x)^2 = x^2`.

### The fifth instance of the same lesson, one level down

That proof is four lines of algebra and it first cost **twenty minutes** --
against a seven-second baseline for the whole of `Spec.Ed25519.Group`,
associativity included.  Bisecting with a sandboxed copy of the module found
it immediately: `curve_eq`, and nothing else.

Written over `Spec.Curve25519`'s `fadd`, `fsub` and `fmul`, every step puts
`prime` in scope of a degree-four nonlinear goal, and the solver tries to
reason about `2^255 - 19` itself.  Rewritten over an arbitrary positive
modulus `n` -- `sub_zero`, `zero_sub`, `mul_cong`, `cross`, `neg_sq_int` and
`curve_eq_gen` all take `n: pos`, and only the last two lemmas in the file
mention the curve at all -- the same statement takes **fifteen seconds**.
Z3 also needed three explicit hints for the degree-four ring identity
(`paren_mul_right` twice and a spelled-out factorisation); without them the
one assert burned its rlimit.

This is the same rule as the opaque invariants, moved down a level.  Parts 25
and 26 said: keep `on_curve` and `peq` out of the query.  Part 27 says: keep
the seventy-eight-digit *literal* out of the query, whatever the query is
about.  Generalising over the modulus is the cheapest way to do it, and it
costs nothing -- the general lemma is instantiated once.

### Tidying

`Hacl.Ed25519.Point` loses `point_mul` and `point_mul_step`, now dead, and
shrinks from 471 lines to 300.  The three places that compress a multiple of
the generator -- key generation, the nonce commitment `R`, and the public key
inside signing -- became one function, `point_mul_g_compress`, so the
congruence argument is made once rather than three times.  gcc's
specialisation set changed by one in each direction as a result
(`point_compress` lost, `point_double` gained), which is the expected churn
when a call site count changes; the baseline is 66 now.

`make verify` is 6m56 with three windows in the tree.  All RFC 8032 vectors
pass.  Commits `070aca6` (code) and `3f339f1` (README), pushed to
`origin/perf`.

### What is left

The fixed-base window, on secp256k1 and Ed25519, is now the only structural
gap on the curves and the largest single gap in the library.  Every row that
starts from the generator -- k256 secret-to-public 3.13x, k256 sign 2.58x,
ed25519 keygen 2.67x, ed25519 sign 3.11x -- is behind for exactly that one
reason, and the variable-base rows next to them (k256 ECDH 1.71x, p256 DH
responder 0.76x) show what closing it is worth.  The hard part is proving a
*compiled-in* table of multiples of `g` correct: `smul (d * 2^(64i)) g`
cannot be unfolded, so it wants either a handful of compiled-in base points
and run-time additions, or normalisation of a 256-step `repeati` over
concrete field arithmetic.  Still not scoped.

---

## Part 28 — The Ed25519 fixed-base window

### What was wrong

Ed25519 signs and generates keys by multiplying a point that is fixed at
compile time.  Until this part it did so with the *variable*-base window
of Part 27: two hundred and fifty-six doublings and sixty-four additions
to walk a scalar that was always going to be multiplied into the same
generator, plus fifteen additions to build a table of small multiples of
a point that never changes.  HACL\* has a table compiled into the binary;
this is the last structural gap between the two.

### The idea

Split the scalar into four sixty-four-bit pieces,

```
k = k0 + k1 2^64 + k2 2^128 + k3 2^192
```

so that

```
k G = k0 G + k1 (2^64 G) + k2 (2^128 G) + k3 (2^192 G)
```

and walk the four pieces *together*.  Sixteen rungs suffice rather than
sixty-four, each four doublings and four additions, because the same
doubling chain serves all four pieces.

| | doublings | additions | table | total |
| --- | ---: | ---: | ---: | ---: |
| ladder (Part 26) | 256 | 256 | 0 | 512 |
| variable-base window (Part 27) | 256 | 64 | 15 | 335 |
| fixed-base window (this part) | 60 | 64 | 60 | 184 |
| all four tables compiled in | 60 | 64 | 0 | 124 |

The fourth row is "Plan A": 124 operations, but 256 field constants in
`Hacl.Ed25519.Tables` rather than 9.  It was rejected for now, and the
upgrade is a change to the first twenty lines of the implementation.
"Four separate windowed multiplications, then add" was also considered
and is 367 operations — *worse* than doing nothing.  Sharing the doubling
chain is the whole of the win.

A cost model fitted to the two measured points of Part 27 —
`t = A·ops + b·limb-copies + C` with `A ≈ 0.158 us/op`, `C ≈ 25 us` for
the hash, the inversion and the compression — predicted 60 us for key
generation.  The measurement came in at 60.7.

### Saying what a constant is

The three extra base points have to be in the binary, and this is the
part with no precedent in the repository.  `[2^64] G` is
two-to-the-sixty-fourth additions; `smul` cannot be unfolded and the
solver has no idea what the number is.

The answer is to state it as a doubling **chain**.  `Spec.Group.Smul`
gains

```
dblk (g: grp 'a) (n: nat) (p: 'a) : 'a          (* n doublings *)
dblk_ok : eqv (dblk n q) (smul (pow2 n * m) p)  (* given eqv q (smul m p) *)
```

and the normaliser evaluates `dblk eg 64 g` on concrete field elements at
typechecking time.  Sixty-four Ed25519 doublings take about a second; a
probe measured eight at 0.9 s and a hundred and ninety-two at 37 s, which
is what made the design viable at all.  The normaliser sees through the
record-literal projection `eg.dbl -> point_double` without help.

Three decisions made this cheap:

1. **Chain the chains.**  `b2` is stated as sixty-four doublings of `b1`,
   not a hundred and twenty-eight of `g`.  Sixty-four doublings three
   times rather than one, two and three times: 64 evaluations against
   384.

2. **Store affine representatives** `(x, y, 1, x·y)` rather than whatever
   quadruple the chain produces.  Nothing requires the same quadruple —
   `point_equal` is projective equality and the normaliser decides it on
   concrete numbers just as readily.  Three nontrivial constants per base
   point instead of four, `z` a literal one, and both

   ```
   assert_norm (point_equal b1 (G.dblk SM.eg 64 g))
   assert_norm (on_curve b1)
   ```

   decided by the normaliser.  **No SMT query ever sees a base point.**

3. **`opaque_to_smt` on the nine coordinates.**  This one was learned the
   hard way.  With the literals visible, the wholly routine
   limb-extraction lemmas of `Hacl.Ed25519.Tables` — five `assert_norm`s
   and a five-way dispatcher per constant, a pattern that has worked
   since Part 3 — began timing out: first one dispatcher, then, after the
   rlimit was raised, a different one, with the module taking over twenty
   minutes.  Nine two-hundred-and-fifty-bit literals sharing one SMT
   context is enough to poison lemmas that have nothing to do with them.
   Hidden, the module is back to 42 seconds, and no rlimit anywhere was
   raised.

This is the fifth form of the session's central lesson, and the second at
the level of literals: *the normaliser and the solver want different
things, and a constant that only the normaliser needs should be invisible
to the solver.*

### Sharing the window

`Hacl.Ed25519.PointWin`'s table layer now carries a scale.  Entry `d` of
the `j`-th table has to be described as the `d 2^{64j}`-th multiple of
`G`, **not** as the `d`-th multiple of `2^{64j} G`, because it is `G`
that the answer is a multiple of and there is no route from one reading
to the other that does not go through associativity of `smul` — a theorem
the abstract group does not have and which would cost an induction over
the equivalence to get.  Carrying the scale through `ent`, `tok`,
`build_table` and `win_add` costs one extra parameter; the variable-base
window passes `n = 1` and the two readings coincide.  The table build's
`succ_ok` is subsumed by `add_ok` and was deleted.

### Two timings worth recording

**Nonlinear arithmetic in a loop with the addition law in scope.**  The
generalised `build_table` needs `vd * n + n == (vd + 1) * n` to
re-establish its invariant.  Asked for inline, the module went from
1m33 to **over twenty minutes**.  Hoisted into

```
let mul_zero (b: nat)   : Lemma (0 * b == 0)                = ()
let mul_succ (a b: nat) : Lemma (a * b + b == (a + 1) * b)  = ...
let mul_one  (a: nat)   : Lemma (a * 1 == a)                = ()
```

— three one-line lemmas proved where nothing else is in scope — it is
2m59.

**A failing proof is not a slow proof.**  `build_tables` was left running
for twenty-eight minutes twice, and the whole implementation module was
split in two on the theory that its verification condition was too large.
The split was worth making anyway, but it was not the problem: the
generator's `fmul` was called before the `felem` facts about its operands
were in scope, and the twenty-eight minutes were Z3 grinding on something
unprovable.  With the two lemma calls moved three lines earlier the same
function verifies in **28 seconds**.  Before assuming a proof is hard,
check that it is true.

### Shape

`point_mul_g_win` is three functions, not one:

- `build_tables` — the four base points staged through one quadruple of
  scratch arrays, each dead as soon as its table is built;
- `win_loop` — sixteen rungs, invariant `rep acc (hi k i) g` where
  `hi k i` is the four pieces of `k` each shifted right by `4i` and
  weighted by its base point;
- `point_mul_g_win` — allocation, and two calls.

Between them they name thirty-two arrays.  The digit arithmetic — that
`hi k 16 = 0`, that `hi k 0 = k`, and that
`hi k i = 16 hi k (i+1) + Σ_j dig(k,j,i) 2^{64j}` — is pure natural-number
reasoning in `Spec.Ed25519.Base` with no curve in scope, and even there
the step lemma needed its regrouping spelled out
(`(16q + d) w == 16 (q w) + d w`, three times) to go from a five-minute
grind to a second.

### Measured

gcc, `-std=c11 -O3`, one core, 36/36 runs kept:

| benchmark | Part 27 | now | HACL\* | ratio |
| --- | ---: | ---: | ---: | --- |
| ed25519-keygen | 84.8 us | **60.7** | 31.8 | 3.40x → **1.91x** |
| ed25519-sign-64B | 200.0 | **153.9** | 65.4 | 3.82x → **2.35x** |
| ed25519-verify-64B | 202.7 | **187.5** | 76.4 | 3.24x → **2.46x** |

clang, 28/36 runs kept:

| benchmark | Part 27 | now | HACL\* | ratio |
| --- | ---: | ---: | ---: | --- |
| ed25519-keygen | 77.8 us | **51.3** | 31.8 | 2.45x → **1.61x** |
| ed25519-sign-64B | 191.3 | **139.0** | 65.1 | 2.94x → **2.13x** |
| ed25519-verify-64B | 188.6 | **165.1** | 76.9 | 2.45x → **2.15x** |

Verification moves least because only one of its two multiplications is
fixed-base.  Nothing outside Ed25519 moved: k256 ECDH 153.9/1.70x, k256
sign 171.7/2.63x, k256 verify 318.9/3.54x, k256 secret-to-public
155.4/3.16x, p256 dh-initiator 271.0/1.74x, p256 dh-responder
270.2/**0.76x**, p256 sign 286.7/1.68x, p256 verify 549.7/1.27x.

Key generation at 1.91x is the closest Ed25519 has ever been, from 3.40x
two parts ago.  All RFC 8032 vectors pass; one new compiler specialisation
(`Hacl_HPKE_Labeled_labeled_expand_impl__t`) was taken into the baseline.

### Next

secp256k1 wants the same treatment — `secret-to-public` is 3.16x and
signing 2.63x, and both are dominated by a fixed-base multiplication that
is still variable-base code.  The proof machinery is now entirely reusable:
`dblk`/`dblk_ok` are in the abstract group, and `Spec.K256.Smul` already
instantiates it.

---

## Part 29 — The secp256k1 fixed-base window

Roadmap item 4, second curve.  Ed25519's fixed-base window was Part 28;
this is the same construction on secp256k1, and it was a port rather than
a design.  The interesting content is not the speedup, which came out
where it was predicted, but the two places where the port did *not* go
through and why.

### What was built

Four modules, two of them new to the library and two of them the second
copy of something Ed25519 already had.

`spec/Spec.Group.Split4.fst` is `Spec.Ed25519.Base`'s digit section moved
out whole.  `dig`, `part`, `hi`, `digs`, and the three facts that `hi`
starts at zero (`hi_top`), ends at the scalar (`hi_bot`) and multiplies by
sixteen and adds four digits at each rung (`hi_step`).  None of it mentions
a curve and none of it is specific to a group; it is arithmetic about a
256-bit natural number split four ways.  Moving it cost one line — `hi_bot`
needed `assert_norm (pow2 0 == 1)` once the base-point literals were no
longer in the same file to supply it by accident, which is a small instance
of the same lesson as everything else here.

`spec/Spec.K256.Base.fst` says what `2^64 G`, `2^128 G` and `2^192 G` are.
Six `[@@"opaque_to_smt"]` coordinates, three affine points `(x, y, 1)`, and
three `q{j}_ok` lemmas each of which is two `assert_norm`s (the chain and
the curve equation) and one application of `Spec.Group.Smul.dblk_ok`.  The
chains are linked — `q2` is sixty-four doublings of `q1`, not a hundred and
twenty-eight of `g` — so the normaliser does sixty-four secp256k1 doublings
three times rather than one, two and three times.  It verifies in about a
minute, which is comparable to Ed25519's twenty-eight seconds once the
larger prime is accounted for.

Six constants, not nine: a projective point has three coordinates where an
extended twisted-Edwards point has four, and the third is a literal one.

`code/k256/Hacl.K256.Tables52G.fst` holds their limbs.  secp256k1's constant
idiom is much shorter than Ed25519's — `lit_limbs` and `mk_static_array`,
five lines apiece, against a list, a seq, five `*_at_k` lemmas, a dispatcher
and an `*_ok` — so this is under a hundred and fifty lines.

`code/k256/Hacl.K256.PointMulG.fst` is the window: `g_rep`/`q{1,2,3}_rep`,
`hi_start`, `hi_end`, `rung_step`, `shift_ok`, `dig_at`, `load`, `rung`,
`build_tables`, `win_loop`, `point_mul_g_win`.  Structurally identical to
`Hacl.Ed25519.PointMulG`, one coordinate narrower throughout.

`Hacl.K256.PointWin`'s table layer gained a scale exactly as Ed25519's did
(`ent`, `tok`, `build_table`, `win_add` all take an `n`; `rep_one` added,
`succ_ok` deleted), and `Hacl.K256.PointMul.point_mul_g` became a one-line
wrapper.

### What it bought

gcc, 36/36 runs kept:

| benchmark | before | after | HACL\* | ratio before | ratio after |
| --- | ---: | ---: | ---: | --- | --- |
| k256-secret-to-public | 155.4 us | **111.0** | 48.9 | 3.16x | **2.27x** |
| k256-ecdsa-sign | 171.7 | **126.3** | 66.1 | 2.63x | **1.91x** |
| k256-ecdsa-verify | 318.9 | **270.5** | 89.9 | 3.54x | **3.01x** |
| k256-ecdh | 153.9 | 154.8 | 90.3 | 1.70x | 1.71x |

clang, 34/36 runs kept: `secret-to-public` **111.8** (2.26x), signing
**131.3** (2.01x), verification **262.9** (2.91x), ECDH 149.7 (1.67x).

The ECDH row is the control.  It is genuinely variable-base, nothing in
this change touches it, and it did not move; the other three did.  The
three that moved are exactly the three that begin with a multiplication by
the generator, and verification, which does one fixed-base and one
variable-base multiplication, moved by about half as much as the two that
do only fixed-base — 15% against 28% and 26%.  That is the arithmetic
working out: 184 point operations against 335 on one of the two halves.

Ed25519 was re-measured in the same tables and is unchanged within noise
(keygen 61.5/1.94x gcc, 50.7/1.59x clang).

### Eight literals in one context

The first attempt put the six new constants in `Hacl.K256.Tables52`, beside
the generator's two.  The file had been taking about sixty seconds.  With
eight it ran for **eighteen minutes** and was killed without finishing.

This is Part 28's lesson again and it is worth restating because the
mechanism is not obvious.  Every one of the coordinates is
`opaque_to_smt`, and everything asserted about them is settled by the
normaliser — `assert_norm (leval q1x_list == <literal>)`,
`assert_norm (KB.q1x == <literal>)`.  The solver is never asked to compute
with them.  But an `assert_norm` leaves its conclusion in scope as a
hypothesis, and its conclusion contains the literal.  Eight
two-hundred-and-fifty-six-bit numbers sitting in the context of every query
the file asks afterwards is enough to stop it terminating, even though no
query is *about* them.

Moving them to `Hacl.K256.Tables52G`, a module whose entire content is those
eight blocks: **two seconds**.

The remedy is now routine and the diagnosis should be too.  If a file that
was fast becomes slow when constants are added to it, the constants are the
problem even if nothing uses them.

### A failing proof is still not a slow proof, but neither is a rebuild

Part 28's lesson cost twenty-eight minutes twice.  This time it nearly cost
more, in a new disguise.  Three successive attempts to verify
`Hacl.K256.PointMulG` — first the whole file, then with everything after the
spec section deleted, then with everything but the module header deleted —
each ran past ten minutes with no output.  A module header cannot take ten
minutes, so the conclusion "something is pathologically wrong with the
imports" was tempting and wrong.

Running `make` without piping the output showed it immediately:

```
  CHECK          Hacl.K256.Tables52.fst
  CHECK          Hacl.K256.Field52.fst
  CHECK          Hacl.K256.Point.fst
  CHECK          Hacl.K256.PointStep.fst
  CHECK          Hacl.K256.PointWin.fst
```

Removing the constants from `Hacl.K256.Tables52` had invalidated its
`.checked`, and every k256 module downstream of it was being re-verified,
serially, ahead of the file under test.  None of the three "hangs" had
reached `Hacl.K256.PointMulG` at all.

Two process notes follow.  Never pipe a long build through `tail` while
diagnosing; the per-module progress is the diagnosis.  And a single-target
`make` is not a single-module check when a dependency has changed — use
`make verify -j16`, which at least does the rebuild in parallel.

### Nonnegativity of a product, at every call site

`win_add`'s postcondition is `rep a (e + d * n) p`, and `rep`'s second
argument is a `nat`.  So every call has to establish `d * n >= 0`.  Both
factors are naturals, so this is true by definition of `nat`, and F\* will
find it — in a small context.  In `point_mul_win`'s loop, whose context
carries the complete addition law and a sixteen-entry table invariant, the
query

```
16 * (kv vk / pow2 (v vj)) + kv vk / pow2 (v j2) % 16 * 1 >= 0
```

times out.

This is the fourth member of the scale-arithmetic family and it joins the
other three:

```
let mul_zero (b: nat) : Lemma (0 * b == 0) = ()
let mul_succ (a b: nat) : Lemma (a * b + b == (a + 1) * b)
  = Math.distributivity_add_left a 1 b
let mul_one  (a: nat) : Lemma (a * 1 == a) = ()
let mul_nat  (a b: nat) : Lemma (a * b >= 0) = Math.nat_times_nat_is_nat a b
```

`mul_nat` has to be called before *every* `win_add` — once in the
variable-base window and four times per rung in the fixed-base one.  Five
one-line lemma calls; without them the module does not verify at any rlimit
that finishes.

The first attempt at this appeared to pass and then failed on a rerun,
which is the classic signature of a query that is right at the rlimit.  A
proof that passes once is not a proof that passes.

### Index arithmetic, hoisted

The same treatment, applied pre-emptively, to the loop's index facts.  Each
rung reads four nibbles, at bit positions `4i`, `4i + 64`, `4i + 128` and
`4i + 192`, and for each of the four `adigit` wants "under 256 and divisible
by four" while `SZ.mul`/`SZ.add` want "fits in a `size_t`".  Twelve facts,
every one of them trivial, asked for in a body that also carries the
addition law.  Asked inline they cost more than the rung.

```
let shift_ok (i: nat { i < 16 })
  : Lemma (i * 4 >= 0 /\ i * 4 < pow2 32 /\ ... /\
           i * 4 + 192 < 256 /\ (i * 4 + 192) % 4 == 0)
  = assert_norm (pow2 32 > 256)

let dig_at (k: nat) (i: nat { i < 16 }) (j: nat { j < 4 })
  : Lemma (Split.dig k j i == k / pow2 (i * 4 + 64 * j) % 16) = ()
```

`dig_at` exists only to commute `64 * j + 4 * i` into `i * 4 + 64 * j`,
which is the form `adigit`'s postcondition arrives in.  One product
commutation.  In a small context it is free; in the rung's context it was
the difference between verifying and not.

The whole module verifies in about half an hour, most of it `win_loop`.
That is slow but it is the same order as `Hacl.Ed25519.PointWin`'s nine
minutes and `Hacl.K256.PointWin`'s twelve, and the shapes are the same.

### Where the curves stand

P-256 is now the only curve here still walking the generator bit by bit,
and the four modules it would copy have each been written twice.  Its
`dh-initiator` is 1.74x, its signing 1.68x and its verification 1.27x, so
the return is smaller than it was on either of the other two — P-256's
variable-base ECDH is already *faster* than HACL\*'s at 0.76x, which says
the field and the window are both in good shape and only the compiled-in
table is missing.  The other outstanding P-256 item, the special-prime
reduction, is probably worth more.

Remaining, in rough order of value: the P-256 special-prime field; Plan A
for Ed25519 and secp256k1 (compile the four sixteen-entry tables in rather
than building them, a further ~30%, at 256 and 192 field constants
respectively); one GF(2^128) reduction per four GHASH blocks; the P-256
fixed-base window; the remaining compiler specialisations; `mont_mul` for
RSA and FFDHE.

---

## Part 30 — The P-256 fixed-base window, and what the third copy costs

Roadmap item 4, third and last curve.  Part 28 was Ed25519, Part 29 was
secp256k1, and this is the same four modules on P-256.  There is nothing
new in the construction.  What is worth recording is that there is nothing
new in the construction — the whole of this part went through on the first
attempt, and the measurement at the end is the largest of the three.

### The result

gcc, 35/36 runs kept:

| benchmark | before | after | HACL\* | ratio before | ratio after |
| --- | ---: | ---: | ---: | --- | --- |
| p256-dh-initiator | 271.8 us | **165.3** | 158.8 | 1.73x | **1.04x** |
| p256-ecdsa-sign | 286.9 | **181.7** | 168.9 | 1.69x | **1.08x** |
| p256-ecdsa-verify | 547.7 | **448.7** | 426.6 | 1.27x | **1.05x** |
| p256-dh-responder | 272.3 | 274.9 | 356.4 | 0.77x | 0.77x |

clang, 31/36 runs kept:

| benchmark | after | HACL\* | ratio |
| --- | ---: | ---: | --- |
| p256-dh-initiator | 151.3 us | 155.9 | **0.97x** |
| p256-ecdsa-sign | 172.2 | 169.4 | **1.02x** |
| p256-ecdsa-verify | 392.6 | 429.2 | **0.91x** |
| p256-dh-responder | 241.1 | 355.0 | **0.68x** |

Under clang, three of P-256's four operations are now *faster* than HACL\*'s
portable C and the fourth is within 2%.  Under gcc all four are within 8%.
That the two compilers disagree about which side of 1.0x three of these rows
fall on is the right way to read them: whatever is left is not algorithmic.

`dh-responder` is the control — it is variable-base, nothing here touches
it, and it did not move.

P-256 gained more from the window than either of the other two curves, and
for a reason worth stating because it predicts where this kind of work pays.
The window saves the same 151 point operations on every curve (335 → 184).
What differs is what a point operation costs relative to everything else in
the benchmark, and P-256's Renes–Costello–Batina addition is the most
expensive of the three.  Against that, P-256 started closest to the
reference, so the same absolute saving is a larger fraction of the remaining
*gap*: 1.73x → 1.04x closes 95% of it where secp256k1's 3.16x → 2.27x closed
41%.

Cumulatively, P-256 ECDH has gone 401 us → 271 (variable-base window) → 165
(fixed-base window), against HACL\*'s 159.  Signing has gone 417 → 287 →
182 against 169.  Neither has ever had a field change: both are still on the
shared four-limb Montgomery core.

### The third copy

Every module verified on the first attempt:

| module | lines | time |
| --- | ---: | ---: |
| `Hacl.P256.PointWin` (scaled by `n`) | ~730 | 1m40 |
| `spec/Spec.P256.Base.fst` | ~140 | 46 s |
| `code/p256/Hacl.P256.TablesG.fst` | ~140 | 10 s |
| `code/p256/Hacl.P256.PointMulG.fst` | ~600 | 45 s |
| `Hacl.P256.PointMul` (one-line wiring) | — | seconds |

The comparison that matters is `Hacl.P256.PointMulG` at 45 seconds against
`Hacl.K256.PointMulG` at about twenty minutes.  Same file, same lemmas, same
four hundred lines of Pulse contract.  Two things account for the
difference, and both are lessons already in this report being collected
rather than learned.

First, P-256's `Hacl.P256.PointWin` states its invariants over the limb
*sequences* rather than over the points they read as.  That was forced, back
in Part 21, by P-256's Montgomery field: `pt x y z` is three applications of
`fev`, and `fev v` is `eval (vals v) * R^-1 mod p`, so a rung with five
triples in flight puts thirty seventy-eight-digit literals into a context
that needs none of them. secp256k1, whose field is direct, could afford
`rep` over points and took it.  The fixed-base window inherits whichever
convention its curve's variable-base window chose, and P-256's — adopted
under duress — is the better one.  Its rung's verification condition
mentions no field at all.

Second, everything expensive was already written.  `Spec.Group.Split4` was
lifted out of Ed25519 in Part 29 and reused here without a character
changed.  `mul_zero`/`mul_succ`/`mul_one`/`mul_nat`, `shift_ok` and `dig_at`
were each discovered the hard way once and transcribed twice.  The separate
constants module was discovered the very hard way once — eighteen minutes
and a kill — and is now the first thing written rather than the last.

The honest summary of the three curves is: Ed25519 cost two days and taught
the lessons, secp256k1 cost a day and re-taught one of them in a sharper
form, P-256 cost an afternoon and taught nothing.  That is the shape one
wants, and it is an argument for doing the third instance of anything.

### Montgomery constants

The one genuinely new thing is small.  P-256's field runs in Montgomery
form, so the compiled-in base points cannot be stored as coordinates:
`Hacl.P256.Field.fconst a x` requires

```
vals (G.static_array_elems a) == limbs (x * pow2 256 % P.prime)
```

and returns an array carrying `fev v == x`.  So the split between
`Spec.P256.Base` and `Hacl.P256.TablesG` falls in a natural place —
`Spec.P256.Base` says what the *curve points* are, in coordinates, with
`assert_norm` deciding the chain equation and the curve equation on them;
`Hacl.P256.TablesG` says what the *limbs* are, and its `assert_norm` carries
the multiplication by `R`.  Neither module ever asks the solver to compute
with either.

This also sharpens the case for the separate module.  On secp256k1 the eight
literals that killed `Hacl.K256.Tables52` were the coordinates themselves.
Here each `assert_norm` is `q1x * pow2 256 % prime == <literal>` — the
literal, *and* a product with `2^256`, *and* a reduction modulo a
seventy-eight-digit prime, twelve of them.  Put in `Hacl.P256.Tables` beside
the eight existing constants they would almost certainly not have
terminated.  In their own module: ten seconds.

### Where the library stands on curves

| | field | variable-base | fixed-base | worst ratio (gcc) |
| --- | --- | --- | --- | ---: |
| X25519 | radix 2^51 | ladder | n/a | 1.25x |
| Ed25519 | radix 2^51 | 4-bit window | 4-way split | 2.45x |
| secp256k1 | radix 2^52, special prime | 4-bit window | 4-way split | 2.87x |
| P-256 | radix 2^64 Montgomery | 4-bit window | 4-way split | 1.08x |

P-256 is now the *best* of the four against the reference despite having the
only unspecialised field, which is a comment on how much of an elliptic
curve's time is scalar multiplication and how little is the field, once the
field is merely reasonable.

Two things remain available and both are now well understood:

- **Plan A**, on all three curves: compile the four sixteen-entry tables in
  rather than building them at run time.  That removes the sixty additions
  of the table build from 184, a further ~30%, at 256 field constants for
  Ed25519 and 192 for each of the Weierstrass curves.  Given the above, each
  would want a module of its own, and possibly several.
- **P-256's special-prime field**, the last item on P-256's list.
  `p = 2^256 - 2^224 + 2^192 + 2^96 - 1` reduces by shifted subtractions
  rather than a multiply.  secp256k1's equivalent was worth about 25% of its
  ECDSA operations.  It is a larger project than either of the window
  changes — Part 29's secp256k1 field took five modules of new specification
  — and with P-256 already at 1.04x it now buys less than it would have a
  month ago.

Past the curves, the queue is: one GF(2^128) reduction per four GHASH
blocks; the sixty-seven remaining compiler specialisations; and `mont_mul`
windowing for RSA and FFDHE modexp, which at 1.26x is now the largest
remaining ratio in the library that is not AES-GCM or a vectorised hash.

---

## Part 31 --- The flat cost: AESKEYGENASSIST and the AES key schedule

### The shape of the number

AES-GCM has been the largest gap in the table for a long time, and the
number everyone quoted was the bulk one: 4.58x EverCrypt's Vale assembly at
256 KiB.  That is where roadmap item 2 points --- one GF(2^128) reduction per
four GHASH blocks --- and it is a real target, because a probe decomposing
the call puts GHASH at 2.11 cycles per byte against 1.58 for the counter
mode, which makes GHASH 57% of bulk AES-GCM and about four times slower than
a good deferred-reduction pclmul implementation.

But the table had a second number in it that nobody had looked at:

| bytes | us | MB/s | cyc/B |
|---:|---:|---:|---:|
| 0 | 4.698 | --- | --- |
| 64 | 4.800 | 13.3 | 225 |
| 1024 | 5.955 | 172.0 | 17.45 |
| 16384 | 23.887 | 685.9 | 4.37 |
| 262144 | 328.178 | 798.8 | 3.76 |

A zero-length AEAD call cost 4.698 microseconds.  Sixty-four bytes cost
4.800.  The difference is 0.102 microseconds for sixty-four bytes of actual
work, and 4.698 microseconds of something else --- roughly fourteen thousand
cycles, paid unconditionally, on a call that may have nothing to encrypt at
all.  Against the reference that is 77.45x at sixty-four bytes and 18.16x at
a kilobyte, and essentially all of it is this.

### Finding the cause without a profiler

`perf` is not installed in this environment, and the internals of
`Hacl.AES.GCM` are `static` in the generated C, so the usual approaches were
both unavailable.  What was available was reading the code and then finding a
measurement that could only come out one way if the reading was right.

`Hacl.AES.Core.sbox_impl` is:

    sbox x = affine (ginv x)

with `ginv` the inverse in GF(2^8) computed as *a^254* --- an addition chain
of fifteen `fmul_impl`s, each of which is seven `xtime_impl`s and eight
`fmul_step`s.  So one S-box is on the order of three hundred and fifty
operations, and because the addition chain is a chain, on the order of three
hundred and fifty *cycles*.  `Hacl.AES.Key.ks_word_impl` calls it four times
per expanded word.  AES-128 expands ten words, AES-256 thirteen --- but
AES-256's schedule also applies `SubWord` without the rotation at `i mod 8 =
4`, so the counts are 40 and 52 S-boxes respectively.

That gives a prediction with no free parameters.  If the fixed cost is
entirely the S-box, then

    cost(AES-256) / cost(AES-128) = 52 / 40 = 1.300

Measured:

    aes128-gcm empty          4.681 us     14044 cyc
    aes256-gcm empty          6.096 us     18289 cyc

    18289 / 14044 = 1.302

Nothing else in a GCM call --- not the IV handling, not `hkey_impl`, not
`j0_impl`, not the tag --- differs between the two key sizes in that ratio.
Three significant figures of agreement on a ratio predicted from source
reading is as good as a profile.

It also settles the "is it really the key schedule and not `hkey_impl`"
question that the previous segment left open, which was the right question to
ask: `hkey_impl` encrypts a block of zeroes, and a block encryption is the
same work at both key sizes up to the round count, 10 against 14, which is a
ratio of 1.4 and not 1.3.

### Why the S-box is algebraic, and why that must not change

The obvious fix is a 256-byte table, which is four cycles.  It is not
available.  The key schedule's input is the *key*, so a table indexed by a
byte of the key is a cache-timing oracle on the key --- the textbook AES
side channel, and precisely the thing this library's secret-integer layer
exists to make unwriteable: `Hacl.Secret.UInt8.t` has no `index` at all, so
the table-driven version cannot be typed here even if someone wanted it.

The algebraic S-box is therefore correct, and correct at a price, and the
price is only visible because it is paid in the one place that had never been
measured.

### The instruction, and the reason it had been passed over

`AESKEYGENASSIST` computes, for two of the four input words, `SubWord` and
`RotWord(SubWord(_))`, the latter exclusive-ored with an 8-bit immediate
round constant.  It is constant-time and it is exactly the instruction the
hardware provides for this problem.

The previous note in the README said:

> The key schedule is still the portable one.  It runs once per message
> rather than once per block, and `AESKEYGENASSIST` takes a round constant as
> an immediate, so it would need one extern per round.

Both halves of that are true and both are the wrong conclusion.  "Once per
message" is only cheap if messages are large; the benchmark sweeps down to
sixty-four bytes and nobody read that row.  And the immediate does need one
extern per value --- *unless the value is zero*.  With a zero round constant
the instruction is nothing but `SubWord`, and `Hacl.AES.Key` already carries
the round constant in a register and exclusive-ors it in by hand, a shape
that fell out of counting the key schedule in bytes rather than in words
(Part 1's `rcidx b = ceil(b / keylen)` invariant).  So the round constant
never needed to come from the instruction at all, and one binding serves
every round of both key sizes.

### The axiom

Four lanes are defined; only one is used, so only one is stated.

    assume val subword (a: t)
      : r: t { forall (i: nat). i < 4 ==>
                 Seq.index (bv r) (8 + i) == sbox (Seq.index (bv a) (12 + i)) }

Verified in C first, before any F* was written, against a transcription of
the FIPS 197 table: bytes 8..11 of `_mm_aeskeygenassist_si128(a, 0)` are the
S-box of bytes 12..15 of `a`.  (Bytes 0..3 are the S-box of bytes 4..7, and
12..15 and 4..7 are the rotated copies.  A weaker postcondition than the
truth is sound for an `assume val` and easier to test.)

### The module

`code/aes/Hacl.AES.SubWord.fst`, about 150 lines, verified in 11 seconds.
Three functions with identical specifications:

- `subword_ni` --- write the four bytes at offsets 12..15 of a caller-owned
  sixteen-byte scratch block, `Vec.load`, `Vec.subword`, `Vec.store`, read
  back offsets 8..11.
- `subword_portable` --- four `sbox_impl`s into offsets 8..11.
- `subword4` --- `if Vec.supported () { ... } else { ... }`.

This is the same three-function shape as `Hacl.AES.Block`, for the same
reason: the two paths have the same postcondition, so the dispatcher has
nothing to prove, and no caller can tell which ran.

`Hacl.AES.Key` then changed by replacing

    let t0 = bxor (sbox_impl p1) rc;
    let t1 = sbox_impl p2;
    let t2 = sbox_impl p3;
    let t3 = sbox_impl p0;

with

    SW.subword4 sb p1 p2 p3 p0;
    ... vals_index sb 8..11 ...
    let t0 = bxor A.(sb.(8sz)) rc;
    let t1 = A.(sb.(9sz));
    ...

and threading a sixteen-byte scratch array down from `key_expansion_impl`.
It reverified in 1m24 on the first attempt with no change to any proof ---
because the specification of the four bytes is literally the same four
`sbox` applications it was before.  The scratch block is the caller's so that
a whole schedule allocates once and branches thirteen times rather than
thirteen allocations.

### Two things that went wrong

**The refinement did not survive the Pulse binding.**  `Vec.subword` returns
a refined type, but at `--ifuel 0` the quantified postcondition was not in
scope after Pulse bound the result to a variable; the proof state showed
`squash (r == Hacl.Vec128.subword a)` and nothing else.  The fix is a pure
lemma in a context where the refinement *is* visible:

    let subword_index (a: Vec.t) (i: nat { i < 4 })
      : Lemma (Seq.index (Vec.bv (Vec.subword a)) (8 + i) ==
               sbox (Seq.index (Vec.bv a) (12 + i)))
      = ()

called four times.  This is the second time a quantified refinement on an
`assume val` has had to be instantiated by hand; worth remembering as an
idiom rather than rediscovering.

**`inline_for_extraction` destroyed the target attribute.**  `subword_ni` was
written `inline_for_extraction` by analogy with `Hacl.AES.NI.cipher_vec`, and
extraction failed with

    error: inlining failed in call to 'always_inline' 'Hacl_Vec128_subword':
    target specific option mismatch

because the body was inlined into a caller that does not carry
`target("aes,...")`.  The correct analogy is `cipher_ni`, not `cipher_vec`:
the function immediately below a `Vec.supported ()` dispatch must be a real
function with the attributes, and only functions *above* it in the fast path
may be inlined.  Dropping `inline_for_extraction` from both paths fixed it
and costs thirteen calls per key schedule.

### The numbers

Expanding an AES-128 key: 14,044 cycles to 1,021.  Empty AEAD call: 4.681 us
to 0.340.

gcc 15.2.0 `-O3`, pinned, three rounds, 22/36 runs kept, against EverCrypt
dispatching to Vale assembly.  Control rows (`chacha20poly1305` 0.76x,
`poly1305` 1.39x, `chacha20` vector 5.3x) match the committed table to the
digit, and the reference column did not move.

| AES-128-GCM | before | after | speedup | was | now |
|---|---:|---:|---:|---:|---:|
| 64 bytes | 13 MB/s | 138 MB/s | **10.3x** | 77.45x | **7.54x** |
| 1 KiB | 172 MB/s | 637 MB/s | **3.70x** | 18.16x | **4.97x** |
| 16 KiB | 672 MB/s | 812 MB/s | **1.21x** | 5.38x | **4.51x** |
| 256 KiB | 803 MB/s | 809 MB/s | 1.01x | 4.53x | **4.48x** |

| AES-256-GCM | before | after | speedup | was | now |
|---|---:|---:|---:|---:|---:|
| 64 bytes | 10 MB/s | 117 MB/s | **11.7x** | 84.56x | **7.43x** |
| 1 KiB | 139 MB/s | 583 MB/s | **4.19x** | 20.01x | **4.77x** |
| 16 KiB | 610 MB/s | 768 MB/s | **1.26x** | 5.55x | **4.39x** |
| 256 KiB | 753 MB/s | 772 MB/s | 1.03x | 4.49x | **4.41x** |

clang 22/36: 140 MB/s and 7.39x at sixty-four bytes, 868 MB/s and 4.22x at
256 KiB.  Neither compiler does anything special with either version.

### What this says about the method

Every part of this report until now has been about making a loop faster.
This one did not touch a loop.  The generated C for the cipher, the counter
mode and the GHASH is byte-for-byte what it was; the 256 KiB row moved by
one percent, which is noise.

The cost was flat, and a throughput benchmark hides a flat cost perfectly ---
it is divided by the message length before it is printed.  Thirty parts of
careful work on cycles-per-byte had left a fourteen-thousand-cycle constant
term untouched and, worse, unnoticed, in the one primitive whose gap everyone
already knew about.  The row that exposed it, `aes128-gcm-enc | 64`, has been
printed by every single benchmark run in this session.

The generalisable habit is small: when a ratio against a reference varies
strongly with input size, the interesting quantity is the *intercept*, not
the slope, and it can be read straight off a size sweep by extrapolating to
zero --- or, here, by simply calling with length zero, which the API allows.

### What is still there

Roadmap item 2 is untouched and is now the largest AES item: GHASH at 2.11
cyc/B against roughly 0.5 for a deferred-reduction implementation, 57% of the
bulk cost.  Below it, the counter mode at 1.58 cyc/B is close to
single-block `AESENC` latency (4 cycles x 10 rounds / 16 bytes = 2.5), which
suggests the four-block interleave is not covering as much as it could and
that six or eight blocks --- what the Vale assembly does --- would help.

---

## Part 32 --- One GF(2^128) reduction per four GHASH blocks

### The observation

The four-way GHASH loop already had four independent `PCLMULQDQ` chains
against the precomputed powers `h^4, h^3, h^2, h` of the hash key.  What it
did not have was a shared reduction.  Each block computed a full 256-bit
carry-less product and then folded it back to 128 bits *before* adding it
into the accumulator.  Counting operations in `Hacl.AES.GF128.NI`:

| piece | operations |
|---|---:|
| `raw_product` | 4 `PCLMULQDQ` + ~12 others |
| `mul_r_vec` (one fold) | ~22 shifts and exclusive-ors |
| `gmul_vec` | 1 `raw_product` + **2** `mul_r_vec` |

So a four-block turn was 16 multiplies and **eight** folds, and at ~22
operations each the folds were the majority of the loop.  The reduction, not
the multiplication, was what GHASH cost.  That is the whole finding; the rest
is mechanics.

### The plan

The 256-bit product is linear in each operand and the fold is linear, so the
four products can be summed as two registers --- the sum of the four low
halves and the sum of the four high halves --- and the fold applied once to
that sum.  Four multiplies, one fold, instead of four multiplies and four
folds (eight `mul_r_vec` calls).

### The three specification facts, and why none of them is hard

Nothing here says anything new about the reduction polynomial `r_block`.

1. **`Spec.GF128.Poly.mul_r_two v1 u2 v2 u3 v3`** ---
   `halves v1 r_block u2 v2 /\ halves v2 r_block u3 v3 ==> gmul v1 r_block ==
   gadd u2 u3`.  This is literally the existing `gmul_three` with its first
   line (`gmul_split x y u1 v1`) removed: the statement that *folding twice
   terminates*, said about one register rather than about a product.  Removing
   that line is what makes it reusable, because in the deferred version the
   register being folded is a sum, not the high half of any single product.
   `gmul_three` is now `gmul_split x y u1 v1; mul_r_two v1 u2 v2 u3 v3`.

2. **`Spec.CLMUL.bswap_gadd a b`** --- `bswap (gadd a b) == gadd (bswap a)
   (bswap b)`.  One line, by `Seq.lemma_eq_intro`: both sides are the same
   `Seq.init`.  It is what allows the six accumulating exclusive-ors to be
   performed in the *multiplier's* bit order rather than GHASH's, so three
   byte reversals happen at the end instead of twelve.

3. **`Spec.GF128.Algebra.gmul_defer4`** --- twenty block parameters, under
   `--fuel 0 --ifuel 0 --z3rlimit 300`.  It is `gmul_split` four times
   (turning each product into `gadd u_i (gmul v_i r_block)`), then `regroup4`
   (associativity and commutativity of `gadd` rearranging the eight
   half-products into a low sum and a high sum), then `mul_r_sum4` --- three
   applications of the `gmul_gadd_left` distributivity that `Spec.GF128.Algebra`
   already had for the Horner rearrangement --- to pull `gmul _ r_block` out
   of the high sum.

The supporting definition is `sum4 a b c d = gadd a (gadd b (gadd c d))`,
chosen to be *definitionally* the association `horner4` and `ghash_step4`
already produce, so that `gmul4_vec` slots into `ghash_loop4_ni` with no
glue lemma at the call site.

### The one thing that is easy to get backwards

`raw_product x y` ensures

```
Poly.halves (bv x) (bv y) (CL.bswap (bv (snd r))) (CL.bswap (bv (fst r)))
```

--- note the **crossed** order.  The GHASH-order *low* half is the byte
reversal of the *high* register (`snd`), and the *high* half is the byte
reversal of `fst`.  `mul_r_vec a` ensures `halves (bswap (bv a)) r_block
(bswap (bv (fst r))) (bswap (bv (snd r)))`, uncrossed.  Getting the pairing
right the first time is the difference between a five-minute proof and an
afternoon.

### Code

`Hacl.AES.GF128.NI.gmul4_vec x1 y1 x2 y2 x3 y3 x4 y4 : Pure Vec.t`, ensuring
`Vec.bv r == Alg.sum4 (gmul x1 y1) (gmul x2 y2) (gmul x3 y3) (gmul x4 y4)`.
Four `raw_product`s, six `vxor`s, then exactly the tail `gmul_vec` already
had.  `ghash_loop4_ni`'s body became:

```
let cur = !av;
xor_block_bv cur d0;
let res = gmul4_vec (Vec.vxor cur d0) y4 d1 y3 d2 y2 d3 y;
ghash_step4 ...;
av := res;
```

Both `gmul4_vec` and the rewired `ghash_loop4_ni` verified on the first
attempt.  Budget note: `Spec.GF128.Poly.fst` takes 6m23 to check and
`Spec.GF128.Algebra.fst` 3m35, so the spec side dominates the edit-check
loop even though it is the smaller diff.

### Validation

`make verify -j16` clean, `extract` clean, `make test` --- all **450 CAVP
GCM** cases pass, the HPKE AES-128-GCM suites pass, `make clones` unchanged
at 67.

### Microbenchmark (256 KiB, gcc -O3, core 6)

Measured by calling the AEAD with `msg_len=N, aad_len=0` versus `msg_len=0,
aad_len=N`, since only the AEAD entry points are non-`static`.

| | before | after |
|---|---:|---:|
| GHASH alone | 2.11 cyc/B | **1.28** |
| AES-128-GCM total | 3.68 cyc/B | **2.88** |
| CTR, by difference (**control**) | 1.58 | 1.60 |

The control not moving is the point: the change is confined to GHASH and the
measurement says so.

### Benchmark suite

The immediate post-change gcc run kept only 7 of 36 rounds, so it was
repeated; the re-run and the clang run both kept **36/36** and agreed with
it to about 1%.  Control rows were exact throughout
(`chacha20poly1305-enc | 262144` 0.76x, `poly1305 | 16384` 1.40x), and the
*reference* column was stable across all three runs (AES ref 3628 / 3663 /
3637 MB/s, 1.0% spread).

gcc:

| benchmark | size | before | after |
|---|---|---:|---:|
| aes128-gcm-enc | 256 KiB | 809 MB/s, 4.48x | **1034 MB/s, 3.52x** |
| aes128-gcm-enc | 16 KiB | 812, 4.51x | **1033, 3.49x** |
| aes128-gcm-enc | 1 KiB | 637, 4.97x | **753, 4.13x** |
| aes128-gcm-enc | 64 B | 138, 7.54x | **142, 7.29x** |
| aes128-gcm-dec | 16 KiB | --- | 1033, 3.53x |
| aes256-gcm-enc | 256 KiB | 772, 4.41x | **966, 3.50x** |

clang:

| benchmark | size | before | after |
|---|---|---:|---:|
| aes128-gcm-enc | 256 KiB | 868 MB/s, 4.22x | **1052 MB/s, 3.46x** |
| aes128-gcm-enc | 64 B | 140, 7.39x | **145, 7.16x** |
| aes256-gcm-enc | 256 KiB | --- | 971, 3.50x |

First time the primitive has been over a gigabyte a second on either
compiler.  The small-message rows barely move, which is expected: at 64
bytes the loop runs once and the flat costs dominate.

### The assembly, and what is left

`gcc -O3 -S` on `dist/Hacl.c`; the four-way loop is inlined into
`Hacl_AES_GF128_NI_ghash_loop_ni`, so there is no `ghash_loop4_ni` symbol to
look for.

Four-block loop body: **205 instructions per 64 bytes** = 3.2 per byte.
16 `pclmulqdq`, **7 `pshufb`**, 47 `pxor`, 17 `psllq`, 14 `psrlq`,
13 `pslldq`, 10 `psrldq`.

Two things worth recording:

* 3.2 instructions a byte at the ~2.5 IPC this machine manages on vector code
  is 1.28 cycles a byte, which is what was measured.  **GHASH is now
  throughput-bound rather than latency-bound** --- the difference between a
  dependency problem and a work problem, and it means further gains have to
  come from removing instructions, not from more interleaving.
* There are **7** `pshufb` and not 11 because the four byte reversals of the
  hash-key powers are loop-invariant and gcc hoists them out.  That they are
  invariant is a consequence of `bswap_gadd` --- of accumulating in the
  multiplier's bit order rather than GHASH's.  A one-line extensionality
  lemma bought four hoisted instructions per turn.

The single remaining fold is about 40 of the 205.  An eight-block window
would halve its frequency again, worth roughly a further 10% of GHASH, at
the cost of `h^5..h^8` and a `regroup8`; the spec lemmas generalise
mechanically.  Below GHASH, the counter mode is still 1.60 cyc/B against a
single-block `AESENC` latency bound of 2.5, so the four-block interleave is
covering some but not all of the latency; Vale interleaves six.

---

# Part 33 — The counter is a lane, not a carry chain

Deferring the GHASH reduction (Part 32) did more than speed AES-GCM up; it
changed which half was worth looking at.  Before it, GHASH was 2.11 cycles a
byte against counter mode's 1.58.  After it, GHASH was 1.28 and counter mode
was untouched at 1.55, so for the first time the counter was the larger half.

## What the assembly said

`gcc -std=c11 -O3 -S dist/Hacl.c`, then isolating
`Hacl_AES_NI_ctr_block4_ni__Mkparams_1` (the AES-256 instance, fifty-six AES
operations) between its label and its `.size` directive:

| | instructions |
|---|---:|
| whole four-block turn | **225** per 64 bytes |
| of which AES | ~78 |
| of which counter arithmetic | **~139** |

The 139 broke down as 26 `movzbl`, 12 `shrq`, 12 `subq`, 11 `notl`, 11 `orl`,
11 `sall`, 9 `andl`, 8 `addl`, and the rest moves.  This is four copies of
`Hacl.AES.Counter.inc32_impl`: a constant-time carry chain over the last four
bytes of the counter block, in which each carry is materialised as a mask
(`sub`, `not`, `or`, shift) instead of a branch.

That shape is correct and necessary for a counter that might be secret.  It is
pure waste for a driver that already knows its four counters are consecutive.

Worse than the count: each chain ended in

```
movl  %r8d, 12(%rcx)
```

and the next block began with

```
movdqu (%rcx), %xmm0
```

A four-byte store immediately under a sixteen-byte load of the same address.
No store-to-load forwarding network on any x86 handles a narrow store feeding
a wide load; the load has to wait for the store to retire to cache.  Three of
those per turn, and because each chain reads the previous chain's result, the
four were serial through memory.  The AES core itself was already clean —
round keys loaded once per round and shared across all four blocks — so the
counter was the entire problem.

## The identity

`inc32 b` takes the last four bytes of a sixteen-byte block as a big-endian
u32, adds one mod 2^32, and leaves the first twelve alone.

`Spec.CLMUL.bswap a = Seq.init 16 (fun j -> a.[15-j])` reverses the *whole*
register.  After it, bytes 0..3 are `c15, c14, c13, c12`.  Read
little-endian — which is what `Spec.SHANI.lanes = words_from_le 4` does —
that is exactly the big-endian value of the counter field.

So:

* `bswap` puts the counter in lane zero and fixes its endianness at the same
  time, in one instruction, for free;
* `PADDD` adds one to lane zero with no cross-lane carry, wrapping at 2^32,
  which *is* `inc32` and nothing else;
* `bswap` puts it back.

And the four lanes partition the sixteen bytes: lane 0 of `bswap c` is bytes
15..12 (the counter), lanes 1–3 are bytes 11..0 (the twelve `inc32` does not
touch).  There is no leftover case.

Three instructions, and since the reversal can be held across the four blocks
the whole turn costs one `PSHUFB` and one `PADDD` per block, plus a single
sixteen-byte store of the fifth counter at the end.

## The target-attribute problem

`PADDD` was already bound — `Hacl.Vec128.add32`, for SHA-256's message
schedule.  But it was declared inside `HACL_VEC128_SHA`, i.e.
`__attribute__((target("ssse3,sse4.1,sha")))`, and GCC refuses to
`always_inline` a callee whose target feature set is not a subset of the
caller's.  An AES-NI caller carries `target("aes,pclmul,ssse3,sse4.1")`, which
does not include `sha`, so the inline would have failed.

`_mm_add_epi32` is SSE2 and part of the x86-64 baseline, so the fix was to
introduce a third group in `c/Hacl_Vec128.h`:

```c
#define HACL_VEC128_BASE __attribute__((always_inline)) static inline
```

with no `target` at all, and move `add32` into it.  A target-free binding
inlines into SHA callers and AES callers alike.  The only genuinely new extern
is `Hacl_Vec128_lane_one`, `_mm_set_epi32(0,0,0,1)`.

This is the third distinct target-attribute lesson in this codebase, after
"`inline_for_extraction` on the NI path itself destroys the attribute" and
"`inline_for_extraction` on a helper whose callers already carry it is fine".
The general rule is now clear: attribute a binding with the *narrowest* set of
features the instruction actually requires, not the set the first caller
happened to have.

## The proof, and a forty-minute lesson

Bottom up, each verifying first attempt:

* `Hacl.Spec.Bytes.le_nat_byte` — reading a byte back out of a little-endian
  number, `S8.v s.[k] == (le_nat s / pow2 (8*k)) % 256`.  1m25.
* `Spec.SHANI.lane_slice` / `lane_val` / `lane_byte` — the lane a `PADDD`
  axiom states itself over, in terms of the bytes underneath it.  24 s.
* `Hacl.AES.Counter` — `lane_of`, `lane_of_bound`, `lane_of_reg`,
  `byte_of_lane`, `lane_zero_be32`, `lane_rest`, and then `inc32_lanes`.
* `Hacl.AES.NI.inc32_vec` and `inc32_vec_ok`.  35 s.

Then `inc32_lanes` hung z3 for over forty minutes.  It had been written the
obvious way:

```fstar
let aux (j: nat { j < blocklen }) : Lemma (...) =
  if j < 12 then ... else ... in
FStar.Classical.forall_intro aux;
Seq.lemma_eq_intro (CL.bswap r) (inc32 c)
```

Diagnosis, which is worth recording as a recipe:

1. Reconstruct the `fstar.exe` command from `ps -eo args`.
2. Drop `--silent`, add `--query_stats`, redirect to a **file** — pipes buffer
   and you lose the partial output when you kill it.
3. `--admit_except Hacl.AES.Counter.inc32_lanes` to time one definition alone.

The results were unambiguous: `inc32_lanes` admitted-except verified in **5
seconds**, and all 259 queries in the module summed to **72 seconds**.  So the
cost was neither elaboration nor any individual named lemma.  It was the
quantified local `aux` interacting with the surrounding context — z3 was
instantiating it against everything in scope.

The fix was to hoist `aux` into two top-level lemmas with narrow hypotheses
(`inc32_lanes_low`, `inc32_lanes_high`) and call them at sixteen concrete
indices.  The same sixteen facts, none individually harder, and the module
went to **2m25**.

**This is now standard practice in this codebase**, alongside the two earlier
idioms (name the intermediate sequence; restate the invariant in terms of the
spec function rather than erased locals).  A `Classical.forall_intro` over a
local lemma with a rich context is a landmine; if the index range is small and
concrete, just enumerate it.

Caveat learned the hard way: **`--admit_except` still writes a `.checked`
file**.  Delete it before re-running for real.

## Results

Assembly, same symbol, same flags:

| | before | after |
|---|---:|---:|
| `ctr_block4_ni__Mkparams_1` | 225 | **114** |

The new body: 52 `aesenc`, 4 `aesenclast`, 20 `movdqu`, 12 `movdqa`, 8 `pxor`,
**8 `pshufb`**, 5 `movups`, **4 `paddd`**.  The AES-128 instance is 94.

Microbenchmark, 256 KiB, gcc, core 6, new `dist/Hacl.c` against
`git show HEAD:dist/Hacl.c` in an identical harness.  (Only the AEAD entry
points are non-`static`, so the split is measured as `msg_len=N, aad_len=0`
versus `msg_len=0, aad_len=N`.)

| | before | after |
|---|---:|---:|
| total | 2.78 cyc/B | **1.71** |
| GHASH only (**control**) | 1.23 | 1.22 |
| CTR by difference | 1.55 | **0.49** |

0.49 cycles a byte is *below* the 0.625 that one `AESENC` per cycle would
allow, which says this machine has two AES units.

Benchmark suite.  gcc was run twice; the first run kept only 6/36 but had
exact control rows, and the re-run kept **36/36** and agreed to within 0.2%.
clang kept 27/36.

gcc (`r33g2`, 36/36, controls 0.76x and 1.41x — exact):

| benchmark | size | before | after |
|---|---|---:|---:|
| aes128-gcm-enc | 256 KiB | 1034 MB/s, 3.52x | **1631, 2.24x** |
| aes128-gcm-enc | 16 KiB | 1033, 3.49x | **1598, 2.26x** |
| aes128-gcm-enc | 1 KiB | 753, 4.13x | **1003, 3.10x** |
| aes128-gcm-enc | 64 B | 142, 7.29x | **148, 6.95x** |
| aes128-gcm-dec | 16 KiB | 1033, 3.53x | **1594, 2.28x** |
| aes256-gcm-enc | 256 KiB | 966, 3.50x | **1486, 2.28x** |
| aes256-gcm-enc | 16 KiB | 958, 3.52x | **1453, 2.30x** |

clang (`r33c`, 27/36):

| benchmark | size | before | after |
|---|---|---:|---:|
| aes128-gcm-enc | 256 KiB | 1052 MB/s, 3.46x | **2025, 1.80x** |
| aes128-gcm-enc | 16 KiB | — | **1992, 1.82x** |
| aes128-gcm-dec | 16 KiB | — | **1971, 1.87x** |
| aes256-gcm-enc | 256 KiB | 971, 3.50x | **1791, 1.91x** |

clang is now **24% faster than gcc** on this primitive.  That gap existed
before and was hidden: when a hundred and thirty-nine instructions of serial,
memory-bound carry chain sat between the AES blocks, neither compiler's
scheduling of the AES itself mattered.  With the counter gone, it does, and
clang interleaves the four blocks better.

The small-message rows barely moved (7.29x to 6.95x), as expected: at 64 bytes
the key schedule still dominates and there is only one counter increment.

## Validation

`make verify -j16` clean in **54m12** — editing `lib/Hacl.Spec.Bytes.fst`
forces a full-tree rebuild, which is worth knowing before starting.  `make
extract` 1m47 clean.  All **450 CAVP GCM** vectors pass, the HPKE AES-GCM
suites pass, and a new `vec128 lane_one constant` check was added to
`tests/test_vec128.c`.  `make clones` unchanged at **67**.

Committed as `25fdbbd`, "AES-CTR: the counter in a lane, 3.52x to 2.24x".

## Where this leaves AES-GCM

GHASH is the larger half again: 1.22 cycles a byte of 1.71.  The eight-block
window is therefore the natural next item — the single remaining fold is about
forty of the two hundred and five instructions a four-block turn takes, so
halving its frequency is worth roughly a further ten per cent of GHASH, at the
cost of `h^5` through `h^8` and a `regroup8`; the spec lemmas generalise
mechanically from `gmul_defer4`.

The idea floated at the end of Part 32 — six- or eight-block *counter*
interleaving, to match what EverCrypt's Vale assembly does — is now obsolete.
At 0.49 cycles a byte, counter mode is at the machine's AES throughput and
there is nothing left in it.

---

# Part 34 — Eight GHASH blocks to a reduction

Part 33 put counter mode at 0.49 cycles a byte, which put GHASH back on top:
1.22 of AES-GCM's 1.71.  Part 32's deferral — one GF(2^128) reduction per four
blocks instead of four — left an obvious loose end, which it named at the
time: the fold is a fixed cost per *group*, and nothing in the argument cared
that the group was four.

## The estimate, and what it missed

The estimate in Part 32 was "about forty of the two hundred and five
instructions a four-block turn takes, so halving its frequency is worth
roughly a further ten per cent of GHASH."  The measured answer was **sixteen**
per cent under gcc.  The extra came from somewhere the estimate did not look:
eight independent `PCLMULQDQ`s give the multiplier twice as much to work on at
once, so it is not only instruction count that improves.

## The algebra was already general enough

This is the payoff for how `Spec.GF128.Algebra` was written in Part 32 —
nothing there mentions the number four except in the arity of the lemmas.

| eight-way | is | cost |
|---|---|---|
| `sum8` | two `sum4`s added | a definition |
| `regroup8` | `regroup4` twice + `gadd_shuffle` | 3 lines |
| `mul_r_sum8` | `mul_sum4` twice + one `gmul_gadd_left` | 3 lines |
| `gmul_defer8` | `gmul_defer4` with 4 → 8 | mechanical |

`gadd_shuffle` is the one genuinely new exclusive-or fact —
`(a+b)+(c+d) == (a+c)+(b+d)` — eight booleans a bit, proved by extensionality
in six lines.  `mul_sum4` is `mul_r_sum4` with the reduction constant
generalised to an arbitrary multiplier, which the Horner step needs at `h4`.

### The one part that needed thought

`horner8` is `horner4` applied twice: once to the first four blocks, once to
its result.  The second application leaves a multiplication by `H^4` in front
of the first group's four terms, and pushing it through raises each of their
powers by four.

That last step is not immediate, because the powers are generated one
multiplication at a time — `h5 = gmul h4 h`, and so on — so "`H^4` times `H^2`
is `H^6`" has to be *walked up the chain*:

```
h2 * h4 = (h * h) * h4 = h * (h * h4) = h * h5 = h5 * h = h6
```

`pow_mul4` does the four of these in order, each reusing the one before it:
five uses of associativity and four of commutativity, and no new reasoning at
all.  This is the general shape of the problem with a Horner window: the
window size enters through the power identities and nowhere else.

The spec module went from roughly 1m30 to **3m37**, and verified first
attempt.

## The implementation

`gmul8_vec` is `gmul4_vec` with eight `raw_product`s.  The accumulation of
sixteen product halves into two registers was factored into two helpers:

```fstar
inline_for_extraction
let xor4 (a b c d: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> CL.bswap (Vec.bv r) ==
            Alg.sum4 (CL.bswap (Vec.bv a)) ... )
```

which carries the `xor_block_bv` and `CL.bswap_gadd` bookkeeping that says
*the byte reversal of a sum is the sum of the reversals* — the fact that lets
all the exclusive-ors happen in the multiplier's bit order so that only three
`bswap`s happen at the end.  `xor8` is two `xor4`s and one more.  Rewriting
`gmul4_vec` to use them took twelve lemma calls out of it and left it stating
what it does rather than how it proves it, which is worth doing on its own.

### Three loops, not two

The eight-way pass leaves at most one group of four behind, so `ghash_loop4_ni`
gained a `start` parameter and an erased `acc0`, and now runs from wherever the
eight-way pass stopped rather than always from zero.  The one-block loop takes
what is left after that.

Keeping the four-way loop matters for correctness of *performance*, not of
results: without it, a message with `n % 128 >= 64` would do up to seven serial
multiplies at ~30 cycles of latency each instead of one four-way turn.

The extra powers are computed inside the same test as before, nested:

```
if lim > 0     { y2, y3, y4 = ...
  if lim8 > 0  { y5, y6, y7, y8 = ...; eight-way; four-way from lim8 }
  else         { four-way from 0 } }
else           { nothing }
```

so a message short of 128 bytes pays for four powers as it always did, and one
short of 64 pays for none.

### Two small Pulse lessons

Both failures on the way were about **the size of the Pulse context**, not
about the mathematics:

1. A missing `vals_len vd` — the new precondition of `ghash_loop4_ni` mentions
   `Seq.slice (vals vd) 0 n`, which cannot even be *stated* without knowing
   `Seq.length (vals vd) == Seq.length vd`.
2. `Seq.length (Seq.slice (vals vd) 0 n) % 16 == 0` **timed out**.  This is
   trivial — `Seq.length (Seq.slice s 0 k) == k` and `n % 16 == 0` is a
   hypothesis — but in a Pulse context with a hundred other hypotheses the
   query blew up.  Hoisting it into a four-line top-level lemma
   (`slice_len_mod`) and calling it fixed it instantly.

That is the same lesson as Part 33's `Classical.forall_intro` blowup, in a
different costume: **when a query that ought to be trivial is slow, take the
fact out of the rich context and hand it in as a hypothesis.**

## Results

Microbenchmark, 256 KiB, core 6, against `git show HEAD:dist/Hacl.c`:

| | gcc before | gcc after | clang before | clang after |
|---|---:|---:|---:|---:|
| total | 1.694 cyc/B | **1.507** | 1.350 | **1.261** |
| GHASH | 1.222 | **1.029** | 0.922 | **0.824** |
| CTR (**control**) | 0.472 | 0.478 | 0.428 | 0.437 |

Benchmark suite (gcc `r34g`, 23/36, controls 0.77x and 1.37x; clang `r34c`,
**36/36**):

| benchmark | size | gcc before | gcc after | clang before | clang after |
|---|---|---:|---:|---:|---:|
| aes128-gcm-enc | 256 KiB | 1631, 2.24x | **1868, 1.98x** | 2025, 1.80x | **2205, 1.68x** |
| aes128-gcm-enc | 16 KiB | 1598, 2.26x | **1792, 2.04x** | 1992, 1.82x | **2141, 1.71x** |
| aes128-gcm-dec | 16 KiB | 1594, 2.28x | **1801, 2.05x** | 1971, 1.87x | **2148, 1.72x** |
| aes256-gcm-enc | 256 KiB | 1486, 2.28x | **1680, 2.05x** | 1791, 1.91x | **1931, 1.79x** |
| aes128-gcm-enc | 1 KiB | 1003, 3.10x | 1022, 3.11x | 1150, 2.71x | 1174, 2.71x |
| aes128-gcm-enc | 64 B | 148, 6.95x | 149, 7.06x | 153, 6.76x | 154, 6.80x |

**1.98x is the first time AES-GCM has been inside a factor of two of
hand-written assembly.**  The small-message rows do not move, as designed: at
1 KiB the key schedule still dominates, and at 64 bytes neither loop runs.

For the record, the arc of this primitive across the whole session: 875 us →
**140 us** on 256 KiB, 12x of the reference → 1.98x.

## Where the remaining instructions go

The eight-way turn is **363 instructions for 128 bytes** against the four-way
turn's 227 for 64 — so the fold is visibly what came out, and per byte it is
2.84 against 3.55.

But 111 of the 363 are `movdqa` and 28 `movaps`, and **41 touch the stack**.
Eight powers, eight data blocks and sixteen product halves do not fit in
sixteen XMM registers, and gcc spills.

### The experiment that failed

The natural fix is to accumulate the halves *as they are produced* rather than
in a tree, so that each product dies immediately and only two accumulators
stay live.  Rather than do the proof work first, this was tested by
hand-patching a copy of the generated C — which is exactly what generated C is
good for:

| | gcc | clang |
|---|---:|---:|
| tree (shipped) | 1.029 | 0.824 |
| interleaved accumulation | **1.526** | 0.827 |

gcc got **a third slower**.  Given a serial chain for the sum it serialises
the products that feed it, and loses far more in the multiplier than it saves
in spills; clang is indifferent.  The tree stays.

The lesson is worth keeping: *test a scheduling hypothesis on the generated C
before proving anything about it.*  Ten minutes of `python3` and `gcc` saved a
day of writing an associativity chain for an answer that was negative.

## Where this leaves AES-GCM

A sixteen-way window would make the register pressure worse, not better, so
this is probably the end of the line for the reduction.  What is left between
this code and EverCrypt's Vale assembly is that the assembly **interleaves the
two halves** — it runs the AES rounds of one group against the GHASH multiplies
of the previous one, so the AES units and the multiplier are busy at the same
time.  Here they run in sequence: 0.48 + 1.03 = 1.51, and the ideal would be
max(0.48, 1.03) = 1.03.  That is the whole of the remaining 1.98x, and it is a
much larger structural change than anything in Parts 32 to 34.

Committed as `944b2e4`, "GHASH: eight blocks to a reduction, 2.24x to 1.98x".

---

# Part 35 — Ed25519's group order on the four-limb Montgomery core

## Why this row

After Part 34 the worst remaining ratio in the table was Ed25519 signing at
**2.35x**.  Before touching anything, a breakdown probe (`/tmp/ed/p.c`, best
of seven, `taskset -c 6`):

| | HACL\* | hacl-pulse |
|---|---:|---:|
| sign | 63.5 us | 155.3 us |
| secret_to_public | 31.3 | 61.3 |
| expand_keys | 31.2 | 61.5 |
| sign_expanded | 32.0 | 92.3 |
| sha512(32B) | 0.68 | 0.48 |

Two *independent* gaps, which is the useful part of the measurement:

1. the fixed-base scalar multiplication is 2x slower (61 vs 31), and
2. `sign_expanded` carries an extra **31 us** that HACL\* spends about one
   microsecond on.

`sign_expanded` does one fixed-base multiplication and then some arithmetic
modulo the group order.  61 of its 92 us is the multiplication, so the 31 is
the arithmetic.  Our SHA-512 is *faster* than HACL\*'s (0.48 vs 0.68 on 32
bytes), so the two hashes in a signature cannot account for more than about
two of it.

## What was there

`code/ed25519/Hacl.Ed25519.Scalar.fst` did everything **bit by bit**:
`reduce_op` was 512 rounds of double-and-conditionally-subtract, `qmul_op`
256 rounds.  Its header explained why, and the explanation was *"here there
is no `uint128`"* — a premise that roadmap item 1 made obsolete a long time
ago.  It was also the last user of the eight-limb, thirty-two-bit
`Spec.Bignum256` stack.

## The design

Reuse `Hacl.Impl.Mont4` with the order as data, exactly as `Hacl.K256.Scalar`
does.  The only real question is how to reduce a 512-bit digest.

**Why not the obvious thing.**  `amul`'s precondition (and `Spec.Field4.res`)
insists both operands are already below the modulus, so a wide value cannot be
fed straight to a Montgomery reduction.  And `2^256 / q ≈ 16`, so reducing a
bare 256-bit half would need four conditional subtractions against tables for
`8q`, `4q`, `2q`, `q` — except that `csub_op` ties its `nm` argument to
`d.nm`, so a caller has no way to pass those tables.  Barrett would need a
second representation and a second set of constants.

**What was done instead.**  Cut the digest into four 128-bit chunks.  Since
`2^128 < q`, every chunk is a residue *for free* — no reduction, no
comparison, just two limbs and two zeros.  Weighting them is then three
ordinary constant multiplies, because of a small fact that makes the whole
thing work:

> Montgomery multiplication by a constant of the form `R k mod q` cancels the
> radix and leaves `a k mod q`.

So `2^128`, `2^256` and `2^384` become three tables holding `2^384 mod q`,
`2^512 mod q` and `2^640 mod q`.  The middle one is exactly `qmod.r2`, which
the modulus record already carries, so only two tables are new.  Three
multiplies and three additions replace five hundred and twelve conditional
subtractions.  A thirty-two-byte scalar is the same fold over two chunks.

`Spec.Ed25519.Scalar.mmul_const` is the fact, and its proof is four lines:
`mmul_ok` states its conclusion multiplied by `R`, the goal does too once
`eval p == R k mod q` is unfolded, and `rcancel` removes the common factor.

## The little-endian byte layer

`Spec.Field4` has only the big-endian pair, because that is what P-256 and
secp256k1 need.  Adding the mirror *there* would have forced a full reverify
of everything downstream, so it went into `Spec.Ed25519.Scalar`, which nothing
else depends on.

Reading is far cheaper to prove than the big-endian version, for a reason
worth writing down: `Hacl.Impl.Bytes.load_le #S64.t` already returns `le_nat`
of its eight-byte window, so `eval_le` never unfolds a byte at a time — it
cuts once per limb with `le_nat_split`.  Writing still needs the per-digit
division lemma, a copy of `store_be_digit` with `(7-m)` replaced by `m`.

## Proof engineering: where the time actually went

The arithmetic design was right on the first attempt and
`spec/Spec.Ed25519.Scalar.fst` verified immediately.  **All** of the
difficulty was in Pulse function bodies, and every instance of it had the same
shape and the same fix.

**Symptom.**  A Pulse `fn` that should take ninety seconds runs for an hour
without producing an error.

**Cause, three times over.**  A lemma call inside a Pulse block whose
conclusion needs several rewriting steps, combined with `qmod_ok ()` (which
injects `modulus_ok` — five sequences of four sixty-four-bit literals, plus
`mont_ok`) into the same SMT context.  Z3 does not fail; it grinds.

**Fix, three times over.**  Package the reasoning into an ordinary pure
lemma outside the Pulse block, so the heavy context appears in a small
standalone query, and leave the Pulse body with a single call:

- `chunk_res` — pulled `chunk_eval`, `q_bound`, `qmod_m` and an `assert_norm`
  out of `load_chunk`.  60+ minutes → 90 seconds.
- `fold_step` — pulled `mmul_const`, `madd_ok` and `lemma_mod_add_distr` out
  of `fold_chunk`.  Same.
- `reduce64_ok` / `reduce32_ok` — pulled `digest_split` and `fold_ok` out of
  the two reduction functions.

A fourth instance was different and is the one worth remembering: `reduce64`
hung until the six `table qXX_arr 4sz` calls were wrapped in
`inline_for_extraction fn`s with abstract postconditions (`vals v == qmod.ms`
rather than the literal list), which is precisely what `Hacl.K256.Tables`
already does and which I had not copied.  **Four constant tables inlined into
one SMT query is enough to stall it.**

Two smaller ones:

- A four-iteration `while` loop reading four limbs would not close; unrolling
  it and proving the quantifier in a separate `load_le_quant` lemma with a
  four-way case split did, and generates better C.
- `x / pow2 0` does not simplify to `x` on its own.  The invariant now says
  `% 256` for the lowest byte and the bridge lemma does the division by one.

## Bisection method

Since the failure mode is a *hang* rather than an error, the only way to
locate it is to truncate the file and re-verify.  Head through `store_le`:
2m11.  Plus `fold_chunk`: 2m10.  Plus `reduce64`: hang.  Then `reduce64` was
rebuilt statement by statement — weak postcondition first, then the `with`
bindings, then the intermediate `assert`s, then the closing lemma, then the
real postcondition — and each step timed.  Every intermediate fact proved in
seconds; only the assembled whole did not.  That is what pointed at the
context rather than at any one obligation.

## Results

`make verify`, `make extract`, `make test` (all five RFC 8032 vectors, plus
HPKE) and `make clones` all pass; the specialisation count is unchanged at
sixty-eight.  `fold_chunk` had to be marked `inline_for_extraction` to keep it
there — gcc was cloning it otherwise.

The probe, rebuilt:

| | HACL\* | before | after |
|---|---:|---:|---:|
| sign | 57.5 us | 137.5 | — |
| secret_to_public | 28.5 | 67.7 | — |
| sign_expanded | 29.0 | 92.3 | **69.5** |

`sign_expanded − secret_to_public`, which is the scalar arithmetic and
nothing else: **31 us → 1.8 us**.

Full suites, three rounds each, `r35g` and `r35c` (controls in range:
chacha20poly1305-enc/256KiB 0.76x gcc and 0.82x clang, poly1305/16KiB 1.35x
and 1.41x):

| | gcc before | gcc after | clang after |
|---|---:|---:|---:|
| ed25519-sign-64B | 2.35x | **1.92x** | **1.62x** |
| ed25519-keygen | 1.91x | **1.94x** | **1.63x** |
| ed25519-verify-64B | ~2.4x | **2.22x** | **1.88x** |

Signing is no longer the worst row in the table; secp256k1 ECDSA signing
(1.91x) and AES-128-GCM (1.98x) now bracket it.

## What is left

All of it is the scalar multiplication.  `secret_to_public` is 67.7 us against
28.5 — a clean 2.4x on the fixed-base window alone, with no arithmetic
overhead left to hide behind it.  Roadmap item 6's "Plan A" — compiling in the
four sixteen-entry tables rather than building them at run time, 256 field
constants for Ed25519 — is the next thing to try, and is worth about 30% on
all three curves.

A housekeeping item is now unblocked as well: with `Hacl.Ed25519.Scalar` off
`Spec.Bignum256`, the thirty-two-bit stack has no *scalar* users left, though
`Spec.Bignum256` itself is still referenced by nine other modules and is not
simply dead.

Committed as `ae104e3`, "Ed25519's group order on the four-limb Montgomery
core".

---

# Part 36 — Compiling in Ed25519's fixed-base window

## The item

Roadmap item 6's "Plan A", which the previous part nominated: the fixed-base
window builds four sixteen-entry tables of multiples on entry, and those
tables could be constants instead.

The window computes

    k G = k0 G + k1 (2^64 G) + k2 (2^128 G) + k3 (2^192 G)

in sixteen rungs of four doublings and four additions.  The four tables cost
sixty point additions — 4 tables × 15 entries, each one addition — out of the
188 operations the whole multiplication does.  Just under a third of the work,
paid on every signature and every key generation, to recompute something that
never changes.

## What it cost to say

Three constants become sixty-four, and the interesting thing is that the proof
does not get harder in proportion.

`Spec.Ed25519.Base` already states the three scale points `2^64 G`, `2^128 G`,
`2^192 G` as doubling *chains* (`Spec.Group.Smul.dblk`), which the normaliser
evaluates on concrete field elements — sixty-four doublings in about a second
— and `dblk_ok` converts into a statement about `smul`.  Each table then
climbs from its scale point one addition at a time:

    assert_norm (on_curve e_d);
    assert_norm (point_equal e_d (point_add e_{d-1} e1));
    G.smul_add_congr eg ((d-1)*n) n g e_{d-1} e1;
    step (d-1);
    SM.smul_ok ...;
    point_equal_trans ...

Two `assert_norm`s per entry, each about 15 ms, and one congruence.
`Spec.Ed25519.Win0` .. `Win3` are 486 lines each and verify in 12 and 21
seconds.

**Storing the entries affine is load-bearing.**  Each entry is `(x, y, 1,
x·y)`, not whatever quadruple `point_add` produced.  A projective point
carries the denominators the previous addition left behind, and they compound:
by the fifteenth entry the normaliser is being asked to compare numbers that
are no longer small, and `assert_norm` stops returning.  Renormalising to
affine at generation time in Python, and checking the affine form against a
reference double-and-add, keeps every `assert_norm` in the tens of
milliseconds.

The code side is `Hacl.Ed25519.Win0` .. `Win3`: four eighty-element limb
lists each (radix 2^51, one flat array per coordinate, sixteen entries of five
limbs), wrapped in `G.mk_static_array`.  About 500 lines each, 2m20 to verify,
2m19 for all four with `-j4`.

Two new pieces of scaffolding:

* **`Hacl.Impl.Lit51`** — the radix-51 counterpart of the existing `Lit4` and
  `Lit52`, plus `chunk l d = ltake 5 (ldrop (5d) l)` and `chunk_slice`, which
  says that cutting the *list* that way agrees with `Seq.slice` on the
  sequence.  That is what lets one `assert_norm` per entry-coordinate settle
  five limbs instead of five separate ones.  11 seconds.
* **`Hacl.Ed25519.WinTable`** — the bridge.  `ent_lit` takes four `leval
  (chunk l d) == coord q` facts plus `on_curve q` and `point_equal q (smul
  (d n) g)` and produces the window layer's `ent`; `tok_all` takes sixteen
  `ent`s to a `tok`.  The only module that opens `rep`.  10 seconds.

## Two obstacles, one real and one imaginary

**Real: `win_add` needed four permissions.** `Table.table` hands back an
existentially quantified fraction, one per call.  `Pulse.Lib.Array.PtsTo.share`
*halves* a permission; there is no rule that weakens a permission to an
arbitrary stated target.  So sixteen `Table.table` calls give sixteen fractions
that cannot be made equal, and every function that consumes them has to be
polymorphic in all sixteen.  `PointWin.win_add`'s `(#ptb: perm)` became
`(#ptx #pty #ptz #ptt: perm)`, and `PointMulG`'s `rung` and `win_loop` grew
sixteen binders each.  Mechanical, but it touches eighty `pts_to`s.

This is also why the old code copied the three base points into owned buffers
before using them: four existentials are not one.  With `win_add`
generalised, the sixteen read-only arrays are read where they lie.

**Imaginary: the sixteen-minute "hang".** After the rewrite, `PointMulG` ran
for sixteen minutes twice with no output.  The natural suspicion was the new
constants — sixteen eighty-element literal lists entering the caller's SMT
context — and the natural fix was `opaque_to_smt` on the four flat sequences
of each table, plus a `reveal_seqs` helper to let `tbl_ok` see through them
locally.  Worth doing on its own merits, and it did not help.

Bisection by truncation found it, and the answer was a surprise: the file
still hung when cut back to the *module header and four pure lemmas*, none of
which mention the new modules, and it still hung when the four `module W? =`
lines were deleted.  `z3` was spinning at 100%.  The offending lemma was
`hi_end`, unchanged from before, six lemma calls, previously ten seconds.

What had changed was its *neighbourhood*: the rewrite deleted `g_rep`,
`b1_rep`, `b2_rep` and `b3_rep`, which sat immediately above it.  That is
enough to change the solver's starting state, and with it whether a query
terminates at all.  `#restart-solver` before `hi_end` fixes it; the lemma then
takes 18.5 seconds and the whole file 56.

The lesson is narrower than "big constants are slow", and more annoying:
**deleting a declaration can make an unrelated later declaration diverge.**
Nothing about `hi_end` was wrong, and no amount of looking at the new code
would have found it.  The technique that did find it — cut the file after each
declaration, verify, repeat — is the only reliable one, and it is worth
reaching for *before* forming a theory about the cause.  The two rounds of
`opaque_to_smt` work were spent on a theory that fit the facts and was false.

An `rlimit` does not save you here, incidentally: the query had
`--z3rlimit 100` and ran for sixteen minutes regardless.

## Numbers

Three rounds each, `-std=c11 -O3`, `taskset -c 6`.

| | gcc before | gcc after | HACL\* | ratio before | ratio after |
|---|---:|---:|---:|---:|---:|
| ed25519-keygen | 60.7 us | **45.7 us** | 31.2 us | 1.91x | **1.46x** |
| ed25519-sign-64B | 124 us | **93.4 us** | 64.1 us | 1.92x | **1.46x** |
| ed25519-verify-64B | 168 us | **150.8 us** | 76.1 us | 2.22x | **1.98x** |

| | clang before | clang after | HACL\* | ratio before | ratio after |
|---|---:|---:|---:|---:|---:|
| ed25519-keygen | 51.3 us | **36.0 us** | 31.1 us | 1.61x | **1.16x** |
| ed25519-sign-64B | — | **73.5 us** | 63.9 us | 1.62x | **1.15x** |
| ed25519-verify-64B | — | **127.6 us** | 75.6 us | 1.88x | **1.69x** |

Key generation and signing each lost about 25%, which is what removing 60 of
188 point operations predicts (60/188 = 32%, less the fixed costs of hashing,
encoding and inversion).  Verification lost 10%, as expected: it does one
fixed-base multiplication and one variable-base, and only the first is
affected.

Under clang, Ed25519 signing at 1.15x is now closer to the reference than
X25519 (1.25x), which is worth noting because X25519 has had far more
attention.  Under gcc, signing at 1.46x is no longer bracketed by secp256k1
ECDSA (1.91x) and AES-GCM (1.98x) — it sits just past MD5.

Cost: 256 field constants, about 10 KB of `.rodata`, as sixteen
`static const uint64_t Hacl_Ed25519_Win?_t?_arr[80]`.  `Hacl.Ed25519.Tables`
loses the nine base-point constants it no longer needs, so the net is 247.

## What is left

The same change is available on secp256k1 and P-256, at 192 field constants
each (three coordinates rather than four), and would be worth a comparable
fraction.  The four generated modules per curve are now a template: the
Python that computes the points and cross-checks them, the spec generator and
the code generator are all parameterised by little more than the curve's
addition law.

`make verify`, `make extract`, `make test` and `make clones` (68) all pass.
Committed as `6f1d89e`, "Ed25519: compile in the fixed-base window's four
tables".

---

## Part 37 — secp256k1's fixed-base window, compiled in

The same change Part 36 made to Ed25519, made to secp256k1.
`Hacl.K256.PointMulG` splits a 256-bit scalar into four sixty-four-bit
pieces and walks them together against `G`, `2^64 G`, `2^128 G` and
`2^192 G` — sixteen rungs of four doublings and four additions, 184 point
operations against the 335 a bit-at-a-time fixed-base multiplication would
cost. Each rung reads one sixteen-entry table per piece, and those four
tables were being built on entry: sixty additions out of 184, a third of
the work, on every signature and every `secret-to-public`.

They are now constants. `spec/Spec.K256.Win0..Win3` name all sixty-four
multiples and prove each is the multiple it claims to be;
`code/k256/Hacl.K256.Win0..Win3` hold their limbs as twelve
`static const uint64_t [80]` arrays in radix 2^52 — 192 field constants,
about eight kilobytes of `.rodata`, against Ed25519's sixteen arrays and
256 constants.

### Results

gcc, `-std=c11 -O3`, `taskset -c 6`, three rounds, per-benchmark minimum:

| row | before | after | ratio before | ratio after |
| --- | ---: | ---: | ---: | ---: |
| `secret-to-public` | 111 us | **75.3 us** | 2.27x | **1.55x** |
| ECDSA sign | 126 us | **91.1 us** | 1.91x | **1.40x** |
| ECDSA verify | 271 us | **233.9 us** | 2.59x | **2.59x** |
| ECDH | 173 us | **153.9 us** | 1.73x | **1.75x** |

clang: 76.1 us (**1.55x**), 98.9 us (**1.50x**), 231.6 us (**2.55x**),
152.0 us (**1.71x**).

`secret-to-public` is the pure fixed-base row and moved 32%, which is
almost exactly the sixty-out-of-184 the table build was costing. Signing
moved 28%: it is one fixed-base multiplication plus scalar arithmetic that
the window does not touch. Verification moved 14% — it does one fixed-base
and one variable-base multiplication, and only the first half gained. ECDH
is the control: variable-base on both ends, unchanged within noise. The
shape of the four numbers is the check that the saving went where it was
supposed to.

secp256k1 ECDSA sign was the worst asymmetric row in the table at 1.91x
and is now 1.40x, which moves it from last place to between RSA-PSS verify
and MD5. The worst remaining row is secp256k1 ECDSA *verify* at 2.59x,
whose variable-base half is the next thing that would have to change.

### What it cost

An afternoon of wall-clock, and every step verified on the first attempt
except two.

The construction is Ed25519's transposed, and transposing it is mechanical
because the hard parts were already solved. `[2^64] G` cannot be unfolded,
so `Spec.K256.Base` keeps stating the three scale points as doubling
*chains* that the normaliser evaluates on concrete field elements at
typechecking time; each table climbs from there one addition at a time,
entry `d` proved equal to `e_{d-1} + e_1` by `assert_norm` and lifted to
`smul (d n) g` by `Spec.Group.smul_add_congr`. Entries are stored affine,
`(x, y, 1)`, which is what keeps both the chain equation and the curve
equation decidable; a projective triple carries the denominators the
previous addition left and by the fifteenth entry the numbers stop being
comparable. k256 is in fact *easier* than Ed25519 here: its `rep`/`ent`
are stated over `K.proj_point` rather than over four limb sequences, so
the bridge lemma is shorter, and its points are three coordinates rather
than four, so there are twelve tables rather than sixteen.

The two things that did not go through first time:

**`tok_all`'s sixteen-way case split.** `d < 16 ==> d == 0 \/ ... \/ d ==
15` is arithmetically trivial and timed out at `--z3rlimit 200` with
sixteen `ent` facts in scope. Hoisted into a separate `lt16` lemma proved
in an empty context at rlimit 20, it is instant. Same lesson as Part 36's
`decompress_on_curve`, one level down: it is not the goal that is hard, it
is the company it keeps.

**A generator bug that looked like a hang.** The spec generator passed
`e_d` rather than `e_{d-1}` as `peq_trans`'s middle argument, making every
`e_d_ok` goal false. A false goal burns its whole rlimit rather than
failing fast, so the symptom was indistinguishable from a proof that is
merely slow.

### A methodological note: 36 minutes is not a hang

`Hacl.K256.PointMulG` took 36m22s to check after the change, and the first
instinct was to treat that as a stall and start bisecting. Three rounds of
truncation-bisection later — prefix through the spec lemmas: 11s; through
`rung`: 7m26s; through `win_loop`: killed at 20 minutes — the useful
experiment turned out to be the one not run first: check out the
*pre-change* file and time it. It takes 32 minutes. The module was always
slow, the twelve permission binders cost about 13%, and roughly an hour of
bisection bought nothing that one baseline measurement would have given in
thirty-two minutes.

The rule that would have saved it: before localising a regression,
establish that there *is* one. Two runs of the old and new file, in that
order, dominate any amount of clever bisection.

### State

`Hacl.K256.Tables52G` is deleted — it existed only to hold the three extra
base points' six field constants, and nothing else used it.
`Hacl.K256.PointWin.win_add` is generalised from one table permission to
three. `make verify`, `extract`, `test` and `clones` (68) all green;
committed as `f77e256` and pushed.

P-256 is the last curve without a compiled-in window, at 192 field
constants, and its fixed-base rows are already at 1.04x–1.08x, so the
remaining headroom there is small. Roadmap item 6 is otherwise complete.

## Part 38 — The triangle squaring, and a solver pathology

The four modexp rows were the largest remaining block of red in the
table: RSA-PSS signing 1.23x, FFDHE 1.25x, the generic 2048-bit modexp
1.26x, RSA-PSS verify 1.38x. They are one cause and not four — the same
Montgomery ladder. The 4-bit window had already taken them from 1.98x to
1.25x, so what was left was the `n x n` multiply itself.

### Where the time was

Microbenchmark at len 32 (2048 bits), gcc, `taskset -c 6`, before:

| | ours | HACL* |
| --- | ---: | ---: |
| `bn_mul` | 1072 ns | 828 |
| `reduction` | 1191 | — |
| `mont_mul` | 2243 | 1882 |

Pure-C loop-shape experiments (`/tmp/bnp/v.c`) separated the causes:

| variant | ns |
| --- | ---: |
| the loop we emit | 1087 |
| HACL*'s 4x unrolled row | 834 |
| hoisting `res_j` out of the loop | 1105 |
| triangle only | 637 |
| triangle + unrolled | 552 |

So unrolling is worth 23% and the triangle 41%, and they compose.

### Two changes

**Four columns to an iteration.** `mul_row` now runs a four-`col` loop
over `n - n % 4` plus a one-at-a-time tail. Four independent mulx-adc
chains in one iteration have loads to overlap with; a single column has
only the loop back-edge. `mont_mul` 2243 -> 1990, level with 1986.

**A real squaring.** `a_i a_j` occurs at weight `i + j` twice. So
`Hacl.Bignum.Base.sqr` computes the strict upper triangle only, doubles
it once, and adds the `n` diagonal terms. 496 products against 1024 at
len 32. Measured 579 ns against the multiply's 931, and HACL*'s `bn_sqr`
at 550. `Montgomery.mont_sqr` = `sqr` + `reduction` ≈ 1613, against
HACL*'s `bn_mont_sqr_u64` at 1676 — we are *ahead* there, because theirs
memsets a `4*len` VLA per call. `Exponentiation.mont_sq` now calls it.
Four fifths of a windowed exponentiation is squarings.

The invariant is `A_k^2 = 2 T_k + D_k`, preserved by `(x + a b^k)^2 =
x^2 + 2 x a b^k + a^2 b^{2k}`. The doubling cannot carry out because
`2 T_n <= A_n^2 < b^{2n}`.

### Results

gcc `r37g` / clang `r37c` against `r36g` / `r36c`:

| benchmark | r36g | r37g | r36c | r37c |
| --- | ---: | ---: | ---: | ---: |
| bn2048-modexp-consttime | 1.25x | **0.97x** | 1.31x | **0.94x** |
| ffdhe2048-secret-to-public | 1.25x | **0.96x** | 1.28x | **0.92x** |
| ffdhe2048-shared-secret | 1.25x | **0.96x** | 1.31x | **0.92x** |
| rsapss-2048-sign | 1.23x | **0.94x** | 1.29x | **0.94x** |
| rsapss-2048-verify | 1.38x | **1.14x** | 1.34x | **1.12x** |

Absolute (gcc, µs): modexp 5663 -> 4394; ffdhe s2p 5756 -> 4468; ffdhe
shared 5754 -> 4458; rsapss sign 5716 -> 4437; rsapss verify 198 -> 166.
The full-table diff shows nothing else outside ±3% run-to-run noise.

### The congruence-merge pathology

This was the real cost of the segment, and it is worth recording because
it will recur. Every hang had one shape: **Z3 proves two integer index
terms equal in the arithmetic theory but does not propagate that
equality into congruence closure underneath an uninterpreted function.**

It does not fail cleanly. It searches, burning the whole rlimit — 600 is
about three minutes, 1200 about six — or, when the rlimit counter does
not advance, running unbounded. Ninety minutes was observed.

It bites wherever a Pulse loop hands back an invariant at `k + 1` and is
asked for it at `SZ.v (SZ.add k 1sz)`; where the loop exits at `vj` and
the contract wants `n`; where `pre v (SZ.v nn)` must meet `num v` via
`Seq.length v == SZ.v nn`; and where `pw 2 (2*e + SZ.v bit)` must meet
`pw 2 (2*e)`.

The demonstration: an `assert (pure ...)` of the invariant at
`SZ.v vj + 1` succeeded in **2.6 s**; the identical invariant at
`SZ.v (SZ.add vj 1sz)` burned rlimit 600 in **190 s**.

The fix works every time: a standalone lemma taking the equation as a
hypothesis and restating the fact at the new index, proved by `()` in an
empty context, called explicitly. Six went in: `idx_subst`, `tri_subst`,
`dg_subst`, `pre_len`, `pw_ext`, and `tri_close` for the algebra. An
in-body `assert (pure ...)` only helps when it is *syntactically* what
the callee delivered; it does not help when a rewrite is still needed.

Factoring the body into a smaller `fn` also helps, for a different
reason — it shrinks what congruence closure has to chew — and that is
what `cols` and `ladder_bit` are.

### The ninety-minute query

`Hacl.Bignum.Montgomery` ran 90+ minutes after `mont_sqr` went in. The
*second* thing done, after one bisection, was to `git checkout` HEAD's
`Base.fst` and `Montgomery.fst` and run the identical probe. **HEAD hung
at the same query.** So there was no regression; `ladder_step` was a
latent hang whose luck my new definitions happened to change. That
redirected the work from "what did I break" to "this query needs
restructuring" — and hoisting the conditional half into `ladder_bit`,
whose contract mentions only the two arrays it touches, took the module
from not terminating to **55 seconds**. This is the third time in this
session that checking the baseline first has been the difference between
an hour wasted and a win.

### The admit harness

What made the segment tractable. Copy the module to `Foo.X.fst`, rename
the `module` line, put `#push-options "--admit_smt_queries true"` after
the opens and `"--admit_smt_queries false --query_stats"` immediately
before the declaration under test. Contracts are still enforced, so the
region under test is checked faithfully. 7–8 min turn-around became 1–4.
Remember `rm -f .depend` when adding or removing the file.

Diagnostic: `--query_stats` prints per-goal wall time and rlimit. If
total SMT time is small but wall time large, the current query is the
one spinning; `ps aux | grep z3-4`, column 10 is cumulative CPU.

### Verification times

`Hacl.Bignum.Base` 7 m 51 s, `Hacl.Bignum.Montgomery` 2 m 02 s (from
not terminating), `Hacl.Bignum.Exponentiation` 5 m 49 s, `make verify
-j16` 9 m 20 s, extract 1 m 44 s, `make test` OK, `make clones` OK (68).

Committed as `425fd09` and pushed. README roadmap item 8.

What is left on these rows is the reduction, not the multiply: 1035 ns
against the multiply's 931 and the squaring's 579, so it is now the
larger half of both. HACL*'s almost-Montgomery variant skips the
conditional subtraction inside the ladder and corrects once at the end;
that is the obvious next thing. Karatsuba is the other, but HACL* only
uses it above len 32, so it buys nothing at 2048 bits.

---

## Part 39 --- The AES key schedule in registers (r38g / r38c)

### Why

Part 38 left AES-GCM as the largest remaining gap, and the gap was entirely at
the short end: 7.06x of EverCrypt at sixty-four bytes against 1.98x at 256
KiB.  A direct measurement of the fixed cost (`/tmp/gcmp/g.c`, a zero-length
call) put it at 328.9 ns, and a measurement of the schedule alone
(`/tmp/gcmp/k.c`) at 258.1 ns for AES-128 and 323.4 for AES-256.  The
schedule was 78% of the fixed cost of a call.

`subword4` -- one AESKEYGENASSIST with its loads -- measures 8.6 ns, and an
AES-128 schedule needs ten.  So at most 86 of the 258 ns is S-box work and
the remaining 172 is the loop structure: four bytes loaded, exclusive-ored
and stored per word, with the store of one word feeding the load of the next.

### What was done

The recurrence was rewritten sixteen bytes at a time:

    K_i = (k ^ (k << 4) ^ (k << 8) ^ (k << 12)) ^ t

shifts in bytes, `k` the round key one key length down, `t` of period four
(RotWord(SubWord(w3)) ^ Rcon at a multiple of the key length, SubWord(w3)
halfway through an AES-256 round key).

New C primitives in `c/Hacl_Vec128.h`, all single instructions:
`Hacl_Vec128_bcast_rot` (PSHUFB with 9,10,11,8 repeated),
`Hacl_Vec128_bcast_sub` (PSHUFB with 8,9,10,11 repeated),
`Hacl_Vec128_word_bcast` (PSHUFD / `_mm_set1_epi32`).  `shift_left_bytes_4`
restated byte-wise.

New F* in `code/aes/Hacl.AES.Key.fst`: `prefix_xor`, `round_term`,
`ks_round_vec`, `ks_block_ni`, `ks_loop_ni`, with the old word loop kept as
`ks_loop_scalar` behind a `Vec.supported ()` dispatch.

### The proof, which was most of the work

Three separate SMT pathologies, each worth recording:

1. **`( ^^ )` blocks congruence.**  `Spec.Byte.( ^^ )` is
   `U8.v (U8.logxor (uint_to_t a) (uint_to_t b))`.  Knowing `b == 0` as
   integers does not give `a ^^ b == a ^^ 0`: `0uy` encodes as a bit-vector
   literal, `uint_to_t b` as a boxing application, and congruence closure
   does not cross.  Not caused by `--smtencoding.elim_box` (tested with it
   off).  Fix: do the algebra at `FStar.UInt.logxor` (`lx`, `lx_is`,
   `lx_zero`, `lx_assoc`) and cross back one application at a time.
   `xor_cong` and `xor_drop` are the two bridges used everywhere else.

2. **Symbolic indices under `Seq.index`.**  `forall i < 4. Seq.index x (8+i)
   == ...` will not discharge `Seq.index x (8 + j % 4)` for symbolic `j`.
   Ground offsets are fine.  Fix: state at literal indices (`is_rot_term`,
   `is_sub_term`), instantiate quantified axioms through a small named lemma
   at literal arguments (`subword_index`).

3. **`unfold` on a four-term expression.**  `pfx` was `unfold`, so every
   derived fact carried `(byte0 a i ^^ byte0 a (i-4)) ^^ (byte0 a (i-8) ^^
   byte0 a (i-12))` with its conditionals.  Sixteen of those in one context
   and Z3 spends its whole budget on the hypotheses.  Making `pfx` an
   ordinary definition took `round_all` from failing at 500 s to succeeding
   at 0.00 s.  This was the single largest win in the whole exercise.

Beyond that, the governing constraint is that a Pulse `fn` query carries the
heap, the slprops and every byte of the key.  Measured there: a goal of
`Seq.length (Seq.slice vw0 b b2) == 16` did not close at rlimit 800 in
345 s.  The same goal closes instantly as a standalone lemma.  So every
bridge is its own lemma -- `block_step`, `block_tele`, `block_grp4/8/12`,
`mk_join4/8/12`, `mk_low`, `mk_high`, `load_index`, `load_index4`,
`grp_mod`, `slice_index` -- and all offset arithmetic is asserted at the top
of `ks_block_ni`, before any loads, where the context is three values wide.
Reordering the function body to hoist those asserts took it from failing at
rlimit 800 to verifying with one 68 s query.

Also: an `[@@SMTPat]` on `Seq.index (Seq.slice s lo hi) i` was actively
harmful in the Pulse context and was removed; the lemma is now called
explicitly, sixteen times, inside `load_index`.

Module verification time: 2m05s (was ~2-3 min before the change).
`make verify -j16` 9m02s, `make extract` 1m46s, `make test` passes, `make
clones` unchanged at 68.

### Microbenchmarks (gcc -O3 -march=native, core 6)

| | before | after |
| --- | ---: | ---: |
| `ks128` | 258.1 ns | **26.4 ns** |
| `ks256` | 323.4 ns | **49.0 ns** |
| gcm128 n=0 | 328.9 ns | **89.8 ns** |
| gcm128 n=0 aad=16 | -- | 93.8 ns |
| gcm128 n=64 | -- | 181.9 ns |
| gcm128 n=1024 | -- | 740.8 ns |
| gcm128 n=16384 | -- | 8712.8 ns |

The 89.8 ns that remains is 26.4 ns of schedule and roughly 60 ns of GHASH
key powers -- `H` through `H^8`, eight PCLMULQDQs and eight reductions.

### Benchmark deltas, r37 -> r38

Only the AES-GCM short rows moved.  Everything else is within 4%.

gcc:

| primitive | size | r37 | r38 |
| --- | ---: | ---: | ---: |
| aes128-gcm-enc | 64 | 7.06x | **3.18x** |
| aes128-gcm-enc | 1024 | 3.11x | **2.38x** |
| aes256-gcm-enc | 64 | 6.89x | **3.27x** |
| aes256-gcm-enc | 1024 | 3.14x | **2.41x** |

clang:

| primitive | size | r37 | r38 |
| --- | ---: | ---: | ---: |
| aes128-gcm-enc | 64 | 6.84x | **3.27x** |
| aes128-gcm-enc | 1024 | 2.72x | **2.03x** |
| aes256-gcm-enc | 64 | 6.98x | **3.09x** |
| aes256-gcm-enc | 1024 | 2.81x | **2.06x** |

Absolute: aes128-gcm-enc at 64 bytes goes 148 -> 328 MB/s (gcc), the
reference unchanged at 1044.  At 16 KiB and 256 KiB nothing moves, which is
the control -- the schedule is a fixed cost and bulk throughput should not
see it.

### What is next

Two items were added to the README roadmap:

10. **An expanded-key context for AES-GCM.**  The remaining 89.8 ns is all a
    function of the key.  EverCrypt exposes `EverCrypt_AEAD_create_in` and
    the reference shim pays it once; ours pays per call.  An `init` +
    `encrypt_with_ctx` pair makes the comparison symmetric and should take
    the 64-byte row to about 1.3x.  Small proof burden, mostly API design.
    This is now the largest single number available in AES-GCM.

11. **Deferring the one-bit shift in GHASH**, 27% of the eight-way loop.
    `Spec.CLMUL.shift_lo_gen`/`shift_hi_gen` are already generic in the
    coefficient function; what is missing is a block-from-a-bit-function
    constructor.

Commit `73b6161` on `perf`, pushed.


---

# Part 40 --- Where the GHASH aggregation passes should start

## The question

Part 39 left the fixed cost of an AES-128-GCM call at 89.8 ns and pointed at
an expanded-key context as the next move.  Profiling the call first said
something different.  The breakdown, gcc `-O3 -march=native`, `taskset -c 6`:

| stage | ns |
|---|---:|
| `ks128` | 26.6 |
| `hkey` | 2.4 |
| `j0` (12-byte IV) | 0.0 |
| `gtag` a=0 c=0 | 41.5 |
| `gtag` a=0 c=64 | 98.2 |
| `ctr` 64 B | 11.5 |
| whole call, n=0 | 90.8 |
| whole call, n=64 | 169.0 |

The schedule is no longer the largest term.  `gtag_impl` is, and inside it:

| component | ns |
|---|---:|
| `ghash_upd` n=0 | 4.9 |
| `ghash_upd` n=16 | 17.9 |
| `cipher_impl` (one AES block) | 15.4 |
| `gadd_at`, `copy_exact`, `put_lenblock` | ~0 |

which accounts for 41.5 as one AES block on `J0` plus one GHASH
multiplication of the length block plus stack.  Both are dependent chains.
Neither is cacheable.  That already casts doubt on the context idea, and the
doubt turned out to be right -- see *The correction* below.

## The finding

The interesting number is `gtag` a=0 **c=64** at 98.2, of which 62 is a
64-byte `ghash_upd`.  Sweeping `ghash_upd` against a patched copy of
`dist/Hacl.c` with the two dispatch thresholds moved:

| config | 64 | 128 | 160 | 192 | 256 | 384 | 512 | 768 | 1024 | 2048 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| shipped (4-way from 64, 8-way from 128) | 69.5 | 147.6 | 179.3 | 176.5 | 194.7 | 238.4 | 284.5 | 376.9 | 468.7 | 834.7 | 1555 |
| serial only | 64.7 | 123.4 | 152.3 | 182.3 | 241.2 | 359.4 | 477.9 | 714.5 | 959.1 | 1888 | 3775 |
| 4-way from 128, no 8-way | 62.3 | 100.8 | 132.2 | 128.4 | 157.3 | 216.2 | 270.4 | 388.9 | 498.9 | 950.0 | 1843 |
| 4-way from 128, 8-way from 768 | 62.8 | 102.8 | 134.1 | 130.9 | 159.9 | 217.3 | 274.8 | 387.3 | 480.4 | 855.5 | 1594 |

Both shipped thresholds were set to the smallest size at which the pass can
run at all, and both are far too low.  One group of four loses to four
serial multiplications: three multiplications have been spent to buy three
reductions, and on this machine the reduction is the cheaper half.  Two
groups win.  The eight-way pass is worse -- it trails the four-way pass to
five hundred and twelve bytes and is only level at seven hundred and
sixty-eight -- because it spends four more multiplications to go from one
reduction in four to one in eight.

## The change

`four_limit` returns 0 below 128 bytes; `eight_limit` returns 0 below 768.
Both are provably neutral: `ghash_start` asks only for `lim % 64 == 0 /\
lim <= n` and `lim8 % 128 == 0 /\ lim8 <= lim`, and 0 satisfies all four.

The one real obligation is `lim8 <= lim`.  With independent thresholds on
`n` that can break -- at n=100 a naive `eight_limit` would still be fine,
but the contract no longer *proves* it, because `four_limit`'s postcondition
no longer pins `lim` to `n - n % 64`.  The fix is to pass `lim` in:

```fstar
let eight_limit (n: SZ.t { SZ.v n % blocklen == 0 }) (lim: SZ.t)
  : Pure SZ.t (requires SZ.v lim <= SZ.v n /\
                        (SZ.v n >= 128 ==> SZ.v lim == SZ.v n - SZ.v n % 64))
         (ensures fun r -> ... /\ SZ.v r <= SZ.v lim)
  = lim8_bounds (SZ.v n);
    if SZ.lt n 768sz then 0sz else SZ.sub n (SZ.rem n 128sz)
```

with a matching extra conjunct on `four_limit`.  Verified first try, no new
lemmas.

Alongside it, `ghash_upd_impl`'s `tb` scratch block moves inside the
`rem > 0` branch.  In Pulse a `let mut` inside an `if` needs no invariant
work at all; the frame is local to the branch.

## Two things that looked like wins and were not

**An `n == 0` early-out in `ghash_upd_impl`.**  `gtag_impl` hashes three
buffers and two of them are usually empty, and `ghash_upd` at n=0 measures
4.9 ns, so guarding the `ghash_loop_ni` call with `nblk > 0` looked free.
It is not free.  A/B on the sweep:

| variant | 768 | 2048 |
|---|---:|---:|
| both reverted | 378.6 | 826.1 |
| `tb` hoisted only | 376.4 | 831.3 |
| `nblk > 0` guard only | 384.5 | 862.6 |
| both | 398.4 | 878.0 |

The guard costs 4% at large sizes and gains nothing measurable at small
ones (`gtag` a=0 c=0 was 41.5 with and 41.7 without).  The 4.9 ns is the
probe harness floor, not the function.  Removed.

**Caching the CPU feature test.**  `Hacl_Vec128_supported` calls
`__builtin_cpu_init` and four `__builtin_cpu_supports` on every dispatch
point, which measures 2.16 ns in a tight loop, and a GCM call makes eight of
them.  Caching it in a `static signed char` took the microbenchmark to 0.039
ns -- and moved the whole-call number not at all (153.3/86.9 without the
cache against 151.2/90.1 with, three runs each, well inside the noise).  The
calls are spread out and overlap with real work.  Reverted: a change with no
measurable benefit is not worth a data race question, however benign.

Both of these are worth recording because both were confidently predicted
from a component measurement and both were wrong at the whole-call level.

## Results

`ghash_upd`, gcc, sequential runs on core 6:

| bytes | before | after | |
|---|---:|---:|---:|
| 64 | 70.8 | 62.9 | -11% |
| 96 | 101.4 | 93.4 | -8% |
| 128 | 151.7 | 97.9 | **-35%** |
| 160 | 180.6 | 127.3 | -30% |
| 192 | 179.1 | 127.5 | -29% |
| 256 | 195.1 | 155.7 | -20% |
| 320 | 219.6 | 184.3 | -16% |
| 384 | 239.3 | 211.8 | -11% |
| 512 | 289.5 | 269.1 | -7% |
| 768 | 378.9 | 383.9 | +1.3% |
| 1024 | 467.4 | 478.9 | +2.4% |
| 2048 | 832.8 | 847.9 | +1.8% |

The regression above 768 is code layout, not work: a build of the new
`Hacl.c` with the branches manually removed measures the same 878 at 2048,
so it is the presence of the conditional in the function, not the value it
computes.  It is not worth triplicating the call site to recover 2%.

Under clang the picture differs in one instructive place.  clang's serial
multiplication is 14.0 ns a block against gcc's 17.9, and its aggregated
loop is faster still (2048 bytes: 625 ns against gcc's 833).  So clang's
four-way pass *wins* at 64 bytes where gcc's loses:

| bytes | 64 | 96 | 128 | 192 | 256 | 512 | 2048 |
|---|---:|---:|---:|---:|---:|---:|---:|
| clang before | 46.3 | 65.4 | 100.1 | 121.0 | 139.1 | 204.7 | 625.3 |
| clang after | 47.8 | 71.2 | 65.9 | 85.5 | 103.6 | 185.4 | 624.9 |

The four-way threshold that is right for gcc is one size too high for
clang; the eight-way threshold, where the large gains are, is right for
both.  Shipping one threshold means gcc gains at 64 bytes and clang neither
gains nor loses there.

Benchmark, r38g -> r39g (gcc):

| primitive | size | before | after | was | now |
|---|---:|---:|---:|---:|---:|
| aes128-gcm-enc | 64 | 328 MB/s | 351 MB/s | 3.18x | **2.98x** |
| aes256-gcm-enc | 64 | 266 MB/s | 282 MB/s | 3.27x | **3.12x** |
| aes128-gcm-enc | 1024 | 1323 | 1323 | 2.38x | 2.40x |
| aes128-gcm-dec | 16384 | 1850 | 1869 | 1.99x | 1.98x |
| aes128-gcm-enc | 262144 | 1858 | 1877 | 1.99x | 1.97x |

Nothing else in the gcc table moves by more than 1.7%.  The clang run
(r39c) kept only 17 of 36 samples and shows a uniform 1-2% downward drift
across untouched primitives (blake2s, sha1, chacha20), so it is a slower
session rather than a regression.

## The correction

Roadmap item 10 claimed an expanded-key context would take the
sixty-four-byte row from 3.18x to about 1.3x, on the grounds that the bulk
of the 89.8 ns fixed cost was the GHASH key powers.  That is wrong, and the
measurement above says why: the powers are not precomputed at all.
`ghash_start` builds them inside the call and only when it is about to run
an aggregated pass, which after this change a short message does not do.
The cacheable part is the schedule (26.6) and `H` (2.4), so a context is
worth about 29 ns of 89: the sixty-four-byte call would go 157 -> ~128 ns,
which is 2.98x -> about **2.4x**.

It is still worth doing -- the comparison against EverCrypt's
`create_in`/`encrypt` handle is asymmetric today, and a context is the
natural place to cache the key powers too, which would make these
thresholds irrelevant at short lengths and turn a 64-byte GHASH into one
group of four.  But it is no longer obviously the top of the list.

## What is left of the fixed cost

Of the 42 ns `gtag_impl` spends with no associated data and no message,
15 are one AES block on `J0` and 19 are one GHASH multiplication of the
length block.  Both are latency chains.  Nineteen nanoseconds for a single
`gmul` is about 57 cycles, which is a long way above the ~21 cycles of
`PCLMULQDQ` latency on the critical path, and the difference is the one-bit
shift and the byte reversal around it -- which is exactly roadmap item 11.
That is the next thing to try.

## Commit

`8c93f00` --- *Start the GHASH aggregation passes where they begin to pay*.
`code/aes/Hacl.AES.GF128.NI.fst` (both limits), `code/aes/Hacl.AES.GHash.fst`
(the `tb` hoist), `README.md` (new section, item 10 corrected), `dist/Hacl.c`.
`make verify` 5m27s, `make extract` 1m45s, `make test` green, `make clones`
68 unchanged.

---

## Part 41 --- Removing the one-bit shift from GHASH

Roadmap item 11, taken in a stronger form than the item proposed.

### The idea

GHASH's bit order is the reverse of `PCLMULQDQ`'s, so after `PSHUFB` the
carry-less product sits one bit low.  `raw_product` corrected this with a
255-bit left shift by one, which on SSE is six instructions (`PSRLQ`,
`PSLLQ`, a byte shift, three `POR`s) because there is no 128-bit shift.  In
the eight-way loop eight products are formed before any reduction, so the
shift was the largest remaining item in the multiplier --- about 27% of the
loop.

Item 11 proposed hoisting it out of the loop, which linearity permits.  The
shift can be removed outright instead.  Write `NS(a,b)` for the unshifted
multiplier; then `NS(a,b) = x * (a*b)`.  Storing the key as `H' = H/x`
makes `NS(a,H') = a*H`.  The powers recurrence needs no change at all:
started at `H'` it produces `H^i/x` at every step, which is the pre-divided
form of `H^i`.  That observation is the three-line `power_step` lemma.

The division is done once, at GCM key expansion.  A per-call vector `xdiv`
was costed at ~2.5 ns and would have been a net loss at short lengths.

### Proof chain

1. `Spec.CLMUL.clmul_halves_ns` --- the unshifted registers reverse to the
   halves of `pshift P 1`, `P = pmul (pbits x) (pbits y)`.
2. `Spec.GF128.Poly.psplit` --- reduce an arbitrary 256-coefficient
   polynomial from its two halves.  This is `gmul_split` generalised off
   products, and it is what makes everything else possible.
3. `Spec.GF128.Algebra.pmod_shift1` --- `pmod (pshift a 1) n == xtimes
   (pmod a n)` given `pget a (n-1) == false`.  A restatement of `x^(k+1) =
   x * x^k`; the one place where defining `pmod` as a sum over set bits pays
   off.  Side condition from `Poly.pcoef_top`.
4. Existing `gmul_xt_right` moves the `x` into the operand, giving
   `Spec.CLMUL.pmodx : pmod (pshift1 x y) 256 == gmul x (xtimes y)`.
5. `Poly.xtimes_xdiv` closes the loop at key setup.

Supporting: `bsum_shift1`, `pmod_unfold`, `halvesp`, `pmod_three`,
`pmod_defer4`, `pmod_defer8`, `gmulx_three`, `pterm_p`, `psplit_low/high/bit`.

### `xdiv`

`xdiv v` = shift the 16-byte big-endian block left one bit; if the bit that
fell off (MSB of byte 0) was set, `v[0] ^= 0xc2` and `v[15] ^= 1`.  That
constant is `R/x = x^127 + x^6 + x + 1`, which is also `x^-1`.

The first version tested `vi == 15` inside the loop.  Hoisting byte fifteen
out of the loop --- it has no successor to supply a carry --- removed the
only branch in the body:

| | ns |
|---|---:|
| `xdiv_impl`, branch in loop | 13.84 |
| `xdiv_impl`, byte 15 hoisted | **5.12** |

That 8.7 ns is the difference between a 5.9% regression and a 2.0% one at
sixteen bytes.

### Back-to-back A/B against `8c93f00` (gcc, one core)

`Hacl_AES_GCM_aes128_encrypt`, 16-byte AAD:

| bytes | before | after | gain |
|---:|---:|---:|---:|
| 16 | 126.2 ns | 128.7 ns | **-2.0%** |
| 64 | 170.8 | 163.7 | +4.2% |
| 256 | 298.7 | 265.4 | +12.5% |
| 1024 | 746.9 | 610.6 | +22.3% |
| 16384 | 8843 | 6871 | +28.7% |
| 262144 | 137157 | 105936 | +29.5% |

The sixteen-byte row is the 5 ns of key division, which the one-shot API
pays on every call.  A context (roadmap 10) removes it.

### Benchmark suite, `r39` -> `r41`

gcc (77 rows; nothing outside AES-GCM moved by 3%):

| primitive | size | r39g | r41g | gain | was | now |
|---|---:|---:|---:|---:|---:|---:|
| aes128-gcm-enc | 16384 | 1860 | **2326** MB/s | +25.1% | 1.97x | **1.57x** |
| aes128-gcm-enc | 262144 | 1877 | **2329** | +24.1% | 1.97x | **1.58x** |
| aes128-gcm-dec | 16384 | 1869 | **2318** | +24.0% | 1.98x | **1.58x** |
| aes256-gcm-enc | 16384 | 1675 | **2031** | +21.3% | 2.03x | **1.68x** |
| aes256-gcm-enc | 262144 | 1692 | **2039** | +20.5% | 2.03x | **1.69x** |
| aes128-gcm-enc | 1024 | 1323 | **1555** | +17.5% | 2.40x | **2.02x** |
| aes256-gcm-enc | 1024 | 1182 | **1380** | +16.8% | 2.39x | **2.04x** |
| aes256-gcm-enc | 64 | 282 | 291 | +3.2% | 3.12x | 2.99x |
| aes128-gcm-enc | 64 | 351 | 357 | +1.7% | 2.98x | 2.92x |

clang:

| primitive | size | r39c | r41c | gain | was | now |
|---|---:|---:|---:|---:|---:|---:|
| aes128-gcm-dec | 16384 | 2205 | **2644** MB/s | +19.9% | 1.66x | **1.39x** |
| aes128-gcm-enc | 262144 | 2185 | **2610** | +19.5% | 1.67x | **1.40x** |
| aes128-gcm-enc | 16384 | 2206 | **2633** | +19.4% | 1.65x | **1.38x** |
| aes128-gcm-enc | 1024 | 1534 | **1809** | +17.9% | 2.06x | **1.74x** |
| aes256-gcm-enc | 262144 | 1920 | **2261** | +17.8% | 1.77x | **1.50x** |
| aes256-gcm-enc | 16384 | 1929 | **2241** | +16.2% | 1.75x | **1.51x** |
| aes256-gcm-enc | 1024 | 1358 | **1551** | +14.2% | 2.07x | **1.81x** |

AES-128-GCM at 256 KiB is now **1.38x** of EverCrypt's Vale assembly under
clang, from 1.98x when this session's GCM work began and 4.48x before any of
it.

### Thresholds

Re-swept over twelve A/B builds of `dist/Hacl.c` (four-way 64/128/192,
eight-way 256/384/512/768).  128 and 768 remain optimal: the serial multiply
got cheaper, but so did the aggregated passes, so the crossovers did not
move.

### F*/Pulse notes

- `bsum_ext` against a hand-written lambda will not connect to a closure
  inside a definition; write a trivially-proved unfolding lemma
  (`pmod_unfold b n : Lemma (pmod b n == bsum (fun k -> ...) n) = ()`) and
  call it at both instantiations.
- `xsum_zero` on a raw summand closure fails where `conv_def` followed by
  `xsum_zero (fun (_: int) -> false)` succeeds.
- Rewriting under a binder wants `Classical.forall_intro` of a *named* `aux`
  lemma, not `bsum_ext` alone.
- Anything mentioning `xt _ 1` needs `--fuel 2` locally; these modules push
  `--fuel 0`.
- `Hacl.AES.GF128.fst` is arithmetic-heavy: `xdiv_impl` needs
  `--z3rlimit 1500` and the module takes ~25 minutes on its own.

### Files

`aa2aff0` --- *Remove the one-bit shift from GHASH by pre-dividing the hash
key*.  `spec/Spec.GF128.Poly.fst`, `spec/Spec.GF128.Algebra.fst`,
`spec/Spec.CLMUL.fst`, `code/aes/Hacl.AES.GF128.NI.fst`,
`code/aes/Hacl.AES.GF128.fst`, `code/aes/Hacl.AES.GMul.fst`,
`code/aes/Hacl.AES.GHash.fst`, `code/aes/Hacl.AES.GCM.fst`, `README.md`,
`dist/Hacl.c`.  `make verify`, `make extract`, `make test` (450 CAVP cases)
and `make clones` (68) all green.

---

## Part 42 --- An expanded-key context for AES-GCM

Roadmap item 10.

### The split

`Spec.GCM.gcm_encrypt_w v w iv a m` is `gcm_encrypt` with the expansion
already done; `gcm_encrypt v key iv a m` is now `gcm_encrypt_w v
(key_expansion v key) iv a m`, by definition.  Same for `gcm_decrypt_w`.

Implementation: `expand_impl` (key expansion + `hkey_impl`), `encrypt_w` /
`decrypt_w` (everything after), and the one-shot `encrypt` / `decrypt` are
the two in sequence over a stack context.  No proof moved; verified first
try.

Context is two arrays: `ek` (176 / 240 bytes) and `hk` (16, pre-divided by
`x`).  One array would need `Hacl.Impl.Sub` to lend out two windows at once,
which it cannot; nothing needs them adjacent.

Exports: `aes128_expand`, `aes128_encrypt_expanded`,
`aes128_decrypt_expanded`, and the AES-256 three.  One-shot four unchanged.

### Direct measurement (gcc, one core)

`Hacl_AES_GCM_aes128_encrypt` vs `..._encrypt_expanded`, 16-byte AAD:

| bytes | one-shot | expanded | gain |
|---:|---:|---:|---:|
| 16 | 131.4 ns | **95.8** | +37.1% |
| 64 | 166.6 | **132.7** | +25.5% |
| 256 | 270.1 | **233.9** | +15.5% |
| 1024 | 600.5 | **569.2** | +5.5% |
| 16384 | 6772 | **6702** | +1.0% |

Fixed cost removed: **35.6 ns**, against the roadmap's estimate of 29.  The
difference is the 5 ns of key division added by Part 41.

### Benchmark suite, `r41` -> `r42`

`shim_pulse.h` now builds the context in `bs_aes128gcm_setup`, which is what
the reference shim has always done with `EverCrypt_AEAD_create_in`.  Only
the four short-message AES-GCM rows moved; bulk is unchanged, as expected.

gcc:

| primitive | size | r41g | r42g | gain | was | now |
|---|---:|---:|---:|---:|---:|---:|
| aes256-gcm-enc | 64 | 291 | **462** MB/s | +58.8% | 2.99x | **1.90x** |
| aes128-gcm-enc | 64 | 357 | **496** | +38.9% | 2.92x | **2.11x** |
| aes256-gcm-enc | 1024 | 1380 | **1560** | +13.0% | 2.04x | **1.81x** |
| aes128-gcm-enc | 1024 | 1555 | **1695** | +9.0% | 2.02x | **1.87x** |

clang:

| primitive | size | r41c | r42c | gain | was | now |
|---|---:|---:|---:|---:|---:|---:|
| aes256-gcm-enc | 64 | 285 | **444** MB/s | +55.8% | 3.06x | **1.97x** |
| aes128-gcm-enc | 64 | 326 | **477** | +46.3% | 3.19x | **2.18x** |
| aes256-gcm-enc | 1024 | 1551 | **1784** | +15.0% | 1.81x | **1.57x** |
| aes128-gcm-enc | 1024 | 1809 | **2018** | +11.6% | 1.74x | **1.56x** |

AES-256-GCM at sixty-four bytes is the first AES-GCM measurement in this
session to go under 2x of EverCrypt's Vale assembly at a short length.

### Validation

`make verify` clean first try, `make extract` clean, `make clones` 68.
`tests/test_gcm.c` now runs every case twice, once per path: *all 450 CAVP
cases passed, one-shot and expanded*.

### Not done

Caching the GHASH key powers in the context.  That would make the
aggregation thresholds of Part 40 irrelevant and turn a sixty-four-byte
GHASH into one group of four, but it is the larger half: the powers are
`Vec128` values and the context is bytes.

### Files

`f76996a` --- *Add expanded-key entry points for AES-GCM*.
`spec/Spec.GCM.fst`, `code/aes/Hacl.AES.GCM.fst`, `tests/test_gcm.c`,
`Makefile` (six new Custard entries), `README.md`, `dist/Hacl.c`,
`dist/Hacl.h`.  Session-side: `bench/shim_pulse.h`.

---

## Part 43 — Poly1305, and the byte loop underneath everything

### Where Poly1305 stood

1.35x of HACL\*'s portable C at 256 KiB, running the *same* algorithm: five
limbs of twenty-six bits, schoolbook product, one carry chain.  Three things
were tried.

### 1. The 5·r precomputation — worth ~2%

`r` went from five limbs to nine, with `r[5..8] = 5·r1 … 5·r4` filled once
per message by `load_r` and related by a new `has5` invariant.  `mul_limbs`
computes `h_i · (5 r_j)` instead of `5 · (h_i · r_j)`: twenty-five multiplies
instead of thirty-five.

Measured (gcc, 1 KiB): 3.427 → 3.343 cpb.  gcc compiles `5*x` to a single
`lea rax,[rax+rax*4]`, so the ten "extra" multiplies were never in the object
code.

### 2. The two-parallel carry chain — worth 0%

Reworked `Spec.Poly1305.Field.chain` and `carry_chain_impl` into HACL\*'s
shape: one chain from limb 0, one from limb 3, each carrying two places, the
wrap from the top rejoining them.  Four steps with two independent shifts
each instead of six serial steps.

Measured: 3.383 cpb.  Noise.  The carry chain was not the critical path.

### 3. `load_le` — worth 1.18x gcc, 1.54x clang

The generated C for `Hacl.Impl.Bytes.load_le`:

```c
static uint64_t Hacl_Impl_Bytes_load_le__t_1(uint8_t *b, size_t off) {
  size_t n = Hacl_Secret_Word_nbytes__t_1;   /* a C global, = 8 */
  uint64_t acc = 0;
  for (size_t j = 0; j < n; j++)
    acc = (acc << 8) | b[(off + n) - (j + 1)];
  return acc;
}
```

Eight serially dependent iterations per word, two words per sixteen-byte
Poly1305 block.  And because the trip count is a class field, which Custard
emits as a global, no compiler unrolls it.

#### The shape experiment that decided the design

Three C shapes, counting `movzbl` in the generated assembly:

| shape | gcc | clang |
| --- | --- | --- |
| `b[0] \| b[1]<<8 \| …` (or-tree) | 8 byte loads | **merged to one load** |
| `b[0] + b[1]<<8 + …` (add-tree) | 8 byte loads | **merged** |
| `acc = acc<<8 \| b[k]` unrolled | 8 byte loads | **merged** |

clang merges all three; gcc merges none.  But in the real benchmark gcc went
3.28 → 2.65 cpb with the or-tree and 3.28 → **3.88** with the unrolled chain.
gcc does not merge, so what it gets is eight independent loads and a
three-deep or-tree — and what it gets from the chain is eight loads on an
eight-deep chain, which is *worse* than the loop.  **The or-tree form is not
an aesthetic choice; it is the whole effect on gcc.**

#### The implementation

`load_le4` / `load_be4` read exactly four bytes with no loop.  Four is the
useful width: `bits` is at least thirty-two for every `word` instance, so no
precondition is needed and both instances use it.  `load_le` keeps its
signature and dispatches on `nbytes` — 4, 8, or the old loop — and the old
loop is hoisted into `load_le_loop` so that its proof keeps its original Z3
context.  (It did *not* survive being wrapped in an `if`: the extra
hypotheses alone made it time out.)

Proof: `le_nat_prefix` (extending a prefix by a byte adds it scaled),
`or_byte_le` (`UInt.logor_disjoint` with the operands the right way round),
`be_nat_prefix` / `or_byte_be` as mirrors, `or_half` for joining two
four-byte halves, and `le4_ok` / `be4_ok` — pure lemmas parameterised on the
four machine values, with the equations relating them as hypotheses.  Both
`le4_ok` and `be4_ok` verified first try.

### The store half, written and thrown away

`store_le4` / `store_be4` are the same idea and verified just as easily.
They cost ChaCha20 and Salsa20 **12%**.

| variant (gcc, chacha20 @ 16 KiB) | |
| --- | --- |
| HEAD | 520 MB/s |
| loads only | 518 MB/s |
| loads + stores (with dispatch) | 453 MB/s |
| loads + stores (no dispatch branch) | 433 MB/s |

Counting `xmm` references in `Hacl_Chacha20_encrypt`: 141 before, 122 after.
A *store* loop has no dependency between iterations, so gcc — which does
know `nbytes == 4` by IPA-CP even though it will not unroll against a global
— was already vectorizing ChaCha20's sixteen-word keystream store into SSE.
Hand-written stores gave the vectorizer a shape it did not recognize.

The asymmetry is the lesson: a serial dependency cannot be vectorized at
all, so the load loop had no escape hatch and was worth a fifth of Poly1305;
the store loop had one and was already taking it.  **Reverted.**

### Results (r44g / r44c vs r42g / r42c)

gcc:

| | before | after | |
| --- | --- | --- | --- |
| poly1305 1 KiB | 897 MB/s | 1055 MB/s | 1.18x |
| poly1305 16 KiB | 929 MB/s | 1099 MB/s | 1.18x |
| poly1305 256 KiB | 931 MB/s | 1098 MB/s | 1.18x |
| chacha20poly1305-enc 256 KiB | 324 MB/s | 346 MB/s | 1.07x |
| nacl-secretbox 256 KiB | 323 MB/s | 339 MB/s | 1.05x |

clang:

| | before | after | |
| --- | --- | --- | --- |
| poly1305 1 KiB | 875 MB/s | 1347 MB/s | 1.54x |
| poly1305 16 KiB | 898 MB/s | 1381 MB/s | 1.54x |
| poly1305 64 B | 655 MB/s | 926 MB/s | 1.41x |
| nacl-secretbox 16 KiB | 309 MB/s | 354 MB/s | 1.15x |
| sha2-512 256 KiB | 300 MB/s | 316 MB/s | 1.05x |
| hmac-sha2-512 256 KiB | 299 MB/s | 311 MB/s | 1.04x |

No regression over 3% on either compiler.  Poly1305 goes from 1.35x of
HACL\* to **1.14x** under gcc, and under clang past it (1347 vs HACL\*'s
~1250 MB/s).

### Things that cost time and are worth remembering

- **A standalone C model mispredicted badly.**  A hand-written fused
  Poly1305 inner loop ran at 1.65 cpb and suggested the `d`/`e` scratch
  arrays were the problem; making `d` a stack local in the real generated C
  changed nothing, and hand-fusing the whole block loop was worth 7%, not
  2x.  Patch `dist/Hacl.c` and measure that.
- **`make verify` had been passing on a stale `.checked`.**  `is_product`
  and `fmul_ok` had been generalised to take five `nat`s without their call
  sites being updated; this only surfaced after `rm -f .depend`.
- **Adding definitions to a module breaks unrelated proofs downstream.**
  Three separate instances this part: `Hacl.Poly1305.Load.store_tag`,
  `Spec.Poly1305.Field.ripple_eval`, and `load_le_loop` once it was wrapped
  in an `if`.  Hoisting into a top-level definition fixes it; raising the
  rlimit does not.
- **Linear arithmetic times out in a big context.**  `32 + 8*(3-k) ==
  8*(7-k)` would not prove inside a lemma whose `requires` was four
  quantified frame conditions.  Pulled out into its own lemma: instant.

### Next

GLV for k256 verify (2.52x, the largest remaining gap), Shamir's trick for
the two verifies, caching GHASH key powers in the AES-GCM context, P-256's
special prime, MD5 (1.43x), and Poly1305 at radix 2^44 on `uint128`.

---

## Part 44 --- ML-KEM: a bit string is a number

### Where this started

Roadmap item 9 said the biggest single number left was a *specialisation*
gap: `make clones-available` listed thirteen functions gcc would clone and
could not, because the interprocedural constant propagation budget is spent
on a 2 MB translation unit, and four of the thirteen were in ML-KEM.
Recompiling with `--param ipa-cp-large-unit-insns=1000000 --param
ipa-cp-unit-growth=100` was worth 1.33x on encapsulation.

ML-KEM is not in `bench.c` (HACL\* has no ML-KEM), so `/tmp/gcmp/mk.c` was
the harness: keypair/enc/dec over all three parameter sets, `taskset -c 2`.

| mlkem768, us | keypair | enc | dec |
| --- | --- | --- | --- |
| normal budget | 114.84 | 153.04 | 198.26 |
| big IPA budget | 113.14 | 115.02 | 157.07 |

### The bisect

Rather than guess which of the four clones mattered, each candidate was
given `__attribute__((noclone,noinline))` in turn *in the big-budget build*
and the sweep re-run.  Anything that returns the numbers to the normal-budget
row is the clone that was doing the work.

| noclone'd in the big-budget build | keypair | enc | dec |
| --- | --- | --- | --- |
| nothing | 113.1 | 115.0 | 157.1 |
| `MLKEM_Encode_encode_poly` | 114.9 | 153.2 | 198.4 |
| `MLKEM_Sample_sample_poly_cbd_impl` | 113.2 | 115.1 | 157.2 |
| `Hash_SHA3_sha3_512` | 113.3 | 115.3 | 157.4 |
| `Hash_SHA3_shake128` | 113.1 | 114.9 | 157.0 |

The encoder is the entire story.  The other three --- and by extension the
other twelve entries in `clones-available`, none of which is on an ML-KEM
hot path at all --- are worth nothing measurable.

### What the encoder was doing

`Hacl.Impl.MLKEM.Encode.encode_poly` is `ByteEncode_d` as FIPS 203 states
it, bit by bit.  Generated C, eight times per output byte:

```c
size_t i1 = (base + j) / d;   /* d is a run time parameter */
size_t r  = (base + j) % d;
b_j = (f[i1] >> r) & 1;
```

Two integer divisions per bit, 3,072 of them to encode a 384-byte key
polynomial.  The clone turned each into a multiply and a shift.
`decode_poly` divides only by the constant 8, so it never appeared in the
clone list, but it is still a bit-at-a-time loop.

### The model

Per the rule established in Part 31 --- after a standalone model once
predicted 2x for what turned out to be 7% --- the rewrite was first modelled
by patching `dist/Hacl.c` directly, so the comparison is between two builds
of the same 2 MB file.

| mlkem768, us | keypair | enc | dec |
| --- | --- | --- | --- |
| HEAD, normal budget | 114.84 | 153.04 | 198.26 |
| HEAD, big IPA budget | 113.14 | 115.02 | 157.07 |
| accumulator encoder only | 97.52 | 108.38 | 151.70 |
| accumulator encoder + decoder | **98.12** | **104.49** | **137.49** |

Better than the clone ever was, and it does not depend on a compiler
heuristic.  Bit-exactness against HEAD was checked with a DJB hash of
ek/dk/ct/ss over all three parameter sets before writing any F\*.

### The proof

The whole content is `spec/Spec.MLKEM.Pack.fst`, ~400 lines, which says that
packing 256 `d`-bit values least significant first is writing down
`N = sum_j f_j 2^(d j)`, that `Hacl.Spec.Bytes.le_nat` of the byte string is
the same `N`, and therefore that bits may be moved in and out of `N` in any
chunks.

- `enc_num d f i` --- the prefix as a number.  It masks with `% pow2 d`,
  which means **no precondition on the caller**: `coeff_bit` does not read
  above bit `d` either, so the two agree on unreduced inputs as well.  One
  `AND` per coefficient.
- `enc_bit` --- bit `p` of `enc_num` is `coeff_bit d f p`.  Split the sum at
  `p / d`, push the high part out (`high_add_bit`), drop the low part
  (`low_drop`), reconcile the mask (`mask_bit`).
- `byte_val_num`, `byte_encode_prefix` --- lift to bytes, and give byte `o`
  of the final encoding from only the prefix read so far, valid once
  `8 o + 8 <= d i`.  This is the form the loop invariant needs.
- `bits_val_num` --- the decoder direction, `bits_val b off m == le_nat b /
  pow2 off % pow2 m`, three lines of induction on `stream_bit_num`.

It verified on the first real attempt with one fuel bump.  The Pulse side
took six more iterations.

Two choices in the implementation are worth reusing.  The register is never
wider than `8 + d <= 20` bits, so each step's operands are provably disjoint
and their sum provably in range, and the bits can be combined with `add_mod`
rather than `logor` --- same instruction, no bitwise reasoning in the proof.
And `S32` has no `mask_low`, so both registers are `S64` even though 32 bits
would do.

### Result

| mlkem768, us | gcc before | gcc after | | clang before | clang after | |
| --- | --- | --- | --- | --- | --- | --- |
| keypair | 116.81 | 98.10 | 1.19x | 192.12 | 95.35 | **2.01x** |
| enc | 154.21 | 105.45 | **1.46x** | 171.64 | 124.70 | 1.38x |
| dec | 199.52 | 136.96 | **1.46x** | 233.83 | 172.73 | 1.35x |

512 and 1024 move by the same proportions (512: gcc 1.21/1.55/1.48, clang
2.10/1.49/1.43; 1024: gcc 1.18/1.46/1.44, clang 1.87/1.37/1.38).

The clang keygen column is the point of the whole exercise.  clang never
cloned anything, so it was paying every division in full, and key generation
encodes two complete twelve-bit vectors.  A speedup that one compiler grants
at its own discretion and the other does not grant at all is not a speedup;
it is a bug report about the source.

Known-answer tests pass unchanged for all three parameter sets.
`clones.baseline` is unchanged at 69; `clones-available` is down from
thirteen entries to twelve, `encode_poly` having left it.  r45g and r45c
show nothing in the rest of the suite moving by as much as 4%.

### Things that cost time

- **`decreases` must stay non-negative after the body.**  `while (nb < d) {
  nb += 8; }` with measure `d - nb` fails on the last iteration: `<<` on
  `int` is well-founded only on the non-negative part.  `d + 8 - nb` with
  `nb < d + 8` in the invariant is the same measure in range.  The error
  names `meas` and looks like an arithmetic failure.
- **The staircase.**  `SZ.v i == 256` after the loop, from `~(i < 256)` and
  `i <= 256`, timed out at rlimit 600.  Splitting it into `256 <= v i`,
  `v i <= 256`, `v i == 256` as three separate `assert`s made all three
  instant at rlimit 40.  Each assert is its own query over a much smaller
  set of relevant facts; the single combined query drowns in the invariant's
  quantified frame condition.
- **Nonlinearity belongs in a top-level lemma.**  `d * (i+1) <= 256 * d`
  inside the loop body cost the whole rlimit; as `enc_room`, four lines at
  the top level, it costs nothing.  Rule: a goal mentioning a product of two
  variables does not belong in Pulse code.
- **The invariant bound was wrong, not slow.**  The decoder's outer
  invariant said `nb < d`; it has to be `nb < 8`.  The fill loop exits with
  `nb` in `[d, d+8)`, so after taking `d` bits the remainder is `< 8`, which
  only implies `< d` when `d >= 8`.  Found by reading which conjunct of a
  long `Failed to prove` was listed, not by raising the rlimit.
- **`by` is a reserved word**, and the syntax error points at the `=`.
- **`FStar.Math.Lemmas.lemma_mult_comm` does not exist**; it is `swap_mul`.
- **Python `str.replace` has no word boundaries.**  Patching the module with
  a script replaced a post-loop idiom in `decompress_poly` as well as in
  `decode_poly`, and the deleted `stream_bit_impl` turned out to still be
  used by `Hacl.Impl.MLKEM.Sample` --- caught by `make verify`, not by the
  single-module check.
- **`make extract` can silently no-op.**  `ALL_CHECKED_FILES` comes from
  `.depend`, which is included after `mk/extract.mk` is parsed, so the
  dependency list expands empty and only `Hacl.fst.checked` is considered.
  `rm dist/Hacl.c` forces it.

### Next

GLV for k256 verify (2.52x, the largest remaining gap), Shamir's trick for
the two verifies, caching GHASH key powers in the AES-GCM context, P-256's
special prime, MD5 (1.43x), and Poly1305 at radix 2^44 on `uint128`.

---

## Part 45 --- secp256k1: twenty-one is not a field element

### Where this started

`r45g` said the largest remaining gaps were k256-ecdsa-verify 2.57x,
aes128-gcm-enc-64B 2.09x, ed25519-verify 2.00x, k256-ecdh 1.73x,
k256-secret-to-public 1.53x and k256-ecdsa-sign 1.39x.  Four of the six are
secp256k1, so secp256k1 is what got looked at.

The first guess was the ladder, and the first thing done was to read
HACL\*'s `Hacl_K256_ECDSA.c` rather than guess again.  Its fixed-base
`point_mul_g` is the *same* four-table, sixteen-rung shape ours is, rung
for rung.  So the 1.53x on `secret-to-public`, which is pure fixed-base, is
not algorithmic at all; it is one level down, in the field.  (Its
variable-base `point_mul` and its verification *are* algorithmically
different -- GLV plus Shamir -- which is why verify is the worst of the
four and why it stays the worst after this part.)

### What the generated C said

Counting operations in the two formulas, ours against HACL\*'s:

```
             ours                           HACL*
point_add    14 fmul, 14 fadd, 5 fsub,      12 fmul, 4 fmul_small_num,
             18 fcopy                       12 fadd, 5 fsub, 6 fnormalize_weak
point_double 7 fmul + 2 fsqr, 8 fadd,       6 fmul + 2 fsqr,
             14 fcopy                       5 fmul_small_num
```

Three differences, and only one of them turned out to matter:

* HACL\* has `fmul_small_num` and we did not.  The Renes-Costello-Batina
  formulas are stated against a field, so they say `fmul b3 t` where they
  mean twenty-one times `t`.  Taken literally that is a five-by-five
  schoolbook -- twenty-five word multiplications and a 128-bit carry pass
  -- to multiply by a five-bit number.  `8x` in the doubling was three
  carry passes.
* Our `fadd`/`fsub` run a full carry chain every time, written as a `while`
  loop over the array; HACL\*'s are lazy, with explicit `fnormalize_weak`.
* Our `fsqr` is literally `fcopy; fmul`.

### Six C-level experiments

Everything was modelled by patching `dist/Hacl.c` directly, before writing
a line of Pulse.  `/tmp/gcmp/k.c` times secret-to-public / ecdh / sign /
verify under `taskset -c 2` and prints a DJB hash of the outputs so a
wrong model announces itself.

An early sweep gave numbers 45% off.  A control -- adding an *unused*
static function to the 2 MB translation unit -- moved too, so the machine
was disturbed; three interleaved rounds gave the settled table.  This is
the third time in this session that a one-shot `for v in A B C` sweep has
lied, and the control is now part of the protocol.

| variant | s-to-pub | ecdh | sign | verify |
|---|---|---|---|---|
| base (HEAD) | 76.2 | 154.0 | 91.1 | 236.7 |
| control (unused fn) | 74.7 | 153.9 | 90.4 | 234.2 |
| A lazy fadd/fsub, no carry (wrong, ceiling) | 65.0 | -- | 81.5 | -- |
| B symmetric 15-mult `fsqr` | 75.1 | -- | -- | -- |
| C `fsmall` small-constant multiply | 65.8 | 126.3 | 83.3 | 200.4 |
| F straight-line `carry_chain` only | 76.0 | 156.4 | 92.2 | 238.2 |
| G = F + straight-line `fadd`/`fsub` | 70.5 | 139.6 | 86.5 | 215.3 |
| **H = C + G** | **64.0** | **125.0** | **80.4** | **193.2** |
| I = H + lazy adds (ceiling, wrong) | 60.4 | -- | 76.9 | -- |
| J = H + aliased fmul | 64.7 | 123.8 | 80.5 | 193.6 |

Three of the six were worth nothing, and that is the more useful half:

* **B**: gcc already CSEs `fmul(out, a, ac)` with `ac == a` down to the
  fifteen distinct products.  `fsqr` can go on being `fcopy; fmul`.
* **F**: gcc already unrolls `carry_chain`.
* **J**: gcc already eliminates the `fcopy` churn around aliased calls.

And **I** priced the thing we were *not* going to do: a full lazy-reduction
rewrite is six per cent on top of H, for a proof obligation on every
intermediate bound in both formulas.  Declined.

The rule: only shapes the compiler *cannot* fix are worth fixing by hand.
A twenty-five-multiplication product where a five-multiplication one would
do is such a shape; a pointer-walking five-element add loop is such a
shape; a redundant copy is not.

### The implementation

`Spec.K256.Field52.fsmall_spec n a = carry_pass (scale n a)`.  `scale`,
`eval_scale` and `scale_ble` were all already in `Spec.Bignum52`, so the
correctness lemma is eight lines and is `fadd_spec_ok` with `addw a b`
replaced by `scale n a`:

```fstar
let fsmall_spec_ok (n: nat) (a: Seq.seq nat)
  : Lemma (requires felem a /\ n <= 32)
          (ensures felem (fsmall_spec n a) /\
                   fev (fsmall_spec n a) == (n * fev a) % prime)
  = scale_ble n a lim;
    Math.lemma_mult_le_right lim n 32;
    ble_mono (scale n a) (n * lim) (32 * lim);
    assert_norm (32 * lim + 64 < base * 65);
    assert_norm (base - 1 + cf * ((32 * lim + 64) / base) <= lim);
    pass (scale n a) (32 * lim) 64 lim;
    eval_scale n a;
    Math.lemma_mod_mul_distr_r n (eval a) prime
```

The bound is stated once at the largest -- for every `n <= 32` at once --
rather than one carry-pass shape per constant.  The pass that follows is
the same either way, so the slack costs nothing, and there is one lemma
instead of four.  It checked first try.

The Pulse side is five reads, five `mulk n`, five writes and one
`carry_chain a (32 * lim) 64`.  It is **in place on a single array**, which
is what every call site wants and which sidesteps the aliasing that
`fsmall a2 a2 21` would otherwise force the separation logic to argue
about.  The one site where source and destination differ -- `oz = 8 a0` in
the doubling -- does `fcopy oz a0; fsmall oz 8uL`, and gcc removes the
copy.

Four bridge lemmas keep `Spec.K256` verbatim:

```fstar
let two_x   (x: K.felem) : Lemma (K.fadd x x == (2 * x) % prime) = ()
let three_x (x: K.felem) : Lemma (K.fadd (K.fadd x x) x == (3 * x) % prime)
  = Math.lemma_mod_add_distr x (x + x) prime
let eight_x (x: K.felem) : Lemma (...) = four lemma_mod_add_distr
let b3_x    (x: K.felem) : Lemma (K.fmul K.b3 x == (21 * x) % prime) = ()
```

At each call site the instance is supplied at the ghost pre-value:

```
  with va2. assert (A.pts_to a2 va2);
  b3_x (fev (vals va2));
  fsmall a2 21uL;
```

Seven call sites, three in `point_add` and four in `point_double`.  The
`b3` constant table (`KT52.b3_arr`, `fb3`) and the second scratch element
`au` became dead in both and were deleted.

`fadd` and `fsub` were then straight-lined -- the five-element `while` in
`fadd`, the three-element one in the middle of `fsub`.  Both verified first
try; the `Seq.equal` assert that was already there did all the work.

Everything in this part verified on the first attempt, which is unusual
enough to be worth recording: the reason is that `carry_chain` was already
parameterised by its entry bound, so `fsmall` is a new caller of existing
machinery rather than new machinery.

### Measured

`taskset -c 2`, best of three interleaved rounds, hash `65da7292`
unchanged throughout:

```
              gcc              clang
  s-to-pub    76.0 -> 63.9     77.2 -> 70.0
  ecdh       156.2 -> 125.5   153.5 -> 136.1
  sign        92.4 -> 80.4     99.4 -> 92.1
  verify     238.2 -> 194.1   234.5 -> 210.7
```

1.15-1.24x under gcc, 1.07-1.13x under clang.  Full suite into `r46g` and
`r46c`: exactly the four k256 rows move by more than four per cent under
either compiler, and nothing regresses.

Against HACL\* the four rows are now, gcc / clang:

```
  secret-to-public   1.28x / 1.42x   (was 1.53x)
  ecdh               1.39x / 1.52x   (was 1.73x)
  ecdsa-sign         1.19x / 1.39x   (was 1.39x)
  ecdsa-verify       2.12x / 2.29x   (was 2.57x)
```

### One clone lost

`make clones` reported `-Hacl_Bignum_Exponentiation_mont_sq4`.  The
baseline is meant to shrink, but a `-` can also mean the IPA-CP budget was
exhausted by unrelated growth -- and this change *shrinks* the unit, so
that was unlikely.  Confirmed from the suite: `bn2048-modexp-consttime`,
`rsapss-2048-sign` and `rsapss-2048-verify` are all unchanged, so the clone
was worth nothing.  Baseline updated to 68.

### Commits

`b8bb02f` (code, spec, dist), `624187d` (README: the architecture section
*Twenty-one is not a field element*, the performance-table row at its new
1.19x, and roadmap item 12).

### Next

Roadmap item 12 is now the largest single gap and it is algorithmic: GLV
plus Shamir for k256 verify (2.12x) and Shamir alone for ed25519-verify
(1.98x).  After that: AES-128-GCM at 64 bytes (2.14x) and the GHASH key
powers in the AES-GCM context, P-256's special prime, MD5 (1.43x), and
Poly1305 at radix 2^44 on `uint128`.

---

## Part 46 --- The powers of the key belong with the key

Roadmap item 10's remaining half: caching the GHASH key powers in the
AES-GCM expanded-key context.  Sixty-four-byte AES-128-GCM was the largest
non-curve gap in the library at 2.14x.

### The measurement that framed everything

A harness at `/tmp/gcm/g.c` -- expanded-key AES-128-GCM encryption at 64,
128, 256, 1024 and 16384 bytes with a sixteen-byte AAD and a twelve-byte
IV, plus a DJB hash of all the outputs so that a wrong variant announces
itself -- and a series of patched copies of `dist/Hacl.c`:

| variant | 64 | 128 | 256 | 1024 | 16384 |
|---|---:|---:|---:|---:|---:|
| base (HEAD) | 129.8 | 169.6 | 237.2 | 600.3 | 6942 |
| `gN` GHASH stubbed out | 57.8 | 67.6 | 88.6 | 217.8 | 2701 |
| `gT` four-way from 64 only | 142.0 | 168.5 | 238.3 | 598.9 | 7034 |
| `gQ` cached powers, old thresholds | 131.0 | 146.8 | 209.2 | 527.0 | 6786 |
| `gP` cached + four-way from 64 | 117.5 | 147.1 | 207.8 | 523.9 | 6791 |
| `gP128` cached + both unconditional | 114.4 | 147.1 | 203.4 | 514.7 | 6803 |

GHASH is 73 of the 131 ns at sixty-four bytes and 61% of the time at
sixteen kilobytes.  `gT` is the one worth keeping: lowering a threshold
without paying for the powers first makes short messages *worse*, which is
exactly what *Where the GHASH loop should start aggregating* predicted
when it raised those thresholds in the first place.  `gP128` was the best
of the sweep over three interleaved rounds and became the target.

### The implementation

- `Spec.GF128.Algebra`: `hblk` (the i-th sixteen-byte window of a value
  sequence, zero if out of range), `pow_step`, `powlen = 128`, `pows_ok`
  -- the recurrence only, no closed form -- and `pow_adv`, one application
  of `gmul_xt_left` that turns `gmul a (xtimes b)` into the step the
  recurrence wants.
- `Hacl.AES.GF128.NI`: `four_limit` and `eight_limit` unconditional,
  `load_pow` replacing the `gmul_vec`/`power_step` chain in `ghash_start`,
  and `ghash_loop_ni` taking the 128-byte context.
- `Hacl.AES.GHash`: `ghash_upd_impl` takes the 128-byte context and uses
  `Hacl.Impl.Sub.sub h 0 16` at the two portable `gmul_add_impl` sites.
- `Hacl.AES.GCM`: `hkey_impl` builds the eight powers with a 16-byte key
  scratch, a 16-byte accumulator and seven `gmul_impl` / `copy_range`
  pairs; every signature widened; both stack contexts bumped to 128.

### Two proof lessons

**Where a fact is proved matters more than whether it is true.**  Asserting
`pows_ok` at the point of the last `copy_range` failed; asserting the seven
`pow_step`s individually, the seventh failed while the first six passed --
the context there holds eight intermediate array states and the frames
relating them.  Moving the conjunction into `pows_build`, a pure lemma over
eight blocks and the seven products between them, went through at once.

**A Pulse `fn` whose last statement is a lemma call loses it.**  The body
ending `pows_build ...;` `}` reported the postcondition unproved at that
line; adding `()` after it made the same body verify.  (A trailing `assert
(pure ...)` works too, which is how it was found.)

Also: `mask_and`'s `assert_norm (UInt.logand #8 255 0 == 0)` drifted past
its rlimit once the file grew, and now gets `assert_norm (pow2 8 == 256)`
in front of it.

### Measured, pinned to core 2, best of three interleaved rounds

Hash `cb5ec1ef` in every run, before and after.

| | gcc before | gcc after | clang before | clang after |
|---|---:|---:|---:|---:|
| 64 | 129.8 | 114.6 | 134.5 | 114.9 |
| 128 | 170.7 | 138.3 | 157.8 | 135.6 |
| 256 | 236.9 | 189.5 | 212.2 | 184.9 |
| 1024 | 600.6 | 509.7 | 499.6 | 462.0 |
| 16384 | 6958 | 6889 | 6010 | 6042 |

The Pulse result matched the `gP128` model and beat it at 128 and 256
bytes under gcc.

Full suite into `r47g` / `r47c`; against `r46g` / `r46c` exactly four rows
move past 4% and nothing regresses:

```
                      gcc     clang
aes128-gcm-enc   64  1.15x    1.17x
aes128-gcm-enc 1024  1.15x    1.07x
aes256-gcm-enc   64  1.11x    1.14x
aes256-gcm-enc 1024  1.14x    1.07x
```

Against EverCrypt, sixty-four-byte AES-128-GCM 2.14x -> **1.87x**,
AES-256-GCM -> **1.71x**.  256 KiB is 1.59x -> 1.56x, which is noise.

`make verify`, `make extract`, `make test` (all 450 CAVP cases through both
the one-shot and expanded paths) and `make clones` (68, unchanged) all
clean.  `tests/test_gcm.c` and the benchmark shim needed `hk[128]`.

### Commits

`d3b9f65` (spec, code, dist, tests), `846c20e` (README: the architecture
section *The powers of the key belong with the key*, roadmap item 10 fully
done, the context description, the 256 KiB row).

### Next

Bulk GHASH is now the AES-GCM gap: 13.7 cycles per sixteen-byte block on
this Zen 2 against a ~6-cycle `pclmul` throughput bound.  `raw_product`
uses four `PCLMULQDQ` where Karatsuba uses three, and the inner loop
byte-reverses the key on every block where a pre-swapped copy in the
context would not.  Otherwise: GLV plus Shamir for k256 verify (roadmap
12, 2.12x), Shamir for ed25519-verify (1.98x), P-256's special prime
(roadmap 5), MD5 (1.43x), and Poly1305 at radix 2^44 on `uint128`.

---

## Part 47 --- Karatsuba in the bulk GHASH multiplier, with both folds deferred

### Where the time was

Part 46 left bulk GHASH as the last large gap in AES-GCM: thirteen and a
half cycles per sixteen-byte block, against a `PCLMULQDQ` throughput bound
of about six.  Compiling `dist/Hacl.c` to assembly and counting the
inlined eight-way loop body gave the diagnosis:

| | instructions | `pclmul` | `movdqa` | `pxor` |
|---|---:|---:|---:|---:|
| eight-way body, before | 247 | 32 | 82 | 55 |
| four-way body, before | 144 | 16 | 41 | 35 |

Eighty-two register copies for eight blocks.  The multiplier is not the
bottleneck; the traffic around it is.  (The same census confirmed that gcc
already hoists the loop-invariant key byte-reversals -- eleven `pshufb`
for eight blocks, not sixteen -- so a pre-byte-swapped key in the context,
which Part 46 had floated, would buy nothing.)

### The C model, and what it said

Four variants were written as intrinsics in `/tmp/gh/g.c` and checked to
agree bit-for-bit:

| variant | gcc | clang |
|---|---:|---:|
| base (four multiplies, fold per block) | 12.7 | 11.3 |
| Karatsuba only | 12.2 | 10.7 |
| deferred fold only | 11.7 | 10.1 |
| **both** | **10.7** | **8.85** |

Cycles per block.  Neither half alone is worth much; together they are
1.19x under gcc and 1.29x under clang.

### First attempt, and the regression that taught the lesson

The first Pulse implementation did Karatsuba in `kara_product` and the
assembly of the middle term in `kara_fold`, with `raw_product` defined as
one followed by the other, and `gmul4_vec`/`gmul8_vec` accumulating the
three raw registers and folding once.  `Spec.CLMUL` gained `shl8`/`shr8`,
`kfold_lo`/`kfold_hi` and their additivity, and `Spec.CLMUL.kara_mid` from
the bilinearity of `conv` over `padd` that `Spec.CarryLess` already had.
Both modules verified first try.

The measurement (nanoseconds, AES-128-GCM encrypt, best of two interleaved
rounds against the previous commit's binary):

| size | gcc before | gcc after | clang before | clang after |
|---|---:|---:|---:|---:|
| 64 | 99.8 | 98.6 | 109.4 | 108.8 |
| 128 | 122.1 | **137.5** | 127.4 | **131.0** |
| 256 | 171.6 | 177.8 | 171.0 | 170.8 |
| 1024 | 473.0 | 452.1 | 425.7 | 416.8 |
| 16384 | 6494 | 6000 | 5550 | 5258 |
| 262144 | 103166 | 95695 | 87570 | 83109 |

Bulk gained 5--8%, and 128 bytes lost **twelve per cent** under gcc.  The
first guess was that `raw_product` -- now three multiplies and ten cheap
instructions instead of four and five -- was the culprit, since a single
isolated multiply has nothing to amortise and two of the new instructions
sit on the dependency chain.  Restoring the four-multiply `raw_product`
and keeping Karatsuba only in the group multipliers recovered about half
of it (128 bytes: 129.6 gcc, 134.9 clang) but not all.

The real cause was arithmetic rather than scheduling.  Per group of
eight, the first version was:

* $-8$ `PCLMULQDQ`;
* $+16$ for folding the eight data operands' lanes (shift and xor);
* $+16$ for folding the eight key operands' lanes --- *hoisted out of the
  bulk loop by the compiler, but not hoisted when the loop runs once*;
* $+16$ for taking the squares back out, `mm = mf ^ ll ^ hh`, per block;
* $+7$ for the third accumulator;
* $-32$ for the per-block assembly that is no longer done;
* $+4$ for the one assembly at the end.

In bulk that is about $-8$ multiplies for $+15$ cheap instructions and a
clear win.  At 128 bytes the key folds are live too and it is $+31$, which
on Skylake --- where `PCLMULQDQ` and `pxor` compete for port 5 --- is a
wash at best.

### The fix: the squares correction is linear too

`mm_i = mf_i + ll_i + hh_i` is linear in all three, so

```
sum_i mm_i  =  sum_i mf_i + sum_i ll_i + sum_i hh_i
```

and the correction, like the assembly and like the reduction, may be done
once for the group.  That removes sixteen of the thirty-one added
instructions, and removes them from the cold path as well as the hot one.

`kara_parts` now returns the three raw registers and does nothing else;
`kara_fold` takes all three and does the correction and the assembly
together.  `Spec.CLMUL` gained `kmid` with the same four lemmas the
`kfold`s have -- a bit-level characterisation, additivity over `gadd`, and
the chain up through `sum4` and `sum8`.  The per-block halves are then
ghost blocks that are never computed, and `pmod_defer4`/`pmod_defer8` take
them unchanged, exactly as they were written to.

One F\* wrinkle: `let mm = CL.kmid (Vec.bv ll) ... in` inside the body of
a `Pure` function taints the whole body with `GTot`, because `Vec.bv` is
ghost.  Binding it is what does the damage, not using it; an `unfold let
kmid_of (ll hh mf: Vec.t) : GTot G.block` used in lemma-argument position
is fine.

### Result

| | instructions | `pclmul` | `movdqa` |
|---|---:|---:|---:|
| eight-way body, before | 247 | 32 | 82 |
| eight-way body, after | **194** | **24** | **58** |
| four-way body, before | 144 | 16 | 41 |
| four-way body, after | **118** | **12** | **33** |

Microbenchmark, best of two interleaved rounds:

| size | gcc before | gcc after | clang before | clang after |
|---|---:|---:|---:|---:|
| 64 | 99.2 | 98.8 | 110.8 | 106.9 |
| 128 | 121.6 | 121.8 | 126.8 | 129.0 |
| 256 | 171.7 | 168.0 | 172.7 | 166.7 |
| 1024 | 481.4 | **443.6** | 426.7 | **395.5** |
| 16384 | 6545 | **5977** | 5556 | **5052** |
| 262144 | 104971 | **97028** | 89722 | **81149** |

Full suite `r48g` / `r48c` against `r47g` / `r47c`, at a 2% threshold:

| benchmark | size | gcc | clang |
|---|---:|---:|---:|
| aes128-gcm-enc | 1024 | 1.09x | 1.10x |
| aes128-gcm-enc | 16384 | 1.09x | 1.14x |
| aes128-gcm-enc | 262144 | 1.09x | 1.14x |
| aes128-gcm-dec | 16384 | 1.09x | 1.13x |
| aes256-gcm-enc | 1024 | 1.07x | 1.11x |
| aes256-gcm-enc | 16384 | 1.08x | 1.12x |
| aes256-gcm-enc | 262144 | 1.08x | 1.12x |

Nothing regresses by as much as two per cent under either compiler.
Against EverCrypt, 256 KiB AES-128-GCM goes from 1.56x to **1.43x** under
gcc and to **1.22x** under clang; 16 KiB decryption to 1.44x and 1.22x.

Committed as `734c6d4` (code) and `221b55a` (README, new architecture
section *Karatsuba, and what a group of blocks may put off*, the
performance-table row, and roadmap item 13).

### Lessons

* **A linear step can always be moved past a sum.**  This change is the
  reduction-deferral argument applied twice more, to the squares
  correction and to the half-assembly.  Looking for linearity is a more
  productive habit than counting instructions.
* **Measure the cold path, not just the bulk path.**  The compiler hoists
  loop-invariant work out of a loop that runs many times and cannot hoist
  it out of a loop that runs once; a change that is free in bulk can cost
  twelve per cent at 128 bytes, and the published suite has both.
* **Binding a ghost value in a `Pure` body taints the effect.**  Using it
  in lemma-argument position does not.

---

## Part 48 --- A square is not a product

### The finding

Reading the generated C for the Curve25519 field, `Hacl_Curve25519_fsqr`
sits directly below `fmul` and is

```c
static void Hacl_Curve25519_fsqr(uint64_t *out, uint64_t *a, uint64_t *c) {
  Hacl_Curve25519_copy(c, a);
  Hacl_Curve25519_Field_fmul(out, a, c);
}
```

A grep found the same shape in `Hacl.K256.Field52.fst` and
`Hacl.P256.Field.fst`.  **Every field in the library squares by copying its
argument and running a full multiply.**  For five limbs that is twenty-five
wide multiplies where fifteen suffice.

### Probing in C first

Before writing any F\*, the HACL\* Field51 squaring formula was patched into
a copy of `dist/Hacl.c` and measured.  x25519 moved (clang -10%), but
ed25519 did not move at all --- because `point_double` squares *inline*
(`copy au x1; fmul aa au x1`) rather than calling `fsqr`.  Patching the
three inline sites too gave ed25519-verify -6%.

A head-to-head harness against `libevercrypt.a` (symbol collisions resolved
with `objcopy --redefine-syms`) put numbers on the gap, pulse/ref:

| variant | dbl gcc | add gcc | dbl clang | add clang |
|---|---|---|---|---|
| base | 1.62 | 1.52 | 1.27 | 1.27 |
| + dedicated fsqr | 1.48 | 1.49 | **1.10** | 1.28 |
| + `always_inline` fmul | 1.37 | 1.32 | 1.15 | 1.19 |
| both | 1.34 | 1.32 | 1.07 | 1.22 |

Two distractor hypotheses died here.  Our `fmul` is **not** slower than
HACL\*'s --- 203 instructions against 200, 25 muls each; an apparent 1.78x
was entirely HACL\*'s `static inline` version being inlined into the
measuring loop while ours was a call.  And the dead zero-initialisation of
stack temporaries that Pulse emits (384 bytes a `point_double`) is free:
both compilers already elide it.

### The arithmetic

Scaled words `d0 = 2a0`, `d1 = 2a1`, `r2 = 38a2`, `r3 = 19a3`, `s4 = 19a4`,
`r4 = 38a4` --- all below `2^64` because the limbs are below `2^52`.

```
c0 = a0*a0 + r4*a1 + r2*a3   <= 77 lim^2
c1 = d0*a1 + r4*a2 + r3*a3   <= 59 lim^2
c2 = d0*a2 + a1*a1 + r4*a3   <= 41 lim^2
c3 = d0*a3 + d1*a2 + s4*a4   <= 23 lim^2
c4 = d0*a4 + d1*a3 + a2*a2   <=  5 lim^2
```

against the `colb = 95 lim^2` the chain already accepts.  **The carry chain,
the wrap and `Cols.chain` are reused letter for letter**, which is why the
proof was five short lemmas stated against `fold19 (part a a nl)` rather
than a specification of squaring.  Two helpers carry the whole thing:

```fstar
let sqpair (x y: nat) : Lemma (x * y + y * x == (2 * x) * y)
let sqdbl  (x y: nat) : Lemma (x * (19 * y) + y * (19 * x) == (38 * y) * x)
```

One proof gotcha: a column lemma whose *requires* is stated over the
products (`x <= i*(lim*lim)`) cannot be discharged at a call site that only
knows the word bounds.  Restating it over the six words (`colw3`), with the
product bound derived internally, fixed it.

### Results, full suite, 3 reps, taskset -c 2

Against r48 (old/new, >1 is better):

| | gcc | clang |
|---|---|---|
| x25519-scalarmult | 1.10x | 1.10x |
| x25519-base | 1.12x | 1.11x |
| ed25519-verify-64B | 1.14x | 1.07x |
| ed25519-sign-64B | 1.12x | 1.06x |
| ed25519-keygen | 1.11x | 1.05x |

Nothing else in the suite moves by more than 2%.

### The K256 half, which was reverted

The identical rewrite for K256's radix-2^52 field (nine unfolded columns,
`c4 = d0*a4 + d1*a3 + a2*a2` hitting exactly `colb`) verified first try and
passed everything.  Then:

- In isolation the new `fsqr` is **faster** under both compilers: gcc 27.7
  -> 26.8 ns, clang **40.2 -> 27.5 ns**.
- Whole-program `k256-ecdsa-verify`: gcc 213 -> 201 us (-5.5%), clang 207 ->
  214 us (**+3.5%**), reproducible across six interleaved runs.
- Rebuilding the *new* file with only the old `fsqr` body restored (R)
  landed at clang 208-211, between the two --- so roughly half the clang
  loss is the square in context and half is code layout.
- `noinline` on the generated `fsqr` did not help, so it is not inlining
  alone.  Register pressure in the inlined `point_double` is the best
  explanation.

The theoretical ceiling says this was always going to be small: ten saved
`mulx` is about 3 ns, k256 verify does on the order of 800 squarings, so
2.5 us out of 205 --- about 1%.  The measured +-5% swings are scheduling
noise around a 1% effect.  Reverted, so the commit ships a uniformly
positive change.  k256's real answer is roadmap item 12 (GLV + Shamir),
where the 2.1x lives.

### What is still open on Ed25519

After the fix `point_double` is ~1.48x (gcc) / ~1.10x (clang) of HACL\*'s
and `point_add` ~1.5x / ~1.25x.  `point_add` has **no squarings**, so its
gap is gcc declining to inline `fmul` --- eight call sites exhaust the
inline budget where HACL\* has fewer.  `always_inline` is worth 13-18% at
the C level; the F\* analogue is `inline_for_extraction` on the Pulse `fn`,
which would emit eight copies of a 200-instruction body.  Untried.

P-256 was skipped deliberately: its `amul` interleaves Montgomery reduction
with the multiply, so a dedicated square is a structural change rather than
a column rewrite.

Commit: `3963bf3`.  Benchmark data: `r50g`, `r50c`.

---

## Part 49 --- A constant-time violation, found by a performance probe

### How it was found

The item on the table was Ed25519 verification, the largest remaining ECC
gap at 1.74x under gcc and 1.59x under clang.  Splitting it:
`point_mul_g` (fixed base, sixty-four table lookups and sixty-four adds,
no doublings) is 41.2 us under gcc and 27.1 under clang; `point_mul_win`
(variable base, sixty-four iterations of a four-fold double plus an add)
is 86.7 and 67.6.  Together that is 87% of verification under gcc and 81%
under clang.

Breaking `point_mul_win`'s loop body apart gave, per iteration under gcc:
`win_dbl4` 844 ns (66%), `point_add` 266 ns, and the constant-time table
lookup 178 ns.  Under clang the same lookup was **52 ns**.  A 3.4x
compiler disparity on a function that is nothing but sixteen masked
selects is not a code-generation difference; sixteen masked selects of
five limbs is eighty and-or pairs, and eighty dependent ALU ops do not
fit in 52 ns of nothing.  That was the thread.

### What clang was doing

A standalone microbenchmark of four restructurings of the scan put
clang's version of the current shape at 9.67 ns against gcc's 56.71.
Disassembling it showed a jump table indexed by the secret digit:
`jmpq *%rcx` off `.LJTI1_0`.

The real shipped library had no jump table, but it had the same idea
spelled out longhand: `testq %rcx,%rcx; je` / `cmpq $1,%rcx` /
`cmpq $2,%rcx` / ... where `%rcx` holds the secret digit.  1042 lines of
assembly, 207 branches.  clang had unrolled the sixteen-iteration scan,
observed that the loop counter is compared against the literals 0..15 and
that the runtime index must equal exactly one of them, and emitted a
sixteen-way value specialisation on the secret.

### Settling it behaviourally

Reading assembly is not evidence that survives a compiler upgrade, so the
claim was settled by timing `Hacl_Bignum_Base_table_select` itself, once
per digit, `-std=c11 -O3`, `taskset -c 2`, min of 5 reps of 1e6
iterations, n = 5 limbs:

| d | 0 | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 15 | spread |
|---|---|---|---|---|---|---|---|---|---|---|
| gcc | 57.2 | 57.2 | 57.2 | 57.2 | 57.2 | 57.2 | 57.2 | 57.2 | 57.2 | **1.1%** |
| clang | 3.73 | 3.88 | 4.07 | 4.72 | 5.97 | 6.55 | 7.20 | 8.31 | 8.94 | **157.8%** |

Monotonic in the secret, which is what a linear scan of compare-and-branch
looks like.  Reproduced at `-O3` with and without `-march=native`.  `-O2`
is flat under both compilers.

A control on HACL\*'s equivalent, `Hacl_Impl_PCurves_PrecompTable_...`'s
`precomp_get_consttime`, in the same harness: flat to about 2% under both
compilers.  HACL\* is not affected.  Its body is fifteen entries of twenty
limbs, 300 selects; ours is sixteen of five, 80.  The difference is
presumably that clang's inliner-and-unroller cost model finds the
specialisation profitable at 80 and not at 300.  That is a difference in a
heuristic, not in a guarantee.

### Variants measured, before choosing

Standalone, n = 5, ns, mean over d and spread over d:

| variant | gcc | clang |
|---|---|---|
| current shape, no barrier | 52.5 / 1.4% | 5.5 / **150%** |
| current shape + barrier on mask | 57.2 / 1.1% | 61.0 / 1.7% |
| loops swapped + barrier, select-accumulate | 50.4 / 2.2% | 49.5 / 1.6% |
| loops swapped + barrier, `masked` + `logor` | **35.0** / 2.4% | **37.5** / 1.3% |

Two findings there.  The barrier belongs on the **mask**: a barrier on the
secret leaves the sixteen comparisons against literals exactly where they
are, and clang still specialises.  And `masked m x` (`= select m x zero`)
followed by `logor` is materially faster than `select`-accumulation --
one `or` per entry into a register accumulator, against `and`, `andn`,
`or` into a memory location.

The loop swap matters for a reason that is not about constant time at
all: the old shape ran limbs outermost and accumulated into `res[j]`,
sixteen read-modify-writes through memory per limb, with the limb count a
runtime parameter so neither loop could unroll.  Entries innermost gives
a register accumulator and a compile-time trip count of 16.

### The fix

`lib/Hacl.Launder.fst` is one declaration:

```fstar
[@@ custard_extern "Hacl_Launder_u64"; custard_c_header "Hacl_Launder.h"]
assume val launder (x: S64.t) : r: S64.t { r == x }
```

`c/Hacl_Launder.h` implements it as `__asm__("" : "+r"(x))` under GNU and
clang, with a **local** `volatile uint64_t` fallback otherwise -- local,
because a `static` volatile would be a data race.  It is header-only, so
no Makefile change beyond adding `table_select` to `CUSTARD_ENTRIES` so
the test can reach it.

The proof was rebuilt around a predicate rather than an inline
conditional:

```fstar
let mask_for (m: S64.t) (i k: nat) : prop =
  (i == k ==> S64.v m == pow2 64 - 1) /\ (~(i == k) ==> S64.v m == 0)
```

with `or_zero` / `zero_or` from `UInt.logor_lemma_1` and
`UInt.logor_commutative`, carried from values to terms by the
`v_extensional` SMT-pattern lemma already in `Hacl.Secret.UInt64.fsti`.
`--fuel 0 --ifuel 0 --z3rlimit 400`.

One F* gotcha cost a verification round: `[| S64.zero; 16sz |]` gives the
array the *refined* element type `r:t{v r == 0}`, and `A.pts_to mk
(wm: Seq.seq S64.t)` then fails with ``Ill-typed term ...
`Prims.l_True == (v r == 0)` ``.  The codebase's existing fix is to bind
first: `let zm = S64.zero; let mut mk = [| zm; 16sz |];`.

### After

| | gcc | clang |
|---|---|---|
| spread over the digit | 1.1% -> 1.6% | **157.8% -> 1.2%** |
| lookup, ns | 57.2 -> 34.3 | 3.7--8.9 -> 37.8 |

`tests/test_launder.c` is the regression test: the barrier is the
identity over fixed values and a 100k LCG sweep; `table_select` returns
the right entry for all sixteen digits; and the per-digit spread, min
over 7 reps of 200k iterations, is under 75%.  Validated by splicing the
*original* `table_select` into the *new* `dist/Hacl.c`: it fails at 141%
under clang, exit 1, and passes under gcc.  Also checked: removing the
barrier from the new shape leaves the spread at 2.1% / 2.2%, so the loop
restructuring alone defeats the specialisation.  Both were kept anyway --
the restructuring happens to defeat it, the barrier is meant to.

### What it costs

gcc, `r51g` against `r50g`:

| benchmark | r50g | r51g | change |
|---|---:|---:|---|
| ed25519-keygen | 41,392 | 39,003 | **-5.8%** |
| ed25519-sign-64B | 84,302 | 80,302 | **-4.7%** |
| ed25519-verify-64B | 133,017 | 128,276 | **-3.6%** |
| k256-ecdsa-sign | 79,502 | 76,459 | **-3.8%** |
| k256-secret-to-public | 63,190 | 61,109 | **-3.3%** |
| p256-ecdsa-verify | 452,859 | 445,501 | **-1.6%** |

clang, `r51c` against `r50c`:

| benchmark | r50c | r51c | change |
|---|---:|---:|---|
| ed25519-keygen | 34,409 | 43,504 | **+26.4%** |
| ed25519-sign-64B | 70,080 | 88,967 | **+27.0%** |
| ed25519-verify-64B | 120,166 | 136,975 | **+14.0%** |
| k256-secret-to-public | 68,799 | 76,762 | **+11.6%** |
| k256-ecdsa-sign | 91,641 | 98,039 | **+7.0%** |
| k256-ecdsa-verify | 205,376 | 218,944 | **+6.6%** |
| k256-ecdh | 135,032 | 142,609 | **+5.6%** |
| p256-dh-initiator | 152,038 | 158,066 | **+4.0%** |
| p256-ecdsa-sign | 171,774 | 179,210 | **+4.3%** |
| p256-ecdsa-verify | 396,211 | 410,665 | **+3.6%** |
| p256-dh-responder | 239,386 | 247,670 | **+3.5%** |
| bn2048-modexp-consttime | 4,287,609 | 4,360,367 | **+1.7%** |

X25519 moved by less than 1% under both, as it should: the Montgomery
ladder selects with `cswap`, not with a table.

The clang column is the honest accounting of a bug, not a regression.
Those rows were previously measuring a sixteen-way branch on the secret.
The README's clang figures for Ed25519, secp256k1 and P-256 have been
restated accordingly.

### Two performance items rejected on the way

**`always_inline` on `fmul`.**  `Hacl_Curve25519_Field_fmul` is already
emitted `static inline` and gcc still declines to inline it into
`point_add`.  Forcing it: ed25519-verify -6.5%, ed25519-keygen -6.5%, but
x25519 **12% worse** (54.4 -> 61.0 us).  The Montgomery ladder and the
Edwards point operations want opposite decisions from one function, and
the lever is a non-portable C attribute F* cannot express.  Dropped.

**K256 dedicated squaring**, carried over from Part 48: 32% faster in
isolation under clang and still 3.5% *slower* on `k256-ecdsa-verify`
there, 5% faster under gcc.  A control build -- the new `dist/Hacl.c`
with only the old `fsqr` body spliced back -- landed between the two, so
roughly half the clang loss was code layout.  Reverted; k256's time is
not in the multiply.

Commit: `4441507`.  Benchmark data: `r51g`, `r51c`.

---

## Part 50 --- The audit that Part 49 implied

Part 49 found one constant-time violation by accident, while probing
Ed25519 verification for performance.  The obvious next question is
whether it is the only one.  F* cannot answer it -- the property is about
machine code, not about the program -- so the answer has to be measured,
once per masked selection, against the compiler in use.

### Method

For each candidate: run the shipped function once per value of the secret
it selects on, minimum over 7 repetitions, `taskset -c 2`, and take the
spread between the fastest and slowest value.  A masked select is flat to
a few percent.  A branch on the secret is not, and -- as Part 49 showed --
is usually *monotonic* in the secret, which is what a linear cascade of
compares looks like.

### Candidates and results, `-std=c11 -O3`

| selection | secret varied over | gcc | clang |
|---|---|---:|---:|
| `table_select`, n = 4 | the sixteen digits | 3.2% | 2.1% |
| `Hacl_Ed25519_PointWin_win_add` | the sixteen digits | 2.4% | 3.9% |
| X25519 scalar multiplication | six scalar bit patterns | 1.5% | 2.3% |
| `bn_eq_mask`, 32 limbs | position of first difference | 3.0% | 1.8% |
| `bn_lt_mask`, 32 limbs | position of first difference | 1.8% | 1.4% |
| ML-KEM `eq_mask_bytes`, 1088 B | position of first difference | 1.7% | 2.3% |
| AES S-box | all 256 input bytes | 2.8% | 3.5% |

All flat.  No second instance of the defeat.

Three of these are worth a note.

**`win_add` is the one that matters most for the fix.**  It is where
`table_select` is called with the limb count a *literal* 5 rather than a
runtime argument, which is strictly more information than the exported
function gives the optimizer, and it is where a surviving specialisation
would actually be exploitable.  2.4% / 3.9%: the barrier survives
inlining.  It was not kept as a standing test because it takes seventeen
pointer arguments and exporting it to reach them is a bad trade.

**The ladder is tested instead of `cswap`.**  `Hacl.Curve25519.Field.cswap`
carries `FStar.Attributes.CInline`, which Custard emits as a C99 `inline`
definition with no external definition; adding it to `CUSTARD_ENTRIES`
puts `inline void Hacl_Curve25519_Field_cswap(...);` in `Hacl.h` and the
test TU then fails to link -- and `tests/` builds with `-Werror`, so it
fails earlier still, on `inline function declared but never defined`.
Dropping the attribute to suit a test would change the ladder's code
generation, which is not a trade worth making either.  Timing the whole
scalar multiplication over scalars of all-zero, all-one and alternating
bits is the stronger statement anyway: 255 conditional swaps, and if any
one of them branched the patterns would not agree.  They agree to 1.5%
under gcc and 2.3% under clang.

**The AES S-box is the most promising-looking candidate that turned out
clean.**  There is no S-box table -- the inverse is computed in the field,
seven squarings and eight multiplications, each of which is eight masked
selects on a bit of a secret byte.  A hundred and twenty two-way selects
on a secret ranging over exactly 256 values is the shape that invites
enumeration, and the per-value timing over all 256 is flat to 2.8% / 3.5%.
The reason is probably the same one that protects HACL\*'s
`precomp_get_consttime`: the body is far too large for the specialisation
to look profitable.

### What was shipped

`tests/test_consttime.c`, which runs six of the seven as a standing test
with thresholds of 10--75%.  The thresholds are known to bite: splicing
the old `table_select` into the current `dist/Hacl.c` fails the
`table_select` row at 141%.  `Hacl.Impl.Select.eq_mask_bytes` and
`Hacl.AES.Core.sbox_impl` were added to `CUSTARD_ENTRIES` so the test can
reach them.  `make test` passes under gcc and the file passes under clang;
`make clones` is unchanged at 67.

### What is left

The long tail, in decreasing order of plausibility: the conditional
subtractions in the Montgomery reduction; the `Hacl.Secret` selects inside
the point addition and doubling formulas; and ML-KEM's compression and
sampling, which are 103 uses of `uint16 gte_mask` but all against the
fixed modulus 3329 rather than against a range of literals, which is the
weaker shape for this rewrite -- the optimizer has nothing to enumerate.

Commit: `492dbd3`.

---

## Part 51 — Re-ranking against HACL\* best, and the HMAC row that did not belong

### The question that started it

The README's performance table bolded the ratio against HACL\*'s portable
scalar C.  That is the right column for judging an extraction pipeline --
same algorithm, same instruction set, two compilers of F\* to C -- but it is
not what a user choosing a library faces, and this repository uses AES-NI,
CLMUL and SHA-EXT intrinsics while that column does not.  Comparing our
intrinsics against someone else's scalar C and bolding the result is
flattering in a way that does not survive scrutiny.

Re-ranked against **HACL\* best** (`/tmp/gapbest.py`, which is `gap.py` with
`Tref_*` replaced by `Tbest_*`), the order changes and the worst row in the
suite is not ChaCha20:

| row | vs best |
|---|---:|
| hmac-sha2-256 262144 | **6.84x** |
| chacha20 262144 | 5.31x |
| chacha20poly1305-enc 262144 | 5.14x |
| poly1305 262144 | 4.18x |

ChaCha20 and Poly1305 are honest: AVX2 lanes against scalar C, and
unreachable without a vector backend.  HMAC-SHA-256 was not honest, because
SHA-EXT already exists in this library.

### The arithmetic that gave it away

Our own one-shot SHA-256 does 256 KiB in 227 us.  Our HMAC-SHA-256 did the
same 256 KiB in 1,136 us.  HMAC is two hashes, but only one of them touches
the message; a 256 KiB HMAC should cost a 256 KiB hash plus one block.  A
factor of five means the two are not running the same code.

### The cause

`Vec.sha_supported ()` is tested in exactly one place in the library:
`Hacl.Hash.SHA2.fst`'s one-shot `sha224`/`sha256`.  HMAC never calls it.  To
hash `(K0 ^ ipad) || msg` without materialising the concatenation it calls
`Hacl.Hash.SHA2.Core.hash_prefixed`, which is generic in the word type `t`.
Generic code cannot branch into `Hacl.Hash.SHA2.NI`, which exists only at
`S32.t`, and there is no way to obtain the equality witness that would let
it.  So HMAC-SHA-256 ran scalar compression rounds on a machine already
issuing `sha256rnds2` for every other SHA-256 call.

### The fix

`hash_prefixed_ni` (Hacl.Hash.SHA2.NI) is `hash_prefixed` transcribed at
`S32.t`: drop `{| w |}`, block length a literal `64sz`,
`update_block_impl` → `update_block_ni`, `hash_blocks` → `hash_blocks_ni`
(note the latter takes no `bl` argument), `tail_and_finish` reused
unchanged, `is_sha256 p` added to the precondition.  Verified first try at
`--z3rlimit 100 --fuel 1 --ifuel 1`.

`hmac_impl_ni` (new module Hacl.HMAC.NI) is `hmac_impl` at `params S32.t`
with both long hashes routed through `hash_prefixed_ni`.  One failure:
`is_sha256` lives in `Spec.SHANI`, not `Spec.SHA2`.  Verified on the second
attempt.

`hmac_sha224`/`hmac_sha256` dispatch on `Vec.sha_supported ()`, in the shape
`Hacl.Hash.SHA2.fst` already used.

Duplication rather than a hook in the `word` typeclass, because that class
is a statement about values (`v`, `add_mod`, `logxor`) and the codebase
already made this trade when `hash_blocks_ni` was written as a copy.

### Measured, gcc, min of five, `taskset -c 2`

| size | before | after | our SHA-256 |
|---|---:|---:|---:|
| 64 B | 1,804 | 908 | 465 |
| 1 KiB | 5,969 | 1,733 | 1,294 |
| 16 KiB | 72,685 | 14,918 | 14,484 |
| 256 KiB | 1,145,945 | **225,978** | 226,047 |

HMAC now costs exactly what hashing the same bytes costs.

### Full suite, r52g vs r51g (gcc)

Only HMAC and HKDF-extract move; everything else is a uniform 1.02x of
machine drift.

```
hmac-sha2-256   262144   227,372  <- 1,135,718   4.99x
hmac-sha2-256    16384    14,969  <-    72,798   4.86x
hmac-sha2-256     1024     1,733  <-     6,015   3.47x
hmac-sha2-256       64       907  <-     1,839   2.03x
hkdf-extract-sha2-256        851  <-     1,550   1.82x
```

### Full suite, r52c vs r51c (clang)

```
hmac-sha2-256   262144   677,962  <- 1,304,131   1.92x
hmac-sha2-256    16384    43,187  <-    83,092   1.92x
hmac-sha2-256     1024     3,683  <-     6,384   1.73x
hmac-sha2-256       64     1,197  <-     1,661   1.39x
hkdf-extract-sha2-256      1,046  <-     1,340   1.28x
```

Half the win, for a reason that is not HMAC's.

### A second finding: clang's SHA-EXT code is 3x gcc's

One-shot SHA-256, 256 KiB: gcc **227 us**, clang **678 us**.  55 ns a block
against 165.

- Both emit the instructions (`sha256rnds2|sha256msg1|sha256msg2`: gcc 56,
  clang 68).
- Not unrolling: clang `-O2` gives 690 us, `-O3 -fno-unroll-loops` 696 us.
- Not a bad dispatch: forcing the scalar path (`sha_supported()` → `false`)
  gives clang 1,300 us, so NI still wins under clang, by 2x instead of 5x.
- clang emits `Hacl_Hash_SHA2_NI_update_block_ni__Mkparams` as **23,392
  instructions with 4,746 `mov`s**; gcc emits no such function, having
  inlined it into the block loop.

Suspect: register allocation around the sixteen live `__m128i` of the
message schedule.  Under clang this is now the largest reachable gap in the
suite (SHA-256 and HMAC-SHA-256 both ~4.1x HACL\* best).  Roadmap item 16.

### README

The performance table now leads with **HACL\* best**, bolded and sorted by,
with portable HACL\* demoted to a secondary column; the prose that said the
portable column "is the column that says anything about Pulse" and that best
"is not a fair fight" has been inverted.  The intro paragraph leads with the
best comparison too.  Roadmap items 16 (clang's SHA-EXT) and 17 (a vector
backend, so the ChaCha20/Poly1305 ceiling has a name) added.
`mk/clones.baseline` 67 → 69.

Commit `ac26407`.

---

## Part 52 — The clang SHA-EXT gap was one attribute, not code generation

### What was on the roadmap

Part 51 ended with clang compiling the SHA-EXT block function to 668 us on
256 KiB where gcc compiled it to 227, and recorded the suspicion as
"register allocation around the `Vec.t` intrinsics", with a note that clang
emitted a 23,392-line function containing 4,746 moves.  That suspicion was
wrong, and the 23,392-line figure was a miscount of the surrounding region
rather than of the function.

### The eliminations

| hypothesis | test | result |
|---|---|---|
| unrolling | `-O2`, `-O3 -fno-unroll-loops` | both within 2% of `-O3` |
| wrong dispatch | `sha_supported()` forced false | 1,300 us, so NI still wins |
| missing instructions | `grep -c sha256rnds2\|msg1\|msg2` | gcc 56, clang 68 |
| **the attribute** | **`-march=native`** | **clang 168 us, faster than gcc's 188** |

The last row is the one that pointed somewhere.  If adding the features
globally removes the difference, the problem is the per-function `target`
attribute, not the code underneath it.

### The finding

Disassembling `Hacl_Hash_SHA2_NI_update_block_ni__Mkparams` from clang's
`-S` output: **386 instructions, 39 `callq`, all to one symbol, and zero
`sha256msg1`/`sha256msg2`.**  The schedule had been pushed entirely into
calls.

The symbol was `Hacl_Impl_Sub_sub__t_2`:

```c
__attribute__((target("aes,pclmul,ssse3,sse4.1")))
static uint32_t *Hacl_Impl_Sub_sub__t_2(uint32_t *a, size_t i, size_t j) {
  (void)j;
  return (a + i);
}
```

`Hacl.Impl.Sub.sub` monomorphized at `uint32`, body `a + i`, stamped with
the **AES** feature set.  Its only callers in the whole distribution are the
two SHA-256 block functions; the attribute is not propagation from a caller,
it is a misattribution.  clang declines to inline a callee whose target
features are not a subset of the caller's, and `aes,pclmul` is not a subset
of `ssse3,sse4.1,sha`.

The `uint8` instance `Hacl_Impl_Sub_sub__t` carried no attribute and was
inlined normally by both compilers, which is the control.

### Confirmation before touching the source

Stripping the attribute by hand from `dist/Hacl.c`.  Note that it appears
**twice** -- forward declaration and definition -- and stripping only the
definition changes nothing (667 us), which cost one measurement to learn.

```
clang, as extracted                 667 us
clang, definition stripped          667 us
clang, both stripped                178 us
```

### The fix

`inline_for_extraction` on `Hacl.Impl.Sub.sub`.  Not a corrected attribute:
a monomorphization of a shared helper has no natural home, so whichever
target it is given is wrong for every caller on the other side of the
partition.  Correcting it for SHA would be the same bug pointing at AES.
Inlined, `Hacl_Impl_Sub_sub__t` disappears from `dist/Hacl.c` entirely
(`grep -c` → 0).

Cost: `lib/` is at the bottom of the dependency graph, so this was a full
rebuild -- about 20 minutes of `make verify -j12`.  `make test` clean.
`make clones` reported exactly one change, `-Hacl_Impl_Sub_sub__t_2`, which
is the right sign: gcc had been cloning the function in order to inline it,
and we have now taken it over.  Baseline 69 → 68.

### Measured

Microbenchmark, 256 KiB one-shot SHA-256, `taskset -c 2`, min of 7:

| | before | after |
|---|---:|---:|
| gcc | 227 us | **189 us** |
| clang | 667 us | **178 us** |

Full suite, r53g vs r52g (gcc):

```
sha2-256       262144   189,878  <-  227,204   1.20x
sha2-256        16384    12,223  <-   14,492   1.19x
sha2-256         1024     1,156  <-    1,300   1.12x
hmac-sha2-256  262144   189,995  <-  227,372   1.20x
hmac-sha2-256   16384    12,634  <-   14,969   1.18x
ed25519-keygen           37,650  <-   39,224   1.04x
ed25519-sign-64B         77,431  <-   79,651   1.03x
hkdf-extract-sha2-256       803  <-      851   1.06x
```

Full suite, r53c vs r52c (clang):

```
sha2-256       262144   178,515  <-  668,509   3.74x
sha2-256        16384    11,493  <-   42,328   3.68x
sha2-256         1024     1,050  <-    3,001   2.86x
sha2-256           64       398  <-      523   1.32x
hmac-sha2-256  262144   178,845  <-  677,962   3.79x
hmac-sha2-256   16384    11,925  <-   43,187   3.62x
hkdf-extract-sha2-256       804  <-    1,046   1.30x
```

Ed25519 and HKDF move because they are the library's other heavy users of
`sub`.  gcc shows a consistent 0.97–0.98x on the three bulk `sha3-256` rows
which is almost certainly code layout and not attributable to this change;
noted and not chased.

### Position after the change

SHA-256 and HMAC-SHA-256 are now **1.17x** of HACL\* best under gcc and
about 1.10x under clang.  Under clang SHA-256 had been the largest reachable
gap in the suite; it is now below the median.  What is left in that row is
this repository's intrinsics against Vale's hand-written assembly.

### The lesson, stated narrowly

A `target` attribute is a *partition* of the program, not an optimization
hint.  A function on the wrong side of the partition does not fail to
compile, does not fail its tests, and does not warn.  It silently stops
being inlinable across the boundary, and the only symptom is a number in a
benchmark.  Any helper shared between two instruction-set paths should be
`inline_for_extraction`, so that it has no single home to be assigned to.

Worth noting that gcc hid this for the entire life of the code: gcc inlined
the call anyway, by cloning.  The repository's own clone survey had been
recording that clone as expected since the day it appeared.

Commit `75ac924`.  README gains *One attribute in the wrong place, and three
quarters of the time*; roadmap item 16 struck out.

---

## Part 53 — HKDF-expand, and an estimate that was wrong by ten

### Where the ranking pointed

After Part 52, `gapbest.py` on r53g put the top non-vector gap at

```
hkdf-expand-sha2-256-64B      3,091 ns   vs   1,348      2.29x
k256-ecdsa-verify           185,069 ns   vs  90,266      2.05x
aes128-gcm-enc 64 B             111 ns   vs      61      1.81x
```

Part 51 had looked at `hkdf-expand` and **declined it**, on the reasoning
that expand's HMAC calls are on tens of bytes, so roughly four blocks total,
so NI could be worth about 150 ns of a 3,139 ns benchmark; the row was
labelled "setup overhead, not block throughput".  That was reasoning in
place of measuring, and it was wrong by a factor of ten.

### The measurement that settled it in one command

```
hkdf-expand, 64 bytes out     3,086 ns
hmac_sha256, 17-byte message    799 ns
hmac_sha256, 49-byte message    797 ns
hkdf-extract                    797 ns
```

A 64-byte expand with a 32-byte PRK is exactly two HMAC rounds, on messages
of 17 and 49 bytes.  Those two calls, through the dispatching
`Hacl_HMAC_hmac_sha256`, cost 1,596 ns.  Expand cost 3,086.

The error in the old estimate: "tens of bytes" is not "few blocks".  An HMAC
of a short message is **four** compression blocks -- padded key and message
for the inner hash, key and digest for the outer -- so two HMACs are eight,
and eight blocks at 270 ns scalar against 55 with the extensions is 1,720
ns, which is the whole observed difference.  Short inputs are where HMAC's
fixed cost dominates, so the dispatch matters *more* there, not less.

### Cause

Identical to Part 51's, one level further out.  `expand` does not call
`Hacl.HMAC.hmac_sha256` (which dispatches).  It calls
`Hacl.HKDF.Core.round_one` and `round_step`, which call the generic
`hmac_impl` directly.

### Implementation

Transcribed `round_one`, `round_step` and `expand_impl` at `S32.t` with
`hmac_impl_ni`, and added the `Vec.sha_supported ()` branch to
`expand_sha224`/`expand_sha256`.

Generated the copies mechanically with a Python pass over the original
source (substituting `(#t: Type0) {| w: word t |}` → nothing, `t` → `S32.t`,
`hmac_impl` → `hmac_impl_ni`, adding `is_sha256 p` to each precondition)
rather than by hand.  Worth doing for a 250-line transcription; it is the
difference between one typo and none.

**One wrong turn:** put them in a new module `Hacl.HKDF.NI.fst` first, and
hit `Identifier not found: msg_ok`.  `Hacl.HKDF.Core` has an **`.fsti`**,
which exports only `expand_impl`; `msg_ok`, `round_sizes` and
`round_msg_pointwise` are not visible outside.  Moved the copies into
`Hacl.HKDF.Core.fst` and added one `val expand_impl_ni` to the interface.
That is the better home anyway -- the copy sits directly under its original,
where a reader will see both.

All three verified **first try**, and so did the dispatch in `Hacl.HKDF.fst`.

### Measured

Microbenchmark, `taskset -c 2`:

| | before | after |
|---|---:|---:|
| gcc | 3,086 ns | **1,635 ns** |
| clang | 2,663 ns | **1,610 ns** |

1,635 is twice 809, which is what `hmac_sha256` costs on the same inputs.
Expand is at the floor for an algorithm that is two HMACs.

Full suite, r54g vs r53g (gcc): `hkdf-expand-sha2-256-64B` 3,091 → 1,649,
**1.87x**; nothing else moved.  r54c vs r53c (clang): 2,663 → 1,630,
**1.63x**; nothing else moved.

Against HACL\* best the row goes **2.29x → 1.22x** and leaves the ranking;
`k256-ecdsa-verify` at 2.05x is now the largest non-vector gap.

`make test` — all eight RFC 5869 vectors pass.  `make clones` **unchanged**,
which is the expected result and worth stating: three new C functions and
gcc found nothing new to specialise, because they *are* specialisations.

### The pattern's bill

This is the third transcription of this shape — `hash_blocks_ni`,
`hmac_impl_ni`, `expand_impl_ni` — each differing from its generic original
in exactly one call.  Still behind the wall: `Hacl.HMAC.DRBG.Core`,
`Hacl.HMAC.Cat`, `Hacl.HPKE.Labeled`, `Hacl.Streaming.HMAC`.

A fourth copy is not the answer.  Roadmap item 18 is now the general fix:
make the block function a *parameter* of `hash_blocks`, a higher-order
stateful argument carrying exactly the specification `update_block_impl`
already has, so one generic copy serves both and `inline_for_extraction` +
`monomorphize` specialises it away in C.  A static specialisation hierarchy
pays for an implementation choice in duplicated proof; EverCrypt's runtime
agility pays for the same choice in indirect calls.  Three copies is where
that bill comes due.

### Method note

Two parts in a row have now turned on the same thing: an estimate made from
the shape of the code was wrong, and a two-minute microbenchmark would have
said so.  Part 52's "register allocation" suspicion and Part 53's "150 ns"
estimate were both plausible and both wrong.  Measure the thing, not a model
of the thing.

Commit `923e8d2`.

## Part 54 — ChaCha20 on AVX2, eight blocks wide

### Where the ranking pointed

ChaCha20 at 5.31x, Poly1305 at 4.18x and ChaCha20-Poly1305 at 5.14x of
HACL\* best: the three rows roadmap item 17 says no scalar work can reach.
ChaCha20 is the one with the simplest proof shape and it is also on the
AEAD's path, so it went first.

Baseline on this machine (Xeon Gold 6140, gcc `-O3`, `taskset -c 5`, focused
microbenchmark against the extracted `dist/Hacl.c`):

| | 64 B | 1 KiB | 16 KiB | 256 KiB |
|---|---:|---:|---:|---:|
| ChaCha20 | 2.29 ns/B | 1.70 | 1.67 | 1.66 |
| Poly1305 | 1.72 | 0.93 | 0.88 | 0.89 |
| ChaCha20-Poly1305 encrypt | 6.34 | 2.79 | 2.56 | 2.54 |

### Implementation

**`lib/Hacl.Vec256.fst`** — fifteen `assume val`s realized by
`c/Hacl_Vec256.h`: load/store (stated on bytes), zero, broadcast, iota,
add, xor (stated on bytes *and* lanes, so nothing has to prove xor commutes
with the little-endian reading), rotate (16 and 8 by `vpshufb`, the rest by
two shifts and an or), and the six permutations of an 8 x 8 word transpose.
`lane x i` is defined, as `words_from_le 8 (vv x)`, not assumed.

**`code/chacha/Hacl.Chacha20.Vec256.fst`** — vertical layout: vector *i* is
word *i* of eight block states.  `lane_state vs j` is block *j*'s scalar
state; every round function proves `lanes_step v0 v1 f`, and twenty rounds
reduce to `Spec.Chacha20.rounds` lane by lane.  `init_vec` broadcasts the
state and sets word 12 to `bcast c + iota`; `core_vec` adds the original
back; two `transpose`s put block *j*'s 64 bytes into `t[2j]`, `t[2j+1]`;
sixteen 32-byte load/xor/store steps finish a 512-byte chunk.
`encrypt_blocks8` loops over whole chunks and carries the
`target("avx2")` prologue; `encrypt_vec` is the baseline-target dispatcher
(`mlen >= 512 && supported ()`).  `Hacl.Chacha20.encrypt` calls it and
starts its scalar loop at the returned offset with counter
`ctr0 + n / 64`.  The public postcondition is unchanged.

About 900 lines including proofs; the scalar driver changed by four lines.

### Proof notes

* **Pulse's context is too big for anything quantified.**  Every step that
  needed `forall j < 8` over a freshly updated sequence timed out inline and
  went through in milliseconds as a separate lemma with the exact term in
  its statement (`line_v`, `set12_lanes`, `chunk_step`, `chunk_inv`).  The
  rule that worked: the Pulse body only names sequences and calls lemmas.
* **Hide the predicate when the lemma is about indices.**  Combining the
  two transposes (`i % 2` picks which one wrote `t[i]`) timed out on
  `i % 2 <> 0 ==> i % 2 == 1` because `tr_ok` unfolded into a quantifier
  over lanes.  Stating the lemma for an arbitrary predicate `p` and calling
  it at `tr_ok vk` proved instantly.
* **`--split_queries` no longer exists** in this F\*.  A timeout is
  reported at the first sub-goal of the whole VC, which pointed at
  innocent refinements (`p - b >= 0`) for an hour; the real cost was the
  nonlinear body.  Bisecting in a scratch module took eight seconds per
  run instead of three minutes.
* The driver lemmas (`chunk_spec`, `chunk_ext`, `chunk_ctr`) are pure
  arithmetic on `b % 512`, `b / 64` and `max_len`; `mod512_64` (512 | b
  implies 64 | b, and `b == (b / 64) * 64`) was the missing fact.

### Measured

Same harness, same core:

| | 64 B | 1 KiB | 16 KiB | 256 KiB |
|---|---:|---:|---:|---:|
| ChaCha20, gcc | 2.41 | **0.40** | **0.36** | **0.35** |
| ChaCha20, clang | 2.51 | **0.41** | **0.38** | **0.38** |
| ChaCha20-Poly1305 encrypt, gcc | 6.48 | **1.47** | **1.25** | **1.25** |

ChaCha20 **4.7x** on 256 KiB, the AEAD **2.0x** (its remaining cost is now
mostly Poly1305: 0.89 of 1.25 ns/B).  At 64 B the vector code is not
entered; the 2-5% there is within this machine's run-to-run spread for an
unchanged Poly1305 alongside it.  A first version that called into
`encrypt_blocks8` for every message paid its stack-array setup to return 0
on short ones; the `mlen >= 512` guard removed it.

The double-round loop stays rolled (49 `vpaddd` in the whole function) and
gcc spills about a third of the state, which sixteen registers for sixteen
state vectors plus temporaries makes unavoidable on AVX2; AVX-512's 32
registers and `vprold` would remove both the spills and the shuffle-based
rotates.

`make test` passes, including two new tests: `test_vec256` (every axiom
against a scalar transcription; swapping the `hi128` immediate fails it) and
`test_chacha20_vec` (every length 0..2,100 at six counters including the
last legal blocks, against an RFC 8439 block function written in the test;
the same mutation fails it too).  `make clones` **unchanged**
at 63.

### Next

Poly1305 on four 64-bit lanes (roadmap 17).  Needs 64-bit-lane axioms
(`vpmuludq`, 64-bit add/shift/and) and a reordering lemma for four Horner
chains in *r^4*; the per-lane limb arithmetic should reuse
`Hacl.Poly1305.Field`.

## Part 55 — Poly1305 on AVX2, four blocks wide

### Implementation

**`lib/Hacl.Vec256.fst`** — eight more `assume val`s on 64-bit lanes
(`add64`, `mul32` = `vpmuludq`, `shr64`, `shl64`, `mask26`, `bcast64`,
`set64`, `store64`), each stated on naturals with the wrap written out.
`lane64 v i` is a definition: lanes `2i` and `2i+1` as 32-bit words, low
first.  Realized in `c/Hacl_Vec256.h`; `tests/test_vec256.c` checks each
against a scalar transcription (every shift distance included).

**`spec/Spec.Poly1305.Vec.fst`** — `horner_init`, `horner_step`,
`horner_final`: four chains in *r^4* over blocks ≡ j (mod 4), finished by
multiplying lane j by *r^(4-j)* and summing, are congruent to the
specification's chain in *r*.

**`code/poly1305/Hacl.Poly1305.Vec256.fst`** — radix 2^26, five vectors per
accumulator.  `vfmul` is the scalar `fmul` widened (25 `vpmuludq`, the same
two-way carry chain).  Multipliers *r^2..r^4* are computed with scalar
`fmul` and are 27-bounded after carrying, hence `mul_reduce_ok27`.  The block
load is two 256-bit loads plus `unpacklo64`/`unpackhi64`, which act per
128-bit half, so lanes hold blocks *g, g+2, g+1, g+3*; instead of a permute,
the final multiplier is `set64 (r^4, r^2, r^3, r)`.  The lanes are summed via
`store64`, added as scalar limbs and carried.  `absorb_vec` dispatches when
`n ≥ 8` blocks and AVX2 is present, consuming `4⌊n/4⌋` blocks; the scalar
loop in `absorb_blocks` resumes there.  Public spec unchanged.

### Proof notes

All-lane predicates (`vbounded`, `vmul_post`, `vload`, `vsum`, `vbc`,
`vinv`) are opaque; lemmas open them and argue per lane.  Code uses total raw
intrinsics.  Pitfalls: `S64.zero` is a global and Custard rejects it inside
the `avx2` target closure (use `S64.classify 0uL`, ghost side too);
`U64.v 0x1000000uL == pow2 24` needs `assert_norm`; `SZ.mul g 16sz` yields
`g * 16`, which does not match `16 * g`; the loop `decreases` needed
explicit bounds asserts; implicit ghost arguments to `absorb_vec` must be
passed explicitly.  The module checks in about four minutes.

### Measured

Xeon Gold 6140, `taskset`, ns/B, before (Part 54) → after:

| Case | gcc | clang |
|---|---|---|
| poly1305, 256 KiB | 0.88 → 0.20 (4.4x) | 0.69 → 0.24 (2.9x) |
| poly1305, 16 KiB | 0.88 → 0.18 | 0.69 → 0.19 |
| poly1305, 1 KiB | 0.94 → 0.28 | 0.72 → 0.27 |
| poly1305, 64 B | 1.76 → 1.73 | 1.25 → 1.31 (noise) |
| chacha20-poly1305 enc, 256 KiB | 1.25 → 0.57 (2.2x) | 1.23 → 0.65 |
| chacha20-poly1305 enc, 1 KiB | 1.50 → 0.85 | 1.46 → 0.84 |

Threshold: at 16 blocks the vector path lost 128–255-byte messages; at 8 it
wins from 128 B on both compilers (gcc 166 → 135 ns, clang 127 → 108 ns;
512 B: 506 → 200, 387 → 179).

Clang regression found and fixed: adding the dispatch made clang stop
inlining `absorb_blocks` into `mac`, costing ~12 ns at 64 B (15%).  Making
`absorb_blocks` `inline_for_extraction` restored it.

`make test` passes, including new `test_poly1305_vec` (every length 0..2,100
with four key/message kinds incl. maximal clamped *r* and all-ones data,
against a bignum reference in the test).  `make clones` **unchanged** at 63.

### Next

AVX-512 (ChaCha20 sixteen lanes, Poly1305 eight); regenerate the HACL\*
comparison table on the reference machine.

## Part 56 — The table, regenerated after the vector backends

`table.sh 3` under gcc 15.2.0 and clang 21.1.8 on the Xeon Gold 6140 (no SHA
extensions; EverCrypt sees `shaext=0 avx2=1 aesni=1 pclmul=1 bmi2=1 adx=1`),
against HACL\* `504c298`.  Canaries healthy on every run.  The README table
is the gcc run; it replaces the EPYC 7662 table.

| Row (vs HACL\* best) | EPYC, before | Xeon gcc | Xeon clang |
|---|---|---|---|
| ChaCha20, 256 KiB | 5.31x | 1.09x | 1.10x |
| Poly1305, 256 KiB | 4.13x | 0.97x | 1.00x |
| ChaCha20-Poly1305, 256 KiB | 5.13x | 1.04x | 1.07x |

Against portable HACL\* the three are now 0.12x, 0.26x and 0.15x.  The new
bottom rows are AES-128-GCM (2.04x gcc / 1.84x clang, against Vale) and MD5
(1.57x / 1.92x).  Without SHA-EXT, SHA-256 is scalar against scalar here
(1.02x gcc, 1.10x clang).  Under clang the curve rows are notably worse than
under gcc (X25519 1.71x, secp256k1 sign 1.59x, Ed25519 sign 1.48x) — worth a
look on this machine.

## Part 57 — The clang regressions: a mismatched baseline, MD5, GCM, and X25519 in radix 2^64

Part 56 left AES-128-GCM, MD5 and X25519 as the worst rows, with the clang
column notably worse than gcc's.  There were four causes.

**The clang baseline was gcc.**  `table.sh` compiled hacl-pulse with
`$BENCH_CC` but linked the HACL\* checkout's own `libevercrypt.a`, which its
Makefile builds with `cc`, so every clang row was clang against gcc.
`table.sh` now builds HACL\* with `$BENCH_CC` into
`$HACL_STAR/dist/build-$CC` and caches it there.

**MD5 was not unrolled.**  The step function took the round number as a
runtime value, so every step selected its boolean function, constant, shift
and message index at run time and rotated by a register.  The block update
now calls an `inline_for_extraction` step sixteen times per sixteen-step
group, and everything folds to literals.  256 KiB: 592 → 412 us (gcc),
722 → 399 us (clang).

**GCM ran two passes.**  Encryption did counter mode over the whole message
and then GHASH over the whole ciphertext.  `Hacl.AES.GCM.Stitch` encrypts
eight counter blocks per iteration while hashing the eight ciphertext blocks
written on the previous one, with the eight powers of the hash key loaded
and Karatsuba-folded once per message.  256 KiB aes128-gcm-enc: 93.7 → 67.9 us
(gcc), 84.6 → 68.5 us (clang); Vale is 45.6.  `tests/test_gcm_long.c` checks
every length from 0 to 1300 for both key sizes against the unstitched
decryption.

**X25519 under clang: radix 2^64.**  clang compiled the radix-51 field
at 54.6 us against gcc's 43.  Instead of chasing that, the library gained a
second verified field: four 64-bit limbs, products by `mul_wide` rows,
carries by a new trusted pair `Hacl.Carry64.addc`/`subb`
(`c/Hacl_Carry64.h`, preferring `__builtin_addcll`), and fold by 38.
`scalarmult` dispatches to it when cpuid reports BMI2.  Isolated bench
(`taskset`, -O3), µs per scalar multiplication:

| path | gcc 15.2 | clang 21.1 |
|---|---|---|
| radix 2^51 | 43 | 54.6 |
| radix 2^64, `_addcarry_u64` | 48–50 | 39.6 |
| radix 2^64, `__builtin_addcll` | 48.3 | 36–38 |
| hand-written C prototype of the same algorithm | 38.6 | — |

The gcc loss was examined at length and is diffuse.  The verified `fmul`
matches the prototype's in isolation.  In the ladder there is about 4 us in
`fmul` in context, 2 us in `fadd`/`fsub`, 2 us in inversion, where `fsqr_ip`
is out of line and copies, and 2 us in the ladder's shape: four select-based
conditional swaps per step where the prototype keeps a swap state and does
two.  No gcc flag, inline or noinline placement, memory-output variant,
removal of zero-initialization, or mask in place of multiply moved it by
more than noise.  The 64-bit path ships on every BMI2 machine regardless, by
decision.  Next candidates for gcc: an in-place squaring for inversion, a
swap-state ladder, and an xor-based cswap.

**Table** (`table.sh 3`, Xeon Gold 6140, HACL\* `504c298` built with the same
compiler; canaries healthy):

| Row (vs HACL\* best) | Part 56 gcc | gcc | Part 56 clang | clang |
|---|---|---|---|---|
| MD5 | 1.57x | 1.25x | 1.92x | 0.97x |
| AES-128-GCM | 2.04x | 1.49x | 1.84x | 1.43x |
| X25519 | 1.32x | 1.53x | 1.71x | 1.14x |

The clang column now compares like with like, and that changes other rows.
With HACL\* built by clang, its SHA-512 is a third faster than gcc's, so
SHA-512 and HMAC-SHA-512 go to 1.27x; its P-256 is twice as fast (sign:
63 us against 136), so the three P-256 rows are at 2.82x–2.91x.  This
repository's P-256 is the same speed under both compilers.  P-256 under clang
is the new largest gap.

## Part 58 — Against other libraries

Every comparison up to Part 57 was against HACL\*.  `bench/others.sh` adds
OpenSSL 3.5.5 (system), AWS-LC `ffca127`, libsodium 1.0.22, libjade
2023.05-2, Firedancer `ballet` `849c582` and the dalek crates (curve25519 4.1.3,
ed25519 2.2, x25519 2.0.1), each pinned and built once into `/tmp/others`.

**Harness.**  `others/others.c` is a single driver compiled once per library
against an `ops_*.h` header that defines a `BO_<row>` macro and a `bo_*`
function for each row that library has.  Each binary also links hacl-pulse,
which generates the inputs and is the oracle.  Before timing a row the driver
compares the library's output with hacl-pulse's and exits on a mismatch.  The
comparison is byte for byte for hashes, MACs, ciphers, AEADs, X25519,
Ed25519, ECDH, RSA-PSS with a zero-length salt, and FFDHE.  ECDSA signatures
are cross-verified, and ML-KEM is checked by decapsulating across libraries.
Two details needed handling:

- libjade's secretbox uses the NaCl zero-padding convention.  It is given a
  pre-padded copy of the message, and its output is compared at offset 16.
- Firedancer's P-256 takes compressed keys and, by default, rejects high-s
  signatures, so it uses `fd_secp256r1_verify_allow_high_s`.

Runs are palindromic over the eight binaries (hacl-pulse with gcc and with
clang, plus six others), pinned to one core, for three rounds.
`mkothers.py` drops runs whose canary is more than 2% above the best one
and reduces the rest by minimum.

**Result** (Xeon Gold 6140, 256 KiB bulk; ratio = better hacl-pulse build
over the fastest other):

- hacl-pulse is faster only on secp256k1 signing (0.27x).  That row only
  reflects generic EC code in OpenSSL and AWS-LC; libsecp256k1 was not
  measured.
- Within 1.6x: BLAKE2s 1.03x, Poly1305 1.21x, MD5 1.23x, AES-GCM
  1.31x/1.43x, BLAKE2b 1.45x, ChaCha20-Poly1305 1.46x, X25519 1.53x, and
  SHA-3/SHAKE 1.56–1.58x.  libjade leads Keccak, s2n-bignum leads X25519,
  and OpenSSL leads Poly1305 and GCM.
- 2–4x: ChaCha20 2.02x, SHA-2/HMAC 2.03–2.14x, RSA sign and FFDHE 2.35x,
  Ed25519 3.3–3.9x, SHA-1 3.89x.  The SHA rows reflect AVX2 message
  schedules that hacl-pulse lacks.  The ChaCha20 gap is AVX-512; see Part 59.
- 5x and more: ML-KEM 5–6.4x, against AWS-LC's mlkem-native AVX2.  P-256
  is 5.4–10.7x against `nistz256` assembly and tables, RSA verify 9.5x, and
  Salsa20 10x (no vector backend), which also drives secretbox to 3.9x.

The table and discussion are in the top-level README under *Against other
libraries*.

## Part 59 — The ChaCha20 gap is AVX-512

Part 58 found ChaCha20 2.02x behind libsodium.  I timed 256 KiB pinned to one
core, calling libsodium's internal implementation tables directly
(`crypto_stream_chacha20_dolbeau_{avx2,avx512}_implementation`) and taking
the best of 36 interleaved runs:

| Kernel | 256 KiB |
|---|---|
| hacl-pulse AVX2 (8 blocks) | 100.3 us |
| libsodium AVX2 (8 blocks) | 102.1 us |
| libsodium AVX-512 (16 blocks, `zmm`, `vprold`) | 48.9 us |

The Xeon Gold 6140 has AVX-512F, so libsodium's dispatcher picks the AVX-512
kernel; gdb disassembly confirms `zmm` registers.  OpenSSL has the same
story.  Unmodified, it takes 61 us.  With `OPENSSL_ia32cap=':~0x10000'`
(AVX-512F masked) it still takes 61 us, because it also uses its AVX-512VL
path (`ymm` registers with `vprold`).  With all AVX-512 bits masked
(`:~0xd0230000`) it takes 91 us, which is plain AVX2, and 177 us with AVX2
masked as well.

So among AVX2 kernels hacl-pulse ties libsodium and is about 10% behind
OpenSSL's hand-scheduled assembly.  There is no code-quality problem to fix.
Closing the gap needs an AVX-512 backend: a trusted `Hacl.Vec512` with 16
lanes and native rotate, behind `__builtin_cpu_supports("avx512f")`.
libsodium's Salsa20 also has an AVX-512 kernel (`salsa20_xmm6int-avx512.c`),
which is why it leads libjade's AVX2 Salsa20 by 2x.

## Part 60 — AVX-512 ChaCha20

**Where it pointed.**  Part 59 showed the ChaCha20 gap to libsodium and
OpenSSL was AVX-512 against AVX2, not code quality.

**Implementation.**  `lib/Hacl.Vec512.fst` and `c/Hacl_Vec512.h` give
seventeen trusted axioms for AVX-512F: load and store, zero, broadcast,
iota, lane-wise add, exclusive-or and `vprold`, four unpacks and four
`vshufi32x4` group selections.  `tests/test_vec512.c` checks each against a
scalar transcription, including the rotate at every distance both as a
literal and through a variable.  `code/chacha/Hacl.Chacha20.Vec512.fst` is
the eight-lane kernel at sixteen lanes; the rounds, `init_vec` and
`core_vec` carried over with only the lane bounds changed.  The new part is
the 16 x 16 transpose, proved as two steps with one predicate each (`qa_ok`,
`qb_ok`) and a composition lemma.  `Hacl.Chacha20.Vec256.encrypt_vec` now
runs `encrypt_blocks16` over whole 1024-byte chunks when
`__builtin_cpu_supports("avx512f")`, then `encrypt_blocks8` from that
offset (it gained a start argument and a prefix precondition), then the
scalar loop.

**Proof notes.**  The frame facts of the transpose steps were first written
with `i / 4 <> q` and `i % 4 <> m`; the collection lemmas timed out on
them.  Rewritten linearly (`i < 4q \/ 4q + 4 <= i`, and `4g + k` with
`k <> m`) they go through with empty bodies.  A conditional `let n1 = if
... { encrypt_blocks16 ... } else { 0sz }` could not join the two branches'
`out` contents; moving it into a small `fn` with its own postcondition
fixed that.

**Measured** (Xeon Gold 6140, core 6, best of 7):

| size | before (gcc) | after (gcc) | after (clang) |
|---|---|---|---|
| 1 KiB | 0.415 ns/B | 0.225 ns/B | 0.201 ns/B |
| 16 KiB | 0.390 ns/B | 0.204 ns/B | 0.189 ns/B |
| 256 KiB | 102.2 us | 54.4 us | 48.9 us |

That is level with libsodium's AVX-512 kernel (47–49 us) and ahead of
OpenSSL (57–61 us).  `tests/test_chacha20_vec.c` covers every length from 0
to 2,100 bytes at counters up to the last legal block, so the
AVX-512 → AVX2 → scalar hand-offs are all exercised.

## Part 61 — Vector Salsa20

**What changed.**  Salsa20 was the last stream cipher without a vector
backend: 1.83 ns/B against libsodium's 0.18.  `Hacl.Salsa20.Vec512`
(sixteen lanes, AVX-512F) and `Hacl.Salsa20.Vec256` (eight lanes, AVX2) are
the ChaCha20 modules with the round function replaced -- Salsa20's
`a ^= (b + c) <<< s`, its quarter-round order, column and row rounds -- and
the counter moved from word 12 to word 8.  The transposes, the
exclusive-or and the chunk driver are unchanged, since the keystream is
serialized identically.  No new axioms; both modules verified as first
written (about 3 min and 1.5 min).  `Hacl.Salsa20.encrypt` now calls
`encrypt_vec` first and the scalar loop resumes at `ctr0 + nb / 64`, so
XSalsa20, secretbox and box get it with no changes of their own.

**Numbers** (core 6, best of 7, one-shot calls):

| | before (gcc) | after (gcc) | after (clang) | AVX2 only (gcc) |
|---|---|---|---|---|
| Salsa20, 1 KiB | 1.89 us | 0.219 us | 0.197 us | 0.402 us |
| Salsa20, 256 KiB | 480 us | 45.2 us | 43.3 us | 97.1 us |
| secretbox, 1 KiB | 2.56 us | 1.76 us | 1.68 us | -- |
| secretbox, 256 KiB | 542 us | 98.2 us | 90.5 us | -- |

Salsa20 is now ahead of libsodium's AVX-512 kernel (48 us) and the AVX2-only
path level with libjade's AVX2 (96 us).  secretbox is ahead of libsodium and
libjade (139--141 us); what is left of it is mostly the AVX2 Poly1305.

**Testing.**  `tests/test_salsa20_vec.c` runs every length from 0 to 2,100
bytes at seven counters, up to the last legal block, against an
independent Salsa20 block function, checking that the input is untouched
and nothing past the output is written.  It passed against the old scalar
code first (validating the reference), then with the new dispatch, and
again with `Hacl_Vec512_supported` and then also `Hacl_Vec256_supported`
forced false, so the AVX-512, AVX2 and scalar paths and every hand-off
between them are exercised.

## Part 62 — A field for P-256's prime

**What changed.**  P-256's field ran on `Hacl.Impl.Mont4`, the generic
four-limb CIOS multiplier that takes its modulus as table data and sums
columns in `__int128`.  `code/p256/Hacl.P256.Field64.fst` replaces it for
`fadd`, `fsub`, `fmul`, `fsqr` and `fto`:

- the product is `Hacl.Curve25519.Field64.mul8` (sixteen `mul`s chained with
  `adc` through `Hacl.Carry64`), whose `mrow`, `mrow_add` and `mul8` lost
  their `target("bmi2")` prologue so non-BMI2 code can inline them --
  they use no BMI2 instruction, and X25519 compiles exactly as before
  (48.6 / 48.3 us gcc, 35.5 / 36.3 us clang, noise);
- four Montgomery steps `rstep0`..`rstep3`: `mu == 1`, so the quotient is
  the bottom word `u`, and `p + 1 = 2^96 + 2^192 * 0xffffffff00000001`, so
  `(W + u p) / 2^64` is `W / 2^64 + (u << 32) + 2^64 (u >> 32) + 2^128 u P3`
  -- two shifts and one multiplication per step.  Each step's postcondition
  is `w * W_(k+1) == W_k + u * p` with every power of the radix a numeral,
  linear for Z3; a precondition bounding `W_k + u p` is what proves the top
  carry zero;
- `csub`: `W_4 < 2p`, one borrow chain through the fifth word and a masked
  select;
- `fadd`/`fsub`: one carry chain, then a borrow chain against `p` and a
  select (add), or a masked `p` added back (sub).

`Hacl.P256.Field` keeps its interface.  Three lemmas connect the two views:
`eval (vals s) == ev s` for four words, and "a residue with the value of
`mmul`/`madd`/`msub` has the same `mev`", which reuses `rcancel` and the
existing `mev_*` lemmas.  The module needed `#restart-solver` between its
functions: each verifies in seconds alone, but in one Z3 session `fadd`
ran for over twenty minutes without tripping its rlimit.  The whole module
checks in about six and a half minutes; `rstep0` is the slowest query (23 s).

**Numbers** (core 6, best of 7, HEAD vs this change, same binary harness):

| | gcc before | gcc after | clang before | clang after |
|---|---|---|---|---|
| `fmul` | 33.8 ns | 24.7 ns | 46.5 ns | 18.4 ns |
| `fadd` | 7.0 ns | 4.2 ns | 3.9 ns | 3.3 ns |
| `fsub` | 8.7 ns | 2.4 ns | 3.0 ns | 2.5 ns |
| ECDH initiator | 176 us | 112 us | 163 us | 88 us |
| ECDH responder | 285 us | 180 us | 256 us | 129 us |
| ECDSA sign | 192 us | 131 us | 185 us | 110 us |
| ECDSA verify | 448 us | 292 us | 428 us | 222 us |

Against OpenSSL's `nistz256` assembly (Part 58: ECDH 48 us, sign 24 us,
verify 67 us) that is 2.7x-5.5x, down from 5.4x-10.7x.  What is left is
algorithmic: the generator tables are still built at run time
(`Hacl.P256.TablesG`, about 12% of instructions), verification does two
separate scalar multiplications rather than one interleaved one, and the
fixed-base comb has four sixteen-entry tables where `nistz256` has 150 KB.

**Testing.**  `tests/test_p256.c` (RFC 6979 vectors, ECDH agreement and
rejection) and the whole of `make test` pass.  A C prototype of the same
reduction agreed with the old multiplier on a million random inputs before
the Pulse was written.

## Part 63: P-256 compiled-in generator tables

The fixed-base window (`Hacl.P256.PointMulG`) used to build its four
sixteen-entry tables at run time from `G`, `2^64 G`, `2^128 G` and
`2^192 G` (`Hacl.P256.TablesG`), about 12% of the instructions of a
fixed-base operation.  The tables are now compiled in, exactly as secp256k1's
were in commit `f77e256`:

- `spec/Spec.P256.Win0` .. `Win3`: sixteen affine multiples `d * 2^{64j} G`
  each, every one proved on the curve and `peq` to the previous entry plus
  the scale point by one `assert_norm`, lifted by `Spec.Group.smul_add_congr`;
- `code/p256/Hacl.P256.Win0` .. `Win3`: twelve `static const uint64_t [64]`
  arrays of Montgomery limbs (entry 0 is `(0, R, 0)`, every `z` is `R`), with
  `tbl_ok : tok tx ty tz G scale 16`;
- `code/p256/Hacl.P256.WinTable`: the four-limb chunk lemmas and
  `entry_felem` (`leval chunk == x * 2^256 % p` gives `felem` and `fev == x`).

All eight are generated by a script that also checks `2^64 G` against
`Spec.P256.Base`.  `win_add` takes one permission per coordinate array.
`TablesG` is deleted.

**Numbers** (core 6, `-O3 -march=native`, best of 5, HEAD vs this change; this
harness keeps each iteration's key and nonce dependent on the previous output,
because gcc hoisted the loop-invariant initiator out of the loop):

| | gcc before | gcc after | clang before | clang after |
|---|---|---|---|---|
| ECDH initiator | 97 us | 69 us | 77 us | 59 us |
| ECDH responder | 153 us | 153 us | 116 us | 116 us |
| ECDSA sign | 119 us | 92 us | 98 us | 79 us |
| ECDSA verify | 259 us | 229 us | 195 us | 176 us |

The variable-base responder is the control.

## Part 64: P-256 inversion on the specialised field

Callgrind on a variable-base ECDH after Part 63: `fmul` 57% of instructions,
`fadd` 13%, and `finv` with the generic Montgomery core under it
(`mul_columns`, `carry_run`) about 11%, because `finv` and `fsqrt` were
`Hacl.Impl.Exp4.mexp`.  `Hacl.P256.Exp` ports `Hacl.K256.Exp52`'s
left-to-right square-and-multiply to four 64-bit limbs and `Hacl.P256.Field`'s
`fmul`/`fsqr`; `Hacl.P256.Inverse` calls it with `p - 2` and `(p + 1) / 4`.
The scalar inversion mod `n` still uses `Mont4`.

**Numbers** (same harness, best of 5, HEAD = Part 62, after = Parts 63 + 64):

| | gcc before | gcc after | clang before | clang after |
|---|---|---|---|---|
| ECDH initiator | 96.8 us | 64.8 us | 77.4 us | 49.2 us |
| ECDH responder | 151.7 us | 147.9 us | 117.5 us | 104.9 us |
| ECDSA sign | 118.5 us | 86.3 us | 96.4 us | 68.6 us |
| ECDSA verify | 255.8 us | 224.2 us | 193.8 us | 166.0 us |

Every output is identical before and after.  `make test` passes.  `bench/bench.c`
no longer builds against the current `Hacl_Bignum_Montgomery_precomp`
signature (this predates these changes), so these numbers come from the
P-256-only harness rather than the main table's.

## Part 65: scalar Montgomery multiply and addition-chain inversion

After Part 64 the scalar inversion mod `n` (`qinv`, square-and-multiply on
`Hacl.Impl.Mont4`) took 19-21 us, a quarter of a P-256 signature.
`Hacl.Impl.Mont64` is a generic word-by-word Montgomery multiply (`mul8`
product, four reduction steps of `q = t_k * mu`, one masked final
subtraction); `Hacl.Impl.Mont4F.amulf` puts it behind `Mont4.amul`'s
contract, so both curves' `qmul` change by one call: 42 ns to 24 (clang),
63 to 33 (gcc).  `qinv` becomes a generated addition chain for `n - 2`: odd
powers `x .. x^15`, blocks of ones for the top half, a width-4 sliding window
below.  P-256: 253 squarings, 39 multiplications (binary: 255, 168).
secp256k1: 253 and 42 (binary: 255, 195).  Squarings ping-pong between two
buffers.  Each chain step is a call to one verified `qstep` (square `k`
times, multiply by a table power) with `assert_norm` on the exponent; written
inline, the same chain took 8.5 minutes to check, factored about 1.5.

**Numbers** (core 6, `-O3 -march=native`, best of 5, HEAD = Part 64):

| | gcc before | gcc after | clang before | clang after |
|---|---|---|---|---|
| P-256 `qinv` | 21.4 us | 9.8 us | 19.0 us | 7.4 us |
| P-256 ECDSA sign | 87.1 us | 75.1 us | 68.4 us | 57.4 us |
| P-256 ECDSA verify | 227.1 us | 212.9 us | 165.4 us | 154.3 us |
| secp256k1 ECDSA sign | 112.2 us | 99.4 us | 84.8 us | 72.2 us |
| secp256k1 ECDSA verify | 274.6 us | 260.3 us | 186.6 us | 174.2 us |

ECDH (no scalar inversion) is unchanged and is the control.  `make test`
passes.

**Not kept.**  A dedicated P-256 `fsqr` (cross products computed once) is
about 40% faster than `fmul` on itself but takes only 1-3% off whole
operations.  fiat-crypto's `p256_64.h` Montgomery multiplier is slower than
`Hacl.P256.Field64`'s: 28.6 ns against 17.5 (clang), 70 against 24.4 (gcc).

## Part 66: tables re-measured

Both README tables regenerated at HEAD after Part 65 (`table.sh 3` under gcc
and clang, `others.sh 3`, cores 2, 6 and 10, `mktable.py`/`mkothers.py`).
Against HACL\* best under gcc: ChaCha20 1.09x to 0.53x, ChaCha20-Poly1305
1.06x to 0.67x, Salsa20 1.18x to 0.11x, secretbox 0.93x to 0.16x, P-256
1.28x--1.35x to 0.60x--0.72x, secp256k1 sign 1.23x to 1.08x.  Under clang
P-256 went from 2.8x--2.9x to 0.93x--1.16x.  Against other libraries,
hacl-pulse now leads on ChaCha20, Salsa20, ChaCha20-Poly1305 and secretbox,
and P-256 is 2.5x--3.8x behind AWS-LC rather than 5x--11x.  Absolute times
for every library were about 4% higher than in the previous run; ratios are
the comparison.

## Part 67: RSA verification starts at the exponent's top bit

RSA-PSS verification was 9.5x behind AWS-LC.  A callgrind profile (built
`-march=haswell -madx`, since valgrind cannot run AVX-512) showed why:
`mod_exp_vartime` walked every bit of the 64-bit limb holding `e = 65537`,
so it paid for 64 squarings and two multiplies where 16 squarings and one
multiply are enough.  Each squaring was a `copy` and a `mont_mul`.

Changes, all verified:

- `Hacl.Bignum.Exponentiation`: new `top_bit`, which finds the exponent's
  highest set bit with a variable-time scan (the exponent is public), and
  `seed_acc`, which sets the accumulator to `aM` (and leaves it at the
  Montgomery one when the exponent is zero).  The lemmas `lead_zero` and `lead_one` justify
  dropping the leading zeros and taking the top one for free.  The ladder
  then runs from the bit below that, and squares with `mont_sqr`.  The
  constant-time ladder is untouched and still runs over the full bit length.
- `Hacl.Bignum.Montgomery.precomp`: its ladder step squares with `mont_sqr`
  instead of `copy` + `mont_mul` (about 1.7M to 1.5M instructions per call).

A/B against the previous commit, using the same `bench.c` and interleaved
runs, best of each, in microseconds:

| row | gcc old | gcc new | | clang old | clang new | |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| rsapss-2048-verify | 177.6 | 64.2 | 2.77x | 158.9 | 59.7 | 2.66x |
| rsapss-2048-sign | | | 1.00x | | | 0.96x |
| ffdhe2048 | | | 0.98x | | | 0.96x--0.97x |
| bn2048-modexp-consttime | | | 1.00x | | | 0.96x |

The constant-time rows are noise or layout, not code.  Their C is identical
apart from function order.  Under clang, `mont_sqr` now has three callers
and is no longer inlined into `Exponentiation.mont_sq`, so the code shifts.
In a standalone harness old and new are 4342 and 4359 us; with
`-falign-functions=64 -falign-loops=64` on both they are about 4570, so the
old build was alignment-lucky, and with forced alignment the bench's sign
and FFDHE rows are 1.00x--1.01x.  Under gcc, the old object had four
`Exponentiation.mont_sq.constprop` clones, one per modulus size, and the
new one has none, for the same reason.  That accounts for the remaining 2%
on FFDHE.

Against the other libraries, verification goes from 9.5x to about 3.4x
behind AWS-LC's 18 us, and against HACL\* from 1.28x to 0.46x.  These two
README rows were edited from this A/B run rather than from a full table run.
A verify is now about 3.9M instructions: about 54% exponentiation (about 20
Montgomery operations), 38% `precomp` (about 11 squarings and 65
doublings) and the rest hashing.  Every Montgomery operation is dominated
by the `n^2` reduction, so the next lever for verification, signing and
FFDHE alike is a MULX/ADX dual-carry-chain multiply and reduction.

## Part 68: ML-KEM's NTT in place, with Shoup multiplication

A callgrind profile of ML-KEM-768 put the forward and inverse NTT at 42% of
all instructions (`ntt_inplace` 28%, `intt_inplace` 14%).  The transform was
written in the shape of the specification: each layer a flat loop over all
256 output coefficients, a branch per coefficient choosing the butterfly arm,
the zeta product computed separately for each arm, a sixty-four-bit Barrett
reduction per product, and two buffers used alternately with a copy at the
end.  About 6.1 us (gcc) and 7.3 us (clang) per transform.

Now:

- `Hacl.Impl.MLKEM.Zq.zq_mul_shoup`: multiplication by a constant `z` whose
  companion `zs = floor(z 2^16 / q)` is known.  `t = (y zs) >> 16` in
  thirty-two bits, `r = y z - t q` modulo `2^16`, one conditional
  subtraction.  `shoup_bound` proves `0 <= y z - t q < 2q`, so the sixteen-bit
  wrap is exact.
- `Hacl.MLKEM.Tables.zeta_shoup_arr`: the 128 companions, checked against the
  zeta table by normalization like the zetas themselves.
- `Hacl.Impl.MLKEM.NTT`: each layer is an outer loop over blocks, which reads
  the root and its companion once, and an inner loop of `len` butterflies
  that read both inputs before writing either.  The layer function is
  `inline_for_extraction` and called with literal `len`, so the inner loop
  has a constant trip count in the C and is vectorised.  The invariant
  `part` (opaque to SMT, with start/read/step/next/done lemmas) says which
  coefficients already hold the layer's output; the rest still hold its
  input.  The inverse transform's final scaling by `128^-1` is also Shoup.
  `ntt_inplace`/`intt_inplace` keep their scratch parameter, now unused, so
  no caller changes.

A C prototype of this shape ran an NTT in 0.81 us (gcc) and 0.59 us
(clang) with `-march=native`; the same shape with a runtime `len` was
1.4--2.8 us because nothing vectorised.

ML-KEM-768, best of interleaved runs, in microseconds:

| build | keypair | encaps | decaps |
| --- | ---: | ---: | ---: |
| `bench.c`, gcc `-O3`, old | 98.6 | 106.8 | 138.9 |
| `bench.c`, gcc `-O3`, new | 65.3 | 75.1 | 90.2 |
| `others.c`, clang `-O3`, old (Part 66 table) | 90 | 131 | 190 |
| `others.c`, clang `-O3`, new | 52.8 | 59.7 | 71.1 |
| gcc `-O3 -march=native`, old | 75.2 | 83.0 | 111.5 |
| gcc `-O3 -march=native`, new | 43.9 | 49.9 | 57.5 |
| clang `-O3 -march=native`, old | 70.5 | 105.0 | 158.2 |
| clang `-O3 -march=native`, new | 36.6 | 42.0 | 49.6 |

AWS-LC measured in the same run as the `others.c` rows: 16.6, 17.6 and
20.9 us, so the gap is now 3.2x--3.4x instead of 5.2x--6.4x.  The README's
ML-KEM table is regenerated with `mkkem.py` from three `bench.c` runs; the
three other-library rows were edited from this run.

After the change the profile is `sample_ntt` (SHAKE128 plus rejection) 39%,
SHAKE256 15%, `multiply` (base-case products, still sixty-four-bit Barrett)
11%, CBD sampling 8.5%, NTT 5.8% and inverse NTT 5.1%.  The next levers are
the matrix expansion (several SHAKE128 lanes at once) and the base-case
products.

## Part 69: tables re-measured on Zen 3, and ML-DSA against other libraries

All three README tables were re-run after the issue #1 wiping work, the
ML-DSA merge and the F\* nightly of 10-18.  The machine is now an AMD EPYC
7V13 (Zen 3: AVX2, ADX, SHA extensions, no AVX-512) in a shared virtual
machine, not the Xeon Gold 6140 of Parts 60--68, so the AVX-512 backends do
not run and HACL\*'s best build uses Vale's SHA-EXT code.  `table.sh 3` was
run once under gcc and once under clang; `others.sh 3` twice, and the six
rounds pooled.

**Canary noise.**  The canary ranged from 176 to 191 ms across `others.sh`
runs, about 8%, against the 1--2% of the old machine.  The 2% filter in
`mkothers.py` dropped 110 of 144 runs and left libcrux with none, so both
`mkothers.py` and the new `mkmldsa.py` take the tolerance as an optional
second argument; the README tables use 0.05 (45 of 144 dropped).  At 0.03
every cell agrees with 0.05 to within a few percent.

**ML-DSA contenders.**  `others.sh` now also builds pq-crystals/dilithium
(`ref/` and `avx2/`, all three parameter sets into one archive each,
`-Wa,-I` for the AVX2 assembly's `.include`), mldsa-native (monolithic
multilevel build with the x86-64 arithmetic and Keccak backends) and a
libcrux-ml-dsa 0.0.11 FFI crate.  libcrux-platform 0.0.4 does not build
with the distribution's rustc 1.93 (`__cpuid` became safe later), so the
crate pins 1.99.1 in `rust-toolchain.toml`.  OpenSSL and AWS-LC gain
ML-DSA rows too.  Every implementation's key from a 32-byte seed must
equal hacl-pulse's, and its signatures must equal `sign_deterministic` on
64 messages; AWS-LC's EVP signing is hedged only, so it is cross-verified.
`TIME_MIN` keeps the iteration count a multiple of 64 so that signing
averages over all 64 messages, whose rejection-sampling attempts differ.

ML-DSA-65, microseconds (keygen / sign / verify): hacl-pulse gcc
193/700/193, clang 202/563/194; pq-crystals ref 129/606/138; OpenSSL
173/1039/186; pq-crystals avx2 39/105/41; mldsa-native 36/107/37; AWS-LC
53/147/50; libcrux 40/132/40.  hacl-pulse is 5.1x--5.9x behind the fastest
across 44/65/87.

**Ed25519 and secp256k1 signing under gcc.**  In the main table these went
from 1.27x and 1.08x of HACL\* best to 1.71x and 1.52x.  A/B on this machine,
`dist/Hacl.c` as committed against the same file with `Hacl_Mem_wipe` a
no-op (best of 30 x 200 calls, pinned):

| build | Ed25519 sign | secp256k1 sign |
| --- | ---: | ---: |
| gcc, as committed | 83 us | 85 us |
| gcc, no wiping | 59 us | 56 us |
| gcc, wrappers `always_inline`, `-mmemset-strategy=unrolled_loop` | 61 us | 66 us |
| clang, as committed | 75 us | 77 us |
| clang, no wiping | 73 us | 75 us |

Custard extracts `Mem.wipe` at each element type as an out-of-line
`static void Hacl_Mem_wipe__t_N(T *a, size_t eta)`.  gcc keeps it out of
line, and with a length it cannot see it clears even a 40-byte field
element with `rep stosq`, whose start-up cost dominates; Ed25519's point
addition and doubling wipe seven temporaries each and account for about
14 of the 25 us.  Inlining the wrappers alone recovers about 60%;
inlining plus no `rep stos` recovers all of it on Ed25519.  A store loop
in `c/Hacl_Mem.h` instead of `memset` was slower (101 us), presumably
because it defeats the constant-length lowering after inlining.  The fix
turned out to belong in `c/Hacl_Mem.h` instead; see Part 70.  The 7--11% measured for Ed25519 when the wiping landed does not
reproduce on this machine.

## Part 70: small constant wipes as volatile word stores

Part 69 left Ed25519 and secp256k1 signing 40--50% slower under gcc than
with wiping compiled out.  Two candidate fixes were tried by editing a copy
of `dist/Hacl.c` before touching the source:

| `dist/Hacl.c` built with gcc `-O3` | Ed25519 sign | secp256k1 sign |
| --- | ---: | ---: |
| as committed | 83 us | 84 us |
| `Hacl_Mem_wipe` a no-op | 59 us | 56 us |
| wrappers `static inline` (what `[@@CInline]` on `Mem.wipe` would give) | 78 us | 81 us |
| wrappers `always_inline` (what `inline_for_extraction` would give) | 68 us | 75 us |
| plain store loop in the macro, no `__builtin_constant_p` | 101 us | -- |
| volatile word stores for constant lengths <= 512 bytes | 65 us | 64 us |

`static inline` is not enough: gcc keeps the six scalar wrappers out of
line.  Inlining every wrapper makes the length constant, but gcc still
lowers a constant memset of 128 bytes or more -- Ed25519's nine-element
`unsigned __int128` products, for instance -- to `rep stosq`, and it would
have meant changing `Hacl.Mem.fsti` and re-verifying everything.  The last
row needs neither: `Hacl_Mem_wipe` tests `__builtin_constant_p` on the byte
length, and when it is a multiple of eight of at most 512 it zeroes through
`volatile` eight-byte stores of a type declared `aligned(1), may_alias`,
so it is correct on unaligned buffers and on any element type.  Volatile
stores cannot be removed, so that path needs no asm barrier; every other
length keeps memset and the narrow `"m"` barrier.  gcc folds the test after
inlining, which is why it pays even with the wrappers out of line: the
wrappers become small enough to inline.  `Hacl_Mem_free` keeps the old
memset path unconditionally -- a heap length is never constant -- because
routing it through the new macro changed gcc's inlining enough to trip a
false `-Wstringop-overflow` in `Hacl_RSAPSS_bn_from_be`, which `-Werror`
turns into a build failure.

Tables re-measured with the change (`table.sh 3` under gcc and clang,
`others.sh 3`).  Under gcc, Ed25519 signing went from 85 us (1.71x of
HACL\* best) to 66 us (1.32x), secp256k1 signing from 85 us (1.52x) to
65 us (1.15x), the P-256 rows 5--6% faster, SHA-512 4%, BLAKE2b 7%; no row
got slower beyond noise.  Under clang the table is unchanged within noise,
with Ed25519 and secp256k1 signing 2% slower in the A/B.  The C tests pass
under both compilers with the build's `-Wall -Wextra -Werror`.


## Part 71: vector wipes compiled for the wrong target

ChaCha20 at 256 KiB was 11% slower with wiping than with `Hacl_Mem_wipe`
compiled out, under both compilers, although it wipes about 1.5 KB once per
call.  The wipe was not the cost; the call was.  `encrypt_blocks8` passes
its sixteen-vector scratch arrays to `Hacl_Mem_wipe__t_6`, Custard's
monomorphized `Mem.wipe` at `Hacl_Vec256_t`, and an array whose address
reaches an out-of-line call has to live in memory for the whole loop: gcc
emitted 127 vector stores to the stack and 76 loads in the function, against
46 and 15 without the wipes.

Neither compiler would inline the wrapper because Custard had marked it
`__attribute__((target("bmi2")))`, which an AVX2 caller does not include.
Custard's closure-prologue propagation (`propagate_prologues`, its section
51.3) gives every declaration reached only from functions carrying
`custard_c_closure_prologue` the *first* such string in the program -- one
seed's strings are taken to be as good as another's -- and the first in this
program is Curve25519's `bmi2`.  The only declarations it reached that way
were the two vector wipe instances, `Hacl_Mem_wipe__t_5` (`Hacl_Vec512_t`)
and `__t_6`, called from the ChaCha20, Salsa20 and Poly1305 vector loops.
A declaration that carries its own `Prologue` is left alone, so
`Hacl.Mem.wipe` now has `[@@CPrologue ""]` (in `Hacl.Mem.fst`, so nothing
but that module is re-checked), and both compilers inline every instance.

| ChaCha20, 256 KiB, best of 10 | gcc | clang |
| --- | ---: | ---: |
| as before | 93.8 us | 93.1 us |
| wrappers without the attribute | 85.1 us | 82.7 us |
| `Hacl_Mem_wipe` a no-op | 83.8 us | 82.7 us |
| scratch arrays per iteration, wiped per iteration | 119 us | 126 us |

(The machine alternated between two clock states during these runs; the
table is the faster one.  The last row, from an earlier run in the slower
state, where the first row was 112 us, is the restructuring considered
first and rejected.)

Tables re-measured (`table.sh 3` under gcc and clang; `others.sh 3`, which
on this run needed a 6% canary cut).  Against HACL\* best, ChaCha20 went
from 1.31x to 1.19x under gcc and from 1.02x to 0.94x under clang,
ChaCha20-Poly1305 from 1.17x to 1.10x and from 1.00x to 0.92x, and Salsa20
and secretbox from 0.26x to 0.24x--0.25x under gcc and from 0.19x--0.20x to
0.18x under clang; the other rows moved within noise.  Against the other
libraries, ChaCha20 went from 1.35x to 1.21x of the fastest, ChaCha20-
Poly1305 from 1.33x to 1.23x, and Salsa20 and secretbox from 1.14x to
1.07x--1.08x.  The ChaCha20 gap that remains under gcc, 93 us against
HACL\*'s 79 us, is in the round function's code generation, not in wiping.
The Custard behaviour is worth fixing upstream: a seed's own string should
go to what that seed alone reaches.


## Part 72: a four-word copy loop and store forwarding

Under gcc every P-256 operation ran 1.6--1.9x slower than under clang
(ECDH 88 us against 50, verification 290 against 162), while secp256k1 and
Ed25519, on the same carry primitives, were level or ahead under gcc.  The
field multiply was not the reason: timed alone, P-256's `fmul` took 25 ns
under gcc and 19.6 under clang, but a point doubling, twelve multiplies and
about twenty additions, took 586 ns against 298.

The doubling copies a field element after nearly every operation, because
Pulse will not let an output alias an input, and every copy is
`Hacl.Impl.Mont4.acopy`, a four-iteration loop.  gcc's loop vectorizer turns
it into two 16-byte loads and stores.  When the source was just written by
the multiply's four 8-byte stores -- which is almost always -- the 16-byte
load cannot be forwarded from the store buffer and waits for the stores to
retire.  clang does not vectorize the loop.  Turning the vectorizer off took
the doubling from 586 ns to 430 under gcc; enabling BMI2 (for `mulx`)
changed nothing, and neither did `_addcarry_u64` in place of
`__builtin_addcll` (faster `fmul`, slower doubling), nor dropping the copy
in `fsqr`.

`acopy` is now four loads and four stores in straight-line code, as
Curve25519's `Field64.copy` and secp256k1's `Field52.fcopy` already were.
gcc's SLP vectorizer still pairs a few copies, but the doubling is 414 ns
and inversion 9.0 us instead of 13.7.  Ed25519's five-word loop copy
(`Hacl_Curve25519_Field_copy`) was tried the same way and made no
difference, so it is unchanged.

| best of 8, interleaved, same session | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| P-256 ECDH (initiator) | 88.2 us | 64.3 us | 50.9 us | 51.5 us |
| P-256 ECDH (responder) | 206 us | 149 us | 111 us | 111 us |
| P-256 ECDSA sign | 99.5 us | 75.5 us | 60.9 us | 61.5 us |
| P-256 ECDSA verify | 290 us | 216 us | 165 us | 162 us |

secp256k1 and Ed25519, whose scalar code also uses `Mont4`, moved within
1% under gcc and 4% under clang.  What is left of the gcc gap, about 1.25x,
is the multiply itself: gcc spills and re-materializes carries
(`setc`/`movzbl`/`addb $-1`) between the product's row chains and the four
reduction steps where clang keeps one `adc` chain.

Tables re-measured under gcc (`table.sh 3`; the clang table is unchanged,
since clang never vectorized the loop).  Against HACL\* best, P-256 ECDH
went from 0.64x to 0.47x, signing from 0.66x to 0.51x and verification
from 0.76x to 0.57x; every other row moved within noise.  In the table
against other libraries (`others.sh 3`, 6% canary cut, only the P-256 rows
replaced) the gcc column went from 209 us to 155 for variable-base ECDH,
104 to 77 for signing and 304 to 220 for verification; the ratios, which
take the faster of the two compilers and so are clang's, are unchanged
within noise at 2.2x--3.8x.

## Part 73: no permutation after the last squeezed block

Before starting on a four-way Keccak, a prototype in C put the portable
permutation at about 400 ns, but a one-block SHAKE128 of a 34-byte seed,
which needs one permutation, took 1070 ns.  The squeeze permuted after
every block it emitted, the last one included, and nothing ever read the
state that last permutation produced.  When the output length is a
constant shorter than the rate (SHA3-256, SHA3-512) gcc saw the loop runs
once and deleted the dead permutation; with a runtime length (SHAKE, and
so the ML-KEM PRF and ML-DSA's hashes) it could not.  The streaming XOFs
behind the rejection samplers had the same shape, and there the extra
permutation sat inside a loop whose trip count depends on the data: one
wasted permutation per matrix entry, per `RejBoundedPoly` call, per
`SampleInBall`.

`squeeze_impl` now calls `permute_if`, which permutes only if more output
remains.  `xof_block` in both `Hacl.Impl.MLKEM.XOF` and
`Hacl.Impl.MLDSA.XOF` takes the block index at run time and permutes on
the way in unless it is zero, so the caller's invariant is the state of
block `xof_prev j` rather than of block `j`.  The first attempt put the
`if` straight into `squeeze_impl`'s loop body and the query never came
back (killed after ten minutes); moving it into a helper with its own
specification verified at once.

| gcc, best of 3, interleaved, same session | before | after | |
| --- | ---: | ---: | ---: |
| SHAKE128, 64 bytes | 955 ns | 540 ns | 1.77x |
| SHAKE128, 1 KiB | 3.73 us | 3.31 us | 1.13x |
| SHA3-256, 64 bytes | 528 ns | 494 ns | 1.07x |
| ML-KEM-512 keygen / encaps / decaps | 33.6 / 39.5 / 49.5 us | 30.4 / 35.8 / 45.6 us | 1.09x--1.10x |
| ML-KEM-768 keygen / encaps / decaps | 55.4 / 64.6 / 77.8 us | 49.4 / 57.8 / 71.2 us | 1.09x--1.12x |
| ML-KEM-1024 keygen / encaps / decaps | 86.2 / 97.5 / 114 us | 77.0 / 87.6 / 104 us | 1.10x--1.12x |
| ML-DSA-44 keygen / sign / verify | 126 / 587 / 129 us | 116 / 566 / 121 us | 1.04x--1.09x |
| ML-DSA-65 keygen / sign / verify | 209 / 848 / 213 us | 192 / 819 / 199 us | 1.04x--1.09x |
| ML-DSA-87 keygen / sign / verify | 354 / 795 / 359 us | 324 / 762 / 334 us | 1.04x--1.09x |

Long SHA-3 and SHAKE inputs, where one saved permutation is lost among
hundreds, moved within noise.  The session ran about 7% slower than the
one that produced the README tables, so only the ratios above are
comparable; the tables are left as they are until the four-way Keccak
lands and everything is re-measured once.

## Part 74: a four-way Keccak for the ML-KEM matrix

The matrix `A` is `k * k` SampleNTT calls: 4, 9 or 16 SHAKE128 streams of
three or four blocks each, every block costing a scalar permutation.
`Hacl.Hash.SHA3.Core4.permute4` does four permutations at once on AVX2,
one lane of each state per 256-bit register: pack the four states into
25 vectors, 24 rounds of theta / rho-pi / chi / iota with `vpxor`,
`vpandn` and shift-or rotations (`vpshufb` for the 8- and 56-bit ones),
unpack.  Measured alone, 640 ns per call, 160 ns per state, against
480--527 ns for the scalar permutation (3.1x); a raw C prototype without
the pack, unpack and wipes ran at 122 ns per state.

`Hacl.Impl.MLKEM.Sample4.sample_ntt4_impl` runs four samplers in lock
step over it, until all four are full or sixteen blocks have gone by;
`gen_matrix_impl` calls it while four entries remain and
`Hacl_Vec256_supported ()`, so ML-KEM-512 does its whole matrix in one
batch, ML-KEM-768 in two plus one scalar entry, ML-KEM-1024 in four.

Verification notes.  The permutation's proof is a per-lane invariant for
each step, and every one of them had to be opaque, revealed only in small
`_zero` / `_step` / `_done` lemmas: with the refinement of `rotl64`
(a `rotate_left` on `nat`s) in the context, Z3 looped on facts as
simple as `m < i`.  The fix was to state each step lemma for an arbitrary
value `y` with its property behind an opaque predicate.  Putting the new
lane axioms into `Hacl.Vec256` timed out the ChaCha20 and Poly1305 vector
proofs, which never mention them; they live in `Hacl.Vec256.Lane64`.
Splitting `absorb_pre` out of `absorb_impl` slowed the unrelated
`squeeze_block` in the same module from 24 s to 460 s on one query; moving
its loop step into two small lemmas (`state_byte_lane`, `squeeze_step`)
brought the whole module back to 132 s, from 140 s before.

| gcc, best of 3, interleaved, same session, AVX2 off / on | scalar | four-way | |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 27.3 / 32.5 / 41.3 us | 25.3 / 30.3 / 39.0 us | 1.06x--1.08x |
| ML-KEM-768 keygen / encaps / decaps | 44.3 / 52.3 / 64.5 us | 40.6 / 48.3 / 60.2 us | 1.07x--1.09x |
| ML-KEM-1024 keygen / encaps / decaps | 70.1 / 78.9 / 93.9 us | 60.3 / 69.6 / 83.8 us | 1.12x--1.16x |

The "scalar" column is the same build with `Hacl_Vec256_supported` forced
to false, so only the matrix differs; SHA-3 and SHAKE rows moved within
noise.  This session ran faster than Part 73's, so compare ratios only.
The pack and unpack (25 four-lane gathers each way) and the three wipes
are a quarter of `permute4`'s time and the obvious next step, followed by
the same batching in ML-DSA's `ExpandA`, `ExpandS` and `ExpandMask`.

## Part 75: fewer reductions in the ML-KEM base multiply and CBD

Against AWS-LC's ML-KEM-768 at 13 / 14 / 17 us we were at 3.2x--3.5x, and
OpenSSL's portable C encapsulates in 33 us against our 49 (clang), so not
all of the gap is vectors.  Callgrind on ML-KEM-768 put `NTT.multiply` at
73 k instructions per keygen and 123 k per decaps, and the CBD sampler at
68 k and 80 k: as much as each NTT.

`multiply` did seven Barrett reductions per pair -- one after every product
and sum, plus one for `zeta^2 * zeta` in `gamma_i`.  It now does two:
each output, `a0 b0 + (a1 b1) gamma_i` or `a0 b1 + a1 b0`, is formed in
sixty-four bits (below `2 q^3 < 2^36`) and reduced once by
`Zq.zq_reduce`, a Barrett step with `m = 41285357 = floor(2^37 / q)`
(`m q = 2^37 - 19`), and `gamma_i` comes from a new 128-entry table
(`Tables.gamma_table`, checked against `gammas` by normalization).  The
CBD sampler located each of its `2 eta` bits per coefficient with a
division and a variable shift; it now takes `eta` bytes at a time, which is
exactly four coefficients for every `eta`, and every shift in the group is
a constant after monomorphization.

Verification notes.  The first `base_mul` took 426 s and `multiply` 285 s,
the whole NTT module 28 minutes: the loop invariant's
`forall k. k < 2 i ==> v[k] == multiply_ntts (as_poly va) (as_poly vb)
[k]` sat in every query, and with it Z3 timed out on `2 (i + 1) == 2 i + 2`.
Behind an opaque `mul_prefix`, with the arithmetic in pure `bm0` / `bm1`
and the update in two small lemmas, `base_mul` is 13 s and `multiply`
36 s.  Adding the lemmas perturbed the untouched `part_step`, which now
does its case split explicitly.

| gcc, best / median of 6, interleaved, same session | before | after | median |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 25.4 / 30.1 / 39.3 us | 21.8 / 25.2 / 32.7 us | 1.17x--1.20x |
| ML-KEM-768 keygen / encaps / decaps | 40.6 / 48.4 / 59.3 us | 33.5 / 39.5 / 49.9 us | 1.21x--1.22x |
| ML-KEM-1024 keygen / encaps / decaps | 59.9 / 70.7 / 85.9 us | 49.6 / 56.8 / 70.5 us | 1.23x--1.28x |

Callgrind per ML-KEM-768 operation after: `multiply` 48 k (keygen) and
80 k (decaps), CBD 9 k and 11 k.  What is left at the top is the NTT and
inverse NTT (62 k and 75 k, a Shoup multiply and a conditional subtract per
butterfly), SHAKE256 for the PRF (129 k per decaps, one stream at a time),
and the matrix (85 k plus 43 k in `permute4`).  The first wants AVX2
butterflies over sixteen coefficients, the second the four-way Keccak.

## Part 76: AVX2 clones of the ML-KEM arithmetic, and a four-way PRF

Part 75 left the transforms and SHAKE256 at the top of the profile.  gcc
already vectorized the NTT layers with `len >= 8`, but with SSE2, eight
coefficients per instruction; compiling the whole of `Hacl.c` with
`-mavx2` took ML-KEM-768 from 30.4 / 36.4 / 48.0 to 27.3 / 31.6 / 40.1 us
in the quick harness, which was the cheapest win on the table: no new
proof, just the right instruction set.

So `ntt_inplace`, `intt_inplace`, `multiply` and `cbd_impl` are now each
extracted twice from one `inline_for_extraction` body -- `X_avx2` under
`CPrologue "__attribute__((target(\"avx2\")))"` and `X_` without -- and `X`
is a dispatcher with the body's specification that branches on
`Hacl.Vec256.supported ()`.  The functions that only ever run under AVX2
(`gen_entries4`, `sample_ntt4_impl`, `shake128_absorb_pre`) carry the
attribute directly.  None of them uses `custard_c_closure_prologue`:
Custard refuses a closure that reaches a global also reached from host code
(`Hacl_Secret_UInt64_zero`, then `rc_arr`), and the closure is not needed,
because gcc and clang inline a default-target static callee into an AVX2
caller.

The PRF is `SHAKE256(s || b, 64 eta)`: one 33-byte absorb and one squeezed
block for `eta = 2`, two for `eta = 3`, and a noise vector is `k` of them
with one seed.  `Hacl.Impl.MLKEM.PRF4.prf4_impl` runs four: four
`prf_absorb_pre` (the absorb without its last permutation), one `permute4`,
`squeeze_block` on each lane, and `Sample4.permute4_if (64 eta > 136)` for
the second block.  Its whole proof is `prf_lane`, two applications of
`Spec.SHA3.squeeze_range_eq`.  `Gen.noise_vec_impl` dispatches to
`noise_vec4_impl`, which calls `prf4_impl` once and then `noise_entry` four
times, each extending the verified prefix of the vector by one entry when
`i < k` and doing nothing otherwise; the lanes past `k` compute a PRF
nobody reads.  `prf_absorb_pre` takes the message length as an argument
although it is always 33: as a constant, the inlined whole-block loop of
the absorb extracts to `while (i < 0)`, which `-Wtype-limits` rejects.

Callgrind, ML-KEM-768 encapsulation (instructions, 200 calls):

| | before | after |
| --- | ---: | ---: |
| total | 107.8 M | 77.6 M |
| `multiply` | 12.8 M | 6.1 M |
| `intt_inplace` | 12.0 M | 4.0 M |
| `ntt_inplace` | 6.2 M | 2.6 M |
| CBD | 2.2 M | 0.8 M |
| scalar `shake256` | 12.9 M | 1.8 M |
| `prf4_impl` + `prf_absorb_pre` | -- | 2.2 M |
| `permute4` | 8.6 M | 11.5 M |
| `gen_entries4` | 17.0 M | 12.2 M |

| gcc, best / median of 20, interleaved, same session | before | after | median |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 21.7 / 24.8 / 33.0 us | 18.3 / 21.3 / 27.9 us | 1.16x--1.18x |
| ML-KEM-768 keygen / encaps / decaps | 33.2 / 39.6 / 50.1 us | 29.4 / 33.7 / 43.3 us | 1.12x--1.17x |
| ML-KEM-1024 keygen / encaps / decaps | 49.1 / 56.5 / 69.6 us | 42.8 / 48.1 / 59.3 us | 1.13x--1.18x |

What is left at the top of encapsulation is `sha3_256` of the
encapsulation key (12.7 M, one scalar stream over 1184 bytes, which the
standard requires), `kpke_encrypt`'s own compress and encode (14.6 M), the
matrix (`gen_entries4` and `permute4`, 24 M, of which the rejection
sampling is now the larger part), and the ninth matrix entry for `k = 3`,
still sampled by the scalar `sample_ntt_impl` (6.1 M).

## Part 77: a sixteen-bit conditional subtraction

A cycle profile of ML-KEM-768 encapsulation after Part 76 (TSC, best of
2000, AVX2 host) put the three transforms of a vector at 5.3 k cycles each,
more than the 1184-byte `sha3_256` of the encapsulation key.  Timing single
layers of the forward NTT in isolation showed why.  Every coefficient goes
through `Zq.csub`, and `csub` took its mask from
`Hacl.Secret.UInt16.gte_mask`, which computes the borrow of a
*thirty-two-bit* difference.  gcc dutifully widened every lane of the
butterfly to thirty-two bits, and the `len = 128` layer cost 245 cycles
where a pure sixteen-bit conditional subtraction costs about 49 (that is,
the call overhead).  The `len = 4` and `len = 2` layers went from 465 and
416 to 220 and 196.

`csub` now computes `s = x - q` in sixteen bits and takes the mask from the
top bit of `s`, which is set exactly when the subtraction wrapped, because
`x < 2q` puts a wrapped `s` at or above `2^16 - q > 2^15`.  The first
attempt fed that mask to `S16.select`, and the transforms got three to four
times *slower*: gcc's loop vectorizer gives up on the and-or blend `select`
compiles to (`couldn't vectorize loop`), and nothing was vectorized at all.
The second form, `s + (m & q)`, vectorizes under both gcc and clang.  The
proof is a dozen lines of `small_mod` and `logand_lemma_{1,2}`.  `csub` is
also now `opaque_to_smt`, since otherwise its body leaks into the contexts
of its callers and `Sample.cbd_coef` timed out.

TSC cycles, ML-KEM-768, best of 2000:

| | before | after |
| --- | ---: | ---: |
| `vec_ntt` (3 polynomials) | 5267 | 1421 |
| `vec_intt` (3 polynomials) | 5267 | 1837 |
| `mat_vec_mul` | 10314 | 8330 |
| `dot` | 3430 | 2327 |
| `add` of two vectors | 416 | 171 |
| encapsulation | 92 k | 80 k |

| gcc, best / median of 20, interleaved, same session | before | after | median |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 18.3 / 21.3 / 27.5 us | 16.0 / 17.9 / 23.0 us | 1.18x--1.23x |
| ML-KEM-768 keygen / encaps / decaps | 29.3 / 34.0 / 43.3 us | 25.6 / 29.2 / 36.7 us | 1.18x--1.21x |
| ML-KEM-1024 keygen / encaps / decaps | 42.9 / 48.2 / 59.7 us | 37.4 / 41.9 / 50.2 us | 1.11x--1.21x |

The transforms are now small.  The top of encapsulation is the matrix
(`gen_matrix`, 31 k cycles, of which the four-way rejection sampler's
byte-by-byte squeeze and branchy loop are about half), `mat_vec_mul`
(the base-case products, still reduced with a sixty-four-bit Barrett step),
`sha3_256` of the key (9.4 k), and the encoders: `decode12` (4.4 k) and
`encode10` (3.2 k) are generic bit accumulators that take the bit width at
run time.

## Part 78: branch-free rejection sampling, lane-wise squeeze, and an inlined ML-DSA XOF

After Part 77 the largest item in encapsulation was the matrix, and within
it the rejection sampler.  Timed on its own with a different seed on every
iteration, so that the branch predictor cannot learn one input's pattern
of accepts and rejects, `sample_ntt4` (four matrix entries) cost 16.3 k
cycles under gcc and 13.7 k under clang.  Two things were slow: the
acceptance test was a data-dependent branch that mispredicts about one
candidate in five, and the squeeze copied the state into the block buffer
one byte at a time, with a division and a remainder per byte.

`Sample.push_impl` now always stores `csub d` at `dst[c]` and advances `c`
by `(d - q) >> 31` (as an unsigned 32-bit value), which is 1 exactly when
`d < q` (lemma `accept_bit`).  A rejected value is overwritten by the next
candidate, and the postcondition, which only talks about the prefix below
`c`, is unchanged.  The obvious spelling,
`if d < q then 1 else 0`, does not survive gcc: it jump-threads the test
into the following `c < 256` check and turns it back into a branch.

The samplers' streams now squeeze with `Sponge.squeeze_block_lanes`, which
reads each lane once and writes it as eight bytes with constant shifts
(which compilers merge into one store), then any bytes of a last partial
lane.  Together the two changes bring `sample_ntt4` to 10.7--10.9 k cycles
under both compilers.  The one-shot sponges keep the old byte loop: with
the lane loop inlined into `sha3_256` the code is fine, but gcc's register
allocation of the whole function shifts, and the absorb round loop, which
does not change, gains fifteen register moves per round, making SHA3-256
six percent slower (103.6 k to 109.6 k cycles on 16 KiB).  Putting the byte
loop back into that one function restored 103.6 k.

The full benchmark then showed ML-DSA keygen and verify about nine percent
*slower*, although nothing in them changed except the squeeze.  The
reason: the larger squeeze pushed ML-DSA's `xof_block` (one permutation
and one squeeze) over gcc's inlining threshold, and gcc left a single
out-of-line copy shared by all the samplers, with the rate as a run-time
argument.  `xof_block` is now `inline_for_extraction`, and ML-DSA-65
keygen goes from 422 k cycles (before) and 461 k (out of line) to 389 k.

With 64 different keys per run, ML-KEM-768 is 22.3 / 25.9 / 32.1 us
(best of 3) against 27.8 / 30.5 / 38.2 before.  `bench.c` uses one fixed
seed per operation, which lets the branch predictor learn the old
sampler's branches, so it shows a smaller gain:

| gcc, best / median of 20, interleaved, same session | before | after | median |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 16.0 / 18.5 / 24.3 us | 15.4 / 17.7 / 23.3 us | 1.03x--1.05x |
| ML-KEM-768 keygen / encaps / decaps | 28.4 / 30.0 / 37.2 us | 25.9 / 27.6 / 36.3 us | 1.05x--1.06x |
| ML-KEM-1024 keygen / encaps / decaps | 38.4 / 44.9 / 52.9 us | 36.3 / 42.0 / 50.5 us | 1.05x--1.06x |
| ML-DSA-44 keygen / sign / verify | 104.9 / 534.6 / 112.3 us | 98.3 / 513.6 / 103.5 us | 1.02x--1.09x |
| ML-DSA-65 keygen / sign / verify | 179.4 / 746.5 / 190.7 us | 168.0 / 727.8 / 172.5 us | 1.02x--1.10x |
| ML-DSA-87 keygen / sign / verify | 302.0 / 759.9 / 304.7 us | 284.2 / 673.6 / 277.7 us | 1.04x--1.10x |

SHA-3 and SHAKE are unchanged (all within 0.1% at the median).  One
side effect lands in code this change does not touch: `Hacl.c` is a single
translation unit, and gcc now clones the SHA-512 block function
differently, which makes bulk SHA2-512 3.6% faster and HMAC-SHA2-512 3.5%
slower (108.6 k to 112.3 k cycles on 16 KiB, reproduced in isolation).

## Part 79: an accumulating dot product for ML-KEM

The matrix-vector products `A s`, `A^T r` and `t^T r` each summed `k`
base-case products, and each product reduced every output coefficient
with a sixty-four-bit Barrett step before the addition reduced it again.
Timed on its own (k = 3, best of 20000), the old dot product cost 2744
cycles under gcc and 1690 under clang.

`Hacl.Impl.MLKEM.Dot` now does what the arithmetic allows: for each pair
of coefficients it sums the `k` values of `a0 b0`, `a1 b1` and
`a0 b1 + a1 b0` exactly in thirty-two bits (at most `8 (q - 1)^2`, below
`2^32` for `k <= 4`), reduces the `a1 b1` sum before it is multiplied by
`gamma_i`, and reduces each output once with a thirty-two-bit Barrett
step (`Zq.zq_reduce32`).  The loop has no carried state between pairs and
vectorises; an AVX2 clone is chosen at run time like the NTT's.  The
kernel costs 784 cycles under gcc and 465 under clang, 3.5x and 3.6x
faster.  The proof (`VecLemmas.dot_pair`) is an induction over `k` relating
the three exact sums to the specification's sum of reduced products.

The module sits behind an interface, `Dot.fsti`, for the same reason
`Poly.fsti` does: its implementation refers to the zeta tables, and with
those facts in scope, unrelated queries in `Vec`, `KPKE` and `KEM` timed
out.

| gcc, best of 20, interleaved, same session | before | after | median |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 16.7 / 19.0 / 24.5 us | 15.8 / 17.8 / 22.8 us | 1.05x--1.07x |
| ML-KEM-768 keygen / encaps / decaps | 26.9 / 30.8 / 38.4 us | 24.5 / 27.7 / 34.4 us | 1.10x--1.11x |
| ML-KEM-1024 keygen / encaps / decaps | 38.8 / 43.7 / 53.3 us | 34.6 / 38.7 / 47.1 us | 1.12x--1.13x |

The gain grows with `k`, as it should.  ML-DSA is unchanged (within 0.3%),
and the other 98 rows have a geometric mean ratio of 1.0005, none
outside 0.98--1.03.  (This session's machine is about five percent slower
than Part 78's; compare the columns with each other, not with Part 78.)

## Part 80: ML-KEM's coders in groups of eight

`ByteEncode_d` and `ByteDecode_d` ran one sixty-four-bit shift register
across all 256 coefficients, with `d` a run-time argument.  The register
carries from each coefficient to the next, so nothing unrolls; a decode
of twelve-bit coefficients cost 1372 cycles under gcc.  Eight
coefficients of `d` bits fill exactly `d` bytes, so the register is empty
at every multiple of eight.  Each coder is now 32 groups (`enc_group`,
`dec_group`), each starting from an empty register at byte `d g`, and `d`
is monomorphized through `Codec`.  The grouping matters more than the
constant: in a C prototype, a constant `d` alone took gcc's twelve-bit
decode from 980 to 1396 cycles (slower), and grouping took it to 514.

| cycles, best of 20000 (gcc / clang) | before | after |
| --- | ---: | ---: |
| decode d = 12 / 10 / 4 / 1 | 1372 / 710 / 539 / 465, 833 / 931 / 735 / 661 | 318 / 367 / 147 / 171, 343 / 245 / 73 / 73 |
| encode d = 12 / 10 / 4 / 1 | 1102 / 1053 / 637 / 514, 1249 / 1151 / 759 / 514 | 392 / 367 / 147 / 171, 269 / 269 / 98 / 73 |

The proof reuses the old loop body and invariant unchanged inside each
group.  The group is a separate `inline_for_extraction` function whose
precondition relates `i0` and `o0` linearly (`d i0 == 8 o0`): with the
group index's products `8 g` and `g d` in scope, the encoder's shift
side condition timed out.  The group's postcondition also needed three
stepping-stone assertions, and with them the check took 12 s instead of
timing out after three minutes.

| gcc, best of 20, interleaved, same session | before | after | median |
| --- | ---: | ---: | ---: |
| ML-KEM-512 keygen / encaps / decaps | 14.3 / 16.2 / 20.9 us | 13.1 / 14.7 / 17.5 us | 1.08x--1.19x |
| ML-KEM-768 keygen / encaps / decaps | 22.4 / 25.2 / 31.4 us | 20.7 / 22.9 / 26.7 us | 1.10x--1.22x |
| ML-KEM-1024 keygen / encaps / decaps | 31.1 / 35.3 / 43.1 us | 29.5 / 31.7 / 36.2 us | 1.10x--1.23x |

Decapsulation gains the most because it decodes and re-encodes the
ciphertext as well as encoding it.  The other 107 rows have a geometric
mean ratio of 1.0002, all within 0.96--1.05; the machine switched
between two speeds during this run (ML-DSA-44 keygen at 97 and 106 us on
both sides), so single rows are noisy, while the best-of figures for
ML-DSA agree to 1%.  ML-KEM-768 is now 20.7 / 22.9 / 26.7 us against
AWS-LC's 13 / 14 / 17.

## Part 81: Keccak in one pass per round

Both Keccak-f[1600] implementations, the scalar `Core` and the four-way
AVX2 `Core4`, did each round as three sweeps of the state: theta in
place, rho-pi into a scratch buffer, chi back.  A round is now one pass,
as in the Keccak team's reference code: read the 25 input lanes once,
compute theta's column values in registers, and for each output row form
the five rho-pi lanes as `rotl(a[src] ^ d[col], rho)` and write chi of
them, with iota on lane 0, to the other buffer.  The existing scratch
buffer becomes the other half of a ping-pong, two rounds per loop trip,
so `Core.fsti` did not change.

In C prototypes, the fused scalar round made SHA3-256 1.16x faster on
1184 bytes under gcc and 1.07x under clang.  The four-way permutation
went from 1617 to 1176 cycles under gcc and from 1543 to 1151 under
clang.  The extracted scalar round matches the prototype under clang.
Under gcc, SHA3-256 stays about 8% behind the prototype at every
placement of the loads.  The difference is the one-shot sponge's
byte-at-a-time absorb, not the round.

Proof: each rho-pi register value has a postcondition naming its entry
of `rho_pi (theta a)`, and each store extends a prefix invariant against
`round n a`.  The first attempt left the solver to evaluate
`rho_pi_src 7`, `rotc (rho_pi_src 7)` and the chi neighbours' `% 5` and
`/ 5` on literals inside the 50-call body; one query ran for fifteen
minutes without finishing.  With `Spec.SHA3.rho_pi_src_lit` and
`chi_nbr_lit` supplying those as ground facts, proved by normalisation
like `rotc_lit`, `Core` checks in 40 s at a peak rlimit of 8.  `Core4`
uses opaque `b_ok` and `fr_pre` predicates with small step lemmas.
Lane 0, where iota is folded in, needed its per-state lemma split from
the prefix lemma; together they had polluted the context enough that
`m < 1 ==> m == 0` failed.

| gcc, 20 interleaved runs, same session | before | after | min ratio |
| --- | ---: | ---: | ---: |
| SHA3-256 64 B / 16 KiB / 256 KiB | 493 ns / 51.1 / 814 us | 477 ns / 47.3 / 751 us | 1.03x / 1.08x / 1.08x |
| SHA3-512 64 B / 16 KiB / 256 KiB | 503 ns / 97.7 / 1559 us | 454 ns / 86.4 / 1379 us | 1.11x / 1.13x / 1.13x |
| SHAKE128 64 B / 16 KiB / 256 KiB | 548 ns / 43.3 / 686 us | 501 ns / 38.2 / 606 us | 1.09x / 1.13x / 1.13x |
| ML-KEM-512 keygen / encaps / decaps | 14.6 / 16.2 / 19.4 us | 13.9 / 15.5 / 18.7 us | 1.05x / 1.05x / 1.04x |
| ML-KEM-768 keygen / encaps / decaps | 22.7 / 25.3 / 29.3 us | 21.8 / 24.3 / 28.3 us | 1.05x / 1.04x / 1.04x |
| ML-KEM-1024 keygen / encaps / decaps | 32.4 / 35.1 / 39.8 us | 31.2 / 33.7 / 38.5 us | 1.04x / 1.04x / 1.03x |
| ML-DSA-44 keygen / sign / verify | 107 / 556 / 112 us | 99 / 543 / 106 us | 1.08x / 1.02x / 1.06x |
| ML-DSA-65 keygen / sign / verify | 175 / 800 / 184 us | 162 / 782 / 173 us | 1.08x / 1.02x / 1.06x |
| ML-DSA-87 keygen / sign / verify | 295 / 732 / 305 us | 271 / 706 / 285 us | 1.09x / 1.04x / 1.07x |

The ML-KEM rows were recorded while the machine was in its slower
state, so they are higher than in Part 80; the ratios come from the
same session.  The other 84 rows have a geometric-mean median ratio of
1.0005, all within 0.96--1.04.  Why SHA3-256 gains less than SHA3-512
and SHAKE128 under gcc has not been investigated.


## Part 82: ML-DSA's ExpandA four streams at a time

A callgrind profile of ML-DSA-65 (gcc, no inlining) put `ExpandA` at
51% of key generation, 53% of verification and 13% of signing.  Signing
is dominated by the transforms instead: INTT 31%, NTT 14%, pointwise
products 16%.  ML-DSA used no AVX2 at all.

`ExpandA` is `k * l` independent SHAKE128 rejection samplers, exactly
the shape of ML-KEM's matrix (Part 74 onwards).  The new
`Hacl.Impl.MLDSA.Sample4` copies ML-KEM's `Sample4`.  It runs four
`RejNTTPoly` streams in lock step, ending their absorbs with one
`permute4` and permuting all four before every block after the first.
Each stream reads its block with `squeeze_block_lanes` and feeds it to
the scalar `block128_impl`.  A stream that filled early keeps receiving
blocks and ignores them (`ntt_sampled_stable`).  The per-stream
invariant is one opaque `stream_ok`, as in ML-KEM.  `expand_a_impl`
moved there from `Sample` because it now depends on the four-way
sampler.  It takes four entries at a time while four remain and
`Vec256.supported ()`, then samples into four stack polynomials and
copies them into place.  The 16, 30 and 56 entries of the three
parameter sets leave only ML-DSA-65's last two to the scalar path,
which the tests therefore exercise on an AVX2 machine.  The module
checks in a minute.

| gcc, 12 interleaved runs, same session | before | after | min ratio |
| --- | ---: | ---: | ---: |
| ML-DSA-44 keygen / sign / verify | 89.0 / 484 / 95.4 us | 69.9 / 466 / 77.0 us | 1.27x / 1.04x / 1.24x |
| ML-DSA-65 keygen / sign / verify | 143 / 705 / 156 us | 112 / 673 / 123 us | 1.28x / 1.05x / 1.27x |
| ML-DSA-87 keygen / sign / verify | 243 / 639 / 255 us | 180 / 576 / 191 us | 1.35x / 1.11x / 1.34x |

The other 107 rows, ML-KEM included, have a geometric-mean ratio of
0.997, all within 0.96--1.03.

**Not shipped: a lane-wise absorb.**  The one-shot sponge's absorb
builds each lane with an eight-iteration byte loop.  Replacing it with
`Hacl.Impl.Bytes.load_le` (with a `lane_of_le` lemma) made SHA3-256 on
1184 bytes 4--9% faster in a TSC harness under both compilers.  In the
full suite (5 rounds, 20 runs a side), gcc gained 1--5% on SHA3-256 but
lost 2% on SHA3-512, 4% on long SHAKE128 inputs and 1--2% on ML-KEM.
That is the register-allocation effect that kept the byte loop in the
one-shot squeeze (README, "The sponge"), so the change was reverted.
One fragile query it exposed downstream is fixed anyway:
`verify_mu_impl` now asserts `ct_len p <= sig_len p` before slicing
the signature, which was at 88% of its rlimit.

## Part 83: ML-DSA's transforms and products on AVX2

After Part 82, signing was still mostly the inverse NTT, the NTT and the
pointwise products (31%, 14% and 16% of ML-DSA-65's profile), all
scalar.  The new `Hacl.Impl.MLDSA.NTT.Vec256` does each eight
coefficients at a time, proved against the same `Spec.MLDSA.NTT` as the
scalar `Hacl.Impl.MLDSA.NTT`, and `Hacl.Impl.MLDSA.Poly` picks it on
`Vec256.supported ()`.

- **Lanes.**  Coefficients stay canonical in `[0, q)`.  A reduction is
  `min_u32(x, x - q)` (`VPMINUD`), the Shoup product is `VPMULLD` and a
  high-half product, and the pointwise Montgomery product ends with a
  Shoup multiplication by `2^32 mod q`.  The trusted additions
  (`load_at`/`store_at` at a word offset, `sub32`, `mullo32`, `mulhi32`,
  `minu32`, `perm32`) are in `lib/Hacl.Vec256.Lane32.fst`, and
  `tests/test_vec256.c` checks each against scalar C.
- **Layers of half-width 128 to 8** load the two ends of eight
  butterflies as two vectors and broadcast the block's root.
- **Layers of half-width 4, 2 and 1** work on groups of sixteen
  coefficients.  Before each layer the group's two vectors are shuffled
  (`VPERM2I128`, `VPUNPCK{L,H}QDQ`, two rounds of `VPUNPCK{L,H}DQ`) so
  that lane `j` holds the ends of one butterfly, and back afterwards; the
  roots are one load of eight consecutive table entries and a `VPERMD`.
  The proof states each layer about the whole polynomial (`grp`), so the
  three compose without a locality lemma.
- **Proof engineering.**  Lane quantifiers plus the products in block
  starts and root indices timed out even linear goals, so `blk`, `root`
  and `root_inv` are opaque, each butterfly vector and each small layer is
  a pure function proved in its own context, and loads and stores are
  wrapped in small `fn`s whose postconditions are a single predicate.
  The root-index lemmas are split into a generic `perm32` lemma, an
  arithmetic one, and their combination.  The module checks in about 12
  minutes.

| gcc, 12 interleaved runs, same session | before | after | min ratio |
| --- | ---: | ---: | ---: |
| ML-DSA-44 keygen / sign / verify | 73.2 / 481 / 79.2 us | 53.1 / 245 / 52.8 us | 1.38x / 1.96x / 1.50x |
| ML-DSA-65 keygen / sign / verify | 120 / 694 / 125 us | 89.9 / 340 / 82.5 us | 1.33x / 2.04x / 1.52x |
| ML-DSA-87 keygen / sign / verify | 179 / 590 / 196 us | 139 / 308 / 129 us | 1.29x / 1.91x / 1.53x |

"Before" is the same extracted C with the three dispatches turned off.
The other 107 rows have a geometric-mean ratio of 1.007 (0.93--1.10,
noise; none of them calls the new code).  The inverse NTT still scales
by `256^-1` in a separate pass, and ExpandMask and ExpandS are still one
stream at a time.

## Part 84: ExpandMask, four streams at a time

A callgrind profile of ML-DSA-65 after Part 83 put `ExpandMask` at 37.5%
of signing: each attempt draws `l` mask polynomials, each one
`SHAKE256(rho'' || u16(kappa + r))` of 576 or 640 bytes, so five Keccak
permutations, one stream at a time.  The new `Hacl.Impl.MLDSA.Mask4`
runs four of them over `Hacl.Hash.SHA3.Core4.permute4`.

- **Squeeze.**  `shake4` absorbs the four seeds (`seed_absorb_pre` is
  the absorb without its last permutation, so that `permute4` does the
  four), then squeezes four full blocks and a partial fifth, with one
  `permute4` between blocks.  Each lane's progress is an opaque
  `lane_ok msg blen m q st w`: `m` bytes of `SHAKE256(msg, blen)` are in
  `w`, and `st` is the absorbed state after `q` permutations.  The step
  lemmas are `lane_sq` (a squeezed block, through
  `Spec.SHA3.squeeze_range_eq`), `lane_adv` (a permutation) and
  `lane_done`.
- **Windows.**  `expand_mask_impl` takes four polynomials at a time while
  at least two are left and the processor has AVX2.  A window of fewer
  than four slides back to end at `l` and recomputes, and rewrites with
  the same values, polynomials already done (`prefix_mono`):
  ML-DSA-44 is one window, ML-DSA-65 one window and one scalar
  polynomial, ML-DSA-87 two windows, the second recomputing one.
- **Proof engineering.**  The `ExpandMask` lemmas moved from
  `Hacl.Impl.MLDSA.Pack` (whose interface hid them) to the new module.
  Twice a lemma called as a function's last statement did not discharge
  that function's postcondition until an `assert` restated it.  As in
  `Hacl.Impl.MLKEM.PRF4`, the message length is passed to
  `seed_absorb_pre` rather than inlined, or gcc's `-Wtype-limits` rejects
  the empty whole-block loop.

| gcc, 12 interleaved runs, same session | before | after | min ratio |
| --- | ---: | ---: | ---: |
| ML-DSA-44 sign | 248 us | 214 us | 1.16x |
| ML-DSA-65 sign | 361 us | 323 us | 1.12x |
| ML-DSA-87 sign | 317 us | 290 us | 1.10x |

"Before" is the same extracted C with the dispatch turned off.  Key
generation and verification do not call the new code (0.94--1.02,
noise), and the other 107 rows have a geometric-mean ratio of 0.995.
The test suite also passes with `Hacl_Vec256_supported` forced false,
which exercises the scalar path.


## Part 85: ExpandS, four streams at a time and without the acceptance branch

ML-DSA key generation spent about a quarter of its time in `ExpandS`:
`l + k` polynomials, each `RejBoundedPoly(rho' || u16(r))`, two or three
SHAKE256 blocks, one stream at a time.

- **Four streams.**  `Hacl.Impl.MLDSA.Bounded4` is `Mask4` for
  `RejBoundedPoly`: `seed_absorb_pre` absorbs the four 66-byte seeds,
  `permute4_if` shares every permutation, and each lane feeds the scalar
  `block256_bounded_impl` until all four have 256 coefficients or eight
  blocks have gone by (`bstream_ok`, opaque, tracks a lane: bytes
  squeezed, permutations so far, the partial polynomial).  Its
  `expand_s_part_impl` uses the same sliding windows as `ExpandMask`.
- **That alone did almost nothing.**  Timed in isolation `ExpandS` went
  from 14.5 to 13.1 us (ML-DSA-44) and not at all for ML-DSA-65, whose
  35 us is about three times what its 22 blocks of Keccak and 11 x 256
  coefficients ought to cost.  The instruction count fitted the expected
  time, so the cycles were stalls: the acceptance test, `if (c < 256 &&
  ok)`, is a branch on a random nibble, rejected with probability 1/16
  for `eta = 2` and 7/16 for `eta = 4` -- the worst case for a predictor.
- **Branch-free acceptance.**  `push_bit_impl` stores every nibble's
  coefficient at `dst[c]` while `c < 256` and adds `inc`, the top bit of
  the (declassified) `lt_mask`, to the count; a rejected value lies past
  the count, where `push_post` already said nothing, and is overwritten by
  the next store.  The uniform sampler, which rejects one candidate in a
  thousand, keeps the branch.  This is ML-KEM's Part 78 fix.  Stating the
  shift's value inline in `half_impl` slowed `Hacl.Impl.MLDSA.Sample` from
  5.4 to 7 minutes; as a separate `mask_bit` lemma it costs nothing.  The
  first placement of `push_bit_impl`, before the uniform sampler, also
  timed out an unrelated loop-exit assertion there.

`bench.c` calls `keypair` on the same `xi` every time, so the predictor
learns the acceptance pattern and the branch costs nothing there: the
interleaved A/B (3 rounds, 12 runs) shows key generation at 1.01--1.06x,
everything else at a geometric mean of 0.996.  With a fresh seed per call,
as in real use (best of 30 x 100 calls, `xi[0]` or `rho'[0]` varied):

| gcc, fresh seeds | ExpandS before | after | ratio | keygen before | after | ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ML-DSA-44 | 12.2 us | 10.4 us | 1.16x | 48.6 us | 46.4 us | 1.05x |
| ML-DSA-65 | 29.7 us | 14.0 us | 2.13x | 95.6 us | 80.2 us | 1.19x |
| ML-DSA-87 | 24.7 us | 17.5 us | 1.41x | 129.0 us | 123.4 us | 1.05x |

"Before" is the previous commit's sampler (four-way dispatch off, branchy
acceptance).  The test suite also passes with `Hacl_Vec256_supported`
forced false.

## Part 86: Rejection samplers timed over many inputs

Part 85 found that `bench.c` timed ML-DSA key generation on one seed, so
the branch predictor learnt `ExpandS`'s acceptance pattern and the table
showed none of the cost that a real caller, with a new seed every time,
pays.  The same is true of every rejection sampler measured on a fixed
input: ML-KEM's matrix sampler (`rho`), ML-DSA's `ExpandA`, `ExpandS`,
`ExpandMask` and `SampleInBall`, and the number of signing attempts.  Both
harnesses now cycle through 64 inputs, keeping the minimum-over-runs
reduction.  `TIME_MIN` starts each batch at 64 calls and only doubles it,
so every timed batch calls each input equally often:

- `bench.c`: ML-KEM key generation over 64 `(d, z)` seeds, encapsulation
  over 64 messages `m`, decapsulation over the 64 resulting ciphertexts;
  ML-DSA key generation over 64 `xi`, signing over 64 messages, and
  verification over the 64 resulting signatures.  Each output goes to its
  own buffer, so the next call's inputs do not depend on the last.
- `others/others.c`: every library's ML-DSA key generation over 64 seeds
  (the first public key still checked against hacl-pulse's), and ML-KEM-768
  decapsulation over 64 ciphertexts made by hacl-pulse, each checked
  first.  OpenSSL and AWS-LC already drew fresh randomness for ML-KEM key
  generation and encapsulation; hacl-pulse's shim now derives a fresh seed
  per call from a counter (`ops_pulse.h`), so all three do the same work.

The README tables were regenerated from these runs (gcc 15.2 and clang
21.1, three rounds each, `table.sh`; `others.sh 3`, read at a 6% canary
tolerance because the machine's canary wandered by 8%: at 2% 55 of 72
runs were dropped and the pq-crystals reference had none left).  The
machine was about 8% slower on both sides than for the previous table, so
the HACL\* ratios moved by a few hundredths and the absolute numbers rose.
The other-library tables are the first since the four-way Keccak and the
AVX2 transforms: ML-DSA is now 1.8x--2.1x behind the fastest
implementation (mldsa-native or pq-crystals' AVX2), from 5.0x--5.7x, and
ML-KEM-768 1.4x--1.5x behind AWS-LC, from 3.2x--3.5x.

`mkkem.py` now also prints the ML-DSA absolute table from `bench.c`'s rows.

## Part 87: SHA-1 on the SHA extensions, SHA-512's schedule on AVX2

The other-library table had two rows that were instruction-set gaps rather
than scheduling ones: SHA-1 at 6.2x of AWS-LC, which uses `SHA1RNDS4`, and
SHA-512 at 1.9x--2.0x of Firedancer and OpenSSL, which compute the message
schedule with AVX2.

**SHA-1** (`7877dcd`).  `Spec.SHA1NI` relates `SHA1RNDS4`, `SHA1NEXTE`,
`SHA1MSG1` and `SHA1MSG2` to `Spec.SHA1`, and `Hacl.Hash.SHA1.NI` is one
block on them, dispatched from `Hacl.Hash.SHA1.Core.update_block_impl` when
the CPU has the SHA extensions.

**SHA-384/512.**  A C prototype tried several shapes; the fastest keeps
the sixteen-word window in four YMM registers, computes the next four words
with AVX2 while four scalar rounds run, and holds the state in locals
(about 1850 us/MB under gcc, against about 2400 us/MB before and 1450 us/MB
for OpenSSL).  `Hacl.Hash.SHA2.AVX2` is that shape, verified;
`sha384`/`sha512`, `hmac_sha384`/`hmac_sha512` and `expand_sha384`/
`expand_sha512` dispatch to it on `Hacl_Vec256_supported()`.

Before and after (`ab.sh`, gcc 15.2, two rounds, minimum per row; the
"before" for SHA-1 is the commit before `7877dcd`, and for SHA-512 the
commit after it):

| bench | size | before | after | speedup |
| --- | ---: | ---: | ---: | ---: |
| sha1 | 64 B | 850 ns | 135 ns | 6.3x |
| sha1 | 256 KiB | 1.62 ms | 165 us | 9.8x |
| sha2-512 | 1 KiB | 2951 ns | 2313 ns | 1.28x |
| sha2-512 | 256 KiB | 630 us | 472 us | 1.33x |
| hmac-sha2-512 | 64 B | 1596 ns | 1344 ns | 1.19x |
| hmac-sha2-512 | 256 KiB | 658 us | 481 us | 1.37x |

One-block SHA-512 (64 B) is unchanged, at 440--447 ns, and no other row
moved by more than 2%.  Under clang (a direct timing loop, best of 15),
SHA-512 and HMAC-SHA-512 over 256 KiB went from 771 us and 777 us to 432 us
and 430 us, and SHA-1 is 169 us.

The README's other-library table now has SHA-1 at 1.13x of AWS-LC and
SHA-512 / HMAC-SHA-512 at 1.34x--1.35x of Firedancer; those rows are this
part's numbers, and the other columns are Part 86's.  In the HACL\* table
the three rows are Part 86's hacl-pulse numbers scaled by the speedups
above (SHA-1 0.11x, SHA-512 and HMAC-SHA-512 0.39x).  The test suite passes
under gcc and clang, and with the six new `Hacl_Vec256_supported()` dispatch
sites forced false.

A `target("avx2,bmi2")` attribute helped gcc's prototype further (about
1710 us/MB), using `rorx` for the rotations; it is not used here because
`Hacl_Vec256_supported()` checks only AVX2.

## Part 88: The accelerated blocks behind streaming, HMAC-DRBG and HPKE

Part 87 left the streaming hashes, streaming HMAC, HMAC-DRBG and HPKE on the
portable SHA-2 block function: they are generic in the hash parameters and
called `blocks_scalar` directly.  They now take the block function as a
monomorphized argument, and their instantiations pass
`Hacl.Hash.SHA2.Dispatch.blocks_dispatch32`/`64`, which choose SHA-NI
(SHA-224/256) or AVX2 (SHA-384/512) at run time (`design/notes.md`, "SHA-512
on AVX2").

Before (`d71fdf2`) and after (`ab.sh`, gcc 15.2, two rounds, minimum per row):

| bench | before | after | speedup |
| --- | ---: | ---: | ---: |
| sha2-256-stream-1KiB-chunks (256 KiB) | 1419 us | 193 us | 7.3x |
| sha2-256-stream-64B-chunks (16 KiB) | 93.5 us | 19.3 us | 4.9x |
| hmac-drbg-sha2-256-instantiate+gen-1KiB | 57.0 us | 34.4 us | 1.66x |

Streaming SHA-256 is now within 6% of the one-shot hash (183 us) over the same
input.  No other row moved by more than 3%; the bench has no HPKE row, and
HPKE's time is the Diffie-Hellman.  The test suite passes under gcc and
clang, and with every `Hacl_Vec128_sha_supported()` and
`Hacl_Vec256_supported()` dispatch forced false.


## Part 89: Ed25519's fixed-base multiplication as a signed comb

The four-way window (Part 36's compiled-in tables) still did sixty-four
doublings and sixty-four additions per multiplication by `G`, and Ed25519
signing was at 3.87x of Firedancer.  `Hacl.Ed25519.PointMulComb` replaces
it with ref10's comb: the scalar, reduced mod `q`, is recoded into sixty-four
signed radix-16 digits in `[-8, 8]`; the odd digits are added from thirty-two
tables of `d 256^j G` (`d = 0 .. 8`), the sum is doubled four times, and the
even digits are added from the same tables.  Sixty-four mixed additions (seven
multiplications each, against Niels-form entries with `z = 1`) and four
doublings.

The tables are 4320 limbs, about 34 KB of `.rodata`, generated with their
proofs by `spec/group-gen/ed25519/comb.py` (`Spec.Ed25519.CombB`,
`CombT0` .. `CombT7`, `Hacl.Ed25519.CombData0` .. `7`).  Selection scans all
nine entries of a table with laundered `eq_mask` masks; a negative digit is a
`cswap` of the first two coordinates and a masked negation of the third.
`Hacl.Ed25519.PointMulG`, `Win0` .. `Win3`, `WinTable` and
`Spec.Ed25519.Base`/`Win0` .. `Win3` are gone.

Before (`432b7f7`) and after (`ab.sh`, gcc 15.2, two rounds, minimum per row;
clang 21.1 from a direct timing loop, best of 15; `sign` is
`Hacl_Ed25519_sign`, which multiplies by `G` twice, and `sign_expanded`
starts from expanded keys):

| bench | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 31.6 us | 14.9 us | 37.3 us | 18.9 us |
| sign (64 B) | 64.8 us | 31.1 us | 78.1 us | 39.1 us |
| sign_expanded (64 B) | 33.4 us | 16.7 us | 40.9 us | 20.1 us |
| verify (64 B) | 107.1 us | 88.1 us | 122.7 us | 103.8 us |

No other row moved by more than 4.3%, in either direction, which is this
machine's noise on code that did not change.  In the README's other-library
table, Ed25519 signing (expanded keys) goes from 3.87x of Firedancer to **1.92x**
and verification from 2.91x of dalek to **2.38x**; in the HACL\* table,
signing is Part 86's 73 us scaled by the ratio above, 35 us, **0.63x** of
HACL\*.  The test suite passes under gcc and clang, as do `make lint`,
`make stack`, `make cross` and `test_consttime`.  Every public Ed25519 entry
point hashes before it reaches the comb, so the timing audit cannot choose
digit patterns; instead the gcc and clang object code was checked: the only
conditional branches in the comb are loop bounds and the stack protector.

Verification still runs its variable-base multiplication as a four-bit
window with sixty-four doublings; a variable-time wNAF or Straus double-scalar
multiplication, which ref10 and dalek use, is the remaining gap.

## Part 90: Ed25519 verification as a variable-time double-scalar multiplication

Verification computed `[S]G` with Part 89's comb and `[k]A` with the
four-bit window (sixty-four doublings, sixty-four constant-time table
scans and additions), added `R`, and compared.  Under callgrind that was
about 926k instructions, 629k of them in the window.  Since every input to
`verify` is public, `Hacl.Ed25519.Straus` now computes
`Q = [k](-A) + [S]G` in variable time and compares `Q` with `R`: one shared
chain of 256 doublings; `k` recoded by a width-5 sliding window against a
table of the sixteen odd multiples of `-A`; `S` recoded by a width-3 sliding
window against comb table 0 (`1G .. 8G`, Niels form, already in `.rodata`).
Zero digits are skipped outright and table entries are read by index.
`Hacl.Ed25519.PointWin` keeps only the representation layer that the comb
and Straus share; `point_mul_win` and its rung are gone.

The proof adds two-base lemmas to `Spec.Group.Smul` and a new
`Spec.Ed25519.Straus` (`st q na a b`: `q` is equivalent to
`[a] na + [b] G`; `st_verify` turns `st Q (-A) k S` into the specification's
`[S]G == R + [k]A`).

Before (`be48cf7`) and after, gcc 15.2 from `ab.sh` (two rounds, minimum per
row) and both compilers from a direct timing loop (best of 15 x 2000 calls,
three runs, best shown):

| bench | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| verify (64 B), `ab.sh` | 90.2 us | 79.0 us | -- | -- |
| verify (64 B), loop | 89.7 us | 78.7 us | 103.3 us | 88.4 us |

12% under gcc and 14% under clang; keygen and sign (unchanged code) moved
by under 4%.  In the README's other-library table, verification goes from
2.38x of dalek to **2.08x**.  The README's HACL\* table (`table.sh`, gcc,
two rounds) gains an Ed25519 verify row, **1.23x** of HACL\* (79 us against
64 us), and its signing row, until now Part 86's figure scaled by Part 89's
ratio, is measured directly: 32 us against 50 us, **0.65x**.  The test suite (RFC 8032 vectors, every
single-bit tampering of the signature, a wrong message, and `S + q`) passes under gcc and clang, as do `make lint`, `make stack` and
`make cross`.

What remains: the 256 doublings carry `T`, which only the doubling that
precedes an addition needs; decompression of `A` and `R` is two
square-root exponentiations (about 137k instructions); and a larger table
for `G` (width 5 or more, a dedicated odd-multiple table) would cut the
`S` additions roughly in half.

## Part 91: Refresh on master `1109fa6`, and P-384

All three harnesses were rerun on master after the RSASSA-PKCS1-v1_5,
P-384, streaming Poly1305 and BLAKE2 parameter-block merges: `table.sh 2`
under gcc and clang and `others.sh 3`.  The other-library run shared the
machine with something else: at the default 2% canary tolerance only 17 of 72
runs survived, so the README table uses 5% (51 of 72); every cell is still a
minimum.

P-384 is now in both harnesses: `bench.c` (hacl-pulse only, `BS_HAVE_P384`,
since HACL\* has no P-384) and `others.c`, against OpenSSL and AWS-LC, with
SHA-384 and 48-byte scalars.  Every OpenSSL and AWS-LC P-384 result is checked
against hacl-pulse before it is timed: the ECDH secret byte for byte, and the
signatures by cross-verification.

| P-384 | gcc | clang | OpenSSL | AWS-LC | ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| ECDH | 1.5 ms | 1.3 ms | 419 us | 152 us | 8.8x |
| ECDSA sign | 1.5 ms | 1.4 ms | 250 us | 91 us | 15.0x |
| ECDSA verify | 3.0 ms | 2.7 ms | 574 us | 208 us | 12.8x |

That is by far the largest gap in the table.  The field multiplies through the
generic `nn = 6` Montgomery layer.  The scalar multiplication is
double-and-add over all 384 bits, with no window and no fixed-base table, and
verification does two separate full multiplications.  On P-256 those three
changes (a specialised field, a window and a comb, and Shamir's trick) were
together worth about 5x.

Elsewhere nothing moved by more than the noise.  Against the fastest other
library the gaps are now P-256 (2.3x to 3.9x), RSA-PSS-2048 verify (3.0x),
Ed25519 (about 2x), ML-DSA (about 1.8x to 2.1x, against AVX2 implementations),
RSA-PSS sign and FFDHE (about 1.75x), ML-KEM (about 1.5x) and X25519 (1.43x).
Against HACL\* the largest are X25519 (1.31x), MD5 (1.28x) and Ed25519
verify (1.25x); `gapbest.py` also ranks secp256k1 verify (1.94x) and short
AES-GCM messages (1.5x to 1.7x at 64 B) highest.

## Part 92: P-384's field as a dedicated six-limb Montgomery multiplier

P-384 arrived on the generic bignum layer: about 95% of a scalar
multiplication was `Hacl.Bignum`'s row multiplier (49%), Montgomery
reduction (18%) and modular addition (16%), and one `fmul` cost about 1.1k
instructions.  `Hacl.P384.Field64` replaces it for `fadd`, `fsub`, `fmul` and
`fsqr`: six interleaved Montgomery steps, each adding `x * b` and `u * p`
into a seven-word accumulator, with `mu = 2^32 + 1` and `u * p` from four
multiplications; a masked subtraction finishes it.  `Hacl.P384.Field` keeps
its interface, so nothing above it changed.

Before (`1109fa6`) and after, a direct timing loop (best of 5 x 200 calls,
100 for verify, pinned to one core):

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 1378 us | 710 us | 1471 us | 628 us |
| ECDH | 1392 us | 717 us | 1389 us | 619 us |
| sign | 1506 us | 772 us | 1459 us | 695 us |
| verify | 2824 us | 1451 us | 2825 us | 1268 us |

1.9x under gcc and 2.2-2.3x under clang; callgrind counts 8.0M
instructions for a keygen, down from 15M.  The test suite passes under gcc
and clang, as do `make lint` (with `step` and `mont` added to the
`nowipe` hot leaves, as P-256's `fmul` is), `make stack` and `make cross`.

What remains against AWS-LC (152 us ECDH, 91 us sign, 208 us verify): a
dedicated squaring, a windowed variable-base multiplication (the ladder
does one addition per bit), a precomputed table for `G`, a double-scalar
verify, and faster inversions.

## Part 93: P-384's scalar multiplications as a four-bit window

`Hacl.P384.PointWin` is `Hacl.P256.PointWin` on six limbs: sixteen
multiples of the base built at run time, then ninety-six rungs of four
doublings and one addition, the entry read by masking all sixteen
(`table_select`), so the running time does not depend on the scalar.  It
replaces the bit-at-a-time ladder (384 doublings and 384 additions) for
both `point_mul` and `point_mul_g`.  The result is equivalent to the
specification's triple rather than equal to it, so `PointMul`'s contracts
are now stated up to `peq`, as P-256's are, and ECDH, signing and
verification discharge that with `peq_out`/`add_out` in
`Hacl.P384.Verify` (equivalent points on the curve are at infinity
together and have the same affine coordinates).  The specification side,
`Spec.P384.Group` and `Spec.P384.Smul`, was already there.

Before (Part 92's field) and after, the same timing loop:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 702 us | 483 us | 596 us | 409 us |
| ECDH | 707 us | 490 us | 604 us | 416 us |
| sign | 767 us | 536 us | 660 us | 476 us |
| verify | 1466 us | 1006 us | 1223 us | 847 us |

1.45x under both compilers; against the generic-bignum version of Part 91
that is 2.8x (gcc) and 3.4x (clang).  Tests, `make lint`, `make stack` and
`make cross` pass.

What remains against AWS-LC (152 us ECDH, 91 us sign, 208 us verify): a
precomputed table for `G` (keygen and signing still build sixteen
multiples of `G` per call), a variable-time double-scalar verify, and a
dedicated squaring.

## Part 94: P-384's generator multiplication with compiled-in tables

Keygen and signing multiply the generator, and Part 93 treated it like
any other point: sixteen multiples built per call, then 384 doublings.
`Hacl.P384.PointMulG` is `Hacl.P256.PointMulG` with six pieces instead of
four.  The scalar splits into six 64-bit pieces against `G`, `2^64 G`, ...,
`2^320 G` (`Spec.Group.Split6`), so sixteen rungs of four doublings and six
masked table additions do the whole multiplication: 60 doublings and 96
additions where the window paid 384, 96 and 15.

The six tables, ninety-six affine points in Montgomery form (13.5 KiB), are
constants.  `spec/group-gen/p384/wintables.py` writes `Spec.P384.Base` (the
five base points, each checked by the normaliser as a chain of sixty-four
doublings), `Spec.P384.Win0..5` (each entry on the curve and the previous
one plus the base point) and `Hacl.P384.Win0..5` (the limbs, checked
against those points); `Hacl.P384.WinTable` is the bridge.  The script is
not trusted.  All of it verifies in about three minutes of CPU.

Before (Part 93) and after:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 528 us | 200 us | 415 us | 185 us |
| ECDH | 476 us | 482 us | 409 us | 414 us |
| sign | 546 us | 249 us | 491 us | 251 us |
| verify | 1029 us | 722 us | 868 us | 633 us |

ECDH multiplies the peer's point and does not change.  Verify gains from
its `u1 G` half.  Tests, `make lint`, `make stack` and `make cross` pass.

Still left against AWS-LC (152 us ECDH, 91 us sign, 208 us verify): a
variable-time double-scalar verify, a dedicated squaring, and faster
inversions.

## Part 95: P-384's field inversion by an addition chain

Every keygen, signature and ECDH result leaves the curve through
`Encode.to_aff`, which inverted `z` with the generic constant-time
Montgomery exponentiation (`Hacl.Bignum.Exponentiation.mod_exp_consttime`):
a conversion out of the field, a table scan and a multiplication per window
on top of 384 squarings, all on the generic six-limb multiply.  Under
callgrind that was 656k instructions, 28% of a keygen.

`Hacl.P384.Inverse.finv` raises to `p - 2` with a fixed chain on the
field's own `fsqr` and `fmul`.  With `x_k = x^(2^k - 1)` it builds `x_2,
x_3, x_6, x_12, x_15, x_30, x_60, x_120, x_240, x_255` and `x_32`, then
`((x_255 * 2^33 + x_32) * 2^94 + x_30) * 2^2 + 1 = p - 2`: 385 squarings
and 14 multiplications.  `to_aff` now stays in Montgomery form until two
final `ffrom`s, and drops to 237k instructions (2.8x).  The exponent is
public and the chain fixed, so it is constant-time.

Instructions (callgrind, gcc), before and after:

| operation | before | after |
| --- | ---: | ---: |
| keygen | 2.38M | 1.96M |
| sign | 2.90M | 2.48M |
| verify | 7.85M | 7.85M |

Time, best of two runs:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 212 us | 184 us | 198 us | 155 us |
| ECDH | 516 us | 481 us | 431 us | 377 us |
| sign | 254 us | 228 us | 269 us | 208 us |
| verify | 751 us | 751 us | 691 us | 703 us |

Verify never needs an affine point and does not change.  Tests,
`make lint`, `make stack` and `make cross` pass.

The proof is one lemma per chain step: `sqrn_mul` takes the exponents
`e1`, `e2` and `e = e1 2^n + e2` as ghost arguments and returns `x^e`, so
`finv` is fourteen calls and fourteen `assert_norm`s on constants.  Two
things were needed for Z3 5.3.0, which otherwise sat in single queries for
over ten minutes without honouring the rlimit: `ex` (`MA.exp` at `P.prime`)
is `opaque_to_smt`, with the `pow2` bookkeeping in plain lemmas (`sq1`,
`sq2`, `step_lem`), and the squaring count is passed as halves plus an odd
bit rather than computed with `SZ.div`/`SZ.rem`.  The module checks in
under a minute.

Next: the scalar inverse in signing (`invmod_ct` mod `q`, about 0.8M
instructions), which has no special form to exploit but would gain from a
specialised Montgomery multiply and a chain.

## Part 96: P-384's scalar inversion by an addition chain

Callgrind after Part 95 put the remaining generic exponentiations on top:
signing inverted the nonce with `mod_exp_consttime` mod `n`, and
verification called `mod_inv_prime_vartime` twice, for `s` mod `n` and for
`z` mod `p` in the final `x` check, at about 830k instructions each.

The `z` inverse in `Verify.check_x` is now `Hacl.P384.Inverse.finv`, as in
`to_aff`.  For `n` there is a new specialised Montgomery multiply,
`Hacl.P384.Scalar64` (a scripted copy of `Field64` with `n`'s limbs and
`mu`), its wrapper `Hacl.P384.QField` (`qev`, `qmul`, `qsqr`, `qto`,
`qfrom`), and `Hacl.P384.QInverse`.  The order has no special form below its
top 192 one bits, so the chain builds `x_192` by doubling (`x_2, x_4, ...,
x_128, x_192`) and finishes with a width-four sliding window over the odd
powers `x, x^3, ..., x^15`: 384 squarings and 54 multiplications,
generated by a script, each step an `sqrn_mul` with literal ghost
exponents and an `assert_norm`.  `qinv_plain` (enter, chain, leave) is
258k instructions.  The exponent is public, so it is constant-time and
serves both signing and verification; `Encode.invmod_ct` and
`Verify.invmod` are gone.

Instructions (callgrind, gcc), before and after:

| operation | before | after |
| --- | ---: | ---: |
| keygen | 1.96M | 1.96M |
| sign | 2.48M | 2.09M |
| verify | 7.85M | 6.68M |

Time:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 181 us | 183 us | 152 us | 155 us |
| ECDH | 476 us | 468 us | 401 us | 385 us |
| sign | 239 us | 190 us | 218 us | 160 us |
| verify | 738 us | 627 us | 645 us | 505 us |

Tests, `make lint`, `make stack` and `make cross` pass.

One proof detail: with all 39 window steps in one function the context
grew until Z3 timed out around step 30, so the window is five generated
functions `win0..win4` of eight steps, each taking the odd-power table
under one `tab_ok` predicate.  The module checks in about three minutes.

Next: the field multiply itself, which ECDH and verification spend most
of their time in.

## Part 97: P-384's reduction without multiplications

`Hacl.P384.Field64.step` computed `u * p` as seven words from four
`mul_wide`s (`prow`) and added them to the accumulator.  Because
`2^384 - p = 2^128 + 2^96 - 2^32 + 1`, `u * p = 2^384 u - u (2^128 + 2^96 -
2^32 + 1)`, and the subtrahend is three words plus a low word built from `u`,
`u << 32` and `u >> 32` with one borrow chain.  Its low word equals the
accumulator's (that is what `u` was chosen for), so the step adds `u` to
word 6, subtracts three words from words 1..3 and drops word 0.  A field
multiply goes from 60 `mul_wide`s to 36 and loses the `q` scratch array.

Before the change, a latency-bound chain of field multiplies took 135 ticks
per multiply under gcc and 103 under clang; with the C prototype it took
120 and 92.  The prototype agreed with the old code on two million random
and edge-case inputs.

Instructions (callgrind, gcc):

| operation | before | after |
| --- | ---: | ---: |
| keygen | 1.96M | 1.70M |
| ECDH | 4.81M | 4.16M |
| sign | 2.09M | 1.84M |
| verify | 6.68M | 5.82M |

Time:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| ECDH | 495 us | 466 us | 403 us | 345 us |
| sign | 204 us | 198 us | 178 us | 154 us |
| verify | 688 us | 644 us | 564 us | 488 us |

Tests, `make lint`, `make stack` and `make cross` pass.

Proof: `kval` states the three-word subtrahend linearly, and `r0_eq` shows
that its low word is the accumulator's.  `mu_ok`'s precondition proved in
`step` took Z3 353 seconds.  Moved into a helper `mu` whose result type
carries the cancellation fact, the module checks in 46 seconds.

The remaining gcc/clang gap is mostly spills in gcc's code.  Next: fewer
`fcopy`s in the point formulas, and possibly a dedicated squaring.

## Part 98: P-384's point formulas without copies

The complete addition and doubling formulas went through a scratch element
for every step that overwrites one of its own operands, and through a second
one for every step whose operands coincide: 57 `fcopy`s in all.
`Hacl.P384.Field64`'s `fadd` and `fsub` are now word-level cores (`addw`,
`subw`) like `mont`, taking twelve words, so the field offers in-place forms
that read before they write (`fadd1`, `fadd2`, `fsub1`, `fsub2`, `fmul1`,
`fmul2`, with the digit naming the operand the result replaces), as well as
`fdbl`, `fdbl1` and `fsqr1`.  A script rewrote the formulas mechanically.
They now have no copies and no `w`/`u` scratch, and the proofs went through
unchanged.

Instructions (callgrind, gcc):

| operation | before | after |
| --- | ---: | ---: |
| keygen | 1.70M | 1.68M |
| ECDH | 4.16M | 4.06M |
| sign | 1.84M | 1.82M |
| verify | 5.82M | 5.70M |

Time, the median of three interleaved runs:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 169 us | 151 us | 131 us | 125 us |
| ECDH | 422 us | 400 us | 315 us | 315 us |
| sign | 183 us | 179 us | 142 us | 140 us |
| verify | 598 us | 569 us | 452 us | 433 us |

Under gcc everything is 2-11% faster, and under clang verification is 4%
faster with the rest within noise.  Tests, `make lint`, `make stack` and
`make cross` pass.

## Part 99: P-384's doublings in Jacobian coordinates

Profiling after Part 98 put the field multiply at parity with AWS-LC's
s2n-bignum `bignum_montmul_p384` under clang (88 against 88 ticks in a
microbenchmark), with multiplications at 79% of instructions and doubling at
58%.  The remaining 2x is therefore algorithmic: AWS-LC's scalar
multiplication works in Jacobian coordinates.

Each rung of the variable-base window now converts the accumulator into
Jacobian coordinates (3 multiplications), doubles four times there with
`dbl-2001-b` for `a = -3` (4M + 4S, against 11 multiplications for the
complete homogeneous formula), and converts back (3 multiplications).  The
table addition is unchanged.  Infinity has no Jacobian representative with
`Z <> 0`, so it is carried as the fixed point `(1, 1, 0)` of the doubling.
The conversion picks it with a masked select (`Field.fzero_mask`,
`Field.fcsel`) because whether the accumulator is at infinity is secret.
The doublings work in place and use the rung's existing scratch triple as
their temporaries.

The proof follows the existing group-law machinery:

- `Spec.P384.JacSv` (hand-written) has the formulas in code order and their
  polynomial forms.
- `Spec.P384.JacChecks` is generated by `gen.py`, which gains a `jac`
  hypothesis kind, `Y^2 -> X^3 - 3XZ^4 + bZ^6`.  It checks five identities:
  - doubling preserves the Jacobian equation;
  - doubling agrees projectively with `P.point_double`;
  - the conversions are sound.

  The normalizer checks the five identities in four seconds.
- `Spec.P384.Jac` adds the nonzero argument: `Z <> 0` forces `Y <> 0`
  because the curve has no point of order two (`GroupNR.no_root_f`).  It
  also handles infinity and the invariant `jr` that `win_dbl4` threads
  through its four doublings.

Instructions (callgrind, gcc):

| operation | before | after |
| --- | ---: | ---: |
| keygen | 1.68M | 1.55M |
| ECDH | 4.06M | 3.25M |
| sign | 1.82M | 1.68M |
| verify | 5.70M | 4.75M |

Time, the median of three interleaved runs:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 163 us | 142 us | 131 us | 119 us |
| ECDH | 401 us | 319 us | 318 us | 252 us |
| sign | 186 us | 175 us | 143 us | 141 us |
| verify | 568 us | 495 us | 466 us | 354 us |

ECDH executes 20% fewer instructions and is 20% faster under both compilers.
Verification is 13% faster under gcc and 24% faster under clang.  Keygen and
sign gain less because their fixed-base comb does fewer doublings.  Tests,
`make lint`, `make stack` and `make cross` pass.

Correction: the ECDH instruction counts in Parts 97 and 98 were ECDH minus
sign.  The driver swaps sign for ECDH and the difference was taken against a
run that signs.  They are corrected above, measured as keygen plus ECDH minus
keygen.  The time rows were unaffected.

## Part 100: P-384 verification without an inversion

Verification ended by converting `u1 G + u2 Q` to affine form, a Fermat
inversion of about 400 multiplications, only to compare `x mod n` with `r`.
`Hacl.P384.Verify.check_x` now compares projectively:
- `X == r Z`;
- or, when `r + n < p`, `X == (r + n) Z`.

That is two multiplications and no inversion.  The lemma `xcheck` proves
the two tests equivalent to the affine one for `Z <> 0`; `p` is prime, so
`Z` cancels.  The `r + n < p` test runs on public values and is declassified.

Instructions (callgrind, gcc): verify drops from 4.75M to 4.57M (-3.9%).
Median time for verify: 477 to 429 us under gcc and 356 to 336 us under
clang.  The other operations are unchanged.

## Part 101: P-384 dedicated squaring

`fsqr` was `mont(a, a)`, 36 products.  `Hacl.P384.Field64.msqr` does 15
cross products, doubles them, and adds the 6 squares: 21 `mul_wide`s
into twelve words (`sq_cross`, `sq_diag` and their carry lemmas
`sqx0`..`sqx4` and `sqd`, generated by `spec/group-gen/p384/sqr.py`).
`mred` then reduces the twelve words:
- six reduction-only steps (`rstep`) take the low half `L` to
  `(L + U p) / 2^384 <= p`;
- the high half `H < p` is added;
- one conditional subtraction finishes.

`sq_expand` proves the polynomial identity with `CanonCommSemiring`.  At
first `msqr` was one function, and Z3 ran for twenty minutes on its
verification condition without reaching the rlimit.  Split into `msq12`,
`mred` and a closing lemma `msq_fin` over plain `nat`s, the module checks
with no query above rlimit 13.

Under clang the square drops from 371 instructions to 307.  Under gcc it
gains less: its multiply-heavy code is already longer than clang's.

Instructions (callgrind):

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 1.55M | 1.53M | 1.33M | 1.28M |
| ECDH | 3.25M | 3.17M | 2.59M | 2.46M |
| sign | 1.68M | 1.66M | 1.40M | 1.35M |
| verify | 4.57M | 4.49M | 3.68M | 3.56M |

Time, the median of three interleaved runs:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 138 us | 133 us | 115 us | 105 us |
| ECDH | 304 us | 303 us | 237 us | 230 us |
| sign | 161 us | 158 us | 129 us | 128 us |
| verify | 429 us | 422 us | 336 us | 329 us |

Against AWS-LC (clang, same core; AWS-LC uses s2n-bignum's mulx/adx
assembly and a divstep inversion), P-384 now stands at:

| operation | AWS-LC | ours | ratio |
| --- | ---: | ---: | ---: |
| keygen | 61 us | 105 us | 1.71x |
| sign | 99 us | 128 us | 1.29x |
| verify | 214 us | 329 us | 1.54x |
| ECDH | 161 us | 230 us | 1.43x |

Keygen and sign spend most of their time in the fixed-base comb's 96
complete additions, which is the next target.  Tests, `make lint`,
`make stack` and `make cross` pass.

## Part 102: P-384 fixed base with signed digits

The fixed-base comb read each 64-bit piece of the scalar as sixteen
unsigned 4-bit digits: 16 rungs of 4 doublings and 6 additions, 96
additions in all, each preceded by a constant-time select from a
16-entry table of projective points.  It now reads each piece as
thirteen signed 5-bit digits in -16..16 (Booth recoding, as in AWS-LC
and OpenSSL): 13 rungs of 5 doublings and 6 additions, so 78 additions
and 65 doublings.

A signed digit needs only the multiples 1..16 of each base point:
- the magnitude selects entry `m - 1`;
- the sign mask negates `y` (`fsub` from zero, then `fcsel`);
- a zero digit selects entry 15, adds it, and `fcsel` keeps the old
  accumulator.  This replaces the copy that `win_add` already did.

The tables are now affine: two arrays of 96 limbs per base point, not
three.  `z` is set to Montgomery one before each addition.  This makes
selects a third cheaper and prepares for a mixed addition.

Proof pieces:
- `Spec.Group.Booth6` defines the digits and `hb a i`, the piece above
  digit `i` rounded to nearest.  `hb a 13 = 0`, `hb a 0 = a`, and one
  step is `32 hb(i+1) +- m`.  `rv k i j`, the accumulator after `j` of a
  rung's six additions, is always a natural number.  A negative digit is
  stated as `e = e' + m n` rather than `e' = e - m n`, so the window's
  `rep` never needs a negative multiple.  `rv_step` timed out until each
  piece's weighted term (`hw`) was made opaque and the proof split on `j`.
- `Hacl.P384.PointBooth.neg_add` proves that adding `-(d P)` to
  `(e + d) P` gives `e P`, from associativity, commutativity,
  `point_add_negate` and the identity.
- `win_sadd` is a single signed addition with no secret branches.
  Whether the digit was zero is settled inside the lemma `sadd_ok`, not
  by a branch in Pulse.
- `wintables.py` now emits the chain up to `e16` and the affine tables.
  `WinTable.aent_lit`/`atok_all` replace `ent_lit`/`tok_all`.

Instructions (callgrind):

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 1.53M | 1.35M | 1.28M | 1.10M |
| sign | 1.66M | 1.49M | 1.35M | 1.17M |
| verify | 4.49M | 4.30M | 3.56M | 3.38M |
| ECDH | 3.17M | 3.15M | 2.46M | 2.46M |

Time, the median of three interleaved runs:

| operation | gcc before | gcc after | clang before | clang after |
| --- | ---: | ---: | ---: | ---: |
| keygen | 131 us | 118 us | 112 us | 98 us |
| ECDH | 302 us | 294 us | 240 us | 238 us |
| sign | 158 us | 139 us | 127 us | 111 us |
| verify | 430 us | 407 us | 334 us | 318 us |

ECDH does not use the fixed base; its change is noise.  Against AWS-LC
(clang):

| operation | AWS-LC | ours | ratio |
| --- | ---: | ---: | ---: |
| keygen | 61 us | 98 us | 1.61x |
| sign | 99 us | 111 us | 1.12x |
| verify | 214 us | 318 us | 1.49x |
| ECDH | 161 us | 238 us | 1.48x |

Next is a mixed addition for the affine table entries, with `Z2 = 1`;
it saves a multiplication and some additions per call.  Tests,
`make lint`, `make stack` and `make cross` pass.
