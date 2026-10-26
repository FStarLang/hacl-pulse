# hacl-pulse

[![CI](https://github.com/FStarLang/hacl-pulse/actions/workflows/ci.yml/badge.svg)](https://github.com/FStarLang/hacl-pulse/actions/workflows/ci.yml)

A formally verified cryptographic library written in
[F\*](https://github.com/FStarLang/FStar) and
[Pulse](https://fstar-lang.org/tutorial/book/pulse/pulse.html), and
extracted to C by
[Custard](https://github.com/FStarLang/FStar/blob/master/doc/ref/custard.md).
It reimplements [HACL\*](https://github.com/hacl-star/hacl-star). The
design is new, not a port: where HACL\* had to work around a missing
language feature, this library uses that feature.

Every algorithm comes with a pure specification in `spec/`. Its Pulse
implementation is proved memory-safe and functionally correct against that
specification, and secret-independent: secrets are abstract types that
support only constant-time operations. The specifications also carry
theorems of their own. For example, decryption inverts encryption, both
sides of a key exchange agree, and an honest signature verifies. The
output is one C file and one header, `dist/Hacl.c` and `dist/Hacl.h`, with
no assembly and no Vale. Code specific to one microarchitecture uses C
intrinsics behind a narrow axiomatized interface and is chosen at run time.

## Algorithms

| family | algorithms |
| --- | --- |
| hashes | MD5, SHA-1, SHA-224/256/384/512, SHA3-224/256/384/512, SHAKE128/256, BLAKE2s, BLAKE2b (one-shot and streaming, with salt, personalization and tree parameters) |
| MACs and KDFs | HMAC (SHA-1, SHA-2) and Poly1305 (one-shot and streaming), HKDF, HMAC-DRBG |
| ciphers and AEAD | ChaCha20, Salsa20, AES-128/256-GCM, ChaCha20-Poly1305, NaCl `box` and `secretbox` |
| elliptic curves | X25519, Ed25519, P-256 ECDH and ECDSA, P-384 ECDH and ECDSA (SHA-384, SHA-256), secp256k1 ECDH and ECDSA |
| bignum | generic Montgomery arithmetic and modular exponentiation, RSA-PSS, RSASSA-PKCS1-v1_5, FFDHE (RFC 7919 groups) |
| post-quantum | ML-KEM (FIPS 203) and ML-DSA (FIPS 204), all three parameter sets each; FrodoKEM, all four parameter sets |
| protocols | HPKE (RFC 9180), all four modes |

Each algorithm is tested against its published vectors: FIPS and RFC
vectors, NIST CAVP and ACVP, and the FrodoKEM known-answer tests. The
tests are the C harnesses in [`tests/`](tests/).

Accelerated code paths are AES-NI and PCLMULQDQ for AES-GCM, the SHA
extensions for SHA-256, AVX2 for ChaCha20, Salsa20, Poly1305 and four-way
Keccak, and AVX-512 for ChaCha20 and Salsa20. All of these are x86-64
only. On other architectures, such as aarch64, the same `Hacl.c` compiles
to the portable code alone.

## Building

You need an F\* that includes Pulse and Custard. The tree tracks F\*
`master` and is checked against the
[`nightly-2026-10-21`](https://github.com/FStarLang/FStar-nightly/releases/tag/nightly-2026-10-21)
build. Older releases are not supported. To install the nightly:

```
curl -L https://github.com/FStarLang/FStar-nightly/releases/download/nightly-2026-10-21/fstar-Linux-x86_64.tar.gz | tar xz
make -j$(nproc) FSTAR_ROOT=$PWD/fstar
```

A source checkout of F\* built through `stage3` also works.
You also need GNU make, a C11 compiler (gcc or clang) and Perl.

| command | effect |
| --- | --- |
| `make` | lint, verify, extract, compile, check stack usage, run the tests |
| `make verify` | verify all F\*/Pulse modules |
| `make extract` | regenerate `dist/Hacl.c` and `dist/Hacl.h` |
| `make test` | build and run the C tests |
| `make cross` | build for aarch64 and run the tests under `qemu-aarch64` |
| `make CC=clang` | build with clang instead of gcc |
| `make DIST_ONLY=1 test` | build and test an existing `dist/` without F\* |

Extraction also writes the Custard unit interface `obj/build/Hacl.cui`. A
downstream Custard project can extract against it with
`--custard_link <path>/obj/build/Hacl.cui` and
`--custard_monomorphize_types true`, then link with `dist/Hacl.c`.

Verification takes about half an hour on 24 cores, and most of that is the
ML-KEM NTT. The C is compiled with `-std=c11 -O3 -Wall -Wextra -Werror`.

## Performance

These numbers were measured on an AMD EPYC 7V13 (Zen 3, with AVX2, ADX and
the SHA extensions, but no AVX-512), pinned to one core. Each number is the
minimum over interleaved runs. ML-KEM and ML-DSA are timed over 64
different seeds, ciphertexts and messages in turn, because their rejection
samplers make the time depend on the input, and with a single fixed input
the branch predictor learns the outcomes.

### Against HACL\*

The comparison is against HACL\* `504c298`, compiled with gcc 15.2.0
`-O3` like hacl-pulse and built for the same machine with everything it
has: Vale assembly, AVX2, and BMI2/ADX. A ratio **below 1.00 means
hacl-pulse is faster**.

| primitive | size | hacl-pulse | HACL\* | ratio |
| --- | ---: | ---: | ---: | ---: |
| SHA-1 | 256 KiB | 163 us | 1.5 ms | 0.11x |
| Salsa20 | 256 KiB | 95 us | 388 us | 0.25x |
| NaCl secretbox | 256 KiB | 141 us | 548 us | 0.26x |
| HMAC-SHA-512 | 256 KiB | 473 us | 1.2 ms | 0.39x |
| SHA-512 | 256 KiB | 474 us | 1.2 ms | 0.40x |
| RSA-PSS-2048 verify | -- | 50 us | 117 us | 0.43x |
| P-256 ECDH | -- | 64 us | 136 us | 0.47x |
| SHAKE128 | 256 KiB | 548 us | 1.1 ms | 0.49x |
| SHA3-256 | 256 KiB | 686 us | 1.4 ms | 0.50x |
| P-256 ECDSA sign | -- | 75 us | 149 us | 0.51x |
| P-256 ECDSA verify | -- | 211 us | 371 us | 0.57x |
| Ed25519 sign | -- | 32 us | 50 us | 0.65x |
| BLAKE2b | 256 KiB | 329 us | 389 us | 0.85x |
| BLAKE2s | 256 KiB | 527 us | 557 us | 0.95x |
| RSA-PSS-2048 sign | -- | 3.7 ms | 3.9 ms | 0.96x |
| FFDHE-2048 | -- | 3.7 ms | 3.8 ms | 0.96x |
| Poly1305 | 256 KiB | 44 us | 45 us | 0.96x |
| RSA-2048 modexp | -- | 3.7 ms | 3.8 ms | 0.98x |
| AES-128-GCM | 256 KiB | 66 us | 61 us | 1.08x |
| ChaCha20-Poly1305 | 256 KiB | 136 us | 125 us | 1.09x |
| secp256k1 ECDSA sign | -- | 61 us | 56 us | 1.09x |
| HMAC-SHA-256 | 256 KiB | 182 us | 156 us | 1.16x |
| SHA-256 | 256 KiB | 185 us | 157 us | 1.17x |
| ChaCha20 | 256 KiB | 94 us | 79 us | 1.19x |
| Ed25519 verify | -- | 79 us | 63 us | 1.25x |
| MD5 | 256 KiB | 500 us | 392 us | 1.28x |
| X25519 | -- | 48 us | 37 us | 1.31x |

HACL\* has no P-384, so P-384 appears only in the comparison with other
libraries below.

### ML-KEM and ML-DSA

HACL\* has neither, so these numbers are absolute (gcc 15.2.0, then clang
21.1, as gcc / clang):

| operation | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |
| --- | ---: | ---: | ---: |
| keypair | 13 us / 12 us | 20 us / 19 us | 29 us / 27 us |
| encapsulate | 15 us / 14 us | 24 us / 22 us | 33 us / 29 us |
| decapsulate | 19 us / 17 us | 28 us / 26 us | 38 us / 36 us |

| operation | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
| --- | ---: | ---: | ---: |
| keypair | 48 us / 39 us | 83 us / 69 us | 128 us / 104 us |
| sign | 170 us / 129 us | 241 us / 189 us | 319 us / 242 us |
| verify | 50 us / 41 us | 83 us / 68 us | 129 us / 105 us |

Against the ML-DSA implementations people deploy (the pq-crystals reference
and AVX2 builds, OpenSSL 3.5, mldsa-native, AWS-LC and Cryspen's libcrux),
with every public key and deterministic signature checked byte for byte
against hacl-pulse's (AWS-LC signs only hedged, so its signatures are
cross-verified instead):

| operation | hacl-pulse (gcc) | hacl-pulse (clang) | pq-crystals ref | OpenSSL | pq-crystals avx2 | mldsa-native | AWS-LC | libcrux | hacl-pulse ÷ fastest other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| ML-DSA-44 keygen | 49 us | 40 us | 79 us | 106 us | 23 us | **22 us** | 31 us | 23 us | 1.85x |
| ML-DSA-44 sign | 171 us | 134 us | 390 us | 665 us | **68 us** | 70 us | 93 us | 86 us | 1.98x |
| ML-DSA-44 verify | 50 us | 43 us | 86 us | 121 us | 24 us | **22 us** | 30 us | 25 us | 1.91x |
| ML-DSA-65 keygen | 83 us | 69 us | 142 us | 188 us | 40 us | **37 us** | 53 us | 40 us | 1.87x |
| ML-DSA-65 sign | 271 us | 214 us | 609 us | 1,043 us | **106 us** | 109 us | 137 us | 131 us | 2.02x |
| ML-DSA-65 verify | 82 us | 68 us | 139 us | 189 us | 40 us | **38 us** | 51 us | 40 us | 1.81x |
| ML-DSA-87 keygen | 127 us | 107 us | 215 us | 267 us | 63 us | **58 us** | 85 us | 62 us | 1.84x |
| ML-DSA-87 sign | 350 us | 271 us | 775 us | 1,296 us | 134 us | **132 us** | 180 us | 176 us | 2.05x |
| ML-DSA-87 verify | 127 us | 105 us | 224 us | 295 us | 64 us | **57 us** | 81 us | 64 us | 1.84x |

### Against other libraries

How hacl-pulse compares with OpenSSL 3.5.5, AWS-LC, libsodium, libjade,
Firedancer and dalek. Before timing, each contender's output is checked
against hacl-pulse's on the same inputs. Fastest is in bold. The last
column is the better hacl-pulse build divided by the fastest other library:

| primitive | size | hacl-pulse (gcc) | hacl-pulse (clang) | OpenSSL | AWS-LC | libsodium | libjade | Firedancer | dalek | hacl-pulse ÷ fastest other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| secp256k1 ECDSA sign | -- | **61 us** | 82 us | 426 us | 306 us | -- | -- | -- | -- | 0.20x |
| BLAKE2s | 256 KiB | 525 us | **500 us** | 535 us | -- | -- | -- | -- | -- | 0.93x |
| Poly1305 | 256 KiB | 44 us | **36 us** | 38 us | 76 us | 73 us | 37 us | -- | -- | 0.97x |
| Salsa20 | 256 KiB | 95 us | 96 us | -- | -- | 93 us | **90 us** | -- | -- | 1.05x |
| NaCl secretbox | 256 KiB | 142 us | 134 us | -- | -- | 166 us | **127 us** | -- | -- | 1.05x |
| AES-128-GCM | 256 KiB | 66 us | 59 us | 59 us | 58 us | -- | -- | **55 us** | -- | 1.08x |
| SHA-256 | 256 KiB | 182 us | 171 us | 159 us | 159 us | 802 us | 992 us | **157 us** | -- | 1.09x |
| BLAKE2b | 256 KiB | 331 us | 299 us | 333 us | -- | **273 us** | -- | -- | -- | 1.09x |
| SHA-1 | 256 KiB | 161 us | 160 us | 148 us | **146 us** | -- | -- | 799 us | -- | 1.10x |
| HMAC-SHA-256 | 256 KiB | 185 us | 174 us | 156 us | 157 us | 788 us | -- | **156 us** | -- | 1.12x |
| AES-256-GCM | 256 KiB | 75 us | 70 us | 63 us | 62 us | 73 us | -- | **62 us** | -- | 1.13x |
| SHA3-256 | 256 KiB | 680 us | 661 us | 587 us | **575 us** | -- | 707 us | -- | -- | 1.15x |
| SHAKE128 | 256 KiB | 541 us | 546 us | 481 us | **459 us** | -- | 572 us | -- | -- | 1.18x |
| ChaCha20 | 256 KiB | 94 us | 90 us | 75 us | **75 us** | 120 us | 76 us | -- | -- | 1.20x |
| MD5 | 256 KiB | 503 us | 430 us | 354 us | **354 us** | -- | -- | -- | -- | 1.22x |
| ChaCha20-Poly1305 | 256 KiB | 138 us | 127 us | 113 us | **102 us** | 193 us | -- | -- | -- | 1.24x |
| ML-DSA-65 keygen | -- | 83 us | 69 us | 188 us | **53 us** | -- | -- | -- | -- | 1.30x |
| ML-DSA-65 verify | -- | 82 us | 68 us | 189 us | **51 us** | -- | -- | -- | -- | 1.34x |
| HMAC-SHA-512 | 256 KiB | 471 us | 437 us | 325 us | 459 us | 491 us | -- | **321 us** | -- | 1.36x |
| SHA-512 | 256 KiB | 473 us | 442 us | 325 us | 459 us | 504 us | 635 us | **315 us** | -- | 1.40x |
| X25519 | -- | 47 us | 37 us | 35 us | **26 us** | 31 us | 29 us | 26 us | 55 us | 1.43x |
| ML-KEM-768 keygen | -- | 20 us | 20 us | 49 us | **13 us** | -- | -- | -- | -- | 1.52x |
| ML-KEM-768 decaps | -- | 28 us | 26 us | 50 us | **17 us** | -- | -- | -- | -- | 1.53x |
| ML-DSA-65 sign | -- | 271 us | 214 us | 1.0 ms | **137 us** | -- | -- | -- | -- | 1.56x |
| ML-KEM-768 encaps | -- | 24 us | 22 us | 34 us | **14 us** | -- | -- | -- | -- | 1.59x |
| RSA-PSS-2048 sign | -- | 3.6 ms | 4.4 ms | 2.1 ms | **2.1 ms** | -- | -- | -- | -- | 1.73x |
| FFDHE-2048 | -- | 3.6 ms | 4.5 ms | **2.1 ms** | 4.0 ms | -- | -- | -- | -- | 1.75x |
| Ed25519 sign | -- | 17 us | 21 us | 40 us | 8.8 us | 16 us | -- | **8.6 us** | 18 us | 1.95x |
| Ed25519 verify | -- | 79 us | 89 us | 114 us | 39 us | 50 us | -- | 44 us | **38 us** | 2.11x |
| P-256 ECDH | -- | 148 us | 108 us | 49 us | **47 us** | -- | -- | -- | -- | 2.27x |
| RSA-PSS-2048 verify | -- | 50 us | 58 us | 22 us | **17 us** | -- | -- | -- | -- | 2.95x |
| P-256 ECDSA verify | -- | 209 us | 163 us | 67 us | **52 us** | -- | -- | 62 us | -- | 3.12x |
| P-256 ECDSA sign | -- | 75 us | 61 us | 24 us | **16 us** | -- | -- | -- | -- | 3.87x |
| P-384 ECDH | -- | 1.5 ms | 1.3 ms | 419 us | **152 us** | -- | -- | -- | -- | 8.82x |
| P-384 ECDSA verify | -- | 3.0 ms | 2.7 ms | 574 us | **208 us** | -- | -- | -- | -- | 12.81x |
| P-384 ECDSA sign | -- | 1.5 ms | 1.4 ms | 250 us | **91 us** | -- | -- | -- | -- | 15.04x |

A dash means the library does not offer the operation through the API used.
OpenSSL's and AWS-LC's ML-KEM and ECDSA draw from their DRBGs. The
[design notes](design/notes.md#performance) explain the method, what makes
the comparison fair, and where each gap comes from. They also have HACL\*'s
portable C as a second reference and the clang numbers against HACL\*.

The harness is in [`bench/`](bench/). [`bench/REPORT.md`](bench/REPORT.md)
logs every optimization in order.

## Layout

| directory | contents |
| --- | --- |
| `lib/` | secret integers, the `word` type class, byte serialization, vector intrinsics interfaces, wiped scratch memory |
| `spec/` | pure specifications and their correctness theorems |
| `code/` | Pulse implementations, one directory per family |
| `c/` | the handwritten C trusted base: entropy, vector intrinsics, add-with-carry, memory wiping |
| `tests/` | C test harnesses |
| `bench/` | benchmark harness and optimization log |
| `design/` | design documentation: [`notes.md`](design/notes.md) covers this library's design, proofs and performance, and the rest is an inventory of HACL\*'s APIs |
| `dist/` | generated C (not committed; produced by `make extract`) |

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
