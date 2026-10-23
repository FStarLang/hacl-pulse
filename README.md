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
| hashes | MD5, SHA-1, SHA-224/256/384/512, SHA3-224/256/384/512, SHAKE128/256, BLAKE2s, BLAKE2b (one-shot and streaming) |
| MACs and KDFs | HMAC (SHA-1, SHA-2), Poly1305, HKDF, HMAC-DRBG |
| ciphers and AEAD | ChaCha20, Salsa20, AES-128/256-GCM, ChaCha20-Poly1305, NaCl `box` and `secretbox` |
| elliptic curves | X25519, Ed25519, P-256 ECDH and ECDSA, secp256k1 ECDH and ECDSA |
| bignum | generic Montgomery arithmetic and modular exponentiation, RSA-PSS, FFDHE (RFC 7919 groups) |
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
| SHA-1 | 256 KiB | 184 us | 1.6 ms | 0.11x |
| Salsa20 | 256 KiB | 105 us | 433 us | 0.24x |
| NaCl secretbox | 256 KiB | 156 us | 616 us | 0.25x |
| SHA-512 | 256 KiB | 519 us | 1.3 ms | 0.39x |
| HMAC-SHA-512 | 256 KiB | 526 us | 1.3 ms | 0.39x |
| RSA-PSS-2048 verify | -- | 56 us | 130 us | 0.43x |
| P-256 ECDH | -- | 71 us | 151 us | 0.47x |
| SHAKE128 | 256 KiB | 606 us | 1.3 ms | 0.48x |
| SHA3-256 | 256 KiB | 751 us | 1.5 ms | 0.49x |
| P-256 ECDSA sign | -- | 83 us | 164 us | 0.51x |
| P-256 ECDSA verify | -- | 237 us | 414 us | 0.57x |
| Ed25519 sign | -- | 32 us | 50 us | 0.65x |
| BLAKE2b | 256 KiB | 369 us | 428 us | 0.86x |
| BLAKE2s | 256 KiB | 577 us | 615 us | 0.94x |
| FFDHE-2048 | -- | 4.1 ms | 4.2 ms | 0.96x |
| RSA-PSS-2048 sign | -- | 4.1 ms | 4.3 ms | 0.96x |
| Poly1305 | 256 KiB | 49 us | 51 us | 0.96x |
| RSA-2048 modexp | -- | 4.1 ms | 4.2 ms | 0.98x |
| ChaCha20-Poly1305 | 256 KiB | 152 us | 139 us | 1.10x |
| secp256k1 ECDSA sign | -- | 69 us | 63 us | 1.11x |
| AES-128-GCM | 256 KiB | 77 us | 67 us | 1.15x |
| HMAC-SHA-256 | 256 KiB | 205 us | 174 us | 1.18x |
| ChaCha20 | 256 KiB | 103 us | 88 us | 1.18x |
| SHA-256 | 256 KiB | 204 us | 173 us | 1.18x |
| Ed25519 verify | -- | 79 us | 64 us | 1.23x |
| MD5 | 256 KiB | 557 us | 432 us | 1.29x |
| X25519 | -- | 53 us | 40 us | 1.32x |

### ML-KEM and ML-DSA

HACL\* has neither, so these numbers are absolute (gcc 15.2.0, then clang
21.1, as gcc / clang):

| operation | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |
| --- | ---: | ---: | ---: |
| keypair | 15 us / 12 us | 22 us / 19 us | 33 us / 27 us |
| encapsulate | 17 us / 14 us | 26 us / 22 us | 36 us / 30 us |
| decapsulate | 21 us / 17 us | 31 us / 26 us | 42 us / 36 us |

| operation | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
| --- | ---: | ---: | ---: |
| keypair | 54 us / 41 us | 92 us / 70 us | 145 us / 107 us |
| sign | 186 us / 132 us | 268 us / 192 us | 355 us / 244 us |
| verify | 57 us / 43 us | 92 us / 68 us | 145 us / 107 us |

Against the ML-DSA implementations people deploy (the pq-crystals reference
and AVX2 builds, OpenSSL 3.5, mldsa-native, AWS-LC and Cryspen's libcrux),
with every public key and deterministic signature checked byte for byte
against hacl-pulse's (AWS-LC signs only hedged, so its signatures are
cross-verified instead):

| operation | hacl-pulse (gcc) | hacl-pulse (clang) | pq-crystals ref | OpenSSL | pq-crystals avx2 | mldsa-native | AWS-LC | libcrux | hacl-pulse ÷ fastest other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| ML-DSA-44 keygen | 48 us | 40 us | 80 us | 108 us | 23 us | **21 us** | 31 us | 23 us | 1.87x |
| ML-DSA-44 sign | 173 us | 133 us | 387 us | 673 us | **69 us** | 71 us | 93 us | 87 us | 1.92x |
| ML-DSA-44 verify | 51 us | 43 us | 86 us | 121 us | 25 us | **22 us** | 30 us | 26 us | 1.91x |
| ML-DSA-65 keygen | 83 us | 70 us | 145 us | 188 us | 40 us | **37 us** | 53 us | 41 us | 1.90x |
| ML-DSA-65 sign | 275 us | 215 us | 617 us | 1,053 us | **106 us** | 110 us | 160 us | 134 us | 2.03x |
| ML-DSA-65 verify | 84 us | 67 us | 139 us | 188 us | 40 us | **38 us** | 49 us | 41 us | 1.80x |
| ML-DSA-87 keygen | 132 us | 105 us | 213 us | 267 us | 63 us | **57 us** | 86 us | 63 us | 1.83x |
| ML-DSA-87 sign | 353 us | 272 us | 784 us | 1,303 us | 135 us | **131 us** | 184 us | 178 us | 2.07x |
| ML-DSA-87 verify | 128 us | 106 us | 228 us | 292 us | 64 us | **57 us** | 81 us | 65 us | 1.86x |

### Against other libraries

How hacl-pulse compares with OpenSSL 3.5.5, AWS-LC, libsodium, libjade,
Firedancer and dalek. Before timing, each contender's output is checked
against hacl-pulse's on the same inputs. Fastest is in bold. The last
column is the better hacl-pulse build divided by the fastest other library:

| primitive | size | hacl-pulse (gcc) | hacl-pulse (clang) | OpenSSL | AWS-LC | libsodium | libjade | Firedancer | dalek | hacl-pulse ÷ fastest other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| secp256k1 ECDSA sign | -- | **63 us** | 83 us | 410 us | 292 us | -- | -- | -- | -- | 0.21x |
| BLAKE2s | 256 KiB | 516 us | **496 us** | 540 us | -- | -- | -- | -- | -- | 0.92x |
| Poly1305 | 256 KiB | 44 us | **36 us** | 38 us | 76 us | 72 us | 37 us | -- | -- | 0.97x |
| Salsa20 | 256 KiB | 95 us | 95 us | -- | -- | 93 us | **90 us** | -- | -- | 1.05x |
| NaCl secretbox | 256 KiB | 143 us | 136 us | -- | -- | 167 us | **129 us** | -- | -- | 1.06x |
| BLAKE2b | 256 KiB | 333 us | 299 us | 331 us | -- | **273 us** | -- | -- | -- | 1.10x |
| SHA-256 | 256 KiB | 185 us | 173 us | 160 us | 158 us | 797 us | 996 us | **156 us** | -- | 1.11x |
| HMAC-SHA-256 | 256 KiB | 184 us | 175 us | 158 us | 159 us | 796 us | -- | **156 us** | -- | 1.13x |
| SHA-1 | 256 KiB | 165 us | 169 us | 149 us | **146 us** | -- | -- | 808 us | -- | 1.13x |
| SHA3-256 | 256 KiB | 680 us | 672 us | **576 us** | 581 us | -- | 714 us | -- | -- | 1.17x |
| AES-256-GCM | 256 KiB | 79 us | 74 us | 63 us | **63 us** | 73 us | -- | 63 us | -- | 1.18x |
| SHAKE128 | 256 KiB | 546 us | 560 us | 475 us | **463 us** | -- | 580 us | -- | -- | 1.18x |
| AES-128-GCM | 256 KiB | 70 us | 67 us | 58 us | 59 us | -- | -- | **56 us** | -- | 1.19x |
| ChaCha20 | 256 KiB | 93 us | 91 us | **74 us** | 75 us | 118 us | 77 us | -- | -- | 1.22x |
| MD5 | 256 KiB | 503 us | 432 us | **351 us** | 353 us | -- | -- | -- | -- | 1.23x |
| ChaCha20-Poly1305 | 256 KiB | 136 us | 133 us | 113 us | **104 us** | 193 us | -- | -- | -- | 1.28x |
| ML-DSA-65 keygen | -- | 83 us | 70 us | 188 us | **53 us** | -- | -- | -- | -- | 1.32x |
| ML-DSA-65 sign | -- | 275 us | 215 us | 1.1 ms | **160 us** | -- | -- | -- | -- | 1.34x |
| HMAC-SHA-512 | 256 KiB | 481 us | 430 us | 330 us | 464 us | 498 us | -- | **321 us** | -- | 1.34x |
| SHA-512 | 256 KiB | 472 us | 432 us | 330 us | 467 us | 498 us | 636 us | **321 us** | -- | 1.35x |
| ML-DSA-65 verify | -- | 84 us | 67 us | 188 us | **49 us** | -- | -- | -- | -- | 1.36x |
| X25519 | -- | 48 us | 36 us | 35 us | 27 us | 31 us | 29 us | **26 us** | 56 us | 1.38x |
| ML-KEM-768 keygen | -- | 20 us | 19 us | 48 us | **13 us** | -- | -- | -- | -- | 1.44x |
| ML-KEM-768 decaps | -- | 27 us | 26 us | 51 us | **17 us** | -- | -- | -- | -- | 1.52x |
| ML-KEM-768 encaps | -- | 23 us | 22 us | 34 us | **14 us** | -- | -- | -- | -- | 1.53x |
| FFDHE-2048 | -- | 3.7 ms | 4.5 ms | **2.2 ms** | 4.0 ms | -- | -- | -- | -- | 1.68x |
| RSA-PSS-2048 sign | -- | 3.7 ms | 4.5 ms | 2.2 ms | **2.1 ms** | -- | -- | -- | -- | 1.71x |
| Ed25519 sign | -- | 17 us | 20 us | 41 us | 8.9 us | 16 us | -- | **8.7 us** | 18 us | 1.92x |
| Ed25519 verify | -- | 77 us | 89 us | 113 us | 39 us | 51 us | -- | 44 us | **37 us** | 2.08x |
| P-256 ECDH | -- | 149 us | 111 us | 50 us | **48 us** | -- | -- | -- | -- | 2.31x |
| RSA-PSS-2048 verify | -- | 51 us | 59 us | 22 us | **17 us** | -- | -- | -- | -- | 2.99x |
| P-256 ECDSA verify | -- | 211 us | 162 us | 67 us | **54 us** | -- | -- | 62 us | -- | 3.00x |
| P-256 ECDSA sign | -- | 75 us | 61 us | 24 us | **16 us** | -- | -- | -- | -- | 3.85x |

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
