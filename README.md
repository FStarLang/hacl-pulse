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

Verification takes about half an hour on 24 cores, and most of that is the
ML-KEM NTT. The C is compiled with `-std=c11 -O3 -Wall -Wextra -Werror`.

## Performance

These numbers were measured on an AMD EPYC 7V13 (Zen 3, with AVX2, ADX and
the SHA extensions, but no AVX-512), compiled with gcc 15.2.0 `-O3`, and
pinned to one core. Each number is the minimum over interleaved runs. The
comparison is against HACL\* `504c298`, built for the same machine with
everything it has: Vale assembly, AVX2, and BMI2/ADX. A ratio **below 1.00
means hacl-pulse is faster**.

| primitive | size | hacl-pulse | HACL\* | ratio |
| --- | ---: | ---: | ---: | ---: |
| Salsa20 | 256 KiB | 96 us | 393 us | 0.24x |
| NaCl secretbox | 256 KiB | 142 us | 568 us | 0.25x |
| RSA-PSS-2048 verify | -- | 51 us | 119 us | 0.43x |
| P-256 ECDH | -- | 64 us | 137 us | 0.47x |
| P-256 ECDSA sign | -- | 76 us | 148 us | 0.51x |
| HMAC-SHA-512 | 256 KiB | 636 us | 1.2 ms | 0.52x |
| SHAKE128 | 256 KiB | 630 us | 1.2 ms | 0.53x |
| SHA3-256 | 256 KiB | 765 us | 1.4 ms | 0.54x |
| SHA-512 | 256 KiB | 650 us | 1.2 ms | 0.54x |
| P-256 ECDSA verify | -- | 216 us | 376 us | 0.57x |
| BLAKE2b | 256 KiB | 338 us | 388 us | 0.87x |
| BLAKE2s | 256 KiB | 524 us | 563 us | 0.93x |
| RSA-PSS-2048 sign | -- | 3.7 ms | 3.9 ms | 0.95x |
| Poly1305 | 256 KiB | 44 us | 46 us | 0.95x |
| FFDHE-2048 | -- | 3.7 ms | 3.8 ms | 0.96x |
| RSA-2048 modexp | -- | 3.7 ms | 3.8 ms | 0.98x |
| ChaCha20-Poly1305 | 256 KiB | 138 us | 128 us | 1.08x |
| SHA-1 | 256 KiB | 1.6 ms | 1.5 ms | 1.08x |
| AES-128-GCM | 256 KiB | 68 us | 61 us | 1.12x |
| secp256k1 ECDSA sign | -- | 65 us | 57 us | 1.14x |
| ChaCha20 | 256 KiB | 93 us | 81 us | 1.15x |
| SHA-256 | 256 KiB | 185 us | 158 us | 1.17x |
| HMAC-SHA-256 | 256 KiB | 187 us | 160 us | 1.17x |
| MD5 | 256 KiB | 504 us | 397 us | 1.27x |
| X25519 | -- | 48 us | 37 us | 1.28x |
| Ed25519 sign | -- | 66 us | 51 us | 1.30x |

HACL\* has no ML-KEM, so the ML-KEM numbers are absolute (same machine, gcc):

| operation | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |
| --- | ---: | ---: | ---: |
| keypair | 30 us | 50 us | 78 us |
| encapsulate | 36 us | 59 us | 89 us |
| decapsulate | 45 us | 71 us | 104 us |

The [design notes](design/notes.md#performance) have more:

* A second reference column with HACL\*'s portable C.
* The clang numbers.
* ML-DSA against pq-crystals, mldsa-native, AWS-LC, OpenSSL and libcrux.
* A comparison with OpenSSL, AWS-LC, libsodium, libjade, Firedancer and
  dalek.

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
