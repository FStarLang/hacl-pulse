# HACL\* / ValeCrypt / EverCrypt — design documentation

_The design, proofs and performance of hacl-pulse itself are in
[`notes.md`](notes.md). The rest of this directory is the inventory of
HACL\* that hacl-pulse is measured against._

This directory documents the design of the cryptographic library in this
repository, with two goals:

1. **A complete inventory of the public API** — for *both* audiences:
   - **C consumers**: every function, with its exact prototype, buffer sizes,
     preconditions and return conventions (`api-*.md`).
   - **Verified F\* consumers**: the `val` declarations, their formal
     pre/postconditions, and the spec-level theorems (such as
     `decrypt (encrypt p) == p`) that a verified client can actually use
     (`fstar-*.md`).
2. **A high-level description of the implementation**, with emphasis on the
   choices that are surprising or non-obvious.

It is written to be detailed enough that a team could reimplement the library
in a language similar to, but different from, F\*. Low-level implementation
minutiae (loop structure, proof engineering, SMT tactics) are deliberately out
of scope.

**Two APIs, two sources of truth.** The C chapters document the generated C in
`dist/gcc-compatible/`, the flagship distribution; every prototype quoted there
was copied verbatim and mechanically checked against the headers. The F\*
chapters document the `.fsti` interfaces in `code/`, `lib/`, `specs/` and
`providers/evercrypt/`; every signature quoted there was likewise checked
against the sources. The F\* interfaces are strictly more informative: they
carry the disjointness, liveness and length constraints that are erased in the
C output, and the functional-correctness postconditions that have no C
counterpart at all. As `providers/Documentation.md:46-50` puts it, "Instead of
looking at C header files, we strongly advise prospective users to read the
original F\* interface files."

---

## How to read this

Everyone reads chapters 1 and 2 first; the rest depends on which API you are
using.

| Order | Chapter | What it answers |
|---|---|---|
| 1 | [architecture.md](architecture.md) | What are the pieces, how do F\* sources become a `libevercrypt.a`, what is trusted? |
| 2 | [conventions.md](conventions.md) | What contract does *every* generated function obey — naming, types, buffers, ownership, error codes, constant-timeness? |
| 3a | `api-*.md` | **C track:** the complete public C API inventory. |
| 3b | `fstar-*.md` | **F\* track:** the verified-client API — contracts, specs, and available theorems. |
| 4 | [implementation.md](implementation.md) | How is the source organized, and how is one algorithm turned into many specialized implementations? |
| 5 | [surprises.md](surprises.md) | What will trip you up? |
| 6 | [reimplementation.md](reimplementation.md) | How would you actually port this? |

**If you call the library from C**, read 1, 2, the relevant `api-*.md`, then 5.
Chapter 2 §2 (exact C spellings of types and constants) is mostly mechanical
detail; skim it.

**If you call the library from F\* and want to verify your client**, read 1,
then [fstar-api.md](fstar-api.md) — the memory model, effects, the shape of a
contract, and the stateful abstraction pattern — then the relevant
`fstar-api-*.md`, then [fstar-specs.md](fstar-specs.md) for the theorem
catalogue and [fstar-client-guide.md](fstar-client-guide.md) for build setup
and proof idioms. The C chapters are still useful as a name index, since a
`val foo` in `Foo.Bar.fsti` extracts to `Foo_Bar_foo`.

**If you are reimplementing the library**, read everything, but note that the
F\* chapters carry the *specification* — the C chapters only carry the
signatures.

---

## API inventory chapters — C

| Chapter | Covers | Headers documented |
|---|---|---|
| [api-hashes.md](api-hashes.md) | MD5, SHA-1, SHA-2, SHA-3/SHAKE, BLAKE2b/2s, multi-buffer SIMD hashing, agile hashing | `Hacl_Hash_{MD5,SHA1,SHA2,SHA3,SHA3_Simd256,Blake2b,Blake2s,Blake2b_Simd256,Blake2s_Simd128,Base}.h`, `Hacl_SHA2_{Vec128,Vec256,Types}.h`, `Hacl_Streaming_Types.h`, `EverCrypt_Hash.h` |
| [api-macs-kdf.md](api-macs-kdf.md) | HMAC (all hashes), streaming HMAC, HKDF, Poly1305 (scalar + SIMD) | `Hacl_HMAC*.h`, `Hacl_Streaming_HMAC.h`, `Hacl_HKDF*.h`, `Hacl_MAC_Poly1305*.h`, `EverCrypt_{HMAC,HKDF,Poly1305}.h` |
| [api-aead-ciphers.md](api-aead-ciphers.md) | ChaCha20, Salsa20, AES, ChaCha20-Poly1305, AES-GCM, NaCl box/secretbox | `Hacl_AEAD_Chacha20Poly1305*.h`, `Hacl_Chacha20*.h`, `Hacl_Salsa20.h`, `Hacl_AES128.h`, `Hacl_NaCl.h`, `EverCrypt_{AEAD,Cipher,Chacha20Poly1305,Error}.h` |
| [api-curves.md](api-curves.md) | X25519, Ed25519, P-256 ECDSA/ECDH, secp256k1 ECDSA, raw EC arithmetic | `Hacl_Curve25519_{51,64}.h`, `Hacl_Ed25519.h`, `Hacl_EC_Ed25519.h`, `Hacl_P256.h`, `Hacl_K256_ECDSA.h`, `Hacl_EC_K256.h`, `EverCrypt_{Curve25519,Ed25519}.h` |
| [api-bignum.md](api-bignum.md) | Fixed and runtime-length bignums, Montgomery "generic field", RSA-PSS, FFDHE | `Hacl_Bignum{32,64,256,256_32,4096,4096_32}.h`, `Hacl_GenericField{32,64}.h`, `Hacl_RSAPSS.h`, `Hacl_FFDHE.h` |
| [api-pq-hpke-random.md](api-pq-hpke-random.md) | FrodoKEM, HPKE (all 15 variants), HMAC-DRBG, OS entropy, CPU detection, support headers | `Hacl_Frodo*.h`, `Hacl_HPKE_*.h`, `Hacl_HMAC_DRBG.h`, `EverCrypt_DRBG.h`, `Lib_RandomBuffer_System.h`, `EverCrypt_AutoConfig2.h`, `evercrypt_targetconfig.h`, `Hacl_Krmllib.h`, `lib_memzero0.h`, `libintvector.h`, `lib_intrinsics.h`, `Hacl_Spec.h` |

Coverage: essentially every function declared in the 98 public headers of
`dist/gcc-compatible` is documented. The only intentional omissions are the
test-only helpers in `TestLib.h`/`Lib_PrintBuffer.h` (described but not
enumerated) and macro/attribute noise in `libintvector.h`.

---

## API inventory chapters — F\* (verified clients)

| Chapter | Covers |
|---|---|
| [fstar-api.md](fstar-api.md) | **Start here.** The Low\* memory model (`HyperStack`, `loc`/`modifies`, the two buffer dialects, secret vs public integers), the effects (`Stack`/`ST`/`StackInline`/`GTot`), the anatomy of a `val`, CPU features as propositions, and the stateful abstraction pattern (`state_s`/`footprint`/`invariant`/`frame_invariant`) |
| [fstar-specs.md](fstar-specs.md) | The pure `specs/` layer: agile hash/AEAD/HMAC/HKDF/cipher/DH/HPKE specs, spec vocabulary, and a **catalogue of every exported lemma** — including explicit notes on theorems that do *not* exist (no Ed25519/P-256/K-256 sign-then-verify lemma; no ECDH commutativity lemma) |
| [fstar-api-hashes-macs.md](fstar-api-hashes-macs.md) | `Hacl.Hash.Definitions` vocabulary, the **streaming functor as an F\* API** (the `block` record, `seen`, `reveal_key`, framing lemmas), HMAC, HKDF, Poly1305, `EverCrypt.Hash` |
| [fstar-api-aead-ciphers.md](fstar-api-aead-ciphers.md) | `EverCrypt.AEAD` in full (the canonical stateful abstraction), `config_pre`, `encrypt_expand`, and the **end-to-end round-trip argument**; non-agile ChaCha20, ChaCha20-Poly1305, Salsa20, NaCl |
| [fstar-api-curves-bignum.md](fstar-api-curves-bignum.md) | Curve25519 (one signature, C and Vale implementations, differing CPU preconditions), Ed25519, P-256, K-256, bignum type classes, `SafeAPI`, RSA-PSS, FFDHE, and what `_vartime` does and does not mean in the type system |
| [fstar-api-provider.md](fstar-api-provider.md) | `EverCrypt.AutoConfig2` (`getter`, the `b ==> flag` postcondition), `EverCrypt.TargetConfig` and the `CIfDef` left-operand rule, the Vale interop boundary, randomness (a trusted shim), DRBG, the HPKE specialization tactic, FrodoKEM |
| [fstar-client-guide.md](fstar-client-guide.md) | Build setup (`Makefile.include`, `Hacl.fst.config.json`, hints, Z3 pinning), an **annotated real client** from `providers/test/Test.fst`, how to prove the AEAD round trip, recurring proof idioms, and a pitfalls table |

---

## The two API layers, in one paragraph

`Hacl_*` gives you **standalone, self-contained implementations**: one C file
per algorithm, per representation, per vector width. You choose the
implementation; you are responsible for knowing whether the CPU supports it.
`EverCrypt_*` gives you **agility** (algorithm selected by a runtime enum
argument) and **multiplexing** (implementation selected by runtime CPU
detection, including dispatch into verified assembly). Most clients should use
`EverCrypt_*`; clients that already do their own CPU detection, or that want a
minimal binary, should use `Hacl_*` directly. Both layers are verified; the
EverCrypt layer additionally provides higher-level APIs, such as the agile
incremental hash, that have no `Hacl_*` equivalent.

In the F\* API this distinction is visible *in the types*: the specialized
`Hacl.Curve25519_64.scalarmult` requires the caller to prove
`adx_enabled /\ bmi2_enabled`, while `EverCrypt.Curve25519.scalarmult` has the
same postcondition with **no CPU precondition at all**. Multiplexing is
precondition weakening. See [fstar-api.md](fstar-api.md) §5.

---

## The two API *audiences*, in one paragraph

A C client gets names, signatures, and documentation. A verified F\* client
gets machine-checked pre/postconditions, so that length errors, aliasing
errors, use-of-uninitialized-state errors and protocol-order errors become
compile-time failures — and gets the functional-correctness postconditions,
which connect the code to the pure specifications in `specs/` and make theorems
such as `Spec.Agile.AEAD.correctness` (`decrypt k n aad (encrypt k n aad p) == Some p`)
usable in the client's own proofs. Some invariants are *only* enforced for the
verified audience; as `EverCrypt.AEAD.fsti:10-11` says of the key-expansion
protocol, it "is enforced for verified F\* clients but, naturally, isn't for C
clients." Any reimplementation that intends to serve verified customers must
reproduce the *specifications*, not just the entry points.

---

## Quick orientation for a reimplementer

The six ideas that most shape this codebase:

1. **Specification / implementation split.** A pure, naive, executable spec
   (`specs/`) is the correctness oracle; the optimized implementation is proved
   equal to it. Port the specs first — they are your test oracle *and*, for
   verified clients, the vocabulary in which every theorem is stated.
2. **The specification *is* the API for verified clients.** Every stateful
   function's postcondition has the shape
   `as_seq (output) == Spec.f (as_seq (inputs))`, and stateful objects expose
   ghost accessors (`as_kv`, `seen`) that play the same role. Reproducing the
   C entry points without reproducing these contracts serves only half the
   userbase. See [fstar-api.md](fstar-api.md).
3. **Secret independence by typing.** Secret integers admit no comparison,
   division, branching or indexing. Constant-timeness is a type property, not
   an audit result.
4. **Monomorphization with structure.** One generic algorithm becomes many
   fully specialized implementations — each in its own translation unit, so
   that each can be compiled with different CPU-feature flags — while
   preserving the call-graph shape and the ability to swap a single node for
   assembly.
5. **Buffering implemented once.** A single streaming *functor* turns any
   block-based algorithm into an incremental API, with a uniform
   `malloc`/`reset`/`update`/`digest`/`free`/`copy` lifecycle and a
   non-destructive `digest`.
6. **Compile-time and run-time configuration are separate axes.**
   `HACL_CAN_COMPILE_*` macros say what the toolchain can build;
   `EverCrypt_AutoConfig2` says what the current CPU supports, defaults to
   all-disabled, and must be explicitly initialized. In F\*, CPU features are
   *propositions*, and detection functions return a proof-carrying boolean
   (`b ==> flag`) — effectively a capability. This idea ports well to
   languages without a prover.

Start with [reimplementation.md](reimplementation.md) §2 for a suggested build
order, and [fstar-api.md](fstar-api.md) §10 for a table mapping each F\*
mechanism to a portable counterpart.

---

## Relationship to `doc/`

`doc/` is the user-facing Sphinx manual published at
[hacl-star.github.io](https://hacl-star.github.io) — a tutorial-style
introduction for consumers of the library. This `design/` directory is
complementary: it is exhaustive rather than pedagogical, targets people
reimplementing or deeply integrating the library, and documents the generated
artifact rather than the recommended usage.
