# Notes for reimplementers

This chapter is the bridge between the descriptive chapters and an actual
port. It assumes a target language that is "similar to but different from F\*":
i.e. it has a real type system, some form of generics/monomorphization, and can
emit or interoperate with native code, but does not necessarily have F\*'s
dependent types, effect system or SMT-backed refinement checking.

---

## 1. Decide first: what are you reproducing?

HACL\* is simultaneously five things. You can port any subset, but you must
decide which, because they have very different costs.

| Aspect | Cost to reproduce | Can you skip it? |
|---|---|---|
| The **C API surface** (names, sizes, lifecycles) | Low | No, if you want drop-in compatibility |
| The **F\* API surface** (formal contracts + spec-level theorems) | High | Only if you have no verified clients — see below |
| The **implementation techniques** (representations, SIMD, tables) | Medium | Partially — but this is where the performance is |
| The **functional-correctness proofs** | Very high | Yes; replace with differential testing against the specs |
| The **secret-independence discipline** | Low-medium | No — this is cheap to keep and expensive to lose |

The recommendation: keep 1, 3 and 5 in full; replace 4 with an executable
specification plus exhaustive differential testing. Item 5 is the best
cost/benefit ratio in the whole project — a secret-integer newtype with a
restricted API costs a day and rules out an entire vulnerability class.

Item 2 deserves a deliberate decision rather than a default. HACL\* has two
distinct classes of consumers, and the second one is invisible if you only look
at the headers:

- **C consumers** need names, sizes and lifecycles.
- **Verified consumers** — clients that are themselves proved correct — call
  the library from F\* and use its postconditions and the theorems in `specs/`
  inside their own proofs. For them the *contract* is the API: a function with
  the right name but no stated postcondition is useless.

If you intend to serve verified consumers, the port is not "reimplement the
algorithms"; it is "reimplement the algorithms **and** re-establish the
specifications and their connection to the code" in whatever proof system your
target language offers. Concretely, the minimum you must reproduce is:

1. the pure specification layer (`specs/`) and the theorems it exports — see
   [fstar-specs.md](fstar-specs.md) for the full catalogue, and note that it is
   shorter than you might expect (there is, for instance, no exported
   sign-then-verify lemma for Ed25519, P-256 or K-256);
2. for each stateful function, a postcondition of the form
   `as_seq (output) == Spec.f (as_seq (inputs))`;
3. for each stateful object, the ghost accessors (`as_kv`, `seen`) that make
   such postconditions statable, plus the ownership footprint and invariant —
   see [fstar-api.md](fstar-api.md) §6;
4. framing: the guarantee that a call modifies nothing outside its declared
   footprint. Languages with ownership give this for free; languages without it
   need explicit `modifies`-style clauses.

See [fstar-api.md](fstar-api.md) §10 for a mechanism-by-mechanism table of
portable counterparts.

---

## 2. Suggested build order

The dependency structure of the library is close to a DAG, and following it
gives working, testable milestones.

1. **Integer and buffer layer.** Secret/public integer types; fixed-length
   array abstraction; byte (de)serialization in both endiannesses;
   constant-time comparison and selection. (`lib/Lib.IntTypes`,
   `Lib.ByteSequence`, `Lib.Buffer`.)
2. **Specifications.** Port `specs/` first, in the most naive form possible.
   These become your test oracle and your documentation. Do not optimize them.
3. **Hashes.** SHA-2 (the whole family), SHA-3/SHAKE, BLAKE2b/2s. These have no
   dependencies and unlock everything else.
4. **The streaming functor.** Implement buffering *once*, generically, as
   described in [implementation.md](implementation.md) §4. Retrofit it to the
   hashes. Resist the temptation to write per-algorithm `update` buffering.
5. **MACs and KDFs.** HMAC (over the hash interface), HKDF (over HMAC),
   Poly1305.
6. **Stream ciphers and AEAD.** ChaCha20, then ChaCha20-Poly1305. Salsa20 and
   the NaCl box API if you need them.
7. **The SIMD layer**, then re-instantiate 3/5/6 at 128- and 256-bit widths.
   Do this *after* the scalar versions are correct, and validate each width
   against the same vectors.
8. **Bignum and generic exponentiation.** Montgomery arithmetic; a generic
   windowed constant-time exponentiation over a monoid.
9. **Curves.** Curve25519, then Ed25519 (needs SHA-512 and the generic ladder),
   then P-256 and secp256k1 (both reuse the exponentiation machinery).
10. **RSA-PSS, FFDHE** (clients of bignum).
11. **The provider layer**: CPU detection, agile dispatch, agile state.
12. **HPKE, DRBG, FrodoKEM** if needed.

---

## 3. Reproducing the generic-code machinery

The central engineering problem is: *one algorithm, many instantiations,
each in its own translation unit, compiled with different flags.*

- If your language monomorphizes generics (Rust, C++, Zig, Go generics with
  care), you get specialization for free. What you must add by hand is the
  **one-instance-per-translation-unit-with-its-own-compile-flags** discipline.
  In Rust this is `#[target_feature]` plus separate modules and
  `is_x86_feature_detected!`; in C++ it is separate `.cpp` files with different
  `-m` flags; in Zig it is per-function CPU feature sets.
- If your language does not monomorphize, you need the equivalent of the
  specialize tactic: a build-time code generator that instantiates the generic
  call graph and emits one specialized module per index.
- Preserve the *call-graph shape*. Fully flattening the generic code into one
  giant function (what naive inlining gives you) makes the output unauditable
  and unmaintainable, and prevents substituting a single node with an assembly
  implementation.
- Keep the ability to replace one node (e.g. `double_round`, a field
  multiplication) with a hand-written assembly routine without disturbing the
  rest. That is requirement (iv) in `code/meta/DOCUMENTATION.md` and it is what
  makes the Vale integration possible.

---

## 4. Mapping the C ABI

If you want binary or source compatibility with `dist/gcc-compatible`:

| HACL\* concept | C rendering | Notes |
|---|---|---|
| Module path | `A_B_c` name mangling | Prefix may be rewritten by bundling |
| Nullary inductive | `#define`s + `typedef uint8_t` | Values fixed by source order — pin them explicitly in a port |
| Abstract state | pointer to incomplete struct | Client cannot size or stack-allocate it |
| Length/index | `uint32_t` | Never `size_t` |
| Byte buffer | `uint8_t *` | No length carried; passed separately |
| Ghost/erased value | *absent* | Proof-only arguments disappear entirely |
| `Stack` effect function | ordinary function, maybe with a VLA | `alloca` in the msvc distribution |
| `-static-header` module | `static inline` in a header | Duplicated per translation unit |
| `[@@ CIfDef ]` boolean | `#define` | Must be the *left* operand of `&&` to lift to `#if` |

Two ABI hazards to pin down deliberately in a port:

1. Enum numbering (see [surprises.md](surprises.md) §2).
2. The four incompatible error conventions ([surprises.md](surprises.md) §1).
   A new implementation should unify them; a drop-in replacement cannot.

---

## 5. What to keep from the state design

- **Heap-allocated, abstract, explicitly freed.** `malloc`/`free`/`copy`/`reset`.
  Do not expose the layout.
- **`digest` is non-destructive.** It finalizes a copy. Clients depend on this.
- **`copy` is a deep copy**, for the "hash a prefix then branch" pattern.
- **Allocation failure is signalled by `NULL`**, and the client must check.
  In a language with exceptions or `Result`, use that instead, but keep
  allocation failure explicit rather than aborting.
- Keep a 64-bit cumulative length counter internally even if chunk lengths are
  32-bit, and return a distinct "maximum length exceeded" error rather than
  wrapping.
- Zeroize state on `free` (the library uses `Lib_Memzero0_memzero`; see
  `lib/c/Lib_Memzero0.c`).

---

## 6. Testing strategy in the absence of proofs

The proofs are the expensive part. A practical substitute, in decreasing order
of value:

1. **Differential testing against your own specifications.** Because the specs
   are executable, every implementation can be property-tested against them on
   random inputs of random lengths. This catches the overwhelming majority of
   implementation bugs, especially in the buffering logic.
2. **Streaming-vs-one-shot equivalence.** For every incremental API, assert
   that feeding the same input in arbitrary random chunk splits yields the same
   digest as the one-shot call. This is exactly the `spec_is_incremental`
   proof obligation of the streaming functor, and it is easy to test.
3. **Cross-implementation equivalence.** Every vector width and every
   representation of the same algorithm must agree with the scalar one on
   random inputs. Force each dispatch path (the library provides
   `EverCrypt_AutoConfig2_disable_*` for exactly this reason).
4. **Official test vectors** (NIST CAVP, RFC vectors, Wycheproof). Necessary
   but far weaker than 1–3.
5. **Constant-time validation** with `valgrind`/`ctgrind` or `dudect`, since
   your type system's guarantee stops at the compiler boundary just like
   HACL\*'s does.
6. **Edge cases the type system used to cover**: zero-length inputs, lengths at
   block boundaries ±1, maximum lengths, aliased buffers (to confirm you
   document and detect them), all-zero and low-order curve points.

---

## 7. Where the preconditions went

Every generated function is the residue of a proof that assumed liveness,
disjointness, correct lengths and algorithm-specific bounds. None of that is
checked at run time. When porting, you must consciously decide, per function,
whether to:

- **keep the precondition** and document it (matches HACL\*, fastest);
- **check it and return an error** (safer, costs a branch — but note that
  length checks are on *public* data so this does not affect constant-timeness);
- **make it unrepresentable** using your type system (e.g. length-carrying
  slice types make most length preconditions statically impossible; borrow
  checking makes most aliasing preconditions statically impossible).

The third option is the reason a port to a language with slices and ownership
can be *safer* than the original C output while doing less work.

---

## 8. Things that will bite you

- **Endianness is not uniform across the library.** The 25519 family is
  little-endian; P-256/K-256 and RSA/FFDHE are big-endian. See
  [api-curves.md](api-curves.md) and [api-bignum.md](api-bignum.md).
- **Bignum sizes are counted in limbs, not bytes**, and the limb width is part
  of the module name.
- **Some functions allocate and return a buffer**; most do not. Mixing them up
  leaks memory or double-frees.
- **`_vartime` is a security-relevant suffix**, not a performance hint.
- **A `bool` return may mean "verification succeeded" or "input was valid" or
  "no error occurred"** depending on the function; check the specific
  signature.
- **In-place operation is only permitted where documented.** Assume disjoint
  unless told otherwise.
- **CPU dispatch must not cross a translation-unit boundary in the wrong
  direction**: never let a compiler that is allowed to emit AVX2 see the
  fallback function.

---

## 9. Minimum viable subset

If you only need "the algorithms a modern protocol stack uses", the following
subset covers TLS 1.3, Signal, WireGuard, JOSE and most of libsodium's surface,
and is roughly a third of the work:

- SHA-256/384/512, SHA-3/SHAKE, BLAKE2b/2s
- HMAC, HKDF
- ChaCha20-Poly1305 (+ AES-GCM if you can bind to assembly)
- X25519, Ed25519
- P-256 ECDH/ECDSA
- A DRBG plus an OS entropy shim
- The streaming layer for the hashes and HMAC

FrodoKEM, FFDHE, RSA-PSS, secp256k1, Salsa20/NaCl, MD5/SHA-1 and the generic
bignum API can all be deferred or skipped depending on your consumers.
