# hacl-pulse

A reimplementation of [HACL\*](https://github.com/hacl-star/hacl-star) in
modern F\*/Pulse, extracted straight to C by
[Custard](https://github.com/FStarLang/FStar/blob/gebner_custard/doc/ref/custard.md).

The goal is feature parity with HACL\*'s C and F\* APIs.  The design is not a
port: where HACL\* had to work around the absence of a language feature, this
library uses the feature.  `design/` records what HACL\* does and
`design/changes.md` the four commitments this reimplementation starts from.

Status: the SHA-2 family (SHA-224/256/384/512) is specified, implemented,
verified, extracted and tested against the FIPS 180-4 vectors.

```
make            verify, extract, compile, test
make verify     verify everything
make extract    (re)generate dist/
make test       build and run the C tests
```

You need an F\* built from the `gebner_custard` branch, through `stage3` (that
is, with the Pulse plugin and libraries installed).  Point the build at it:

```
make FSTAR_ROOT=$HOME/tools/fstar
```

## Layout

| directory | contents |
| --- | --- |
| `lib/` | the secret-integer layer, the `word` type class, generic byte serialization |
| `spec/` | pure specifications: `Spec.SHA2`, its constants and its lemmas |
| `code/` | Pulse implementations, one directory per family (`code/hash/`) |
| `tests/` | C test harnesses |
| `dist/` | generated C (one `.c`/`.h` pair per unit) |
| `design/` | the inventory of HACL\* that this library is measured against |

## The four design commitments

### Secret integers are types, not an index

HACL\* had a single `int_t t l` indexed by a width and a secrecy level.  Here
each secret width is its own abstract type in its own module —
`Hacl.Secret.UInt8.t`, `Hacl.Secret.UInt32.t`, `Hacl.Secret.UInt64.t` — whose
interface exposes only constant-time operations.  There is no comparison, no
division, no branch on a secret.  `Hacl.Secret.Cast` widens and truncates;
`Hacl.Secret.Declassify` is the single, `friend`-based escape hatch, so an
audit for "where does secret data become public" is a search for one module
name.

The types are abstract in their `.fsti` and equal to `FStar.UIntN.t` in their
`.fst`, so they cost nothing: `Hacl_Secret_UInt32_t` is `uint32_t` in the
generated C.

### Width-parametric code is a type class, not a tactic

HACL\* wrote generic code against `Lib.IntTypes` and then ran a custom
tactic to specialize the call graph.  Here `Hacl.Secret.Word.word` is an
ordinary F\* type class, and Custard monomorphizes it: a dictionary binder is
specialized by construction.  `Hacl.Hash.SHA2.Core` is written once against
`word`; the generated C has a `uint32_t` copy and a `uint64_t` copy, each
calling machine operations directly, with no indirection left.

The same mechanism replaces HACL\*'s algorithm index.  There is no `alg` type:
an algorithm *is* a `Spec.SHA2.params t` record, and the `p` binder carries
`[@@@FStar.Attributes.monomorphize]`, so the four algorithms become four
specialized C functions with their round counts and rotation amounts as
literals.

Two rules make this work, and both are worth knowing before writing new code:

* every field of `params` is either a machine value or `FStar.Ghost.erased`.
  A `nat` field would force Custard to give `params` a C representation, and
  `Prims.int` has none.  Hence `nrounds: SZ.t` with `rounds p = SZ.v p.nrounds`
  for specifications, and `k`/`iv` erased.
* the round-constant tables carry `[@@FStar.Custard.no_specialize]`, which
  stops the normalizer from unfolding them while it computes a specialization
  key.  They are sixty-four nested `Seq.upd`s; reducing that is both pointless
  (they are erased) and explosive.

### `size_t`, not 32-bit lengths

Every length, offset and count is `FStar.SizeT.t`.  Nothing in this library
assumes a 32-bit address space, and nothing needs a `uint32_t`-to-`size_t`
cast at the boundary.

### No assembly

There is none, and there is no Vale dependency.  Where a specific
microarchitecture matters the plan is C intrinsics behind the same `word`-style
interface; see `design/vale-migration`.

## How a hash is put together

Specifications are arithmetic.  `Hacl.Spec.Bytes` defines big-endian
serialization as `be_nat`/`nat_to_be` over `nat`, and the `word` class relates
a machine word to its value with `v` and `of_v` plus an extensionality lemma.
So `Spec.SHA2` never mentions a machine operation, and the implementation's
obligation is always of the form "this word's value is that number".

Specifications are also shaped like the loops that implement them.
`Hacl.Spec.Loops.repeati` unfolds on the *right*, so a `while` whose invariant
is `state == repeati i f acc` discharges its body obligation by one lemma call.
`ws_at` is defined slotwise and recursively, in the order the message schedule
is filled.  `set8` writes the eight state words in machine order.  This is a
deliberate trade: the specification is slightly less pretty than the standard's
prose and the proof is a great deal shorter.

The implementation is generic in `Hacl.Hash.SHA2.Core` — message schedule,
compression, padding, digest — and `Hacl.Hash.SHA2` names the four algorithms.
`Hacl.Hash.SHA2.Ptr` is the C API.

### Slices inside, pointers at the boundary

Internally everything is `Pulse.Lib.Slice.slice`, a pointer and a length that
travel together and that the verifier can reason about.  A slice extracts to a
two-field struct, which is not something a C caller should have to know about,
so the entry points in `Hacl.Hash.SHA2.Ptr` take `Pulse.Lib.ArrayPtr.ptr` and a
`size_t` and convert:

```c
void Hacl_Hash_SHA2_Ptr_sha256(uint8_t *out, uint8_t *input, size_t input_len);
```

The conversion is free at run time.

### The constant tables

`params.k` and `params.iv` are erased: they exist only in specifications.  At
run time each entry point allocates a stack array and stores the literals into
it.  The reason is that Custard has no compile-time array initializers — a
compound literal is not a constant expression at file scope — and the reason it
is cheap to *prove* is that a Pulse store yields `Seq.upd`, so the tables in
`Spec.SHA2.Constants` are written as chains of `Seq.upd`; the fill is equal to
the specification by unfolding rather than by a sixty-four-way case analysis.

The cost is sixty-four (eighty) stores per call, a few percent of one block and
nothing on a long message.  When the backend learns about constant globals the
`fill_*` functions can be deleted without touching anything else.

## Proof engineering notes

Non-obvious things that cost time here, recorded so they cost less next time:

* **Nonlinear arithmetic is off.**  `n * m >= 0`, `(j+1)*b == j*b + b` and
  `j*b <= n*b` are all *not* automatic, and the failure is usually reported as
  "the SMT query timed out" rather than as an unproved goal.  Reach for
  `FStar.Math.Lemmas.{distributivity_add_left, lemma_mult_le_right,
  multiple_division_lemma, multiple_modulo_lemma, euclidean_division_definition}`
  before reaching for `--z3rlimit`.
* **Prefer opaque parameters to derived expressions.**  A lemma over
  `base: nat` with `requires base == len / bl * bl` is cheap where the same
  lemma stated about `len / bl * bl` is hopeless.  Likewise, quantify over byte
  offsets rather than block indices, so no product appears in a trigger.
* **Split large Pulse functions.**  Query cost grows superlinearly in context
  size.  Each of `write_len_be`, `build_tail`, `hash_blocks` and
  `tail_and_finish` exists because the function that contained it could not be
  discharged at any rlimit, and became trivial once separated.
* **A Pulse `ensures` does not see the `requires`.**  Facts needed to typecheck
  a postcondition go in a refinement on the parameter, or as an earlier
  conjunct of the same `pure (... /\ ...)` — conjuncts are checked
  left-to-right.
* **Loop bodies see only the invariant.**  A fact established by a lemma call
  before the loop must be restated as an invariant conjunct.  Refinements on
  enclosing `let`s do carry in.
* **Class methods with no explicit argument need the dictionary written out.**
  `nbytes #t` is a partial application of a monomorphized binder and Custard
  rejects it; write `nbytes #t #w`.

## Roadmap

Following `design/reimplementation.md` §9, in dependency order: HMAC and HKDF
on top of the hashes, the streaming functor, SHA-3, BLAKE2, ChaCha20-Poly1305,
Curve25519, Ed25519, P-256, and the DRBG.
