# hacl-pulse: design and engineering notes

_This document used to be the top-level README; the short
version is now [`README.md`](../README.md)._

A reimplementation of [HACL\*](https://github.com/hacl-star/hacl-star) in
modern F\*/Pulse, extracted straight to C by
[Custard](https://github.com/FStarLang/FStar/blob/master/doc/ref/custard.md).

The goal is feature parity with HACL\*'s C and F\* APIs.  The design is not a
port: where HACL\* had to work around the absence of a language feature, this
library uses the feature.  `design/` records what HACL\* does and
`design/changes.md` the four commitments this reimplementation starts from.

Status: **feature parity with HACL\***, and past it in places -- all four
FrodoKEM parameter sets are here, HPKE is here in all four modes where
HACL\* ships only Base and only over ChaCha20-Poly1305, and ML-KEM
(FIPS 203) and ML-DSA (FIPS 204) are here in all three parameter sets
each, which HACL\* does not have at all.  The one deliberate omission
is an agile provider in the shape of EverCrypt; see the roadmap below.
Everything listed there is specified, implemented, verified, extracted and
tested against the published vectors -- FIPS 180-4, FIPS 202, RFC 4231,
RFC 5869, RFC 7748, RFC 8032, RFC 7919, RFC 9180, FIPS 186-4, PKCS#1 v2.2,
the NIST CAVP sets for AES-GCM and HMAC-DRBG, the FrodoKEM known-answer
tests, the NIST ACVP vectors for ML-KEM and ML-DSA, and the NaCl vectors --
thirty-four C test harnesses in `tests/`.

Performance is measured against HACL\* configured for the machine and allowed
everything it has -- Vale assembly, AVX2, BMI2/ADX -- because that is what a
caller choosing HACL\* would actually get.  On that comparison SHA-3, SHAKE,
SHA-512, HMAC-SHA-512 and BLAKE2b are faster, most of the suite is
within 20%, and the remaining ceiling is the three primitives where AVX2
lanes are worth four to five times a scalar implementation: ChaCha20,
Poly1305 and ChaCha20-Poly1305.  Against HACL\*'s *portable* C -- the
like-for-like comparison, same algorithm and same instruction set -- the
hashes are all ahead and what is behind is the elliptic curves, where what
is left is the scalar multiplication rather than the field.  Modular exponentiation --
RSA-PSS, FFDHE and the generic modexp -- has crossed over: a 4-bit window, a
four-at-a-time inner row and a triangle squaring put all three of those rows
between 0.92x and 0.97x, faster than the reference.  On the curves: P-256's variable-base ECDH
is now *faster* than the reference at 0.76x, secp256k1's is within 1.39x and
X25519 within 1.26x, now that the first two walk their scalars four bits at
a time, as Ed25519 now does too, and now that all three of the curves with a
generator multiply it out of four compiled-in base points rather than one.
P-256 is the one that gained most from the latter, and it has since had a
field specialised to its prime as well, which puts every operation at
0.50x-0.78x of the reference under gcc.  Ed25519 and secp256k1 go
further still and compile in the whole of their fixed-base windows,
sixty-four precomputed multiples of the generator apiece: Ed25519 signing and
key generation are within 1.23x under gcc and 1.37x under clang, and
secp256k1 signing is within 1.15x and `secret-to-public` within 1.24x, now
that its small multiples -- twenty-one, eight, three, two -- are a
limb-by-limb multiply rather than a full field multiplication.  The clang
numbers on all of these rose when the secret-indexed table read was made
genuinely constant-time; see [The compiler is allowed to undo a
constant-time algorithm](#the-compiler-is-allowed-to-undo-a-constant-time-algorithm).
See
[Performance](#performance).

```
make            verify, extract, compile, test
make verify     verify everything
make extract    (re)generate dist/
make test       build and run the C tests
make cross      compile the C for aarch64 and run the tests under qemu
```

You need an F\* with the Pulse plugin and libraries installed, new enough to
have Custard.  A [nightly build](https://github.com/FStarLang/FStar-nightly/releases)
is one -- the tarballs ship Pulse -- and so is a checkout of `master` built
through `stage3`.  Point the build at either:

```
make FSTAR_ROOT=$HOME/tools/fstar-nightly-2026-10-21   # unpacked nightly
make FSTAR_ROOT=$HOME/tools/fstar                      # source checkout
```

The tree tracks `master`: it is verified against the `nightly-2026-10-21`
build above, and nothing older is supported.  F\* changes the encoding its
proofs rest on often enough that supporting a past release means carrying
workarounds for a solver that no longer exists, which is a worse use of the
effort than following `master` and fixing what breaks.

## Layout

| directory | contents |
| --- | --- |
| `lib/` | the secret-integer layer, the `word` type class, generic byte serialization, compile-time tables, wiped scratch memory (`Hacl.Mem`) |
| `spec/` | pure specifications: `Spec.MD5`, `Spec.SHA1`, `Spec.SHA2`, `Spec.SHA3`, `Spec.Blake2`, `Spec.Chacha20`, `Spec.Salsa20`, `Spec.Poly1305`, `Spec.Poly1305.Vec`, `Spec.Curve25519`, `Spec.Ed25519`, `Spec.P256`, `Spec.K256`, `Spec.AES`, `Spec.GF128`, `Spec.GF128.Algebra`, `Spec.GCM`, `Spec.CarryLess`, `Spec.CLMUL`, `Spec.Chacha20Poly1305`, their constants and lemmas, `Spec.HMAC`, `Spec.HMAC.SHA1`, `Spec.HKDF`, `Spec.HMAC_DRBG`, `Spec.FFDHE`, `Spec.RSAPSS`, `Spec.NaCl`, `Spec.Frodo` and its matrix and parameter modules, `Spec.HPKE`, `Spec.MLKEM` and its NTT (with the ring-isomorphism proof `Spec.MLKEM.NTT.Lemmas`), sampling and encoding modules, `Spec.MLDSA` and its parameter, field, NTT, sampling, rounding and encoding modules, with their lemmas and the sign-then-verify proof `Spec.MLDSA.Correctness` |
| `code/` | Pulse implementations, one directory per family (`code/hash/`, `code/chacha/`, `code/salsa20/`, `code/poly1305/`, `code/curve25519/`, `code/ed25519/`, `code/field256/`, `code/p256/`, `code/k256/`, `code/drbg/`, `code/aes/`, `code/bignum/`, `code/ffdhe/`, `code/rsapss/`, `code/aead/`, `code/nacl/`, `code/frodo/`, `code/mlkem/`, `code/mldsa/`, `code/hpke/`) |
| `c/` | handwritten C, and the whole of the trusted computing base on the C side: the platform entropy shim, the 128- and 256-bit vector intrinsics, the 64-bit add-with-carry / subtract-with-borrow used by X25519, and the memory wiping in `Hacl_Mem.h` |
| `tests/` | C test harnesses |
| `dist/` | generated C: one `Hacl.c`, one `Hacl.h` |
| `design/` | the inventory of HACL\* that this library is measured against |

## The five design commitments

### Secret integers are types, not an index

HACL\* had a single `int_t t l` indexed by a width and a secrecy level.  Here
each secret width is its own abstract type in its own module —
`Hacl.Secret.UInt8.t`, `Hacl.Secret.UInt32.t`, `Hacl.Secret.UInt64.t`,
`Hacl.Secret.UInt128.t` — whose interface exposes only constant-time
operations.  There is no comparison, no
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
microarchitecture matters the answer is a C intrinsic behind a narrow,
axiomatized interface, verified against the same specification as the portable
code and tested against an independent transcription of the standard: AES-NI,
`AESKEYGENASSIST` and `PCLMULQDQ` under AES-GCM (`lib/Hacl.Vec128.fst`), the
Intel SHA extensions under SHA-256 and SHA-224, AVX2 under ChaCha20,
Salsa20 and Poly1305 (`lib/Hacl.Vec256.fst`) and under the four-way Keccak
behind the ML-KEM matrix (`lib/Hacl.Vec256.Lane64.fst`) and the ML-DSA
transforms (`lib/Hacl.Vec256.Lane32.fst`), and AVX-512F under ChaCha20
and Salsa20 (`lib/Hacl.Vec512.fst`).  Each is selected at run time by
`__builtin_cpu_supports`.  See `design/vale-migration`.

### Scratch memory is wiped, and its size is ours

Every array the library allocates goes through `lib/Hacl.Mem.fsti`, and is
zeroed before it is released:

```
let mut buf = [| z; n |];      let h = Mem.alloc z n;
Mem.track buf;                 ...
...                            Mem.free h n;
Mem.wipe buf n;
```

`track` produces a ghost resource `must_wipe buf` and only `wipe` consumes
it; `alloc` produces `must_free h` and only `free` consumes it.  Pulse
rejects a function that ends holding a resource, so a forgotten wipe is a
type error ("Leftover resources: Mem.must_wipe buf"), not a review comment.
The wiping is a `memset` followed by an empty `asm` that takes the buffer
as a memory input, which stops the compiler deleting it as a dead store
(`c/Hacl_Mem.h`, trusted).  `free` wipes and then calls `free(3)`; a failed
`malloc` aborts.

The one exception is `Mem.nowipe`, which releases `must_wipe` without
wiping.  It is for the temporaries of the hottest leaves -- the Curve25519
and P-256 field multiplications and squarings, and the Keccak state of
one-shot SHA-3 -- which gcc otherwise keeps in registers.  Wiping them takes
their address and pushes every intermediate value through memory: x25519
becomes 45% slower, P-256 10%, a short SHA-3 twice as slow.  What they leave
behind is in register spill slots, which no wipe reaches anyway; their
callers still wipe everything they hold.

The size of a stack array is never chosen by the caller.  Anything whose
size depends on an argument -- RSA's limbs and PSS buffers, the
`mod_exp_consttime` window table -- or is merely large -- FrodoKEM's
matrices -- is on the heap.  HKDF and HPKE, which used to copy `info` onto
the stack, now stream it; see "HKDF without a buffer the caller sizes".

Two build checks keep it that way (`mk/lint.mk`, both part of `make`).
`make lint` requires every `let mut x = [| ... |]` to be followed by
`Mem.track x`, and forbids `Pulse.Lib.Vec`, `Pulse.Lib.Box`, `with_local`,
`Array.alloc` and `drop_` outside `Hacl.Mem`, and `nowipe` outside the
functions listed in `mk/memlint.pl`.  `make stack` compiles
`dist/Hacl.c` with `-fstack-usage` and fails on any frame gcc cannot bound,
or any frame larger than `STACK_MAX`.

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
`Hacl.Hash.SHA2` is also the C API: there is no wrapper layer.

### Arrays all the way out

Every buffer in the library is a `Pulse.Lib.Array.array`, which extracts to a
bare `t *`.  So an F\* entry point *is* the C entry point, and its name is its
F\* name with the dots turned into underscores:

```c
void Hacl_Hash_SHA2_sha256(uint8_t *out, uint8_t *input, size_t input_len);
```

An array's length is ghost, so a function over a variable-length buffer takes
the length as an ordinary `size_t` argument with `SZ.v input_len == Seq.length
vin` in its precondition.  That is exactly the argument the C signature wants
anyway, and it means fixed-size buffers — a 32-byte key, a 16-byte tag — carry
no length at run time at all.

This replaced an earlier design in which the internals used
`Pulse.Lib.Slice.slice` (a pointer and a length travelling together) and a
`Hacl.*.Ptr` module converted at the boundary.  A slice extracts to a two-field
struct, so the wrapper layer was not optional; and since almost every length in
a cryptographic primitive is a compile-time constant, the length field was dead
weight in most of the library.  Sixteen wrapper modules and about two thousand
lines of C went away with it.

### The constant tables

`params.k` and `params.iv` are erased: they exist only in specifications.  At
run time the tables are `static const` arrays in the program image,

```c
static const uint32_t Hacl_Hash_SHA2_Tables_k256_arr[64] = { 0x428a2f98U, ... };
```

which is `Pulse.Lib.GlobalArray`: `mk_static_array` takes a list that has to
reduce to a literal, and the elements become the C initializer directly.  The
one thing the axiomatization does *not* hand out is write permission — the
postcondition of `array_of_static_array` gives an existential fraction and
never a full one — which is what licenses the `const`, and which means a table
is acquired and never released.  `Hacl.Impl.Table` is the three lines that
turn one into an array, and `drop_table` gives the (fractional) permission
back.

`table` is `inline_for_extraction`, and has to be.  A `static_array` is
represented as a plain `t *`, and the `const`-discarding cast is emitted at the
`array_of_static_array` call; inside an out-of-line generic helper that call
sees a parameter, by which point the `const` is already gone and the *caller*
is the one that trips `-Werror=discarded-qualifiers`.  Inlining puts the cast
on the named global, where it belongs.

Each table is written once, as a list, in the spec module; the sequence the
specification uses is `Seq.seq_of_list` of it, which is definitionally what
the global array contains.  So the table the linker lays out and the table the
proof is about are the same literals, and no lemma relates them.

That identity lives in the array's *type*:

```fstar
let k256_arr : (a: G.static_array S32.t
                  { G.static_array_elems a == (k256 <: Seq.seq S32.t) })
  = G.mk_static_array k256_list
```

and not in a lemma, because a lemma with one conjunct per table puts six
sixty-four-element lists into a verification condition that already carries a
heap.  In the type each fact arrives on its own; the length comes with it,
since `k256` is an `lseq`.  Even so, `k512` at eighty entries needs
`--z3rlimit 40` at the four call sites where the equation has to be seen
through `params512_with`'s record projection; `k256` at sixty-four does not.

Keccak's rho offsets are the one place the list is a second copy: `rotc` is a
readable twenty-five-way `match` returning a `nat`, and `Seq.init 25 rotc` is
a call rather than a literal spine.  `rotc_seq_ok` is a machine-checked
cross-check of the list against the `match`, which is what makes writing the
offsets twice safe rather than merely convenient.

The previous revision of this library filled the tables at run time, sixty-four
stores per call, because Custard had no array-literal node: `BufCreate` fills a
run uniformly, and a compound literal is not a constant expression at file
scope.  Deleting the `fill_*` functions took nothing with it, as predicted.

### HMAC without copying the message

HMAC hashes `K0 ^ ipad || msg`.  Building that concatenation would mean either
a copy of the whole message or a streaming interface, and HACL\* does the
latter.  Here the hash is instead generalized once: `hash_blocks` and
`tail_and_finish` take a *ghost* block-aligned prefix `pre` and compute over
`Seq.append pre vin` while touching only `vin`, and `hash_prefixed` absorbs one
real prefix block and then reads the caller's buffer directly.  `hash_impl` is
the instance where `pre` is empty.

`Hacl.HMAC.Core` then allocates exactly three small buffers — the padded key,
one scratch block that holds `K0 ^ ipad` and later `K0 ^ opad`, and one digest
— and calls `hash_prefixed` twice.  HMAC of a gigabyte costs the same memory as
HMAC of a byte, with no state machine.  `hash_prefixed` is also what the
incremental interface is built on; see below.

That generality had a cost that took a while to see.  `hash_prefixed` is
generic in the word type, so it cannot branch into the SHA-EXT
implementation, which exists only at thirty-two-bit words -- and the
dispatch on `sha_supported ()` lived only in the one-shot hash.  HMAC-SHA-256
therefore ran scalar compression rounds on a machine whose plain SHA-256 was
issuing `sha256rnds2`, and cost five times what hashing the same bytes cost.
There is no way for code at an abstract word type to obtain the equality
witness it would need, and an implementation-dispatch method has no business
in a typeclass that is otherwise a statement about values, so
`Hacl.Hash.SHA2.NI.hash_prefixed_ni` and `Hacl.HMAC.NI.hmac_impl_ni` are
transcriptions at `S32.t`, in the same way `hash_blocks_ni` already was.
`hmac_sha224` and `hmac_sha256` pick between them at run time.  A 256 KiB
HMAC-SHA-256 went from 1,136 us to 227 us, which is exactly what hashing
256 KiB costs.

### HKDF without a buffer the caller sizes

`expand` hashes `T(i-1) || info || i` once per round.  An earlier version laid
that out in one stack buffer of `hb + |info| + 1` bytes, which let whoever
supplied `info` choose the size of our stack frame (issue #1).  Now each round
is one call to `Hacl.HMAC.Cat.hmac_cat`, which takes the message in four
pieces and streams them through the incremental hash:

```
hmac_cat prk  T(i-1)  pre  info  [i]
```

so the only scratch is two digests and a counter byte, whatever `info` is.
`pre` is a second piece of `info`: HPKE's `LabeledExpand` puts a few dozen
bytes of labels in front of the caller's string, and passing them as their
own piece means neither side is ever copied.  Plain HKDF passes an empty
`pre`, as round 1 passes an empty `T(0)` -- a zero-length window of a one-byte
array, using `Hacl.Impl.Sub`.

The loop invariant never mentions `expand_all` at the round count reached so
far; it is stated against the *final* count, so that on exit it is literally
the postcondition.  `Spec.HKDF.expand_all_index_le` -- `expand_all` at `n`
agrees with `expand_all` at any `m <= n` on the first `m` digests -- is what
lets a round establish it.  The loop measure is the round counter, not the
bytes remaining: the last round overshoots the requested length, so
`len - base` is not a `nat`.

**The block function is an argument.**  Generic code cannot branch into the
SHA extensions, which exist only at thirty-two-bit words, and expand used to
be transcribed at `S32.t` for that reason -- a third copy of the shape after
`hash_blocks_ni` and `hmac_impl_ni`.  Instead, `Hacl.Hash.SHA2.Core.blocks_t`
is the type of `hash_blocks` without its block-length argument; the
incremental hash (`update_with`), `hmac_cat` and `expand_impl` take one as a
`[@@@monomorphize]` parameter; and `expand_sha256` passes
`Hacl.Hash.SHA2.NI.blocks_ni sha2_256` or `blocks_scalar sha2_256` depending
on `sha_supported ()`.  Custard specialises each call site into its own C
function, so there is no indirect call, and there is one proof.
`Hacl.HMAC.DRBG.Core`, `Hacl.HPKE.Labeled` and `Hacl.Streaming.HMAC` still
pass `blocks_scalar`; giving them the SHA extensions is now a one-argument
change each.

### The incremental hash

The streaming state is not a heap-allocated object with a constructor, a
destructor and an error code.  It is three flat pieces of memory that the
caller owns:

```c
uint32_t acc[8];    /* the accumulator */
uint8_t  buf[64];   /* one block of buffered bytes */
size_t   total;     /* how many bytes have been absorbed */
```

plus, ghostly, the message `seen` so far.  A caller who wants a struct can put
the three in one; the library does not need to know.  There is no `malloc`, so
there is no allocation failure to report, and no `free` to forget.

The invariant, `Hacl.Hash.SHA2.Streaming.stream_ok`, says three things: the
accumulator is `absorb p seen (|seen| / bl)`, the first `|seen| % bl` bytes of
the buffer are the bytes of `seen` past its last whole block, and `total` is
`|seen|`.  The buffer is therefore always *strictly* partial: `update` absorbs
it the moment it fills, rather than leaving a full buffer for the next call to
deal with, which is what makes the invariant a single equation instead of a
disjunction.

`update` fills the buffer, and if that filled it, absorbs it and then absorbs
whatever whole blocks follow *directly out of the caller's data* -- no copy --
keeping only the trailing partial block.  That is the same ghost-prefix trick
HMAC uses: `absorb_blocks` hands `hash_blocks` a prefix length and a window,
and `Spec.SHA2.Streaming.absorb_congr` -- absorbing `n` blocks only looks at
the first `n * bl` bytes, so two messages that agree that far absorb alike --
is what bridges "the bytes in this buffer" to "the bytes of `seen`".

`digest` copies the accumulator to the stack and finishes there, so the state
survives: digesting twice gives the same answer, and updating after a digest
continues the same message.  `tests/test_streaming.c` checks both, and checks
the FIPS 180-4 messages fed in nine different chunk sizes chosen to straddle
the block boundary from both sides.

`Hacl.Streaming.SHA2` names the four algorithms and is the C ABI.  One wart: `total` is a `size_t`, so on a 32-bit target a single
state tops out at four gigabytes.  That follows from using `FStar.SizeT` for
every length (see `design/changes.md`); the one-shot interface has the same
limit, and HACL* does not.

### The incremental HMAC, which is an incremental hash plus one block

HMAC is two hashes, but only the inner one ever sees the message, so an
incremental HMAC is an incremental SHA-2 state and one more block:

```
acc, buf, tot   the inner hash, which has already absorbed K0 ^ ipad
opadb           K0 ^ opad, kept for the outer hash
```

`init` derives `K0` from the key, absorbs `K0 ^ ipad` and saves `K0 ^ opad`;
`update` is the inner hash's `update` and nothing else, so it costs exactly
what a bare SHA-2 `update` costs; `digest` finishes the inner hash into a
stack digest and calls the one-shot `hash_prefixed` on `K0 ^ opad` and that
digest.  The key is consumed by `init` and is not part of the state.

The state invariant is one line:

```fstar
unfold let hmac_ok p key vacc vbuf vtot vopadb msg =
  Seq.length key < max_input #t /  stream_ok p vacc vbuf vtot (Seq.append (xor_byte #t (key_block p key) ipad) msg) /  vopadb == xor_byte #t (key_block p key) opad
```

which is to say: the inner stream has seen `K0 ^ ipad` followed by the
message.  Everything else follows from the SHA-2 streaming contract, and
`Hacl.Streaming.HMAC.Core` is under two hundred lines.

Getting there needed one change underneath.  `digest_impl` pads the trailing
partial block on the stack and only *reads* `buf`, but its postcondition used
to leave `buf`'s contents existentially quantified, which threw the state
invariant away.  Taking `buf` at a fractional permission and returning it
unchanged is both truer and more useful: `stream_ok` survives a digest, so a
caller may digest twice or keep absorbing afterwards, which is what
`Hacl.Streaming.HMAC` needs and what the SHA-2 layer had always been able to
promise.  `tests/test_hmac_streaming.c` checks all three.

HACL\*'s streaming HMAC is *agile*: the implementation is chosen at run time
from an enum, the state is heap-allocated behind an abstract pointer, and
there is a `copy` and a `free`.  Here, as everywhere else in this library, the
algorithm is chosen at compile time by which function you call and the state
is four arrays the caller declares — so there is no allocation, no destructor
and no error code, and a `copy` is `memcpy`.

### The sponge

SHA-3 shares almost nothing with SHA-2, so it gets its own stack:
`Spec.SHA3.Constants` (the round constants and rotation offsets),
`Spec.SHA3` (the spec), `Hacl.Hash.SHA3.Core` (Keccak-f[1600]),
`Hacl.Hash.SHA3.Sponge` (absorb and squeeze), `Hacl.Hash.SHA3` (the six named
algorithms, which is also the C ABI).

Two things are different from the SHA-2 stack.

*The spec is written over secret words, not `nat`.*  Everywhere else the spec
speaks in mathematical integers and the implementation refines them, because
everywhere else the algorithm is arithmetic.  Keccak is purely bitwise:
rotate, xor, and-not.  A `nat`-level description would say nothing the word
level does not, and the refinement proof would be pure noise, so `Spec.SHA3`
is stated directly over `Hacl.Secret.UInt64.t` and the implementation's
correctness argument is an indexwise equality of `Seq`s.

*The rate is a runtime value.*  SHA3-224/256/384/512 and SHAKE128/256 differ
only in the rate, the domain-separation byte and the output length, so there
is one copy of the sponge, taking all three as arguments, and six thin
wrappers.  The state is a 25-lane `A.array S64.t` indexed `x + 5*y`, matching
the spec's flattening, plus a second 25-lane buffer the rounds alternate
with.

**A round is one pass over the state.**  theta, rho-pi, chi and iota are
fused, as in the Keccak team's reference code: `fround` reads its 25 input
lanes once, computes the five column parities and theta's five fold-back
values in registers, and then for each output row forms the five rho-pi
lanes as `rotl(a[src] ^ d[col], rho)` and writes chi of them (with the
round constant on lane 0) straight to the other buffer.  Rounds alternate
`st -> b` and `b -> st`, two to a loop trip.  The earlier round did theta in
place, rho-pi into the scratch buffer and chi back -- three read-write sweeps
of the state per round.  Each register value carries a postcondition naming
its entry of `rho_pi (theta a)` (`bval`), and each store a prefix invariant
against `round n a` (`chi_out`); the indices are literals, and
`Spec.SHA3.rho_pi_src_lit` and `chi_nbr_lit` hand the solver
`rho_pi_src 7 == 10` and its like as ground facts, because evaluating `% 5`
and `/ 5` on literals inside a 50-call Pulse context did not finish in
fifteen minutes and with the facts takes forty seconds.  `Core4` is the same
round with vector lanes and its own opaque predicates (`b_ok`, `fr_pre`).
Against the three-pass round, under gcc, SHA3-512 and SHAKE128 are 1.13x
faster on long inputs and SHA3-256 1.08x, ML-KEM 1.04x and ML-DSA
1.02x--1.09x (Part 81 of `bench/REPORT.md`); the four-way permutation alone
went from 1617 to 1176 cycles.

Absorb xors whole message blocks straight out of the caller's buffer, and
stages only the last, padded, block in a 200-byte stack buffer — 200 rather
than the rate because the rate is not known at compile time.  Squeeze emits
`min(rate, remaining)` bytes per permutation, and does not permute after the
last block (`permute_if`), so a SHAKE call shorter than the rate does
exactly one permutation and a long one does not overrun.  The streaming
XOFs the ML-KEM and ML-DSA samplers use (`xof_block`) permute on the way in
instead, for every block but the first, so the block a sampler stops at
is not followed by a permutation either.  They squeeze with
`squeeze_block_lanes`, a whole lane (eight constant shifts, which compilers
merge into one store) at a time and then any bytes of a final partial lane;
the one-shot sponges keep the byte loop, because inlined next to the
absorb rounds the lane loop perturbs gcc's register allocation of the
round loop and costs SHA3-256 six percent.  ML-DSA's `xof_block` is
`inline_for_extraction`, so each sampler gets a copy with its rate fixed.

**Four permutations at a time, on AVX2.**  `Hacl.Hash.SHA3.Core4.permute4`
runs Keccak-f[1600] on four independent states at once, one 64-bit lane of
each per 256-bit register, and proves `w_k == permute v_k` for each.  The
ML-KEM matrix is `k * k` independent SHAKE128 rejection samplers, so
`Hacl.Impl.MLKEM.Sample4` runs four of them in lock step: each stream is the
scalar sampler's state, read block by block with the same `squeeze_block_lanes`
and fed to the same `block_impl` (whose acceptance test is branch-free:
every candidate is stored, reduced by `csub` so that it is a valid
coefficient, and the count advances by the borrow bit of `d - q`; a random
one-in-five rejection is the worst case for a branch predictor), and only the permutations are shared --
the one that ends each absorb (`absorb_pre` is `absorb_impl` without it) and
the one before every squeezed block after the first.  `gen_matrix_impl`
takes four entries at a time while four remain and the processor has AVX2,
and one at a time otherwise.  ML-DSA's `ExpandA` is the same idea:
`Hacl.Impl.MLDSA.Sample4` runs four `RejNTTPoly` streams over the same
scalar `block128_impl`, borrowing ML-KEM's `shake128_absorb_pre` and
`permute4_if`, and its `expand_a_impl` takes four of the 16, 30 or 56
entries at a time (ML-DSA-65's last two go one at a time).  Key generation
and verification, of which `ExpandA` was half, got 1.24x--1.35x faster and
signing 1.04x--1.11x (Part 82 of `bench/REPORT.md`).  The noise vectors are the same idea for SHAKE256:
`Hacl.Impl.MLKEM.PRF4` computes four `PRF_eta(s, b_j)` with one
`permute4` ending the four 33-byte absorbs and, for `eta = 3`, a second one
for the four second blocks, and `noise_vec_impl` calls it once per vector
(the lanes past `k` compute a PRF nobody reads).  ML-DSA's `ExpandMask`
is four SHAKE256 streams of five blocks each: `Hacl.Impl.MLDSA.Mask4`
absorbs the four 66-byte seeds, shares every permutation, and tracks each
lane's squeeze with an opaque `lane_ok` (bytes out, permutations so far);
its `expand_mask_impl` takes four polynomials at a time while at least two
are left, sliding the last window back to end at `l` (ML-DSA-87's second
window recomputes one polynomial), which made signing 1.10x--1.16x faster
(Part 84).  `ExpandS` is the same again: `Hacl.Impl.MLDSA.Bounded4` runs
four `RejBoundedPoly` streams over the scalar `block256_bounded_impl`, with
the same windows.  Most of its time, though, was not Keccak but the
acceptance branch, which rejects a random 1/16 (`eta = 2`) or 7/16
(`eta = 4`) of the nibbles; `push_bit_impl` now stores every nibble and
advances the count by the top bit of the `lt_mask`, as ML-KEM's sampler
does.  Together they made `ExpandS` 1.16x--2.13x and key generation
1.05x--1.19x faster on fresh seeds (Part 85).  The 64-bit lane operations live in their own
module rather than in `Hacl.Vec256`: adding them there perturbed the solver
context of the ChaCha20 and Poly1305 vector proofs enough to time them out.

The proof needed three things that the SHA-2 proof did not.  The round steps
(`theta_c`, `theta`, `rho_pi`, `chi`) are `[@@"opaque_to_smt"]`, because a
transparent 25-element `Seq.init` in the context times out every query in the
same function; each has an index lemma that `reveal_opaque`s it.  Those index
lemmas are stated in the shape the *code* has — `theta_c_eq` in flat indices,
`theta_step` in terms of the parity buffer, `squeeze_range_eq` in absolute
output offsets — because a lemma one rewriting step away from the goal is a
lemma that does not fire.  And the rotation table is filled by a loop over a
25-way `if`-chain rather than by 25 straight-line writes: proving
`Seq.index (upd (upd ...) 24 x) 5 == 5` through a 25-deep chain of updates is
beyond Z3 in a Pulse context, though the `rc` table's 24 straight-line writes
are fine, because there the postcondition is the same chain of updates and the
match is syntactic.

### The incremental sponge

The streaming interface to SHA-3 is the same shape as the one to SHA-2 --
three flat pieces of memory, no allocation, no error code -- with the rate
where the block length was:

```c
uint64_t acc[25];   /* the Keccak state, as lanes */
uint8_t  buf[168];  /* one rate's worth of buffered bytes; 144, 136, 104 or 72
                       for the four SHA-3s, 168 for SHAKE128 */
size_t   total;
```

`Spec.SHA3.Streaming.state_ok` says the lanes are `sabsorb r seen (|seen| / r)`
-- `seen`'s whole blocks, absorbed and permuted -- and that the first
`|seen| % r` bytes of the buffer are the rest.  As in SHA-2 the buffer is kept
strictly partial, and `update` xors whole blocks straight out of the caller's
data.

`digest` is where the sponge differs.  It copies the 25 lanes to the stack,
builds the padded final block there out of the buffered tail (the same
`last_block` the one-shot uses), absorbs it into the copy and squeezes from
the copy, so the real state is untouched -- and, as in SHA-2, the buffer is
taken at a fractional permission and handed back with the same contents, so
`stream_ok` survives a digest rather than being existentially thrown away.
That is what lets a SHAKE state be
squeezed at 16 bytes and then at 200 and get the same stream twice, and lets
an `update` after a `digest` carry on with the same message.
`tests/test_sha3_streaming.c` checks all three, plus the FIPS 202 messages fed
in nineteen chunk sizes that straddle every one of the five rates from both
sides.

One copy of the code serves all six algorithms, since the rate and the
domain-separation byte are ordinary runtime arguments; `Hacl.Streaming.SHA3`
names the six and is the C ABI.  The cost is that
`update` writes the round-constant and rotation tables into stack arrays on
every call, forty-nine stores whatever the call absorbs, because the
direct-to-C backend cannot yet emit a constant global.  That is a backend
limitation, not an interface one.


### BLAKE2, where the digest length is part of the algorithm

BLAKE2 is written once for both widths, like everything else here, over a
`Spec.Blake2.params` record holding the round count, the initialization
vector, the digest length and the four rotation distances.  Three things about
it are unlike SHA-2.

The **digest length is a parameter, not a truncation**: it is mixed into the
first state word before anything is compressed, so BLAKE2b-256 is not
BLAKE2b-512 cut in half.  It therefore has to be part of the record, and the
record has to be a compile-time constant for Custard to fold the rotation
distances into literals, so there is one entry point per length --
`blake2b_512`, `blake2b_384`, `blake2b_256`, `blake2b_160`, `blake2s_256`,
`blake2s_224`, `blake2s_160`, `blake2s_128` -- rather than one that takes a
length.  Another length is four lines.

The **key is data, not a separate mechanism**: a keyed BLAKE2 is the unkeyed
one over the key zero-padded to a whole block, followed by the message.  The
specification says exactly that, in `Spec.Blake2.data`.  The implementation
must not build it -- that would mean copying the message -- so it reads block
*i* straight out of the key or the message, zero-filling past the end, and
`Spec.Blake2.block_at_data` is the proof that the two views agree.  Naming that
view (`block_of`) and proving one lemma about it is much less work than
threading `Seq.append` through a loop invariant.

The **block counter is two words wide** -- 128 bits for BLAKE2b, 64 for
BLAKE2s -- and it counts message bytes, not padded bytes, which is what makes
the padding unambiguous without a length field.  The implementation carries it
as a `size_t` and splits it with two new `word` class methods, `of_sizet_lo`
and `of_sizet_hi`.  Their specifications are stated modulo 2^64, because
`FStar.SizeT.fits` is abstract: nothing in the standard library says a
`size_t` is only sixty-four bits, and the only conversion it offers truncates
to that width.  A caller that needs the split to be exact carries
`SZ.v x < pow2 64` itself.  That obligation surfaces in the C header as "the
message must be shorter than 2^64 minus two blocks", which is vacuous
everywhere and unprovable in general.

Two empty-input cases are worth stating because they are the ones an
implementation gets wrong: an *unkeyed* hash of the empty string still
compresses one block, of zeros, with counter zero; a *keyed* hash of the empty
string compresses only the key block, with counter one block.  Both are in the
test vectors.

### The incremental BLAKE2, where a full buffer may be the last block

The incremental interface is the same three flat pieces of state as SHA-2 --
accumulator, one block of buffered bytes, one `size_t` -- and the same absence
of allocation, destructor and error code.  Two things differ, and both come
from the same fact: BLAKE2's *last* compression is flagged and takes the
message length as its counter, while every other compression is unflagged and
takes a block-aligned counter.

First, **a just-filled buffer is not compressed**.  When `update` is given
data, it cannot compress the block it has just completed: no more data may
ever arrive, in which case that block is the last one and must be compressed
flagged instead.  So the buffer holds between one and `block_len` bytes rather
than between zero and `block_len - 1`, and the loop absorbs `(rest - 1) /
block_len` blocks out of the caller's data rather than `rest / block_len`.
That single `- 1` is the whole difference from `Hacl.Hash.SHA2.Streaming`.
`Spec.Blake2.Streaming.update_split` proves the resulting offsets once, in a
pure context, and the Pulse code just reads them off.

Second, **the state counts the combined stream, not the message**.  Write

    stream key seen = if key is empty then seen else pad_block key ++ seen

for the byte sequence BLAKE2 actually compresses.  The stored `size_t` is the
length of *that*, so it starts at `block_len` for a keyed hash and at zero for
an unkeyed one.  Three things fall out for free:

  * a keyed hash is an unkeyed one whose buffer starts full, so `init` is the
    only function that ever looks at the key, and `update` and `digest` take
    it only as a ghost argument;
  * `Spec.Blake2.last_counter key seen` is exactly `Seq.length (stream key
    seen)`, keyed or not, so `digest` passes the stored `size_t` to the
    flagged compression unchanged;
  * the chunking lemmas in `Hacl.Spec.Chunks` apply verbatim, because
    `stream key (seen ++ data) == stream key seen ++ data`.

`digest` copies the eight-word accumulator into scratch before compressing, so
the state survives; calling it twice gives the same answer and updating
afterwards continues the same message.  Both are in the tests, along with
2160 checks that eight algorithms times three key lengths times ten message
lengths times nine chunk sizes all agree with the one-shot digest.

### ChaCha20, a keystream and nothing else

ChaCha20 is a block function, `Spec.Chacha20.chacha20_block`, applied at a
counter and exclusive-ored into the message.  It needs no state and no
padding, so the implementation is one loop over whole blocks and one short
tail, and the only thing worth saying about it is what is *not* there: the
sixteen-word working state is a stack array that the rounds permute in place,
the column and diagonal rounds are the same four-argument quarter-round at
different indices, and the final feed-forward add is the only place the
original state is read again.  Encryption and decryption are the same
function, exported twice so that callers read the way they mean.

The counter is thirty-two bits and it is the caller's, which is why the
specification carries `max_len ctr` -- the number of bytes that can be
encrypted before it wraps -- as a precondition rather than silently
truncating.

**Eight blocks at a time, on AVX2.**  `code/chacha/Hacl.Chacha20.Vec256.fst`
runs the same rounds on eight blocks at once, *vertically*: vector *i* holds
word *i* of all eight states, so lane *j* of the sixteen vectors is the state
of block *c + j* and every quarter-round is the scalar one with `+`, `^` and
`<<<` replaced by their eight-lane forms.  The proof is the same picture.
`lane_state vs j` reads one block's state out of the vectors, and every round
function's postcondition is `lanes_step v0 v1 f` -- every lane moved by the
scalar `f` -- so twenty rounds of eight lanes are proved by the scalar
specification and no new arithmetic.  What is new is the way out: the
keystream for block *j* is lane *j* of sixteen registers, and memory wants it
as sixty-four consecutive bytes, so an 8 x 8 transpose of thirty-two-bit
words (`unpacklo/hi` at 32 and 64 bits, then `vperm2i128`) runs twice per
chunk, its postcondition stating which lane of which input every output lane
came from.  The byte-level lemma under the exclusive-or is that a register's
bytes are its eight lanes written little-endian, which is a definition, not an
axiom.

**Sixteen blocks at a time, on AVX-512F.**  `code/chacha/Hacl.Chacha20.Vec512.fst`
is the same construction with sixteen lanes.  The rounds and their proof are
the eight-lane ones with the bounds changed; what AVX-512 adds is `vprold`,
so each of the four rotations in a quarter-round is one instruction, and
thirty-two registers, so the state does not spill.  The way out is
different and simpler: a 16 x 16 transpose (two rounds of unpacks within each
128-bit group, then two rounds of `vshufi32x4` moving whole groups) leaves
block *j* whole in register *j*, which is one load, exclusive-or and store of
sixty-four bytes.  Its proof is split the same way, a predicate for each step
and a lemma composing them.

`Hacl.Chacha20.encrypt` calls `encrypt_vec` first, which takes whole 512-byte
chunks when the message has one and the processor has AVX2 -- after
`Hacl.Chacha20.Vec512` has taken whole 1024-byte chunks, if the processor
has AVX-512F -- and says how many bytes it wrote; the scalar loop then starts there, at block counter
`ctr + n / 64`.  The postcondition of the whole function did not change, so
ChaCha20-Poly1305 and HPKE got the fast path without a line of their own.  On a Xeon Gold 6140 this took 256 KiB of ChaCha20 from 1.66 to
0.35 ns/B (4.7x) and ChaCha20-Poly1305 from 2.54 to 1.25 ns/B, under gcc and
clang alike; messages under 512 bytes do not reach the vector code at all.

**In place or not, one function.**  `Hacl_Chacha20_encrypt(out, msg, ...)`
accepts `out == msg` as well as disjoint buffers -- HACL\*'s `eq_or_disjoint`
-- and the proof says so.  Its precondition is not two `pts_to`s but
`Hacl.Impl.InOut.inout out msg pm pos vo vi`: `out` holds `vo`, and the input
`vi` is still available from position `pos` on, either in `msg` (a separate
array, case `out =!= msg`) or in the not-yet-overwritten suffix of `out`
itself (case `out == msg`).  The case split is on a proposition that no code
tests -- it is resolved ghostly with the strong excluded middle -- so it costs
nothing in C.  Every write is at the boundary `pos`, which then moves up;
reads are at or past it, through `read_in`, or through `borrow_in`/`return_in`
for a whole-vector load.  ChaCha20 never looks back, so the 64-byte AVX-512
and 32-byte AVX2 load-xor-store steps and the scalar byte loop all fit the
discipline unchanged.  Pulse callers do not see `inout`: `encrypt_disjoint`
takes the two arrays (an aliased pair would need twice the full permission,
so they can only coincide when empty, and an empty array's `pts_to` can be
had at any fraction), and `encrypt_inplace` takes one.

The same predicate runs through everything built on a stream cipher.
Salsa20's three paths are ChaCha20's with a different core.
ChaCha20-Poly1305 and secretbox's detached functions MAC the ciphertext,
which sits in the output when encrypting and in the input when decrypting;
decryption borrows the whole input with `borrow_in` to compute the tag
before writing anything.  Secretbox hands the message from byte thirty-two
on to Salsa20, and `Hacl.Impl.InOut.Sub` cuts that window out of an `inout`
pair and puts it back (`sub_in`, `unsub_inout`).  AES-GCM, which used to
be in place only, now takes a separate `out` first, like everything else,
and it too may be `msg`.  The cipher reads the ciphertext back from `out`
for GHASH.  HPKE passes its two buffers straight through instead of
copying the message into the ciphertext first.  `tests/test_inplace.c`
checks that in place and out of place agree for ChaCha20-Poly1305,
secretbox and box; the ChaCha20, Salsa20 and GCM tests run both ways
themselves.

One extraction trap.  An implicit like `#pos: nat` on a `fn` that is not
`inline_for_extraction` is a real argument in C, and Custard rejects it
because `nat` has no C type.  The boundary must be `#pos: erased nat`
there.

### Poly1305, five limbs of twenty-six bits

A field element modulo 2^130 - 5 is five 64-bit words holding twenty-six bits
each.  Twenty-six is what makes the schoolbook product fit: five products of
two 28-bit limbs, times five for the `2^130 == prime + 5` wraparound, is under
2^59, so nothing overflows and no carry is needed *inside* the multiplication.
The carry chain runs once afterwards, and it leaves limbs under 2^27; `fadd`
takes a 27-bounded accumulator and a 26-bounded block to a 28-bounded result,
which is exactly what `fmul` accepts.  So the main loop is a load, five adds
and a multiply, with no carry propagation between them.

**A block is loaded as two words, not five bytes at a time.**  Two
`load_le #uint64` calls give the low and high halves -- and those two calls
were, until recently, a fifth of the entire running time, for reasons that
had nothing to do with Poly1305 and are described in
[A machine word is not eight bytes in a loop](#a-machine-word-is-not-eight-bytes-in-a-loop); four of the five limbs
are a shift and a mask of one of them, and limb two is the only one that
straddles the boundary -- twelve bits from the low word, fourteen from the
high.  There is no `logor` anywhere: the operands are disjoint by size, so a
plain addition is equal to the disjunction and avoids `logor_disjoint`
entirely.

**`r` is nine limbs, not five.**  The wraparound in the schoolbook product
multiplies `h_i * r_j` by five whenever `i + j` exceeds four, ten times in
all.  `load_r` precomputes `5*r_1 .. 5*r_4` into `r[5..8]` once per message
and `mul_limbs` multiplies by those instead, which is the form HACL\* uses
and which turns thirty-five multiplies into twenty-five.  It is worth about
2%: gcc was already compiling `5 * x` to one `lea`, so the ten extra
multiplies did not exist in the object code.  It is kept because it is
strictly less work and because the `has5` invariant that carries it costs
one conjunct.

**The carry chain is two chains, not one.**  The six carries after a
multiplication used to run `0 -> 1 -> 2 -> 3 -> 4 -> 0 -> 1`, six deep.  They
now start in two places at once -- one chain at limb zero, one at limb three,
each carrying two places, with the wrap from the top rejoining them -- which
is four steps with two independent shifts in each, again HACL\*'s shape.
That one is worth nothing measurable, and is recorded here because "shorten
the dependency chain" is exactly the kind of change that *sounds* like it
must help: the chain was never the critical path.  What was is in
[A machine word is not eight bytes in a loop](#a-machine-word-is-not-eight-bytes-in-a-loop).

**A short block is padded, not shifted.**  The specification's value of a
block of *n* bytes is `le_nat b + 2^(8n)`, and for a full block the `2^128`
falls exactly on the top of limb four.  For a short one the implementation
copies into a zeroed sixteen-byte scratch, writes `1` at index *n*, and loads
with the top bit off; `le_nat_split` and `le_nat_one_zeros` say that this is
the same number.  That is one branch in the whole algorithm.

**The final reduction is three ripple carries and a mask.**  A *ripple* is the
plain positional carry with nothing wrapped round: `as_nat5 t + c * 2^130 ==
as_nat5 e`.  Ripple the accumulator and fold five times its carry into limb
zero -- sound because `2^130 == prime + 5` -- to get a number congruent to it
and below twice the prime.  Ripple that, and ripple that plus five; the carry
out of the second is exactly the test "is it at or above the prime", because
`prime + 5 == 2^130`.  Select on `eq_mask` of that carry.  The bound that
makes it work is not on the limbs but on the value: a ripple of something
below 2^131 carries at most one.

**The tag** is the canonical limbs repacked into two 64-bit words.  The top
two bits fall off the end, which is sound precisely because the tag is taken
modulo 2^128, and then `s` is added with a two-word constant-time add whose
carry is `lt_mask` of the low word.  Clamping is seven byte masks on a copy of
the key's first sixteen bytes, written to match `Spec.Poly1305.clamp_byte`
byte for byte.

**The driver's loop invariant is a congruence, not an equation.**  `fmul`
wraps the top of the number round to the bottom, so all that survives it is
`feval h % prime == <the specification's accumulator>`; it becomes an equation
once, at the end, in `reduce`.  The loop runs over `len / 16` whole blocks and
the short one is handled outside it, in a function of its own -- a Pulse `if`
has to be the last statement of something for its two branches to be checked
against one written-down postcondition, so the `if` is that function's body
and the postcondition is itself an `if` on the length.

**Four blocks at a time, on AVX2.**  `code/poly1305/Hacl.Poly1305.Vec256.fst`
runs four accumulators side by side, one per sixty-four-bit lane, each a
Horner chain in *r^4* over every fourth block; at the end lane *j* is
multiplied by the power of *r* its blocks are still owed and the four lanes
are added.  That this is the specification's one chain in *r* is
`Spec.Poly1305.Vec` (`horner_init`, `horner_step`, `horner_final`), stated as
congruences so that the lanes never need reducing.  The arithmetic is the
scalar field multiplication widened to four lanes -- twenty-five `vpmuludq`s
and the same two-way carry chain -- with one change: the multiplier is a
power of *r* that has been through a carry, so its limbs are under 2^27
rather than 2^26, and `mul_reduce_ok27` is the scalar lemma with that bit.
Two loads and two `vpunpck{l,h}qdq` turn four blocks into their low and high
words, but the unpacks work inside each 128-bit half, so the lanes hold blocks
*0, 2, 1, 3*; rather than spend a permute per group, the final multiplier is
*r^4, r^2, r^3, r* in that order.

The proof is shaped by what the solver would not do.  The all-lane
predicates (`vbounded`, `vmul_post`, `vload`, `vinv`) are opaque, the Pulse
code passes them from lemma to lemma, and every lemma that opens one proves
it one lane at a time over a total `l64 x i`; the code itself uses the raw
intrinsics, whose refinements are quantified, and never asks the solver to
instantiate them.  `absorb_blocks` calls `absorb_vec` first, which takes the
longest multiple of four blocks when there are at least eight and the
processor has AVX2, and the scalar loop carries on from there; its
postcondition did not change, so ChaCha20-Poly1305 got the fast path too.
`absorb_blocks` is now `inline_for_extraction`: with the dispatch in it
clang stopped inlining it, and the one-block loop out of line made 64-byte
MACs 15% slower.  On a Xeon Gold 6140, 256 KiB of Poly1305 went from 0.88 to
0.20 ns/B under gcc (4.4x) and from 0.69 to 0.24 under clang, and
ChaCha20-Poly1305 from 1.25 to 0.57; messages under 128 bytes do not reach
the vector code.

The streaming interface, `Hacl.Streaming.Poly1305`, is simpler than the
hashes': a whole block can be absorbed as soon as it arrives, because only
the final block is padded differently, so the state is just *r* (with its
multiples by five), the accumulator, a copy of the key for *s*, a block
buffer and a byte count kept modulo sixteen -- so there is no length limit.
`update` tops up the buffer, absorbs it and then every whole block of the
input in place with `absorb_blocks`, which keeps the AVX2 path, and buffers
the rest; `digest` finishes a copy of the accumulator with `absorb_tail`, so
the state survives it.  The one fact the proof adds,
`Spec.Poly1305.Streaming.blocks_acc_extend`, says absorbing the first
*n + k* blocks of a message is absorbing *n* and then *k* more from any
sequence that agrees with it there.  `wipe` zeroes the whole state through
`Hacl.Mem.wipe`, key copy included.

### ChaCha20-Poly1305, three segments and one accumulator

The AEAD is not "encrypt, then MAC three buffers".  The authenticated input is
a *concatenation* -- the additional data, the ciphertext, and a sixteen-byte
block holding the two lengths -- in which the first two are padded out to a
multiple of sixteen with zeros before Poly1305 ever sees them.  A padded
segment's last block is therefore a full block with a zero tail and the
`2^128` bit set, and not Poly1305's own one-bit-padded short block.  Calling
`poly1305_mac` on each piece would authenticate something else entirely.

So the specification says the same thing twice and proves the two equal.
`Spec.Poly1305.poly (mac_input aad ct) r` is the definition, over the
concatenation; `mac_acc` is three passes of `seg_acc` over one running
accumulator, which is what an implementation can actually run; and
`mac_input_acc` is the induction that identifies them.  Underneath it,
`poly_acc_append` says that the accumulator of `a ++ b` is the accumulator of
`b` started from the accumulator of `a` -- true only because both are
block-aligned, which is what the padding buys -- and `poly_acc_seg` says that
absorbing a padded segment is absorbing its whole blocks and then, if the
length is not a multiple of sixteen, one more full block of the tail.

The implementation is then three calls to `Hacl.Poly1305.absorb_seg` and
nothing else: the same `absorb_blocks` loop the plain MAC uses, plus
`absorb_pad` for the one ragged block, which copies the tail into a zeroed
scratch and loads it as a full block.  The length block goes through the same
function -- it is already sixteen bytes, so the padded path is a no-op.  That
is the entire reason `Hacl.Poly1305` exposes four functions instead of one.

**The one-time key is obtained by encrypting thirty-two zero bytes.**  RFC 8439
defines it as the first half of the ChaCha20 block at counter zero;
`otk_is_encrypt` proves that exclusive-or with zero is the identity, so no
keystream-block entry point has to exist.  The message is encrypted at counter
one, and `Spec.Chacha20.max_len 1ul` is the precondition that says the counter
does not wrap.

**Decryption verifies before it decrypts.**  The postcondition is explicit
about it: on failure the plaintext buffer is *unchanged*, not zeroed and not
partially written.  The comparison is sixteen `eq_mask`s folded with `logand`,
and the resulting bit is the only thing in the library that goes through
`Hacl.Secret.Declassify` on this path -- it is the answer the caller asked
for.  Because a secret byte has no decidable equality, the specification's
notion of "the tag is right" is a `prop` (`decrypt_ok`) and the recovered
plaintext is a separate function (`decrypted`), rather than one `option`.

### Curve25519, five limbs of fifty-one bits

Every fast X25519 in existence represents a field element in radix 2^51,
five limbs, because the product of two limbs fits in a 128-bit integer.  This
library took two detours before it got there.  Custard's builtins were
`FStar.UInt8/16/32/64` and `FStar.SizeT`, and unlike karamel there was no
compiler-side emulation, so the first version used **sixteen limbs of sixteen
bits** -- narrow enough that a whole schoolbook column, sixteen limb products
plus carries, stayed inside a 64-bit word with no intermediate reduction at
all, which is what made the proof tractable.  The price was 256 word
multiplies per `fmul` against 25 for HACL\*'s `_51`.  When Custard grew
`unsigned __int128`, exposed as `Hacl.Secret.UInt128`, the representation
moved to **eight limbs of thirty-two bits** and a scalar multiplication went
from 461 to 243 microseconds.

It now runs at **five limbs of fifty-one bits**, and a scalar multiplication
takes 68 microseconds.  The arithmetic is nicer at every level.  Twenty-five
64x64->128 products replace sixty-four 32x32->64 ones.  And because
`5 * 51 == 255` exactly and `2^255 == prime + 19`, the fold constant is 19
rather than 38, and the whole top-limb apparatus -- `freeze_b`, `red255`,
`fold255`, `hi255`, `mask255`, `mask_top` -- disappears: the final reduction
is `add19`, one carry pass, and a select on the carry out.  A limb is allowed
to reach `2^52 - 1` rather than being canonical.

**`fmul` is a straight line, not an array.**  The specification describes it
as nine schoolbook columns, a fold of the top four against 19, and two
128-bit carry passes -- the right shape for the proof, since both halves are
inductions over the limb index, and the wrong shape for the machine.  Written
that way it cost 52.8 ns against HACL\*'s 12.8, which was the whole remaining
gap in X25519.  The implementation now holds everything in local variables.
The reduction constant is folded into `b` up front -- `19 * (2^52 - 1)` still
fits a word, so four extra multiplications collapse nine columns to five --
and the carry between columns is then a *word* rather than a 128-bit value: a
column is under `95 * lim^2`, a little below `2^110.6`, so its quotient by the
base is under `2^60`, and nineteen times the topmost one is still under
`2^64`.  That is what turns two 128-bit passes into one chain of five, with
the top carry wrapping into limb zero in a word and one more step carrying
into limb one.  The scheme only closes with the tight product bound; relaxing
it to `2^111` makes the wrap overflow, so `fmul_spec_ok` carries
`20 * (nl * (lim * lim))` unrounded the whole way, and `fmul_spec` ends in
`carry_fix` -- a single `carry_step` on limb zero -- rather than a second full
pass, because `carry_pass_shaped` already proves every other limb is a proper
digit after the first.  `Spec.Curve25519.Columns` is the bridge: it unfolds
the `repeati` behind `part` into nine explicit columns, moves the nineteen
across each product so it lands in the right operand, distributes `fold19`
into five explicit five-term sums in exactly the association the code
evaluates, and unfolds the carry chain into the straight line the code runs.
No new mathematics, which is the point.  Custard emits ten reads, four scalar
multiplications, twenty-five `mul_wide`s, a chain of shifts and masks, and
five writes; the change was worth 2.1x on every Curve25519 and Ed25519
benchmark.

**And the field asks to be inlined.**  HACL\*'s `_51` is a set of
`static inline` functions in a header, so each disappears into the ladder
body; Custard emits plain `static` functions, and gcc declines to inline a
forty-line `fmul` with thirty call sites.  `FStar.Attributes.CInline` is
Custard's way of saying `static inline` while leaving the definition where it
is -- a request to the C compiler, as distinct from Custard's own `Inline`,
which substitutes the body and emits nothing.  The distinction matters:
forcing the inline with `always_inline` makes X25519 *slower* than not
inlining at all (78 us against 68), because five `fmul`s in a ladder step,
each holding ten limbs and five 128-bit columns, spill.  Letting gcc choose
gives 56.  The attribute is on all eight field operations.

`fscale` is the one operation that needed a wider intermediate:
`121665 * (2^52 - 1)` is about `2^69`, past a word, so it takes a nine-element
128-bit scratch array and carries down from there.  It is also the only
reason those scratch arrays still exist, now that `fmul` has no use for one.

**Bytes go through the radix-32 representation.**  `Spec.Bignum256`'s byte
layer was already proved, so `load` is the 32-bit byte loop followed by five
window extractions, and `store` is eight window extractions followed by the
32-bit byte loop.  The window arithmetic -- which 32-bit limb and which bit
offset each 51-bit limb starts at, and back -- lives in
`Spec.Curve25519.Repack`, in its own module for a proof-engineering reason:
a single window lemma parameterised over the indices timed out at every one
of its call sites, while eight concrete lemmas with literal indices, each
discharging its radix arithmetic with `assert_norm`, verify in forty seconds
together.  In the implementation's ambient context even those would not
close; in a small module of their own they are routine.  `load` masks bit 255
itself, which is why `mask_top` has no callers left.

**Inversion is an addition chain, not square-and-multiply.**  `x^(p-2)` by
scanning the 255 bits of `p-2` would need a lemma about every one of those
bits; the classical chain needs only `fexp_add` and `fexp_mul`, applied to
`x^2, x^8, x^9, x^11, x^22` and then the runs `E5, E10, E20, E40, E50, E100,
E200, E250`.  It is expressed as three in-place moves -- `a := a^2`,
`a := a*b`, `a := a^(2^n)` -- each implemented by copying into scratch and
calling the out-of-place `fmul`.  An eight-word copy against sixty-four
multiplies is not worth avoiding.

**The ladder's body is its own function.**  The loop invariant of the
Montgomery ladder mentions thirteen separate `pts_to`, and stating it inside
a `while` produced a verification condition that would not close in any
rlimit.  Extracting one iteration as `ladder_one`, with a pre- and
postcondition written in terms of `Spec.Curve25519.ladder_at`, leaves the
loop itself with nothing to prove beyond the `repeati_g` bookkeeping.  This
is the single most useful structural move in the whole library.

**The specification was wrong and the proof did not care.**  The doubling
step had `z2' = E * (BB + a24 * E)` where RFC 7748 says
`z2' = E * (AA + a24 * E)`; the two differ by `E^2`, and the `BB` form would
need `a24 + 1`.  Everything above it verified, because a proof says the code
matches the specification and says nothing about whether the specification
matches the RFC.  A thirty-line Python oracle checked against the published
vectors found it in minutes.  `tests/test_curve25519.c` now covers 5.2, 6.1
in both directions, the iterated product at 1 and 1000 rounds, a
non-canonical `u` with the high bit set, and the five small-order points --
for which `ecdh` returns `false` and the shared secret is all zeros.

### Curve25519 again, four limbs of sixty-four bits

On a processor with BMI2, `Hacl.Curve25519.scalarmult` no longer runs the
radix-2^51 code above.  It checks `Hacl.Carry64.supported ()` (a cpuid test
for BMI2) and, if it is set, calls `Hacl.Curve25519.Ladder64.scalarmult64`,
a second and separately verified implementation over **four limbs of sixty-four
bits**; otherwise it calls the radix-51 path, now named `scalarmult51`.  Both
are proved against the same `Spec.Curve25519`, so the dispatch needs no proof
beyond the two postconditions agreeing.

Full-width limbs need a carry flag, which portable C does not have.
`Hacl.Carry64` adds exactly two trusted primitives, `addc` and `subb`, each
stated as one equation over integers (`s + 2^64 c' == a + b + c`, and
`s - 2^64 c' == a - b - c`, with every carry at most one).  `c/Hacl_Carry64.h`
realizes them with `__builtin_addcll`/`__builtin_subcll` where the compiler
has them, `_addcarry_u64`/`_subborrow_u64` otherwise, and `unsigned __int128`
as a last resort; `tests/test_carry64.c` checks both against `__int128` on edge
cases and a million random inputs.  Everything else -- the 4x4 schoolbook
product as rows of `mul_wide` and carry chains, the fold of the high half by
38, `fadd`/`fsub` with their wrap-around corrections, `freeze`, the addition
chain for inversion and the ladder -- is Pulse, verified against
`Spec.Curve25519.Field64`, which relates the four-word representation to the
field.  The ladder and inversion carry `custard_c_closure_prologue` with
`target("bmi2")`, so gcc and clang emit `mulx` for the whole call tree without
the rest of the library being compiled for BMI2, and
`custard_c_closure_guard "defined(__x86_64__)"`, so that call tree exists only
on x86-64; elsewhere `scalarmult` is the radix-51 path.

Two proof-engineering notes.  The closure prologue refuses a closure that
reaches a global variable, so the shared `S64.zero` became one local
`let z0 = S64.classify 0uL` per function -- and writing `S64.classify 0uL`
inline at each use instead made `freeze` time out, though the two are equal
by definition.  And `ladder`'s implicit final query hung until the body ended
with an explicit `assert` of its postcondition.

The win depends on the compiler.  Under clang 21 a scalar multiplication goes
from 54.6 us to 38 us; under gcc 15 it goes from 43 us to 48 us.  The gcc loss
is not in any one place: `fmul` in isolation is as fast as a hand-written C
prototype, and the deficit spreads over `fmul` in context, `fadd`/`fsub`,
the out-of-line squarings in inversion, and the select-based ladder with four
conditional swaps per step.  No flag or inlining change recovered it.  The
64-bit path is used whenever BMI2 is present regardless, since it is the
faster path under clang and HACL\*'s own fastest X25519 has the same shape;
an in-place squaring for inversion and a swap-state ladder are the obvious
next steps for gcc.

### Ed25519, on top of Curve25519's field

Ed25519 lives on the same prime as X25519, so it reuses
`Hacl.Curve25519.Field` unchanged -- the same five limbs of fifty-one bits,
the same `fmul`, the same inversion chain.  Nothing in the signature scheme
needed a second field implementation, which is the main reason `code/ed25519`
holds no arithmetic of its own beyond the group order: of its fourteen
modules, four are nothing but the fixed-base window's constant tables.

Its *scalar* arithmetic, mod the group order `q`, is a different matter,
because `q` is not the field prime and has no special shape.  It began as
eight limbs of thirty-two bits with every operation done bit by bit -- 512
rounds of double-and-conditionally-subtract to reduce a SHA-512 digest, 256
rounds to multiply -- for the reason its header gave at the time: without
`uint128` there was no cheap way to form a 64x64 product.  That premise is
long gone, and the module now sits on the four-limb Montgomery core in
`code/field256`, the same `Hacl.Impl.Mont4` that secp256k1 and P-256 use,
with the order supplied as data: `Spec.Ed25519.Scalar.qmod` is a
`Spec.Field4.modulus` and `Hacl.Ed25519.Tables` carries its six constant
tables.  `Hacl.Ed25519` deliberately mixes the two widths, five-limb arrays
for coordinates and four-limb arrays for scalars.

**Reducing a 512-bit digest without a Barrett step.**  `amul` insists both
its operands are already below the modulus, so a digest cannot simply be fed
to a wide Montgomery reduction, and reducing a bare 256-bit half would need
conditional subtractions against tables for `8q`, `4q`, `2q` and `q` that the
core's interface does not let a caller pass.  Cutting the digest into four
128-bit chunks instead makes every chunk a residue for free, since `2^128 <
q`.  What remains is to weight them, and a Montgomery multiplication by a
constant of the form `R k mod q` cancels the radix and leaves `a k mod q`, so
the three weights `2^128`, `2^256` and `2^384` are three ordinary constant
multiplies against tables holding `2^384 mod q`, `2^512 mod q` and `2^640 mod
q`.  The middle one is `R^2 mod q`, which the modulus already carries, so
only two tables are new.  The whole reduction is three multiplies and three
additions; the old one was five hundred and twelve conditional subtractions.
A thirty-two-byte scalar is the same fold over two chunks.  `sign_expanded`
minus `secret_to_public` -- all the scalar arithmetic in a signature, and
nothing else -- went from 31 us to 1.8.

**The compressed sign bit moved into the top byte.**  At radix 2^32 bit 255
was the top bit of limb 7 and `point_compress` could set it in place before
encoding.  At radix 2^51 it is one past the top of limb 4, so setting it
there would break `store`'s bound precondition.  It is now written into
byte 31 of the encoded output instead, which is sound for a reason that is
pure arithmetic: `b * 2^255` is a multiple of `2^(8i+8)` for every `i < 31`,
so no other byte changes, and byte 31 of a number below `2^255` is below
`2^7`, so the addition does not carry.

**A point is four arrays, not a record.**  Extended coordinates `(x, y, z,
t)` are passed as four separate five-limb arrays side by side, because a
struct of arrays would need its own separation discipline and Custard would
have to lay it out.  `point_add ox oy oz ot x1 y1 z1 t1 x2 y2 z2 t2` is a
wide signature, but the separation logic is then exactly the one the field
operations already use.  One consequence: an addition against a table used to
demand all four coordinates of the table at a *single shared* permission,
which nothing could supply -- `Table.table` hands back an existential
permission per array, and four existentials are not one, and Pulse can halve
a permission but never weaken it to a stated target.  `win_add` therefore
takes four permissions rather than one, and the fixed-base window's sixteen
read-only arrays are read where they lie instead of being copied into owned
buffers first.

**The scalar multiplications are reordered, and that changes what the callers
can assume.**  Neither the comb below nor verification's double-scalar
multiplication walks the scalar the way the specification's ladder does
(the variable-base four-bit window in `Hacl.Ed25519.PointWin`, whose
representation predicates both still use, did the same), so each returns
a point *equivalent* to the one the specification names rather than the same
quadruple.  Every consumer of a multiple therefore has to be shown blind to
the difference: compression is, because it normalises through `Z^-1`
(`point_compress_congr`); addition is, by `point_add_congr`; and the equality
test at the end of verification is, by an argument that needs `on_curve` of
the specification's points too.  For the public key that means knowing that
decompression lands on the curve, which nothing needed before and
`Spec.Ed25519` does not say, so `Spec.Ed25519.Group.decompress_on_curve`
proves it -- `recover_x` returns a square root of `(y^2 - 1)/(d y^2 + 1)`,
which is the affine equation solved for `x`.  The three places that compress
a multiple of the generator are one function, `point_mul_g_compress`, so the
congruence argument is made once.

**The generator has its own comb.**  Signing and key generation multiply a
point that is known at compile time, and `Hacl.Ed25519.PointMulComb`
preprocesses it the way ref10 does.  The scalar, reduced mod `q`, is
recoded into sixty-four signed radix-16 digits `e_i` in `[-8, 8]`
(`Spec.Ed25519.Comb.recode_ok`), and

```
k G = sum_i e_i 16^i G = 16 (sum_{i odd} e_i 16^{i-1} G) + sum_{i even} e_i 16^i G
```

so with thirty-two tables, table `j` holding `d 256^j G` for `d = 1 .. 8`,
the odd digits are thirty-two mixed additions, then four doublings, then the
even digits are thirty-two more.  Sixty-four additions and four doublings
against the four-way window's sixty-four additions and sixty-four doublings.
The tables (`Hacl.Ed25519.CombData`, 4320 limbs, about 34 KB of `.rodata`)
are in Niels form `(y+x, y-x, 2 d x y)` with `z = 1`, so an addition costs
seven multiplications; a negative digit swaps the first two coordinates and
negates the third, a `cswap` and a masked `fsub`.  Selection scans all nine
entries (zero is the identity, `(1, 1, 0)`) with laundered `eq_mask` masks,
three coordinates per pass.

The tables are proved the way the other curves' windows are (below), at a larger scale.
`spec/group-gen/ed25519/comb.py` emits `Spec.Ed25519.CombB`, which proves
the thirty-two base points `256^j G` by chains of eight doublings, and
`Spec.Ed25519.CombT0` .. `CombT7`, four tables each, which climb from each
base point one addition at a time by `assert_norm` on affine coordinates;
`Hacl.Ed25519.CombData0` .. `7` settle the Niels limbs against those points,
`Hacl.Ed25519.CombDataOk` collects them, and `Hacl.Ed25519.CombEnt` is the
per-entry contract the implementation sees.  The verified implementation keeps every quantified
fact -- the table, the digits, the curve -- behind an `opaque_to_smt`
predicate with an intro and an elim lemma, because with any of them in a
Pulse context even `8 * j >= 0` times out.

**Verification multiplies by two scalars at once, in variable time.**
Everything `verify` handles is public -- the key, the message, the
signature, and therefore `k = H(R || A || M)` and `S` -- so it may branch
on scalar bits, which ref10 and dalek both do.  `Hacl.Ed25519.Straus`
computes `Q = [k](-A) + [S]G` and compares it with `R`, rather than
`[S]G` and `R + [k]A` separately: one chain of 256 doublings shared by
both scalars instead of a comb for `[S]G` plus a four-bit window for
`[k]A` with sixty-four doublings and sixty-four additions of its own.  Each
scalar is recoded by a sliding window (`slide`) into digits that are zero
or odd: width five for `k`, against a run-time table of the sixteen odd
multiples `-A, -3A, .., -31A`, and width three for `S`, against comb table
0, whose entries `1G .. 8G` are already there in Niels form.  A zero digit
costs nothing, so a rung is a doubling plus, about one time in six and one
time in four, an addition.  `-A` is two `fsub`s from zero; `y` and `z` are
shared with `A`.

The proof is stated over `Spec.Ed25519.Straus.st q na a b` -- `q` is
equivalent to `[a] na + [b] G` -- which the loop maintains with `a` and `b`
the partial digit sums from the top (`hsum`); `dsum_bits` closes the gap
from digit sums to the scalars' bytes, and `st_verify` turns the final `st`
into the specification's comparison `[S]G == R + [k]A` via
`Spec.Group.Smul`'s two-base lemmas (`lin2`, `cancel`).  As with the comb,
every quantified fact -- the digit bounds, the table, the curve -- lives
behind an opaque predicate, and each rung's three steps (`s_dbl`, `s_adda`,
`s_addb`) are separate functions whose contracts mention only `st`.

**Failure is public.**  Decompression can fail, and a signature can be
invalid; neither fact is secret, so both are ordinary `bool`s rather than
masks.  The only place a mask is declassified is the final field comparison
in `point_equal`, and the sign bit recovered from byte 31 in
`point_decompress`.  Everything upstream of that stays in
`Hacl.Secret.UInt64`.

**Every hash is over a concatenation, and none of them is materialised.**
`sig_r` hashes `prefix || msg`, `sig_k` hashes `R || A || msg`.  Building
those buffers would allocate proportionally to the message.  Instead
`hash2`/`hash3` drive `Hacl.Streaming.SHA2`'s `sha512_init` / `sha512_update`
/ `sha512_digest` directly, feeding the pieces in order.  The cost is that
the `seen` ghost argument has to be spelled out at each step --
`Seq.append (Seq.append (Seq.empty #S8.t) va) vb` -- and reconciled with the
specification's `Seq.append` tree by a single `Seq.equal` assertion at the
end.

**Big literals are the enemy of Z3.**  `d`, `sqrt_m1` and the group order
`q` are 250-odd-bit numbers, and any goal that mentions one of them next to
a `*` or a `%` can run for twenty minutes.  The fix, used everywhere in
`recover_x` and `verify`, is to hoist the statement into a small pure lemma
*parametrized over the constant*: `lt_char (a: nat) (n: pos) (oks: bool)`,
`body dd sm y sign`.  The lemma's own proof never sees the literal, and the
call site only instantiates it.  `recover_x` is five layers of this: a
definition over abstract constants, a definitional lemma tying it to the
spec, a purely boolean skeleton, a definitional lemma tying the two, and the
real characterization proved about the skeleton alone.

**Scratch modules make ten-minute files editable.**  `Hacl.Ed25519.fst`
takes about sixteen minutes to recheck and `Hacl.Ed25519.Encoding.fst` about
ten, which is far too slow to debug one function in.  The working method was
to keep a warm copy of the checked files in a scratch cache directory, write
the new function in a one-line `module Tmp` that `open`s the real module,
and check *that* -- seconds instead of minutes -- then paste the finished
function back and pay the full check once.

`tests/test_ed25519.c` covers all five RFC 8032 §7.1 vectors in both
directions, rejection of every single-bit tampering of a signature,
rejection under a wrong message, rejection of the malleable `S + q`
encoding, and agreement between `expand_keys`/`sign_expanded` and the
one-shot `sign`.

### P-256, a second field and a second scalar field

P-256 is the first curve here whose field is not Curve25519's, and the first
whose group order matters arithmetically rather than only as a range check.
Both are 256-bit primes with no special shape, so both are done in Montgomery
form over four 64-bit limbs by one shared layer in `code/field256/`:
`Spec.Bignum4` fixes the representation, `Hacl.Impl.Mont4` does
Coarsely-Integrated Operand Scanning, and `Hacl.P256.Field` and
`Hacl.P256.Scalar` are two instantiations that never meet.  **That layer
takes its modulus as data**, a record of the modulus, its two's complement
and the Montgomery constants, passed at run time.  Nothing in it mentions a
curve, which is what made secp256k1 almost free.

**A product no longer fits in a column.**  At radix 2^32 the schoolbook
accumulator held `a_i * b_j` in one 64-bit column and every column stayed
under a word; at radix 2^64 one product already fills 128 bits, so the core
splits it -- `plo` of it into column `i + j`, `phi` into column `i + j + 1`.
Since `plo x + base * phi x == x` the number is unchanged, and a finished
column is under `2^67`, which is why `Spec.Bignum4` states its bounds against
`pow2 66` and `pow2 72` where `Spec.Bignum256` could state them against a
word.  The one visible consequence is that a lazy sum no longer fits in a
word either: the scratch buffer that `csub_op` and the four byte decoders
pass around is an array of 128-bit words, narrowed on the way out.

The Montgomery constant `mu = -m^-1 mod 2^64` had to be recomputed for three
of the four moduli.  P-256's prime keeps `mu == 1` -- its low limb is
`2^64 - 1`, so its inverse is still `-1` -- which is a small gift from its
Solinas shape and the only one this representation collects.

**The field has since left that layer.**  `Hacl.P256.Field64` is a
multiplier for this prime alone: the product is X25519-64's sixteen-`mulx`
`mul8`, chained with `adc` through `Hacl.Carry64`, and each of the four
Montgomery steps uses `mu == 1` and `p + 1 = 2^96 + 2^192 * 0xffffffff00000001`
to add `u * p` as two shifts and one multiplication, where the generic step
has four.  Four steps leave a number below `2p`, and one borrow chain and a
masked select finish it.  Addition and subtraction are one carry chain and a
masked correction.  Every step's statement is linear in numerals --
`2^64 * W_(k+1) == W_k + u * p` -- so none needed a lemma beyond the
carry-chain postconditions.  `Hacl.P256.Field` keeps its interface and calls
it for `fadd`, `fsub`, `fmul`, `fsqr` and the entry into Montgomery form,
with three small lemmas connecting `ev4` of four words to `Spec.Mont4`'s
`mev` of their `vals` (any residue with the right value has the specification's
limbs, so `mev_mul`, `mev_add` and `mev_sub` carry over).  `fmul` went from
34 ns to 25 under gcc and from 47 to 18 under clang, and every P-256
operation got 35-50% faster (`bench/REPORT.md` Part 62).  The scalar field
stayed on `Hacl.Impl.Mont4` until it got a faster multiplier of its own
(below).  `mul8` and the two row functions below it lost
their `target("bmi2")` for this -- none uses BMI2, and inlined into X25519's
`bmi2` field they compile exactly as before.

**P-384 followed the same path.**  `Hacl.P384.Field64` is a six-limb
Montgomery field for `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`, interleaved
(CIOS): one verified `step`, `acc := (acc + x * b + u * p) / 2^64`, called
six times, with `mu = 2^32 + 1` and `u * p` built from four multiplications
because three of `p`'s words are all ones.  A conditional subtraction
finishes the product; addition and subtraction are straight-line carry
chains with a masked correction.  `Hacl.P384.Field` keeps its interface and
reaches the generic `Spec.P384` operations through `num_fv` (six words'
`ev6` equals the bignum `num` of their `vals`) and three lemmas over plain
`nat`s (`add_fv`, `sub_fv`, `mul_fv`).  Every P-384 operation got 1.9x
faster under gcc and 2.2-2.3x under clang (`bench/REPORT.md` Part 92).
Its scalar multiplications then moved to `Hacl.P384.PointWin`, the P-256
four-bit window on six limbs, with `PointMul` stated up to `peq` and the
callers bridging through `peq_out`/`add_out` (another 1.45x, Part 93).  Multiplying
`G` then got P-256's fixed-base treatment at six pieces instead of four:
`Spec.Group.Split6` splits the scalar into six 64-bit pieces against
`G, 2^64 G, ..., 2^320 G`, so sixteen rungs of four doublings and six
additions replace 384 doublings.  The ninety-six table points are compiled
in (`Spec.P384.Base`, `Spec.P384.Win0..5`, `Hacl.P384.Win0..5`, bridged by
`Hacl.P384.WinTable`) and generated by `spec/group-gen/p384/wintables.py`;
the normaliser re-checks every point, so the script is not trusted
(keygen 2.2-2.6x, signing 2x, Part 94).  The affine conversion then
traded the generic constant-time exponentiation for a fixed addition chain
on the field's own operations (`Hacl.P384.Inverse`, 385 squarings and
fourteen multiplications, 2.8x for the inversion, Part 95).  Its proof
passes each step's exponents as ghost arguments and keeps `MA.exp`
behind an `opaque_to_smt` wrapper: unfolded, Z3 5.3.0 could spend ten
minutes on one query without hitting the rlimit.

**Keeping them apart is a performance decision, not a taste one.**  The field
modulus `p` and the order `q` are both 78-digit literals, and a goal that
mentions both takes minutes.  So `code/p256` is twenty-seven modules: the on-curve
test and the scalar reduction never appear in the same verification context,
and `Hacl.P256.Key` (private keys, the scalar field) and
`Hacl.P256.Key.Public` (public keys, the field) are separate files for no
other reason.  Seven more are the fixed-base window and its compiled-in
tables.  `code/k256` is split the same way for the same reasons, plus the
modules of its own radix-52 base field.

**`Spec.P256.point_add` and `point_double` are `opaque_to_smt`.**  The
addition formulas are Renes-Costello-Batina, twelve field multiplications
with no special cases -- and about forty lines of nested `fmul`/`fadd` when
unfolded.  Once, in the scalar-multiplication loop, that is fine; on every
iteration of a 256-step ladder it is fatal.  Sealing them means the loop
invariant talks about `point_add` the symbol.

**Scalar multiplication reads nibbles, so it does not use Montgomery form.**
`Hacl.P256.Key.load_scalar` produces four plain limbs with `load_be`;
`qload` is used only where the scalar enters the order field (signing).
`Hacl.P256.PointWin` then walks the scalar four bits at a time against a
sixteen-entry table of small multiples of the input point, built at run time
and read with the constant-time `Hacl.Bignum.Base.table_select`: sixty-four
rungs of four doublings and one addition, 336 point operations rather than
the bit-at-a-time ladder's 512, and about a third faster.  Because the
window adds in a different order from the specification's ladder it arrives
at a different projective representative, so `point_mul` concludes `peq`
rather than equality and requires its input to be on the curve;
`Hacl.P256.Encode.lpt_on_curve` supplies that, and `Ecdh`, `Sign` and
`Verify` cash the `peq` in with `peq_to_aff_point` and
`peq_is_point_at_infinity`.  `Hacl.P256.PointStep` is left holding only
`set_infinity`.

**The generator has its own window.**  Signing, verification and key
agreement all begin with a multiplication by the generator, which is known
at compile time, so `Hacl.P256.PointMulG` does not walk the scalar bit by
bit at all: it splits it into four sixty-four-bit pieces and walks them
together against `G`, `2^64 G`, `2^128 G` and `2^192 G`, sixteen rungs of
four doublings and four additions, 184 point operations rather than 335.
`Spec.P256.Base` says what the three extra base points are, as a doubling
chain the normaliser evaluates at typechecking time, and
`Spec.Group.Smul.dblk_ok` turns that into a statement about `smul`.
Everything below the rung is `Hacl.P256.PointWin`'s, whose table layer
carries a scale for exactly this reason.  ECDH as initiator went from 272 us
to **165** and signing from 287 to **182**, which is 1.04x and 1.08x of
HACL\*.

**The four tables are compiled in.**  They were first built at run time
from the three extra base points, which was about an eighth of the
fixed-base operations.  They are now sixty-four precomputed multiples
`d * 2^{64j} G`, stored as twelve `static const uint64_t [64]` arrays of
**Montgomery forms** (what this field runs in), with entry 0 the point at
infinity `(0, R, 0)` and every `z` equal to `R`.  `spec/Spec.P256.Win0` ..
`Win3` prove each entry on the curve and equal to the previous entry plus
the scale point with one `assert_norm` apiece, lifted to `smul` by
`Spec.Group.smul_add_congr`; `code/p256/Hacl.P256.Win0` .. `Win3` hold the
arrays and `Hacl.P256.WinTable` turns four limb facts into the window's
`ent`.  All eight are generated, and each takes about a minute.  `win_add`
takes one permission per coordinate array, as on the other two curves.
This took ECDH as initiator from 97 us to 69 under gcc and from 77 to 59
under clang, and signing and verification by similar absolute amounts
(`bench/REPORT.md` Part 63).

**Inversion is an exponentiation on the specialised field.**  `finv` and
`fsqrt` were the generic four-limb `mexp`, which multiplies with the general
Montgomery core, and an eighth of a variable-base ECDH was spent there.
`Hacl.P256.Exp`, a port of `Hacl.K256.Exp52` to four 64-bit limbs, does the
same left-to-right square-and-multiply with `Hacl.P256.Field`'s `fmul` and
`fsqr`; it is about 10 us off every operation under clang and 3-5 us under
gcc (Part 64).

**The scalar field has a faster multiplier and an addition chain.**  Signing
needs one inversion modulo the order, and at 19-21 us it was a quarter of
a signature.  `Hacl.Impl.Mont64` is a four-limb Montgomery multiply for any
odd modulus, still taking the modulus words and `mu` as data: X25519-64's
`mul8` for the product, then four reduction steps that each take
`q = t_k * mu mod 2^64`, add `q m` as four `mul_wide`s in two `adc` chains,
and drop a word, then one borrow chain and a masked select.  Each step is
stated as `2^64 * W_(k+1) == W_k + q m` with a bound that says nothing
carries out of the top word, which is all the four-step argument needs.
`Hacl.Impl.Mont4F` puts it behind `Hacl.Impl.Mont4.amul`'s contract (less the
complement table, which the final subtraction no longer uses), so both
curves' `qmul` changed by one call; it went from 42 ns to 24 under clang and
from 63 to 33 under gcc.  `qinv` is then a fixed addition chain for `n - 2`
rather than square-and-multiply: the odd powers `x .. x^15`, blocks of ones
for the top half, and a four-bit sliding window for the rest, 253 squarings
and 39 multiplications where the binary method did 255 and 168 (42 against
195 on secp256k1).  The squarings alternate between two buffers, so none
copies its input.  The chain is generated, each step stating its exponent
and `assert_norm` checking the arithmetic; the steps are calls to one
verified `qstep` -- square `k` times, multiply by a known power -- because
the same chain written out as 180 inline statements took eight and a half
minutes to check and this takes a minute and a half.  `qinv` went from 21 us
to 10 under gcc and from 19 to 7.4 under clang, which is 11-16% off signing
on both curves and 5-7% off verification (Part 65).  Two things tried on the
base field were not kept: a dedicated squaring makes `fsqr` 40% faster but
whole operations only 1-3%, and fiat-crypto's `p256_64.h` multiplier is
slower than `Hacl.P256.Field64` under both compilers.

**Verification is not constant time and need not be.**
`point_mul_double_g u1 u2 Q` is two independent multiplications and one
addition rather than Shamir's trick, because nothing in verification is
secret and the simpler code is the one that verifies.

**`r` travels field -> bytes -> scalar.**  The specification says
`r = x mod q` where `x` is a field element; the implementation stores `x` to
thirty-two big-endian bytes and reloads them into the scalar field, which is
the only conversion the two Montgomery domains share.  Connecting the two
needed a new round-trip lemma in `Hacl.Spec.Bytes`,
`be_nat (nat_to_be n x) == x`.

**Machine literals are surprisingly expensive under `--fuel 0`.**  The loop
guard `SZ.lt i 256sz` was, on its own, an unprovable obligation inside
`point_mul`: `256sz` is `uint_to_t 256`, whose typing needs `pow2 64`, and Z3
will not compute that in a context the size of P-256's.  The cure is a
one-line top-level helper *outside* the options block whose type states the
conclusion -- `let lt256 (x: SZ.t) : (r: bool { r <==> SZ.v x < 256 })` -- and
the whole function then goes through in about a minute.

`tests/test_p256.c` covers the six RFC 6979 A.2.5 ECDSA examples (two
messages times three hashes) in both directions, the prehashed path, every
single-bit tampering of a signature, verification under a wrong message,
private keys that are zero or above the order, a public key that is not on
the curve, all four SEC1 conversions and their round trips, and ECDH from
both ends.


### secp256k1, which is P-256 with two numbers changed

Bitcoin's curve has a different prime, a different order, and `a = 0`
instead of `a = -3`.  Everything else about it is P-256, and the
implementation says so: `code/k256` is a module-for-module copy of
`code/p256` in which the curve arithmetic differs in three files, plus the
base field, which secp256k1 has since taken its own way.

**The scalar field is shared; the base field no longer is.**
`Hacl.K256.Tables` holds the scalar modulus, its complement, the Montgomery
constants and the exponents, and `Hacl.K256.Scalar` is the P-256 scalar
module with those tables underneath, adding not a line to the emitted C --
the Montgomery layer takes its modulus as an argument, so the two curves
share every scalar operation and differ only in the table they pass.  That
includes the faster `Hacl.Impl.Mont64` multiplier; only the inversion chain,
which is a function of the order, is each curve's own.  The
base field went its own way: secp256k1's prime is `2^256 - 2^32 - 977`, which
is close enough to a power of two that a bit above 2^256 folds back with a
single multiply by `2^32 + 977`, so `Hacl.K256.Field52` carries five limbs of
fifty-two bits, leaves them lazily reduced between operations, and has no
Montgomery factor at all.  `Hacl.K256.Tables52` holds the curve constants in
that representation and `Hacl.K256.Exp52` the exponentiation ladder without
the Montgomery apparatus.  P-256 still uses the shared four-limb Montgomery
core.

**The scalar multiplication is shared in shape but not in code.**  Both
curves now walk four bits at a time against a sixteen-entry run-time table:
`Hacl.K256.PointWin` and `Hacl.P256.PointWin` are the same file at five
limbs and at four, 336 point operations rather than 512, worth 26% on
secp256k1 and about a third on P-256.  The proof is deliberately split:
`Spec.Group.Smul` is a commutative group as an abstract record and carries
every inductive argument, including the ladder, over opaque operations;
`Spec.K256.Smul` and `Spec.P256.Smul` instantiate it and connect each
curve's own `point_mul` by a definitional equality of step functions.  The
abstraction is not decoration.  `on_curve` and `peq` unfold into equations
modulo a seventy-eight digit prime, and proving the same ladder theorem with
them in scope does not terminate; having written it once abstractly, the
second curve's spec side cost one second.  The Montgomery field made P-256's
implementation side harder rather than easier -- even its coordinate
projection carries two of those literals -- so its loop invariant is stated
over limb sequences rather than over points.

**The generator has its own window.**  Signing and `secret-to-public`
multiply a point that is known at compile time, so `Hacl.K256.PointMulG`
does not walk the scalar bit by bit at all: it splits it into four
sixty-four-bit pieces and walks them together against `G`, `2^64 G`,
`2^128 G` and `2^192 G`, sixteen rungs of four doublings and four
additions, 184 point operations rather than 335.  Everything below the rung is
`Hacl.K256.PointWin`'s, whose table layer carries a scale for exactly this
reason; the scalar arithmetic is `Spec.Group.Split4`, shared with P-256.

The four sixteen-entry tables are *compiled in*, as Ed25519's were before its
comb, and by the same construction.  They were being built on entry -- sixty point additions
out of a hundred and eighty-four -- from three extra base points stated as
doubling chains in `Spec.K256.Base`, which the normaliser evaluates at
typechecking time and `Spec.Group.Smul.dblk_ok` converts into a statement
about `smul`.  Now all sixty-four multiples are constants:
`Spec.K256.Win0` .. `Win3` name the points and prove each is the multiple it
claims to be, one `assert_norm` per entry that it equals the previous entry
plus the scale point lifted by `Spec.Group.smul_add_congr`, and
`Hacl.K256.Win0` .. `Win3` hold the limbs, twelve `static const uint64_t [80]`
arrays in radix 2^52, a hundred and ninety-two field constants and about eight
kilobytes of `.rodata`.  `Hacl.Impl.Lit52` cuts a literal list the way `entry`
slices the sequence, so one `assert_norm` per entry-coordinate settles five
limbs at once, and `Hacl.K256.WinTable` turns three such facts into the `ent`
the window wants; it is the only module that opens the `rep` abstraction, so
no seventy-eight-digit literal ever reaches a caller's solver context.
`Hacl.K256.Tables52G`, which held the three extra base points' six field
constants, is gone.  secp256k1 `secret-to-public` went from 155 us to 111 to
**75** and signing from 172 to 126 to **91**.

**`a = 0` is a shorter addition law, not a special case of the same one.**
Renes-Costello-Batina give separate algorithms for `a = -3` (4 and 6) and
`a = 0` (7 and 9); K-256 uses the second pair.  Doubling drops from eight
multiplications to six, addition keeps its twelve but loses several
additions, and the constant `3` that P-256 has to keep in Montgomery form
disappears -- the only coefficient K-256 needs is `3b = 21`.  The curve
equation loses its linear term with it: `y^2 = x^3 + 7` is three field
operations where P-256's is six.  Both formulas verified on the first
attempt, which is the clearest evidence that separating `code/field256` was
worth doing.

**Low-S is the one thing with no P-256 counterpart.**  `(r, s)` and
`(r, q - s)` verify against the same key and message, so an ECDSA signature
is malleable as a byte string; Bitcoin's consensus rules forbid the upper
half, and HACL\* exposes that as a second family of entry points rather
than as a flag.  Deciding which half `s` falls in needs an *ordering*, and
every other test in this library is an equality.  `Hacl.Impl.Mont4.ageq`
supplies it by reading the answer out of the carry that the modular
subtraction already computes -- `msub_pre` says that carry is one exactly
when the difference did not go negative -- so the ordering costs one
sixteen-limb subtraction and no new arithmetic.  Half the order joins the
tables, and `Hacl.K256.LowS` is sixty lines.

**The message representative has no truncation question.**  P-256 must say
what to do with a 384- or 512-bit digest; K-256's API only ever takes a
thirty-two byte hash, so `msg_as_qelem` reads all of it and reduces, and
there is one hashed front end instead of three.

There is no RFC with published secp256k1 signatures, so
`tests/test_k256.c` is generated from a short independent Python
implementation of the curve whose group law is anchored on the published
coordinates of 2G.  A hundred and thirty-three checks: five signatures
reproduced byte for byte in both families, the prehashed path, the four
SEC1 conversions and their round trips, four ECDH agreements, and eleven
rejections -- including a high-S signature, which the plain family must
accept and the low-S family must refuse.


### HMAC-DRBG, where the state belongs to the caller

`code/drbg` is SP 800-90A's HMAC\_DRBG over SHA2-256, -384 and -512.  There is
no SHA-1 instance: this library has no SHA-1, and SP 800-90A withdrew it
anyway.

The mechanism is four hundred words of pseudo-code and reduces to one
operation, `update`, which re-keys the pair `(K, V)` from some data:

    K <- HMAC(K, V || 0x00 || data);  V <- HMAC(K, V)
    if data <> "" then
      K <- HMAC(K, V || 0x01 || data);  V <- HMAC(K, V)

Instantiation is `update` from entropy, nonce and personalization string;
reseeding is `update` from entropy and additional input; generation runs
`V <- HMAC(K, V)` until it has enough bytes and then does one more `update`.
`Spec.HMAC_DRBG` says exactly that, and the implementation is the same shape.

**Three things fell out of not wanting to allocate.**

*The state is the caller's.*  `Hacl_HMAC_DRBG_Ptr_instantiate_sha256(k, v,
&ctr, ...)` writes into three buffers the caller owns; there is no
`create_in`, no `free`, and no `state_s` struct.  HACL\* has all three,
because its state has to live somewhere across the `malloc` boundary.  Here
`k` and `v` are `uint8_t[32]` (or 48, or 64) in whatever storage the caller
likes, down to the stack, and the counter is one `size_t`.  A caller that
wants a heap-allocated state can still have one; it just does not need our
help to get it.

*`update` takes its data in three pieces.*  The data the DRBG hashes is a
concatenation -- entropy `||` nonce `||` personalization -- and materializing
it would need a run-time-sized buffer, which is the one thing a
`create_in`-free implementation cannot have.  So `update` takes `d1 d2 d3`
and the callers pass zero-length arrays for the pieces they do not have.
Zero-length arrays are fine: `let mut a = [| z8; 0sz |]` typechecks and
Custard emits `uint8_t a[1]`, which is
portable C, not the GCC zero-length-array extension.

*So HMAC grew a concatenating form.*  `Hacl.HMAC.Cat.hmac_cat out key a b c d`
is HMAC(`key`, `a || b || c || d`) and never builds the concatenation: it
drives the generic streaming SHA-2 across the four pieces, exactly as
`Hacl.Ed25519.hash3` does for Ed25519's `SHA512(R || A || M)`.  `update`'s
first three arguments are the fixed `V || 0x00` prefix and the data pieces,
which is five streaming updates against one scratch block.

**The output loop is the sharpest example of fuel discipline in the library.**
`gen_bytes` is a recursive `GTot` function producing one digest per round.
Written the obvious way -- one `fn`, an `if` in the loop body for the partial
last block -- it verified in 3 minutes 54, of which a single goal took 221
seconds.  Three changes together took it to 15:

* the whole-block and partial-block cases became two top-level `fn`s,
  `gen_full` and `gen_tail`, so each VC is half the size and each can be tuned
  separately;
* the loop invariant became one `unfold let inv`, so it is one term rather
  than one term per occurrence;
* **the module runs at `--fuel 0 --ifuel 0`**, so `gen_bytes` never unfolds at
  all and every step has to come from a lemma (`gen_zero`, `gen_step`,
  `gen_last`, `gen_len`).  Making the unfolding explicit is what did it: at
  fuel 1 the solver unfolds the recursion opportunistically, in a context
  carrying the whole separation-logic state, and each of those is a term the
  size of the loop.

The same lesson appeared twice more in this module and was cured the same way
both times: a `Seq.equal` over a five-fold nested append inside `hmac_cat`
took 6 minutes 32 and takes seconds as a context-free top-level lemma
(`cat5`), and the two copy-back steps at the end of `rekey` took five minutes
until `Hacl.Impl.Copy.copy_exact` was given a postcondition (`vd' == vs`) that
is already the equality wanted, rather than one that has to be derived.  The
rule: *pure reasoning that does not mention the heap belongs in a top-level
lemma, and a Pulse function should only ever apply it.*

**Aliasing, again.**  `rekey` cannot write its result over its own key --
`hmac_cat out key ...` with `out == key` is not expressible, let alone sound
-- so it computes into scratch and copies back.  And Pulse cannot pass the
same array as two arguments, which is why `generate` allocates *two*
zero-length arrays where one would do in C.

**Refusals are values, not preconditions.**  `generate` returns `bool`:
`false` if the reseed counter has passed `reseed_interval` (1024) or the
request exceeds `max_output_length` (65536), and in that case nothing is
written and the state is unchanged -- which is what the postcondition says,
so a caller who ignores the result cannot silently get zeros.  HACL\* makes
the counter bound a runtime check too; the length bound it makes a
precondition, which pushes the check onto the caller.

`tests/test_drbg.c` is generated from the NIST CAVP `drbgvectors_no_reseed`
and `drbgvectors_pr_false` files.  The generator transliterates
`Spec.HMAC_DRBG` into Python, checks it against **all 1440** SHA2-256/384/512
cases in those files, and only then emits a C test covering each
(algorithm, reseeding, personalization, additional input) combination, plus
the counter behaviour at exactly 1024 generates.

### The entropy shim

`c/Hacl_Random.c` is handwritten, trusted, and the only C in the repository
that F\* did not write.  `Hacl_Random_bytes(buf, len)` is `BCryptGenRandom` on
Windows, `getrandom`/`getentropy` elsewhere, and `/dev/urandom` if the
syscall is missing; it retries on `EINTR`, loops over the per-call size caps,
and returns `false` rather than filling the buffer with anything weaker.

It is deliberately not a dependency of anything verified.  Every primitive
that needs random bytes takes them as an argument, so the verified code stays
a pure function of its inputs and a caller with a better entropy source can
use it.  HACL\*'s `Lib_RandomBuffer_System` is bound into F\* as an assumed
`val` and called from verified code; the equivalent here is a C header a C
caller includes, which keeps the trusted surface at one function that F\* has
never heard of.

`tests/test_random.c` checks the things that can be checked without judging
the operating system: that the call succeeds, stays inside the buffer, does
not repeat, and covers the byte range.

### AES-GCM, where there is no table to look up

`code/aes` is FIPS 197 and SP 800-38D: AES-128 and AES-256 in Galois/counter
mode, encryption only, tag length sixteen.  It is the one algorithm here that
HACL\* does not have a portable version of at all -- its AES is Vale assembly,
and the "no assembly" commitment rules that out -- so this is new code rather
than a reimplementation.

**The whole design follows from one refusal: no secret-indexed table.**  The
textbook AES S-box is a 256-byte array indexed by a byte of the state, and the
textbook GHASH is sixteen or two hundred and fifty-six precomputed multiples
of the hash key indexed by four bits of the ciphertext.  Both are cache-timing
side channels, and both are exactly the pattern this library's secret-integer
layer exists to prevent: `Hacl.Secret.UInt8.t` has no `index` at all, so a
table-driven implementation cannot even be written here.

So the S-box is computed:

    sbox x = affine (ginv x)

with `ginv` an addition chain of fifteen multiplications in GF(2^8) -- the
inverse is `x^254`, and `x^254 = ((x^2 . x)^4 . (x^2 . x))^16 . ((x^2 . x)^4
. (x^2 . x)) . x^2` when written to share subterms -- and `affine` eight
rotations and a xor.  That costs about three hundred and fifty serially
dependent operations per byte, which the cipher never pays because `AESENC`
has the S-box inside it, and which the *key schedule* paid forty times per
message until `AESKEYGENASSIST` was bound; see below.  `Spec.AES.sbox_is_algebraic` is the lemma that this
agrees with the 256-entry table of the standard, which is stated once, proved
once by `assert_norm`, and never unfolded again: `sbox_list` is
`opaque_to_smt`, because a 256-element literal in the solver's context makes
every subsequent query slow.

The portable GHASH is the literal 128-step algorithm 1 of SP 800-38D, with
both branches of each step turned into a mask rather than taken.  A field
multiplication is about a hundred instructions per bit of input.  That is
slow, and deliberately so: a correct, portable and constant-time
implementation comes first, and the carry-less multiplier is layered on top
of it the way AES-NI is layered on the portable cipher.  On a machine with
`PCLMULQDQ`, `Hacl.AES.GF128.NI` takes over instead: four `PCLMULQDQ`s for
the 256-bit product and a pair of shift-and-xor passes for the reduction.

**The carry-less GHASH is verified, not assumed.**  The instruction is bound
in `Hacl.Vec128` by a postcondition about polynomials -- bit *k* of the
result is `Spec.CarryLess.conv` of the two 64-bit lanes -- and everything
above it is proof.  `Spec.CarryLess` is a small theory of GF(2) polynomials:
exclusive-or over a range, convolution, its bilinearity, and Gueron's
reflection identity, that reversing two degree-<128 operands and multiplying
gives coefficient *254 - m* of the true product.  `Spec.GF128.Poly` defines
reduction as the linear extension of *x^k* mod *P* -- so linearity is the
definition rather than a lemma, and the multiplicativity of polynomial
multiplication is never needed -- and proves `gmul_is_pmod`, that SP
800-38D's shift-and-add loop computes exactly the reduced carry-less product.
`Spec.CLMUL` bridges GCM's bit numbering, which runs down from the top of
byte zero, to the machine's, which runs up from the bottom, and states the
implementation as three lemmas about eight registers.

The first version needed no reduction step at all: the reduction constant has
degree seven, so the high half of a product by it has degree at most six and
*that* product's high half is empty, which makes the same four-multiply
routine run three times the whole multiplication.  That is an unusually small
thing to verify, and it was the right place to start, but it costs twelve
`PCLMULQDQ`s per block.  `Spec.GF128.Poly.mul_r_coef` replaces the two
reduction multiplies with shifts, by computing the coefficient of the product
by the reduction constant directly: bit *k* is the xor of bits *k*, *k-1*,
*k-2* and *k-7* of the operand, which is four shifts and three xors and no
multiplier.  Four `PCLMULQDQ`s and five `PSHUFB`s per block, down from twelve
and ten.

**The block loop runs four blocks at a time.**  GHASH is Horner's rule, so
the obvious loop makes every multiply wait on the one before it -- about
twenty-two cycles of pure latency per sixteen bytes, which measurement
confirmed was the entire cost.  `Hacl.AES.GF128.NI.ghash_loop4_ni` uses the
standard rearrangement

    acc' = (acc + b0) * H^4 + b1 * H^3 + b2 * H^2 + b3 * H

with the four products independent of one another and the extra powers of the
hash key computed once, in registers, on entry -- and only when there are at
least four blocks, so short messages pay nothing.  That identity is
associativity, commutativity and distributivity of GF(2^128) multiplication,
none of which a one-at-a-time GHASH had ever needed.  `Spec.GF128.Algebra`
proves them, and it is cheap to do so because `Spec.GF128.Poly` already
writes `gmul x y` as a sum over the set bits of the *first* operand: in that
shape multiplication is visibly linear in its first argument, so the only real
work is that multiplying by *x^j* commutes with multiplication, and
commutativity of the convolution.  Nothing there ever looks inside the
reduction polynomial.

**And the four blocks share one reduction.**  Once the multiplies are
independent, the next thing to notice is that the reduction, not the
multiplication, is most of what they cost: `raw_product` is four
`PCLMULQDQ`s and about a dozen other operations, and the two `mul_r_vec`
calls that fold the 256-bit result back into the field are about twenty
shifts and exclusive-ors each.  A four-block turn was therefore running
eight folds for sixteen multiplies.

It needs one.  The 256-bit carry-less product is linear in each operand, so
four products can be accumulated as two registers -- the sum of the four low
halves and the sum of the four high halves -- and the fold applied once to
that sum.  `Hacl.AES.GF128.NI.gmul4_vec` is that: four `raw_product`s, six
exclusive-ors, and then exactly the tail `gmul_vec` already had.  A four-block
turn goes from roughly two hundred and fifty vector operations to a hundred
and ten.

The specification side is three small lemmas and no new reasoning about the
reduction polynomial at all.  `Spec.GF128.Poly.mul_r_two` is the existing
`gmul_three` with its first line removed -- the statement that folding twice
terminates, said about one register rather than about a product, which is
what makes it reusable.  `Spec.GF128.Algebra.gmul_defer4` combines four
applications of `gmul_split` with distributivity of `gmul` over `gadd`, which
`Spec.GF128.Algebra` already had for the Horner rearrangement.  And
`Spec.CLMUL.bswap_gadd` says byte reversal commutes with exclusive-or, which
is one line -- both sides are the same `Seq.init` -- and is what lets the six
exclusive-ors happen in the multiplier's bit order, so three byte reversals
happen at the end rather than twelve.

Measured on 256 KiB: GHASH alone went from 2.11 cycles per byte to **1.28**,
and AES-128-GCM from 3.68 to **2.88**, which is the first time it has been
over a gigabyte a second.  The counter-mode half, measured the same way by
difference, did not move -- 1.58 against 1.60 -- which is the control.  The
benchmark row follows: 809 MB/s to **1034** on 256 KiB under gcc, 4.48x of
EverCrypt's Vale assembly down to **3.52x**, and under clang 868 MB/s to
**1052**, 4.22x down to **3.46x**.  AES-256-GCM moves the same way, 4.41x to
**3.50x**.

The generated assembly says what changed and what is left.  A four-block turn
is 205 instructions for sixty-four bytes, or 3.2 per byte, which at the
three-wide issue this machine manages on vector code is 1.28 cycles a byte:
GHASH is now bound by instruction count rather than by the multiply latency
it used to be bound by, which is the difference between a dependency problem
and a work problem.  Of those 205, sixteen are `PCLMULQDQ` and about forty
are the single remaining fold.  There are seven `PSHUFB`s and not eleven,
because the four byte reversals of the hash-key powers are loop-invariant and
gcc hoists them; that they are invariant is a consequence of accumulating in
the multiplier's bit order rather than GHASH's.

**And the counter is a lane, not a carry chain.**  With the reduction
deferred, GHASH stopped being the larger half of AES-GCM and the counter
mode became it.  Reading the generated assembly for a four-block turn says
why: a hundred and thirty-nine of its two hundred and twenty-five
instructions were not AES at all.  They were four copies of
`Hacl.AES.Counter.inc32_impl`, the constant-time carry chain over the last
four bytes of the counter block -- a `not`, a `movzbl`, a subtract and a
shift per byte to make the carry a mask rather than a branch, which is the
right shape for a counter that might be secret and the wrong shape entirely
for a driver that needs four consecutive counters.  Worse than the
instruction count, each chain ends in a four-byte store to the counter array
and the next counter starts with a sixteen-byte load of it: a narrow store
under a wide load, which no store-forward network will satisfy, so each of
the three round trips cost a stall and the four chains were serial.

The counter never needs to be in memory.  Reversing the sixteen bytes moves
the counter's four bytes to the bottom of the register *and* turns their
big-endian reading into a little-endian one, which is exactly lane zero; a
packed thirty-two bit add of one increments that lane, wrapping at 2^32 and
carrying nothing into the twelve bytes above it, which is precisely what
`Spec.AES.inc32` asks for; and reversing again puts it back.  Three
instructions, and with the reversal kept across the four the whole turn is
one `PSHUFB` and one `PADDD` per block.  `Hacl.AES.NI.inc32_vec` is that,
and the counter is written back to the array once, at the end.

No new instruction was needed: `PADDD` was already bound, for SHA-256's
message schedule.  What it needed was to stop being under the SHA target,
since `_mm_add_epi32` is SSE2 and part of the x86-64 baseline, so the same
binding can be inlined into a SHA function and into an AES-NI one; the only
new extern is the constant one-in-lane-zero.  The proof is
`Hacl.AES.Counter.inc32_lanes`, and it is entirely bookkeeping: a lemma that
reads a byte back out of a little-endian number
(`Hacl.Spec.Bytes.le_nat_byte`), two that connect `Spec.SHANI.lane` -- where
the `PADDD` axiom states itself -- to the bytes underneath it, and then
sixteen concrete instances, one per byte of the block.  Twelve of them say
the byte did not move and four say it is a digit of the incremented counter.

A four-block turn goes from **225 instructions to 114**, and counter mode
from 1.55 cycles a byte to **0.49** -- close to the two-per-cycle `AESENC`
throughput this machine has, which is where a counter mode should be.  The
GHASH half did not move, 1.23 against 1.22, which is the control.  Whole
AES-128-GCM on 256 KiB went from 2.78 cycles a byte to **1.71**.  The
benchmark row follows it: 1034 MB/s to **1631** under gcc, 3.52x of
EverCrypt's Vale assembly down to **2.24x**, and under clang 1052 MB/s to
**2025**, 3.46x down to **1.80x** -- clang schedules the four interleaved
blocks better than gcc does, and with the counter out of the way that
difference is no longer hidden.  AES-256-GCM moves with it, 3.50x to
**2.28x**.

**And then eight blocks share one reduction.**  Which put GHASH back on top,
1.22 cycles a byte of 1.71, and the fold is a cost per *group*, not per
block: the deferral argument never cared that the group was four.  So
`Hacl.AES.GF128.NI.gmul8_vec` runs eight products against eight powers of
the hash key and folds once for a hundred and twenty-eight bytes where two
turns of `gmul4_vec` folded twice.  Eight independent `PCLMULQDQ`s also give
the multiplier twice as much to work on at once.

Nothing in the algebra is new.  `Spec.GF128.Algebra.sum8` is two `sum4`s
added; `regroup8` is `regroup4` twice and one pairing lemma; `mul_r_sum8` is
`mul_r_sum4` twice and one distribution; and `gmul_defer8` is `gmul_defer4`
with four replaced by eight throughout, with exactly one `mul_r_vec` pair
still below it.  The Horner side is the only place that needed thought:
`horner8` is `horner4` applied twice, and the work is pushing a
multiplication by `H^4` through the first group's four terms, which raises
each of their powers by four.  That last step is not free, because the
powers are generated one multiplication at a time, so `pow_mul4` walks up
the chain to show that `H^4` times each of `H`, `H^2`, `H^3` and `H^4` is
`H^5`, `H^6`, `H^7` and `H^8`.

The four-way loop did not go away.  What the eight-way pass leaves behind is
at most one group of four, so `ghash_loop4_ni` gained a starting offset and
now runs from where the eight-way pass stopped; the one-block loop takes the
rest.  Three loops, two more powers' worth of setup, and all of it inside
the same test as before: a message short of a hundred and twenty-eight bytes
computes four powers as it always did, and one short of sixty-four computes
none.

GHASH went from 1.22 cycles a byte to **1.03** under gcc and 0.92 to
**0.82** under clang; the counter half is the control and did not move,
0.47 against 0.48.  The benchmark row follows: 1631 MB/s to **1868** under
gcc, 2.24x of EverCrypt's Vale assembly down to **1.98x**, which is the
first time this primitive has been inside a factor of two of hand-written
assembly; under clang, 2025 to **2205**, 1.80x down to **1.68x**.
AES-256-GCM goes 2.28x to **2.05x**.

The eight-way turn is 363 instructions for a hundred and
twenty-eight bytes against the four-way turn's 227 for sixty-four, so the
fold really is what came out.  Forty-one of those 363 are stack traffic:
eight powers, eight data blocks and sixteen product halves do not fit in
sixteen registers, and gcc spills.  Accumulating the halves as they are
produced rather than in a tree was tried, to keep fewer of them live, and
made gcc a third *slower* -- it serialises the products when the sum is a
chain -- so the tree stays.

**Everything counts in bytes.**  FIPS 197 describes the key expansion in
four-byte words, with conditions `i mod Nk = 0` and `i mod Nk = 4`.  Writing
it that way puts a multiplication by four in front of every buffer index and
a division by four in every invariant.  `Hacl.AES.Key` steps a byte offset by
four instead, so the conditions become `b mod keylen = 0` and `b mod keylen =
16` and no multiplication appears anywhere.  The round constant is carried in
a register and doubled when it is used; the invariant names it by
`rcidx b = b / keylen` rounded up, the number of key-length boundaries the
loop has passed.

**GHASH is a fold, not a hash of a concatenation.**  The GCM tag authenticates
`pad(aad) || pad(ciphertext) || lengths`, which is a sequence no
implementation can build: it is three pieces long, the pieces are in different
buffers, and the padding is in no buffer at all.  `Spec.GF128.ghash_upd h acc
data` is GHASH restated as a fold over an accumulator, and
`Spec.GF128.ghash_upd_append` says that folding a concatenation is folding the
parts in turn.  `Hacl.AES.GHash.ghash_upd_impl` folds one buffer -- whole
blocks straight from the caller's memory, then a partial tail assembled in
sixteen bytes of stack that start at zero -- and `Hacl.AES.GCM` calls it three
times.  Nothing proportional to the input is ever allocated.

**Decryption writes nothing when the tag is wrong.**  `Spec.GCM.gcm_decrypt`
returns `option`, not a plaintext and a boolean, and the implementation
matches: the tag is computed over the ciphertext *before* anything is
decrypted, and the counter-mode pass runs only if it verifies.  A caller that
ignores the return value still never sees forged plaintext, because the output
buffer is left exactly as it was (and in place, that is the ciphertext).  The comparison itself folds sixteen
`eq_mask`s with `logand` and declassifies one bit at the end -- no early exit,
nothing that depends on where the first difference is.

    void Hacl_AES_GCM_aes128_encrypt(uint8_t *out, uint8_t *tag, uint8_t *msg,
                                     size_t msg_len, uint8_t *key, uint8_t *iv,
                                     size_t iv_len, uint8_t *aad, size_t aad_len);
    bool Hacl_AES_GCM_aes128_decrypt(uint8_t *out, uint8_t *msg, size_t msg_len,
                                     uint8_t *tag, uint8_t *key, uint8_t *iv,
                                     size_t iv_len, uint8_t *aad, size_t aad_len);

and the same pair for `aes256`.  `out` is either `msg` itself (in place) or
must not overlap it; the first version was in place only.  The nonce may be
any non-empty length: twelve bytes is the fast path every protocol uses, and
the general case -- a GHASH of the padded nonce -- is implemented because
leaving it out would make this library unable to decrypt what another
implementation produced.  `tests/test_gcm.c` is 450 cases from the NIST CAVP
`gcmtestvectors` set, one per (nonce length, message length, AAD length)
configuration in each direction, including one forgery per configuration that
must be rejected without touching the buffer.

**A nonce must never repeat under one key.**  Two messages sharing a nonce
leak the xor of the plaintexts and enough of the hash subkey to forge
arbitrary messages.  Nothing in the interface can prevent that.


### AES-NI, and how a trusted intrinsic is kept honest

`Hacl.AES.Core` computes the S-box as inversion in GF(2^8) followed by an
affine map, because a table lookup at a secret index leaks through the cache.
That is about a megabyte a second.  `AESENC` does a whole round in one
constant-time instruction.  `code/aes/Hacl.AES.NI.fst` is the cipher written
on it, and `code/aes/Hacl.AES.Block.fst` picks between the two.

**The dispatch is per block, and no caller knows about it.**
`Hacl.AES.NI.cipher_ni` and `Hacl.AES.Cipher.cipher_portable` have the *same*
postcondition, so the dispatcher has nothing to prove -- both branches leave
the same specification value behind.  In exchange CTR, GCM and anything added
later get the fast path with no dispatching variant of their own.
`test_gcm.c`'s 450 CAVP cases run through the new path unchanged.

That is the correctness story; the performance story needed two more steps.
A block cipher whose interface is "sixteen bytes in, sixteen bytes out" stores
its result to memory and reloads it, and the feature test runs again for every
block.  `Hacl.AES.NI.cipher_vec` therefore exposes a register-to-register
form, and `Hacl.AES.CTR` runs **four counter blocks at once** through
`Hacl.AES.NI.ctr_block4_ni`: the counter is incremented four times in
registers, the ten rounds are applied to the four blocks in an interleaved
order, and `AESENC`'s four-cycle latency is covered by three other blocks
rather than by nothing.  The feature test happens once per group of four
blocks rather than once per block.  Together with the GHASH work above
this took AES-128-GCM on 256 KiB from 875 to 319 microseconds.

**One translation unit, two instruction sets.**  AES-NI code has to be
compiled with `-maes`, and the rest of the library must not be, or it would
fault on a machine without the instructions; GCC and Clang both refuse to
inline a `target`-attributed intrinsic into a caller without the attribute, so
a wrapper in a header is not enough.  Custard's `CPrologue` puts a verbatim
string on a declaration and `custard_c_closure_prologue` puts one on a
*copy* of everything that declaration reaches -- a helper the baseline path
also calls keeps its undecorated original for that path.  So `cipher_ni` and its subtree get
`__attribute__((target("aes,pclmul,ssse3,sse4.1")))` and the dispatcher, one
call up, does not.  Feature detection is `__builtin_cpu_supports`.

**Other architectures.**  The same C has to compile where there is no
AES-NI to call: on aarch64 the `target` attribute, the intrinsics and
`__builtin_cpu_supports("aes")` are all errors.  So every function carrying
an x86 `target` also carries `custard_c_closure_guard "defined(__x86_64__)"`,
which puts it and every copy its closure prologue makes inside `#if
defined(__x86_64__)`, and every dispatcher tests `Hacl.X64.x86_64`, an
`assume val` with `custard_c_ifdef "defined(__x86_64__)"`:

```
if (Hacl.X64.x86_64) {
  if Vec.supported () { Hacl.AES.NI.cipher_ni p st w }
  else { Hacl.AES.Cipher.cipher_portable p st w }
} else { Hacl.AES.Cipher.cipher_portable p st w }
```

Custard prints that `if` as `#if` / `#else` / `#endif`; F\* knows nothing
about the flag, so both arms are verified.  Nothing ties the flag's
condition to the guard's, and a call that escapes the test fails only on the
other architecture, as an undeclared function -- which is what `make cross`
is for: it compiles `dist/Hacl.c` and the tests with
`aarch64-linux-gnu-gcc` and runs them under `qemu-aarch64` (all but the
constant-time audit, whose timings under an emulator measure the emulator).

Three things the guard alone does not cover.  A portable function that only
x86 code reaches -- `hash_impl_ni`, `gtag_fin`, the HKDF expansion over
`blocks_ni`, and the streaming and HMAC instances below them -- would be an
unused or dangling `static` on aarch64.  So those roots carry the guard with
an empty `custard_c_closure_prologue ""`, which copies everything only they
reach under the same `#if`.  A parameter that only the `#if` arm reads is
unused in the `#else` arm, because Custard decides on `(void)x` before the
preprocessor runs.  So the flag is tested in the caller that uses the
parameters anyway (ChaCha20, Salsa20 and Poly1305 call their guarded
`encrypt_vec` and `absorb_vec` only under it), rather than inside the vector
function.  And a guard covers functions, not types: `c/Hacl_Vec128.h`
still defines `Hacl_Vec128_t`, as sixteen opaque bytes, off x86-64, for
the pair and triple structs `Hacl.h` declares.

**The intrinsics are axioms, and they are tested.**  `lib/Hacl.Vec128.fst` is
all `assume val`s, realized by `c/Hacl_Vec128.h`; the postcondition of
`aesenc` *is* the claim that the hardware computes `Spec.AES.round`, and
nothing in F\* can check it.  This is the second entry in the trusted
computing base after the entropy shim, and much the bigger one.  Two things
keep it honest.  Each axiom is stated against the specification the rest of
the library is already verified against, so there is one notion of what AES
is and the axiom either matches it or is visibly wrong.  And
`tests/test_vec128.c` evaluates every axiom against a fresh transcription of
FIPS 197 -- its own S-box table, its own ShiftRows, its own MixColumns,
sharing nothing with the library -- on every constant block, on edge cases and
on four thousand random inputs.  Perturbing one coefficient of the reference
makes all 4097 cases fail, which is the check that the test is checking
something.

`lib/Hacl.Vec256.fst`, under ChaCha20 and Poly1305, is the third entry and
is kept the same way.  Its axioms are smaller -- lane-wise add, exclusive-or
and rotate, a broadcast, two constants, and the six permutations of an 8 x 8
transpose, each stated as which input lane every output lane is; and for
Poly1305 sixty-four-bit add, `vpmuludq`, shifts, a 26-bit mask, a broadcast,
a set and a store, each stated on natural numbers with the wrap-around
written out -- and "lane" is not an axiom but a definition, the
little-endian reading of the register's bytes (a sixty-four-bit lane is two
thirty-two-bit ones, low first).  `tests/test_vec256.c` checks each against a
scalar transcription on a thousand random inputs, every rotation and shift
distance and every load misalignment; `tests/test_chacha20_vec.c` runs every
message length from 0 to 2,100 bytes, at counters up to the last legal
block, against an independent RFC 8439 block function, and
`tests/test_poly1305_vec.c` does the same for Poly1305 against a plain
bignum reference, with the largest clamped *r* and all-ones messages among
the inputs.  Swapping one permute immediate in `c/Hacl_Vec256.h` fails both
ChaCha20 tests.  `lib/Hacl.Vec512.fst` is the fourth, with seventeen axioms
(lane-wise add, exclusive-or and `vprold`, a broadcast, two constants, the
four unpacks and four `vshufi32x4` group selections), each checked by
`tests/test_vec512.c` in the same way, the rotate also at a distance the
compiler cannot see; the same two ChaCha20 tests exercise it, since every
length from 1,024 bytes on goes through it on an AVX-512 machine.  Salsa20's
two vector paths use the same two axiom sets, and `tests/test_salsa20_vec.c`
runs every length from 0 to 2,100 bytes at seven counters against an
independent Salsa20 block function.

**The key schedule needed the same treatment, and was worth more than the
cipher.**  It runs once per message rather than once per block, which is why
it was left alone at first --- but a message can be sixty-four bytes long,
and then it is the entire cost.  The portable S-box is the algebraic one: an
inverse in GF(2^8) computed as *a^254* by fifteen field multiplications, each
seven `xtime`s and eight conditional exclusive-ors.  That is about three
hundred and fifty operations, and because each depends on the one before it
is also about three hundred and fifty cycles.  An AES-128 schedule needs
forty of them and an AES-256 schedule fifty-two, so expanding a key cost
fourteen thousand cycles --- more than a thousand cycles per round key, for
an operation that touches 176 bytes.  A table would be four cycles, but the
input is the key, so a table would be a cache-timing oracle on the key and is
not an option.

The measurement that found it is the plainest one available: AES-256's
fixed per-call cost divided by AES-128's is 18289/14044 = 1.302, and 52/40 =
1.300.  Nothing else in the call has that ratio.

`AESKEYGENASSIST` does four S-box lookups in one instruction, in constant
time, and is exactly what the hardware provides for this.  It also
exclusive-ors in a round constant taken as an immediate, which is why this
was passed over once before: an immediate needs one extern per value, and
there are ten of them.  But the round constant may be *zero*, and then the
instruction is nothing but `SubWord` --- and `Hacl.AES.Key` already carries
the round constant in a register and exclusive-ors it in itself.  So one
binding serves every round.  `Hacl.Vec128.subword` is that binding, and its
axiom is about the four bytes it is used for:

    assume val subword (a: t)
      : r: t { forall (i: nat). i < 4 ==>
                 Seq.index (bv r) (8 + i) == sbox (Seq.index (bv a) (12 + i)) }

`Hacl.AES.SubWord` dispatches on `Vec.supported ()` exactly as
`Hacl.AES.Block` does, and both branches leave the same specification value
behind, so `Hacl.AES.Key` proves nothing new: the four calls to `sbox_impl`
became one call to `subword4` and four array reads.  The scratch block is the
caller's, so a whole key schedule allocates sixteen bytes once and branches
thirteen times.

Expanding an AES-128 key went from 14,044 cycles to 1,021.  What that is
worth depends entirely on the message, because the cost it removes is flat:

| AES-128-GCM | before | after | speedup | was | now |
|---|---:|---:|---:|---:|---:|
| 64 bytes | 13 MB/s | 138 MB/s | **10.3x** | 77.45x | **7.54x** |
| 1 KiB | 172 MB/s | 637 MB/s | **3.70x** | 18.16x | **4.97x** |
| 16 KiB | 672 MB/s | 812 MB/s | **1.21x** | 5.38x | **4.51x** |
| 256 KiB | 803 MB/s | 809 MB/s | 1.01x | 4.53x | **4.48x** |

AES-256 is the same shape and a little larger, because its schedule is a
little longer: 10 MB/s to 117 at sixty-four bytes, 84.56x of the reference
down to **7.43x**.  The last two columns are against EverCrypt's Vale
assembly, and its own numbers did not move between the two runs.  Under
clang the figures are 140 MB/s and **7.39x** at sixty-four bytes and 868
MB/s and **4.22x** at 256 KiB, so neither compiler is doing anything
special with either version.

Nothing in the cipher, the counter mode or the GHASH changed.  The lesson is
the one the whole performance section keeps repeating in different words:
the profile was never taken, and a cost that is invisible in a bulk
throughput number can be the entire cost of a realistic call.  Sixty-four
bytes is a TLS record header, a QUIC packet, a database field --- and it was
running at thirteen megabytes a second.

### One attribute in the wrong place, and three quarters of the time

A machine may have the SHA extensions without AES-NI, or the reverse, so
`c/Hacl_Vec128.h` keeps them under two different `__attribute__((target(...)))`
sets and the generated functions that use them carry the matching attribute:
`target("aes,pclmul,ssse3,sse4.1")` for the AES and GHASH code,
`target("ssse3,sse4.1,sha")` for SHA-256's block function.  The header says in
as many words that nothing under one may be called from a function compiled
under the other.

Under clang, SHA-256 on 256 KiB took **668 us** where gcc took 227.  It was
not unrolling: `-O2` and `-fno-unroll-loops` were within 2% of `-O3`.  It was
not the dispatch: forcing the scalar path made clang 1,300 us, so the
intrinsics were still winning, only by half of what they should.  Both
compilers emitted the same count of `sha256rnds2`, `sha256msg1` and
`sha256msg2`.  The tell was that `-march=native` made the whole difference
vanish -- clang became 168 us, *faster* than gcc -- which says the problem was
not the code but the attribute.

Disassembling the block function found thirty-nine `callq` in it, all to the
same symbol, and no `sha256msg1` or `sha256msg2` at all: they had been pushed
out into calls.  The symbol was `Hacl_Impl_Sub_sub__t_2`, which is
`Hacl.Impl.Sub.sub` monomorphized at `uint32`, and whose entire body is

```c
__attribute__((target("aes,pclmul,ssse3,sse4.1")))
static uint32_t *Hacl_Impl_Sub_sub__t_2(uint32_t *a, size_t i, size_t j) {
  (void)j;
  return (a + i);
}
```

Pointer arithmetic, stamped with the **AES** feature set, although its only
callers in the entire distribution are SHA-256's.  clang will not inline a
callee whose target features are not a subset of the caller's, and
`aes,pclmul` is not a subset of `ssse3,sse4.1,sha`, so every `a + i` in the
message schedule and in the round loop became a function call.  gcc inlines
it anyway, which is why gcc never showed the problem -- though gcc was paying
for it too, in a smaller way, by having to clone the function to do so.

Deleting the attribute by hand from the generated C took clang from 668 us to
178.  The fix in the source is not to correct the attribute but to remove the
function: `sub` is now `inline_for_extraction`, so no monomorphization of it
exists to be mislabelled.  Its own doc comment had always claimed that "in C
this is pointer arithmetic and nothing else", and that is now true.

| | before | after |
| --- | ---: | ---: |
| SHA-256, 256 KiB, gcc | 227 us | **190 us** |
| SHA-256, 256 KiB, clang | 668 us | **179 us** |
| HMAC-SHA-256, 256 KiB, gcc | 227 us | **190 us** |
| HMAC-SHA-256, 256 KiB, clang | 678 us | **179 us** |

Under clang that is 3.7x on both rows, and it moves SHA-256 from the largest
reachable gap in the suite to 1.10x of HACL\* best.  gcc gains 1.20x, and
Ed25519, HKDF-extract and the other `sub` callers gain a percent or two
apiece.  `mk/clones.baseline` goes from sixty-nine entries to sixty-eight:
the one that disappeared is `Hacl_Impl_Sub_sub__t_2` itself, which gcc had
been specialising precisely because it could not be left as a call either.

The general lesson is narrower than the usual one and worth stating on its
own.  A `target` attribute is not an optimization hint, it is a *partition*
of the program, and a function that lands in the wrong partition does not
fail to compile and does not fail its tests --- it silently stops being
inlinable across the boundary.  Any helper shared between two instruction-set
paths should be `inline_for_extraction`, so that it has no single home to be
assigned to.

### The key schedule with no memory in it at all

`AESKEYGENASSIST` took the schedule from 14,044 cycles to 1,021 and that was
where it was left.  A profile taken much later put the remaining cost at 258
nanoseconds for an AES-128 schedule and 323 for AES-256, against a 329
nanosecond fixed cost for the whole of AES-128-GCM.  The schedule was still
almost the entire per-call overhead, and a sixty-four-byte message is
nothing but per-call overhead.

**The cost was the round trip, not the S-box.**  `subword4` -- one
`AESKEYGENASSIST` and the loads around it -- measures 8.6 ns, and forty
words need ten of them, so under a hundred nanoseconds of the 258 is the
instruction.  The rest is that the schedule was a loop over *words*: load
four bytes, exclusive-or four bytes, store four bytes, and the store of one
word is the load of the next.  Ten store-to-load forwards per round key with
a dependency through each of them is what four-byte granularity costs.

**A whole round key is one register, and the recurrence fits in it.**  FIPS
197 says each word is the word four back exclusive-ored with the word one
back, except at a multiple of the key length where a transformed word is
mixed in.  Written over sixteen bytes at once that is

    K_i = (k ^ (k << 4) ^ (k << 8) ^ (k << 12)) ^ t

where `k` is the round key one key-length down, the shifts are in *bytes*,
and `t` is a term with period four: `RotWord(SubWord(w3)) ^ Rcon` at a
multiple of the key length, `SubWord(w3)` halfway through an AES-256 round
key.  The four-byte prefix exclusive-or is three `PSLLDQ`s and three
`PXOR`s, and it is a prefix exclusive-or precisely because the *argument* is
shifted rather than the running total --- shifting the total and
exclusive-oring it back would cancel in GF(2).  The period-four term is the
`AESKEYGENASSIST` result put through one `PSHUFB`, with the round constant
broadcast by `PSHUFD` and exclusive-ored in, so `Hacl.Vec128` gains three
axioms -- `bcast_rot`, `bcast_sub` and `word_bcast` -- and
`shift_left_bytes_4` is restated byte-wise.  A round key is then eleven
instructions, one load, one store, and no forwarding at all.

**Three SMT pathologies had to be got around, and each has a name.**  The
first is that `Spec.Byte.( ^^ )` is `U8.v (U8.logxor (uint_to_t a)
(uint_to_t b))`, and knowing `b == 0` as integers does *not* give
`a ^^ b == a ^^ 0`: the literal `0uy` is a bit-vector constant while
`uint_to_t b` is a boxing application, and congruence closure does not cross
between them.  The whole prefix-exclusive-or algebra is therefore done at
`FStar.UInt.logxor`, where the arguments are plain integers, and brought
back one application at a time by `lx_is`; two derived bridges, `xor_cong`
and `xor_drop`, do all the rewriting elsewhere.

The second is that a quantifier over `Seq.index x (8 + i)` will not
discharge a goal about `Seq.index x (8 + j % 4)` with symbolic `j`, though
ground offsets are fine because Z3 normalizes them.  So `is_rot_term`,
`is_sub_term` and the sixteen instantiations in `round_all` are all stated
at literal indices, the same trick `Hacl.AES.SubWord` already used.

The third is the one that cost the most time.  `pfx`, the prefix
exclusive-or, was written `unfold`, so every fact derived from it carried a
four-term exclusive-or of conditionals; sixteen of those in one context and
the solver spends its entire budget on the hypotheses rather than the goal.
Making `pfx` an ordinary definition -- still unfolded by the SMT encoding,
but folded in the terms the solver sees -- took `round_all` from a
five-hundred-second failure to zero.  The same principle governs the rest of
the proof: every bridge between the register's own sixteen bytes and the
expanded key is a standalone lemma (`block_step`, `block_tele`,
`block_grp4`, `mk_join4`, `load_index`, `grp_mod`), because inside the Pulse
function the query also carries the heap, four separated-conjunction
predicates and every byte of the key, and a goal as small as `Seq.length
(Seq.slice vw0 b b2) == 16` will time out there while closing instantly on
its own.

Expanding an AES-128 key went from 258 ns to **26.4**, AES-256 from 323 to
**49.0**, and the fixed cost of an AES-128-GCM call from 329 ns to **89.8**.

| AES-128-GCM | before | after | speedup | was | now |
|---|---:|---:|---:|---:|---:|
| 64 bytes | 148 MB/s | 328 MB/s | **2.22x** | 7.06x | **3.18x** |
| 1 KiB | 1,020 MB/s | 1,323 MB/s | **1.30x** | 3.11x | **2.38x** |
| 16 KiB | 1,850 MB/s | 1,856 MB/s | 1.00x | 1.96x | 1.96x |

AES-256-GCM moves the same way, 6.89x to **3.27x** at sixty-four bytes and
3.14x to **2.41x** at a kilobyte.  Under clang the figures are 6.84x to
**3.27x** and 2.72x to **2.03x**.  Nothing else in the benchmark moved by
more than measurement noise, which is the control: the portable schedule is
still there as `ks_loop_scalar` and is still what runs without AES-NI.

### Where the GHASH loop should start aggregating

GHASH multiplies in `GF(2^128)`, and the multiplication splits into a
carry-less product and a reduction.  The product of four blocks can be
accumulated before a single reduction is applied -- Horner's rule run four
terms at a time -- which is why `ghash_loop4_ni` exists, and eight at a time
is why `ghash_loop8_ni` exists.  Aggregating is not free: four at a time
needs `H^2`, `H^3` and `H^4`, and eight needs `H^5` through `H^8` as well,
so entering the four-way pass costs three extra multiplications and
entering the eight-way pass costs four more.  Those are paid once per
*call*, not once per group, and they do not amortize when the call is
short.

The thresholds were set to the smallest size at which each pass can run at
all: sixty-four bytes for the four-way loop and a hundred and twenty-eight
for the eight-way one.  Measured, both are much too low.  A bare
`ghash_upd` on this machine, gcc:

| bytes | 64 | 96 | 128 | 192 | 256 | 384 | 512 | 768 | 2048 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| serial | 62.3 | 93.4 | 123.4 | 182.3 | 241.2 | 359.4 | 477.9 | 714.5 | 1888 |
| four-way from 64 | 69.5 | 101.4 | 124.3 | 152.4 | 181.2 | 238.0 | 294.9 | 407.1 | 1013 |
| eight-way from 128 | | | 147.6 | 176.5 | 194.7 | 238.4 | 284.5 | 376.9 | 833 |

One group of four loses to four serial multiplications, because three
multiplications have been spent to save three reductions and the reductions
are the cheaper half.  Two groups win.  The eight-way pass is worse still:
it is behind the four-way one all the way to five hundred and twelve bytes
and only level at seven hundred and sixty-eight.  So the four-way pass
starts at two groups and the eight-way pass starts at seven hundred and
sixty-eight bytes, and below each threshold the limit is simply zero --
which the existing contracts already allow, since `ghash_start` asks only
for `lim % 64 == 0 /\ lim <= n` and `lim8 % 128 == 0 /\ lim8 <= lim`.  The
one thing that needed care is the second conjunct: with independent
thresholds `lim8` could overshoot a `lim` that had been declined, so
`eight_limit` now takes `lim` as an argument and returns something no
larger.  The proof is four lines and the existing `lim_bounds` and
`lim8_bounds` do all the arithmetic.

`ghash_upd` on a hundred and twenty-eight bytes goes from 151.7 ns to
**97.9**, on a hundred and ninety-two from 179.1 to **127.5**, on two
hundred and fifty-six from 195.1 to **155.7**; under clang, which has a
faster serial loop and a much faster aggregated one, the same three sizes
go 100.1 to **65.9**, 121.0 to **85.5** and 139.1 to **103.6**.  Above
seven hundred and sixty-eight bytes nothing changes algorithmically and the
measurements move by one to two percent in the wrong direction, which is
the branch's effect on code layout rather than on work done.

The same pass removes a smaller waste.  `ghash_upd_impl` allocates a
sixteen-byte scratch block to hold the final partial block, zeroes it, and
then uses it only if there is a partial block; for any length that is a
multiple of sixteen -- which includes the length block that closes every
GCM tag -- those sixteen stores are dead.  Moving the `let mut` inside the
branch that reads it is a one-line change in Pulse and the frame works out
on its own.

| AES-GCM, gcc | before | after | was | now |
|---|---:|---:|---:|---:|
| AES-128-GCM, 64 bytes | 328 MB/s | 351 MB/s | 3.18x | **2.98x** |
| AES-256-GCM, 64 bytes | 266 MB/s | 282 MB/s | 3.27x | **3.12x** |
| AES-128-GCM, 256 KiB | 1,858 MB/s | 1,877 MB/s | 1.99x | 1.97x |

Whole-call, a sixty-four-byte AES-128-GCM encryption goes from 169 ns to
**157**.  Under clang the sixty-four-byte row does not move, for a reason
worth recording: clang's serial multiplication is already fast enough
(14.0 ns a block against gcc's 17.9) that its four-way pass wins at
sixty-four bytes where gcc's loses, so the threshold that is right for one
compiler is one size too high for the other.  The eight-way threshold,
which is where the large gains are, is right for both.

What is left of the fixed cost is now almost all latency.  Of the 42 ns an
AES-128-GCM call spends in `gtag_impl` with no associated data and no
message, 15 are one AES block encryption of `J0` and 19 are one GHASH
multiplication of the length block, and both are dependent chains that no
amount of dispatch tuning will shorten.  Shortening the multiplication is
the next section.

### Removing the one-bit shift from GHASH

GHASH numbers the bits of a block the other way round from `PCLMULQDQ`.
After reversing the bytes, the carry-less product of two GHASH blocks sits
one bit too low, and `raw_product` has always corrected it the obvious way:
shift the 255-bit product left by one before reducing.  There is no
128-bit shift instruction, so that is a `PSRLQ`, a `PSLLQ`, a byte shift
and three `POR`s per product --- six instructions, and in the eight-way
loop eight products are formed before anything is reduced, so the shift was
the single largest item left in the multiplier.  The roadmap proposed
hoisting it out of the loop and doing it once per group, which the
linearity of the shift permits.

It can be removed altogether instead.  Write `NS(a, b)` for what the
multiplier computes without the shift; then `NS(a, b) = x * (a * b)` in the
field.  If the hash key is stored pre-divided by `x` --- `H' = H / x`, done
once, when the key is expanded --- then `NS(a, H') = a * H` exactly, and
every multiplication the cipher will ever do is correct with no shift at
all.  The key powers need no correction either: starting the recurrence at
`H'` gives `H^i / x` at every step, which is precisely the pre-divided form
of `H^i`.  That is one lemma, `power_step`, three lines long.

`Hacl.AES.GF128`, `.GMul` and `.GHash` have no public exports --- only
`Hacl.AES.GCM` uses them --- so the representation of the key array could
simply be changed, and the specification of every function that mentions
it now reads `Poly.xtimes (vals vh)` where it used to read `vals vh`.  The
portable multiplier, which does not have the shift to begin with, pays one
extra `shift_reduce_impl` per block to compensate; against the
128-iteration bit loop it already runs, that is free.

The proof is four new pieces of polynomial algebra.  `clmul_halves_ns` says
the two unshifted registers reverse to the halves of `pshift P 1`, where
`P` is the carry-less product.  `psplit` reduces an arbitrary
256-coefficient polynomial given its two halves --- the existing
`gmul_split` did this only for products, and generalising it off products
is what makes the rest possible.  `pmod_shift1` says
`pmod (pshift a 1) n == xtimes (pmod a n)` whenever `a` has no coefficient
at `n - 1`, which is the one place the representation of `pmod` as a sum
over set bits pays for itself: it is a restatement of
`x^(k+1) = x * x^k` and nothing else.  The side condition is discharged by
`pcoef_top`, which says the product of two 128-bit blocks has no `x^255`
term.  Composing them with the existing `gmul_xt_right` gives
`pmod (pshift1 x y) 256 == gmul x (xtimes y)`, which is the whole claim.

Dividing by `x` is the mirror image of multiplying by it: shift the block
left by one bit, and if the bit that fell off the bottom was set, add
`R / x`, which is `x^127 + x^6 + x + 1` --- `0xc2` in byte zero and `1` in
byte fifteen.  `xdiv_impl` is sixteen byte operations and
`Spec.GF128.Poly.xtimes_xdiv` proves it inverts `xtimes`.  It is worth
writing the loop so that byte fifteen, which has no successor to take a
carry from, is handled after the loop rather than by a test inside it: the
test was the only branch in the body and removing it took the function
from 13.8 ns to **5.1**, which at sixteen bytes is most of what the change
wins back on the GHASH side.

| AES-GCM | before | after | gain | was | now |
|---|---:|---:|---:|---:|---:|
| AES-128-GCM, 256 KiB, gcc | 1,877 MB/s | **2,329 MB/s** | +24.1% | 1.97x | **1.58x** |
| AES-128-GCM, 16 KiB, gcc | 1,860 MB/s | **2,326 MB/s** | +25.1% | 1.97x | **1.57x** |
| AES-128-GCM dec, 16 KiB, gcc | 1,869 MB/s | **2,318 MB/s** | +24.0% | 1.98x | **1.58x** |
| AES-256-GCM, 256 KiB, gcc | 1,692 MB/s | **2,039 MB/s** | +20.5% | 2.03x | **1.69x** |
| AES-128-GCM, 1 KiB, gcc | 1,323 MB/s | **1,555 MB/s** | +17.5% | 2.40x | **2.02x** |
| AES-128-GCM, 256 KiB, clang | 2,185 MB/s | **2,610 MB/s** | +19.5% | 1.67x | **1.40x** |
| AES-128-GCM, 16 KiB, clang | 2,206 MB/s | **2,633 MB/s** | +19.4% | 1.65x | **1.38x** |
| AES-256-GCM, 256 KiB, clang | 1,920 MB/s | **2,261 MB/s** | +17.8% | 1.77x | **1.50x** |

Measured against the previous commit back to back on the same core, the
whole-call numbers are +29.5% at 256 KiB, +22% at a kilobyte, +12.5% at
256 bytes, +4.2% at sixty-four bytes and **-2.0%** at sixteen, where the
5 ns of key division still outweighs what two GHASH multiplications save.
That last row is an artefact of the one-shot API expanding the key on every
call, and it is the best argument yet for the expanded-key context in the
roadmap: a context divides the key once and the sixteen-byte row joins the
others.

A standalone `ghash_upd` fell 21% at sixteen bytes rising to 30% at two
kilobytes.  The four-way and eight-way dispatch thresholds were re-swept
over twelve A/B builds afterwards, since a cheaper serial multiply could in
principle have moved the crossovers; 128 and 768 are still the right
choices, because the aggregated passes got cheaper by the same factor.

### An expanded-key context for AES-GCM

Every AES-GCM call in this repository used to begin by expanding the key:
about 26 ns of `AESKEYGENASSIST` for AES-128, one block encryption for the
GHASH subkey, and since the previous section 5 ns more to divide that
subkey by `x`.  None of it depends on the nonce, the associated data or the
message, and a caller that talks to the same peer more than once was paying
for all of it on every message.  The comparison was asymmetric too:
EverCrypt exposes `EverCrypt_AEAD_create_in` and encrypts against the
handle, so the benchmark's reference side paid the schedule once and this
side paid it per call.

The split is the obvious one.  `Spec.GCM.gcm_encrypt_w` is `gcm_encrypt`
with the expansion already done --- it takes `w`, the round keys, instead
of `key` --- and `gcm_encrypt` is now literally `gcm_encrypt_w v
(key_expansion v key)`, so the two compose by unfolding one definition and
no caller is ever asked to reason about what a round key is.  On the
implementation side `expand_impl` is the key-expansion and subkey steps,
`encrypt_w` and `decrypt_w` are everything after them, and the one-shot
`encrypt` and `decrypt` are the two in sequence over a stack context.  The
whole change verified first try, which is what one hopes for from a
refactoring that moves no proof.

The context is two arrays, not one.  `ek` is the round keys, 176 bytes for
AES-128 and 240 for AES-256; `hk` is the GHASH subkey, held divided by `x`
-- sixteen bytes at the time of this section, a hundred and twenty-eight
once the next one puts the key's powers beside it.  One array would have been tidier in the header and much
less tidy in the proof: every function underneath wants a whole array it
can be handed, `Hacl.Impl.Sub` lends out one window at a time, and nothing
here needs the two to be adjacent.

| AES-GCM, 64 bytes | one-shot | expanded | gain | was | now |
|---|---:|---:|---:|---:|---:|
| AES-128-GCM, gcc | 357 MB/s | **496 MB/s** | +38.9% | 2.92x | **2.11x** |
| AES-256-GCM, gcc | 291 MB/s | **462 MB/s** | +58.8% | 2.99x | **1.90x** |
| AES-128-GCM, clang | 326 MB/s | **477 MB/s** | +46.3% | 3.19x | **2.18x** |
| AES-256-GCM, clang | 285 MB/s | **444 MB/s** | +55.8% | 3.06x | **1.97x** |
| AES-128-GCM, 1 KiB, gcc | 1,555 MB/s | **1,695 MB/s** | +9.0% | 2.02x | **1.87x** |
| AES-256-GCM, 1 KiB, clang | 1,551 MB/s | **1,784 MB/s** | +15.0% | 1.81x | **1.57x** |

Measured directly, the fixed cost removed is 35.6 ns: a sixteen-byte
AES-128-GCM encryption goes from 131.4 ns to **95.8**, sixty-four bytes
from 166.6 to **132.7**, a kilobyte from 600.5 to **569.2**.  That is more
than the 29 ns the roadmap predicted, the difference being the key division
the previous section added.  AES-256-GCM gains more than AES-128 because
its schedule is half again as long, and at sixty-four bytes it is now
**1.90x** of EverCrypt's Vale assembly, the first AES-GCM measurement in
this repository to go under 2x at a short length.

The entry points are `Hacl_AES_GCM_aes128_expand`,
`Hacl_AES_GCM_aes128_encrypt_expanded` and
`Hacl_AES_GCM_aes128_decrypt_expanded`, and the same three for AES-256; the
one-shot four are unchanged.  `tests/test_gcm.c` now runs all 450 CAVP
cases through both paths.

Caching the key powers in the context as well is the obvious next step, and
is the next section.

### The powers of the key belong with the key

Sixty-four bytes of AES-128-GCM was, for a long time, the largest gap in
the library.  The diagnosis is blunt and took one experiment: stub GHASH
out of the generated C entirely and a sixty-four-byte encryption falls
from 131.0 ns to **57.8**.  GHASH is seventy-three of those hundred and
thirty-one nanoseconds, and sixty-one per cent of the time at sixteen
kilobytes.

*Where the GHASH loop should start aggregating* explains why the fast loop
was not being used on short messages: four-way aggregation needs `H^2`,
`H^3` and `H^4`, eight-way needs `H^5` through `H^8`, and those were
computed at the top of every call by three and then four serial
multiplications.  Three dependent carry-less products and their reductions
cost more than one group of four saves, which is why the four-way
threshold sat at a hundred and twenty-eight bytes and the eight-way one
higher still.  Lowering the thresholds and changing nothing else makes
matters worse, exactly as that section predicted: the four-way pass from
sixty-four bytes measures 142.0 ns against a 129.8 ns baseline.

But the powers are a function of the key alone, and the library has had an
expanded-key context since the previous section.  So the context grows from
sixteen bytes to a hundred and twenty-eight, holding `h/x`, `h^2/x`, ...
`h^8/x` -- the same pre-divided representation the key itself already used,
because that is what the multiplier both consumes and produces, so nothing
else in the file changes shape.  `hkey_impl` builds the eight with seven
calls to the dispatching `gmul_impl`, once per key.  `ghash_start` loads
what it used to compute, both thresholds become unconditional, and the
whole-block loop runs four-way from the first sixty-four bytes and
eight-way from the first hundred and twenty-eight.

**The specification states the recurrence, not a closed form.**
`Spec.GF128.Algebra.pows_ok` says only that each window of the context is
the previous one advanced by the first.  That is exactly what the loops
consume and exactly what the expansion establishes, one step at a time, so
nothing anywhere has to know what `h^5` *is*.  `pow_adv` is the one line
that turns what the multiplier gives -- `gmul a (xtimes b)`, the real
product with one shift omitted -- into what the recurrence asks for, and it
is a single application of `gmul_xt_left`.

**Where a fact is proved matters more than whether it is true.**  Proving
`pows_ok` at the point where the array is written asks the solver to work
in a context holding eight intermediate array states and the frames that
relate them; the seventh step of the recurrence then times out where the
first and the sixth do not.  `pows_build` takes the eight blocks and the
seven products between them, and nothing else, and goes through at once.
The windows themselves come back from the array with one
`Seq.lemma_eq_intro` each.

Measured on one core, best of three interleaved rounds, AES-128-GCM
encryption with a sixteen-byte AAD, in nanoseconds:

| | gcc before | gcc after | clang before | clang after |
|---|---:|---:|---:|---:|
| 64 bytes | 129.8 | **114.6** | 134.5 | **114.9** |
| 128 bytes | 170.7 | **138.3** | 157.8 | **135.6** |
| 256 bytes | 236.9 | **189.5** | 212.2 | **184.9** |
| 1024 bytes | 600.6 | **509.7** | 499.6 | **462.0** |
| 16384 bytes | 6958 | 6889 | 6010 | 6042 |

In the published suite the four short-message GCM rows move and nothing
else does.  Sixty-four-byte AES-128-GCM goes from 2.14x of EverCrypt to
**1.87x** and AES-256-GCM to **1.71x**.  Bulk GHASH is untouched by this
change and is where the remaining gap lives: thirteen and a half cycles
per sixteen-byte block, against four `PCLMULQDQ` that Karatsuba would make
three.  That is the next section.

### Karatsuba, and what a group of blocks may put off

An assembly census of the inlined eight-way GHASH loop says where the
thirteen and a half cycles go: 247 instructions for eight blocks, of which
32 are `PCLMULQDQ` and **82** are plain register copies.  The multiplier is
not the bottleneck; the traffic around it is.

Two of the four multiplies a block are the crossed terms, and only their
sum is ever used.  Over a field of characteristic two Karatsuba computes
that sum exactly, with no borrow to carry and no wider intermediate:

```
(x0 + x1)(y0 + y1) + x0 y0 + x1 y1  =  x0 y1 + x1 y0
```

Folding an operand's two lanes together is a shift and an exclusive-or, and
taking the two square terms back out is two more, so the trade is one
`PCLMULQDQ` against about five cheap instructions.  **On its own that is
not a win.**  The first version of this change did exactly that and cost
128-byte AES-GCM twelve per cent while gaining five on bulk: with nothing
to amortise, the fold sits on the dependency chain and the saved multiply
does not pay for it.

What makes it pay is that everything Karatsuba adds is *linear*, and the
bulk loop adds eight products together before it reduces.  Both the
correction that removes the squares and the assembly of the middle term
into the two halves therefore commute with that sum, and may be done once
for the group rather than once a block.  So `kara_parts` leaves three raw
registers behind -- low, high, and the folded product -- the loop keeps
three accumulators instead of two, and `kara_fold` runs once at the end:
twenty-four multiplies a group instead of thirty-two, and six cheap
instructions a group instead of forty.

**The proof deferred the same way the code did.**  `Spec.CLMUL` gains
`kmid` for the correction and `kfold_lo`/`kfold_hi` for the assembly, each
with a bit-level characterisation and additivity over sums of four and of
eight.  The per-block halves then exist only as ghost blocks that are never
computed, and `Spec.GF128.Algebra.pmod_defer4` and `pmod_defer8` -- which
already took the per-block halves as arbitrary blocks rather than as
registers -- go through unchanged.  The Karatsuba identity itself is two
applications of the bilinearity of `conv` over `padd` that `Spec.CarryLess`
already had.  Nothing in the reduction, or in the argument that removes the
one-bit shift, moved at all.

A single multiplication keeps all four multiplies, for the reason the
twelve-per-cent regression showed: `raw_product` is unchanged, and only
`gmul4_vec` and `gmul8_vec` are Karatsuba.

The eight-way loop body is now 194 instructions with 24 `PCLMULQDQ` and 58
register copies; the four-way body 118 with 12.  In the published suite
AES-GCM moves and nothing else does:

| | gcc | clang |
|---|---:|---:|
| AES-128-GCM, 1 KiB | 1.09x | 1.10x |
| AES-128-GCM, 16 KiB | 1.09x | 1.14x |
| AES-128-GCM, 256 KiB | 1.09x | 1.14x |
| AES-128-GCM dec, 16 KiB | 1.09x | 1.13x |
| AES-256-GCM, 256 KiB | 1.08x | 1.12x |

Against EverCrypt, 256 KiB AES-128-GCM goes from 1.56x to **1.43x** under
gcc and to **1.22x** under clang.  No benchmark in the suite regresses by
as much as two per cent under either compiler.

### The compiler is allowed to undo a constant-time algorithm

A windowed scalar multiplication reads one of sixteen precomputed points,
and the four bits that say which one are secret.  The read is therefore
written to touch all sixteen: build a mask per entry, all ones for the one
wanted and all zeroes for the other fifteen, and fold every entry through
its own mask.  `Hacl.Bignum.Base.table_select` is that loop, and Ed25519,
P-256, secp256k1 and the generic modular exponentiation all go through it.

**The verified statement is about the value, and the property wanted is not
about the value.**  F\* proves that `table_select` returns entry *d*.  It
has no vocabulary for "and takes the same time whichever *d* that was",
because that is a claim about emitted instructions, not about a result.
The constant-time argument is carried entirely by the expectation that a C
compiler will emit mask arithmetic as mask arithmetic.

It is not obliged to.  The sixteen masks are sixteen comparisons of a
runtime value against the literals zero through fifteen; a compiler that
unrolls the loop sees that, and may decide the cheapest correct code is a
cascade that tests the secret digit and jumps straight to the entry it
names.  **clang at `-O3` did exactly this.**  Timed once per digit, the
shipped lookup rose monotonically from 3.7ns at *d* = 0 to 8.9ns at
*d* = 15 — a 158% spread, which is the whole digit legible from outside.
gcc, on the same source, was flat to 1%.

Two changes fix it, and both were measured before being written.

**A value barrier on the mask.**  `Hacl.Launder.launder` is the identity,
and its whole content is that the generated C contains a call the optimizer
cannot see through — an empty `asm` statement with a `"+r"` constraint,
which emits no instruction but returns a value the compiler knows nothing
about.  A laundered mask cannot be recognised as the result of a
comparison, so there is no comparison left to turn into a branch.  The
barrier goes on the mask, not on the secret: laundering the secret would
leave the sixteen comparisons against literals exactly where they were.

**The order of the two loops.**  Accumulating into `res[j]` makes a chain
of sixteen read-modify-writes through memory on every limb, and since the
limb count is a run-time value neither loop can be unrolled around it.
Running the sixteen entries *innermost* keeps the accumulator in a register
and gives the inner loop a trip count known at compile time.  That is worth
about 40% on its own.

The spread goes from 158% to 1.2% under clang and stays flat under gcc, and
the lookup itself drops from 57ns to 34ns under gcc.  `tests/test_launder.c`
is the regression test: it times the shipped function once per digit and
fails if the spread exceeds 75%, which the old code does at 141%.

**What this costs, and why the cost is not a regression.**  Measured over
the whole suite: under gcc, Ed25519 key generation is 6% faster, signing
5%, verification 4%, secp256k1 signing 4% and `secret-to-public` 3%, and
P-256 verification 2% -- gcc was doing the masked work all along and now
does it in a better loop.  Under clang the same rows go the other way:
Ed25519 key generation and signing 21% slower, verification 12%,
secp256k1 `secret-to-public` 10%, signing 7%, ECDSA verification 6%, the
four P-256 operations 3-4%, and the 2048-bit constant-time modexp 2%.
That is the price of the masked scan actually happening.  Those earlier
clang numbers were never constant-time numbers, and a table of them is a
table of a different algorithm.  X25519 is untouched, because the
Montgomery ladder selects with `cswap` and not with a table.

**The rest of the library was then asked the same question.**
`tests/test_consttime.c` is the standing audit: it runs each of the
library's masked selections once per value of the secret it selects on and
fails on a spread.  Six are covered.  The secret-indexed table read at the
four-limb width P-256 uses, since the limb count is what decides whether
the unrolled scan is small enough for the compiler to find specialisation
worthwhile.  The whole X25519 scalar multiplication, timed over scalars of
all-zero, all-one and alternating bits -- `cswap` is `CInline` and has no
external definition to call, and the ladder is the stronger statement in
any case, because if any one of its 255 swaps branched the scalars would
not agree.  The two bignum comparisons, timed by the position of the first
differing limb, which is what an early exit would leak.  ML-KEM's
ciphertext comparison, timed the same way: the Fujisaki--Okamoto transform
re-encrypts and compares, and a compare that stopped early would make the
implicit-rejection path distinguishable and cost the KEM its CCA security.
And the AES S-box, over all 256 input bytes -- there is no S-box table
here, the inverse is computed in the field, which is a hundred and twenty
masked selects on the bits of a secret byte whose value ranges over
exactly the small set that invites enumeration.

All six are flat under both compilers: 1.4% to 3.2% under gcc and 1.4% to
3.5% under clang, against thresholds of 10--75%.  Two of those thresholds
are known to bite -- splicing the old `table_select` back in fails the
`table_select` row at 141% -- so the test is not merely asserting that
timing is noisy.  The audit is not a proof and it is not exhaustive; it is
a question asked of the compiler that is actually in use, which is the only
form the question can take.

### A square is not a product

Every field in this library squared a number the obvious way: copy the
argument and call the multiply.  `fsqr out a` was `copy c a; fmul out a c`.
That is correct, it is one line, and for a five-limb representation it is
twenty-five wide multiplies where fifteen are enough.

**The schoolbook product of a sequence with itself is symmetric about its
diagonal.**  Column *k* of `a * b` is the sum of `a_i * b_j` over `i + j = k`;
when `b` is `a`, the term `a_i * a_j` and the term `a_j * a_i` are the same
product appearing twice in the same column.  Pair them, and the column has
one diagonal term `a_i * a_i` when *k* is even and nothing but doubled
off-diagonal terms besides.  Five columns of five products become five
columns of at most three.

The factor of two is carried **in the word, before the widening**.  For
Curve25519 at radix 2^51 the limbs are below `2^52`, so `2 * a_i` and even
`38 * a_i` still fit in a machine word; the doubling is a single shift on a
64-bit register rather than an addition on a 128-bit accumulator.  The five
columns are then

```
c0 = a0*a0 + (38 a4)*a1 + (38 a2)*a3
c1 = (2 a0)*a1 + (38 a4)*a2 + (19 a3)*a3
c2 = (2 a0)*a2 + a1*a1 + (38 a4)*a3
c3 = (2 a0)*a3 + (2 a1)*a2 + (19 a4)*a4
c4 = (2 a0)*a4 + (2 a1)*a3 + a2*a2
```

where the scaling by 19 is the same wrap past `2^255 - 19` that `fmul`
already does.

**The columns are unchanged, and that is why the proof was cheap.**  The
largest column here is `77 lim^2`, against the `95 lim^2` the multiply's
carry chain is already proved to accept.  So nothing downstream needs a new
argument: `fsqr` hands its five 128-bit columns to the *same* `chain`, the
same wrap, the same final narrowing.  The new lemmas in
`spec/Spec.Curve25519.Columns.fst` do not specify squaring at all --- each
one states the paired form of a column and derives it from the existing
column lemma with `b := a`, nudged by two facts an SMT solver will not find
on its own, that `x*y + y*x == (2x)*y` and that `x*(19y) + y*(19x) ==
(38y)*x`.  All five verified on the first attempt.

Wiring it in meant deleting things.  The Montgomery ladder had a sixth
scratch buffer `t6` threaded through `add_and_double`, `ladder_one`,
`ladder` and `scalarmult` for no reason other than to hold the copy; it is
gone.  `fsqr_ip` in the inversion chain loses a copy and an array.
Ed25519's `point_double` squared **inline** --- `copy au x1; fmul aa au x1`
--- rather than calling the field's `fsqr`, three times, so the three sites
had to be found and replaced individually; the same was true of the `y^2` in
point decompression.  While there, `2 z1^2` is now computed as a square
followed by a doubling rather than a doubling followed by a multiply, which
needs one more field lemma and saves another twenty-five multiplies.

X25519 is 8-9% faster, Ed25519 verification 8-13%, key generation 6-9%,
under both compilers.

**It does not pay everywhere, and the measurement is the only way to
know.**  The same rewrite for K256's five-limb radix-2^52 field verified
just as easily and made the field squaring 32% faster in isolation under
clang --- and then made `k256-ecdsa-verify` 3% *slower* under clang while
making it 5% faster under gcc.  The arithmetic saved is real but small
against what k256 verification actually spends its time on, and at that
scale it is lost in how the two compilers choose to inline and lay out the
point doubling around it.  That change was reverted.  k256's gap is not in
the multiply; it is in the scalar decomposition, which is a separate item.

### SHA-NI, where the instruction is four rounds wide

`SHA256RNDS2` does two rounds of the compression function and `SHA256MSG1`
and `SHA256MSG2` do the message schedule four words at a time.
`spec/Spec.SHANI.fst` is the dictionary between them and `Spec.SHA2`, and
`code/hash/Hacl.Hash.SHA2.NI.fst` is one block written on them.

**The state is packed, and the packing is the whole trick.**  The
instructions want the eight working variables as two registers, `ABEF` and
`CDGH`, in an order that is neither the state's nor its reverse.  Two rounds
send `a` to `c`, `b` to `d`, `e` to `g` and `f` to `h`, which is why
`SHA256RNDS2` returns only the new `ABEF`: the old `ABEF` *is* the new
`CDGH`.  So `unpack abef cdgh == round (round ...)` pins all eight slots and
no injectivity argument is needed anywhere.  `pack_state` and `unpack_state`
say what the four shuffles around the loop do, and each is one
`Seq.lemma_eq_intro`.

**Three loops, not a hundred unrolled lines.**  The reference C keeps the
schedule in four registers whose roles rotate with period four and writes the
body out sixteen times.  Here the schedule is written into the `wsb` array
the portable code already allocates and read back by the rounds, so the block
is a loop over the message, a loop over the schedule and a loop over the
rounds -- one proof step each instead of sixteen.  That costs a store and a
few loads per group of four and it is not where the time goes.  Each loop is
its own `fn`: a Pulse `fn` is a single SMT query, and the three of them
together are far past what Z3 will chew.

**The dispatch is a copy, and the copy is the price of parametricity.**
`Hacl.Hash.SHA2.Core` is generic in the word type -- the same code is
SHA-512 -- so it cannot branch on "this is SHA-256 with thirty-two bit
words".  `hash_blocks_ni` and `hash_impl_ni` are those two functions
specialized, and `sha256`/`sha224` pick between them and the portable ones on
`__builtin_cpu_supports("sha")`.  The padding blocks still go through the
generic `tail_and_finish`: there are at most two of them.  The eleven new
axioms are checked in `tests/test_vec128.c` against a fresh transcription of
FIPS 180-4 on every single-bit input and on a thousand random ones, the same
way the AES ones are.

### SHA-512 on AVX2, where the schedule runs beside the rounds

x86 has no SHA-512 instructions short of AVX-512's SHA512 extension, which
this processor lacks, so the fast implementations (OpenSSL's, Firedancer's)
vectorize only the message schedule and leave the rounds scalar.
`code/hash/Hacl.Hash.SHA2.AVX2.fst` does the same.  The sixteen-word window
`w[t..t+15]` lives in four YMM registers of four 64-bit lanes each; a
`group` runs four scalar rounds on `w[t..t+3] + K[t..t+3]` and, in the same
basic block, computes `w[t+16..t+19]` in the vector unit.  The two chains
are independent, so the out-of-order core overlaps them, and the schedule
costs almost nothing.  The state is eight locals rather than an array, so
the C compiler keeps it in registers; `W + K` goes through one 32-byte store
to `wsb` and four scalar loads that hit store forwarding.

The vector step is the awkward part.  `sigma1` of the new words needs words
that are themselves being computed, so `next4` does it in two halves: the
low two lanes from `w[t+14..t+15]`, then the high two from the low two just
produced.  `window64` (an `alignr` across the register pair) supplies
`w[t+1..t+4]` and `w[t+9..t+12]`; `hi_to_lo64`, `lo_to_hi64` and
`blend_lohi64` move the halves.  Each of the seven new intrinsics is an
axiom in `Hacl.Vec256.Lane64` checked by `tests/test_vec256.c`.

**What the registers hold is one opaque predicate per register.**
`reg p b j x` says that lane `i` of `x` is `ws_at b (j + i)`; `holds` is
four of them at `t`, `t+4`, `t+8`, `t+12`.  Stated as one quantified
proposition over sixteen indices it made queries fail unpredictably; as four opaque
facts that are revealed only inside the lemmas that need them, each lemma
is small.  Past round 64 there is nothing left to schedule, and `next4_ok`
says the new register holds the schedule only where `t + 16 < 80`; that
needs `t % 4 == 0` so the boundary falls on a register.

**Index arithmetic goes in its own lemmas.**  In a context holding the
lane axioms -- whose `SMTPat`s mention `% pow2 64` -- Z3 timed out on
`t + 16 + k - 7 == t + k + 9`, and would not identify `ws_at b i` with
`ws_at b j` for `i` and `j` arithmetically equal.  Every such step is now a
two-line lemma with no vector facts in scope (`ws_idx`, `idx_a`, `idx_b`,
`ws_step4`, `reg_idx`) that states its result as `base + i`, so the call
sites match syntactically.  The lane-movement axioms, at a symbolic lane,
also need the case split written out.

The block function carries `__attribute__((target("avx2")))` behind
`defined(__x86_64__)`, and `sha384`/`sha512`, `hmac_sha384`/`hmac_sha512`
and HKDF's `expand_sha384`/`expand_sha512` choose it on
`Hacl_Vec256_supported()`, with the same per-hash copies of the drivers as
SHA-NI (`Hacl.HMAC.AVX2`, `expand_avx2`).  SHA-512 over 256 KiB went from
630 us to 472 us under gcc and from 771 us to 432 us under clang
(`bench/REPORT.md` Part 87).

**Everything else takes the block function as an argument.**  The
streaming hashes, streaming HMAC, HMAC-DRBG and HPKE are generic in
`params t` and were written against `blocks_scalar p`.  Rather than copy
each of them per instruction set, they now take a
`[@@@monomorphize] blocks: blocks_t p`, and the concrete instantiations pass
`Hacl.Hash.SHA2.Dispatch.blocks_dispatch32` or `blocks_dispatch64`.  Those
two have type `blocks_t p` themselves: under `is_sha256 p` (resp.
`is_sha512 p`) they branch on `Hacl.X64.x86_64` and the CPU flag and call
the accelerated function through a `defined(__x86_64__)`-guarded wrapper,
otherwise `blocks_scalar`.  Custard monomorphizes on the argument, so the
C has one copy of each driver per hash, as before, with the check inside
the multi-block call rather than once per message.  The DRBG needed a
one-shot HMAC over an arbitrary `blocks` (`Hacl.HMAC.Cat.hmac_one`); HPKE
threads `blocks` from `Hacl.HPKE.Suites` through the key schedule into
`labeled_extract`/`labeled_expand`, whose HKDF already took one.  Hashing a
long key and the final padding blocks stay portable: they are at most two
blocks.  Streaming SHA-256 in 1 KiB chunks went from 1.42 ms to 193 us per
256 KiB, and HMAC-DRBG instantiate-and-generate from 57 us to 34 us (Part 88).

### The generic bignum, where the length is a run-time value

Everything above works at a fixed width.  RSA and finite-field
Diffie-Hellman do not: the modulus is whatever the key says it is.
`code/bignum/` is arithmetic on arrays of `uint64_t` limbs, least
significant first, with the limb count passed in.

**The radix is 2^64.**  It is the widest radix for which a
multiply-accumulate is exact in a double word: `(2^64-1)^2 + 2*(2^64-1)` is
`2^128-1`, using every bit and no more, which is what `Hacl.Secret.UInt128`
provides.  A narrower radix -- 2^32, which this was until Custard grew
`unsigned __int128` -- would double the memory and quadruple the multiply
count for no gain, because this layer carries after every column rather than
accumulating a whole product first, unlike the fixed-width 256-bit core.  It
is also the limb type of HACL*'s `Hacl_Bignum64`.

**The postconditions are relational.**  There is no specification sequence
and no `add_spec`.  Addition says

    num res + v c * wt n == num a + num b

where `num` is the number an array of limbs denotes.  That is the whole
contract.  A caller wants to hear that the array is the sum, not that it is
equal to a second definition of addition which is in turn equal to the sum.

**Nothing aliases and nothing allocates.**  Separation logic gives each
argument its own permission, so `res` is disjoint from the inputs by
construction and no precondition has to say so.  Where HACL* allows `res`
and `a` to be the same pointer there are explicit in-place variants,
`sub_from` and `add_masked`, which is also what lets `add_mod` and `sub_mod`
correct their result without a temporary -- necessary here, because the
length is a run-time value and a temporary would have to be a
variable-length array.

    uint64_t Hacl_Bignum_Base_add    (uint64_t *res, uint64_t *a, uint64_t *b, size_t n);
    uint64_t Hacl_Bignum_Base_sub    (uint64_t *res, uint64_t *a, uint64_t *b, size_t n);
    void     Hacl_Bignum_Base_add_mod(uint64_t *res, uint64_t *a, uint64_t *b,
                                      uint64_t *m, size_t n);
    void     Hacl_Bignum_Base_sub_mod(uint64_t *res, uint64_t *a, uint64_t *b,
                                      uint64_t *m, size_t n);
    void     Hacl_Bignum_Base_mul    (uint64_t *res, uint64_t *a, uint64_t *b, size_t n);
    void     Hacl_Bignum_Base_sqr    (uint64_t *res, uint64_t *a, size_t n);
    uint64_t Hacl_Bignum_Base_lt_mask(uint64_t *a, uint64_t *b, size_t n);
    uint64_t Hacl_Bignum_Base_eq_mask(uint64_t *a, uint64_t *b, size_t n);
    void     Hacl_Bignum_Base_zero   (uint64_t *res, size_t n);

`add` and `sub` return the carry or borrow; `mul` and `sqr` write `2n`
limbs; `add_mod` and `sub_mod` require their inputs already reduced, as
HACL* does.  The two comparisons return an all-ones or all-zero mask and
look at every limb whatever the answer is.

Conversion is four functions, both byte orders both ways:

    void Hacl_Bignum_Convert_from_bytes_be(uint64_t *res, size_t n, uint8_t *b);
    void Hacl_Bignum_Convert_from_bytes_le(uint64_t *res, size_t n, uint8_t *b);
    void Hacl_Bignum_Convert_to_bytes_be  (uint8_t *b, uint64_t *a, size_t n);
    void Hacl_Bignum_Convert_to_bytes_le  (uint8_t *b, uint64_t *a, size_t n);

each on exactly `8n` bytes.  HACL* takes a byte count and left-pads to a
whole number of limbs; here that rounding is the caller's, who has to own a
buffer of the right size anyway, and no key length in any standard this
library implements fails to be a multiple of eight.

`tests/test_bignum.c` checks all of it against values computed in Python,
which shares no code with the implementation.

### Montgomery arithmetic

Reducing modulo an arbitrary `n` costs a trial division per limb.
Montgomery's observation is that if you carry `a * R mod n` instead of `a`,
where `R` is `2^(64n)` -- a power of the radix, so that dividing by it is
dropping limbs -- the reduction becomes a multiply and a shift.
`code/bignum/Hacl.Bignum.Montgomery.fst` is that.

    uint64_t Hacl_Bignum_Montgomery_mont_mu (uint64_t m0);
    void Hacl_Bignum_Montgomery_precomp     (uint64_t *res, uint64_t *t1, uint64_t *t2,
                                             uint64_t *wide, uint64_t *n, size_t nn,
                                             uint64_t mu);
    void Hacl_Bignum_Montgomery_reduction   (uint64_t *res, uint64_t *c,
                                             uint64_t *n, size_t nn, uint64_t mu);
    void Hacl_Bignum_Montgomery_mont_mul    (uint64_t *res, uint64_t *a, uint64_t *b,
                                             uint64_t *tmp, uint64_t *n, size_t nn,
                                             uint64_t mu);
    void Hacl_Bignum_Montgomery_from_mont   (uint64_t *res, uint64_t *a,
                                             uint64_t *tmp, uint64_t *n, size_t nn,
                                             uint64_t mu);
    void Hacl_Bignum_Montgomery_modulo      (uint64_t *res, uint64_t *a, uint64_t *acc,
                                             uint64_t *r2, uint64_t *n, size_t nn,
                                             uint64_t mu);

`mu` is a single limb with `mu * m0 + 1 = 0 mod 2^64`, `m0` being the lowest
limb of the modulus; it exists exactly when the modulus is odd.  HACL*
computes it with a sixty-four iteration bit loop.  Here it is six steps of
Hensel lifting from one, `x := x * (2 - m0 * x)`, which doubles the number of
correct bits each time: one, two, four, eight, sixteen, thirty-two,
sixty-four.
Shorter, and the proof is a two-line algebraic identity per step.

`precomp` is `R^2 mod n`, the constant that takes a number *into* Montgomery
form -- entering is `mont_mul` against it, so there is no separate `to_mont`.
HACL\* computes it by doubling, starting at a power of two just below the
modulus and doubling the remaining `2 * 64n - bitlen(n)` times: about two
thousand doublings for RSA-2048.  Here it is a ladder.

In Montgomery form the accumulator stands for `2^m`, and two moves are
available.  A Montgomery squaring doubles `m`, because the spare factor of
`R` it leaves behind is exactly the one the reduction takes away.  A modular
doubling adds one to `m`.  Those are the two moves of binary
exponentiation, so `m` can be walked up to `64n` -- and `m = 64n` says
precisely that the accumulator is `R * R mod n` -- in eleven multiplications
rather than four thousand doublings.

Climbing onto the ladder is the one part that stays linear.  It means having
`2^(64n + 1)` reduced, and doubling is the only operation that raises an
exponent by a fixed amount, so the seed starts as high as it can get for
free: at `2^(64k)`, where `k` is the topmost nonzero limb of the modulus.  A
power of the radix at or below an odd number greater than one is strictly
below it, so that value is already its own residue and can simply be written
down -- and `mu` is the proof that the modulus is odd, which is why
`precomp` now takes it.  That leaves sixty-five doublings for a modulus that
fills its limbs, against four thousand and ninety-six before.

Finding `k` reads the modulus, which is public in every caller -- an RSA
modulus travels with the public key, and the FFDHE primes are in the source
-- so the scan declassifies one comparison per limb.  The number of
doublings that follows depends on the modulus's length and on nothing
secret.

For RSA-2048 the constant now costs 32.5 us where the doubling chain cost
361, an elevenfold improvement, and HACL\*'s own `precomp` takes 95.  It
matters out of proportion to its size for *verification*, where the exponent
is 17 bits and everything else is over in a moment: `rsapss-2048-verify`
drops from 516 us to 198.  The ladder step now squares with `mont_sqr`
rather than copying the accumulator into `mont_mul`.

**One carry bit, not a propagated carry.**  The reduction loop clears one
limb per step by adding a multiple of the modulus.  Each step spills a carry
into the limb above the window -- and that limb is exactly where the next
step adds its own column, so the carry is consumed one step later and never
accumulates.  A single bit suffices for the whole loop, and the final
conditional subtraction reads its decision off that bit and the borrow,
with no temporary.

**Why dropping the factor of `R` is legitimate.**  `modulo` is two
Montgomery steps, one taking a factor of `R` out and one putting it back,
and it ends by concluding `x = y` from `x * R = y * R (mod n)`.  That needs
`R` invertible modulo `n`.  It is, and `mu` hands over the witness for free:
`1 + mu * n` is a multiple of the radix by the very equation defining `mu`,
so its quotient is an explicit inverse of the radix, and a power of that
inverts `R`.  No appeal to Bezout, no gcd, and nothing computed at run time
-- the inverse only ever exists in the proof.

### Modular exponentiation

`code/bignum/Hacl.Bignum.Exponentiation.fst` is the ladder that RSA and
finite-field Diffie-Hellman are built out of.  It runs entirely in
Montgomery form: the base goes in once, the accumulator comes out once,
and everything in between is `mont_mul`.

The constant-time ladder walks the exponent **four bits at a time**.  It
first builds a sixteen-entry table `T[d] = a^d * R mod n`, then repeats a
*rung*: four squarings, a constant-time lookup of `T[d]` for the next four
bits, and one more multiply.  That is five `mont_mul`s per four bits
instead of eight, so a 2048-bit exponent costs about 2,560 of them rather
than 4,096 -- 1.6x, and measured at 1.56x on gcc and 1.58x on clang.  The
variable-time ladder and `mod_inv_prime_vartime` are still bit-at-a-time;
their exponents are public.  The variable-time ladder does skip the
exponent's leading zeros: it finds the top set bit, seeds the accumulator
with `a * R mod n` and squares with `mont_sqr` from there, so `65537`
costs 16 squarings and one multiply rather than 64 squarings and two
multiplies (Part 67).

The window closes most, but not all, of the gap to the reference: RSA-PSS
signing and FFDHE were 1.97x behind HACL* and are now about 1.25x.  What
is left is not the ladder -- it is `mont_mul` itself, which costs us
about 2.19 us per call against HACL*'s 1.77.

    void Hacl_Bignum_Exponentiation_mod_exp_consttime(
        uint64_t *res, uint64_t *a, uint64_t *bb, size_t bbits,
        uint64_t *r2, uint64_t *n, size_t nn, uint64_t mu,
        uint64_t *aM, uint64_t *acc, uint64_t *t, uint64_t *wide);
    void Hacl_Bignum_Exponentiation_mod_exp_vartime(/* the same arguments */);
    void Hacl_Bignum_Exponentiation_mod_inv_prime_vartime(
        uint64_t *res, uint64_t *a, uint64_t *r2, uint64_t *n,
        size_t nn, uint64_t mu, uint64_t *e,
        uint64_t *aM, uint64_t *acc, uint64_t *t, uint64_t *wide);

**The invariant is the whole proof.**  Reading the exponent from the top
down, the accumulator after `i` bits have been consumed holds

    acc == a^(b / 2^i) * R mod n

and one rung takes `i` to `i-1` by `b / 2^(i-1) = 2 * (b / 2^i) + bit i-1`.
That identity, `pw_step`, is the only arithmetic fact the loop needs; the
rest is `mont_cancel`, which is what says that a `mont_mul` of two numbers
in Montgomery form is again in Montgomery form.

**The constant-time one never branches on the exponent.**  The table
lookup is `table_select`, which reads *all sixteen* entries and folds them
together under a mask derived from the digit, so the memory trace is the
same whatever the digit is -- no data-dependent index, and so nothing for
a cache-timing attack to observe.  The mask comes from `get_digit`, which
returns secret words and offers no way to turn one into a `bool`.  The variable-time one branches instead, and is
correspondingly only for public exponents -- which is why it is the one
`mod_inv_prime_vartime` calls: the exponent there is `n - 2`, and the
modulus is public.

Inversion is Fermat's little theorem, `a^(n-2) = a^-1 mod n` when `n` is
prime.  The specification does not mention primality -- it says only that
the result is `a^(n-2) mod n`, which is true unconditionally and is what
the code actually establishes.  Claiming an inverse would require a
primality hypothesis the caller cannot discharge and the library does not
check, so, like HACL*, we do not claim it.

**Almost nothing allocates.**  The length is a run-time value, so every
temporary is a caller-supplied array: a ladder needs three `nn` words of
scratch plus one `2*nn` for the products, and `res` serves as a fourth
while the loop runs.  The one exception is the window table, `16*nn`
words -- 4 KiB for RSA-2048, 16 KiB for FFDHE-8192 -- which
`mod_exp_consttime` takes from the heap with `Hacl.Mem.alloc` and wipes on
the way out.  Threading it through every caller would have changed four
public signatures to no purpose, and a stack array sized by `nn` would let
the caller choose our frame size; see "Scratch memory" below.

`tests/test_montgomery.c` checks every one of these against Python, which
inverts the radix with `pow(R, -1, n)` and multiplies out, and compares
both ladders against `pow(a, b, n)`.

### Finite-field Diffie-Hellman

`code/ffdhe/Hacl.FFDHE.fst` is RFC 7919, the five named finite-field groups
that TLS negotiates.  It is the first thing built on the bignum stack that
a caller would actually reach for, and it is where that stack's "nothing
allocates, nothing is hidden" discipline finally gets to pay for itself.

    void Hacl_FFDHE_ffdhe2048_secret_to_public(uint8_t *pk, uint8_t *sk);
    bool Hacl_FFDHE_ffdhe2048_shared_secret(uint8_t *ss, uint8_t *sk,
                                            uint8_t *pk);
    /* and the same pair for 3072, 4096, 6144 and 8192 */

Every array is exactly the group's size in big-endian bytes -- 256 for
FFDHE-2048, up to 1024 for FFDHE-8192 -- so there is no length to pass and
no length to get wrong.

**One pair of entry points per group.**  HACL* has a single set of
functions that take an `ffdhe_alg` enum, dispatch on it at run time, and
hand back a heap-allocated precomputation context that the caller has to
remember to free.  Here the group *is* the entry point.  The size is a
compile-time constant at every call, the primes live in `static const`
tables that the linker drops if you do not use them, there is no context to
allocate or free, and there is no enum to get wrong.  The cost is ten
symbols instead of four; the benefit is that the C API has no lifetime
rules at all.

**The primes are computed, not transcribed.**  Section 3 of the RFC gives
each prime by a formula -- `p = 2^b - 2^(b-64) + (floor(2^(b-130) e) + X) 2^64 - 1`
-- and then prints it.  `files/gen_ffdhe.py` evaluates the formula, and
checks the result three ways before emitting it: against the top 128 bits
the RFC prints, against the stated bit length, and with Miller-Rabin on
both `p` and `(p-1)/2`.  A transcription error in a 8192-bit constant is
exactly the kind of thing that no test built from the same constant would
ever catch.

**Two literals are all the proof needs.**  `Spec.FFDHE` gives, for each
group, that limb `0` and the top limb are both `2^64 - 1`.  The first says
the modulus is odd, which is Montgomery's precondition; the second, with
`num_top`, says the modulus is bigger than two, which is what makes the
exponentiation's modulus non-zero and the key-validation range non-empty.
Nothing anywhere evaluates the other 254 limbs.

**Peer keys are validated, and the answer is a `bool`.**  `shared_secret`
checks `1 < pk < p - 1` -- the RFC's own range -- with two `lt_mask`s, and
then *declassifies*: the peer's public key arrived over the wire, so
branching on a fact about it leaks nothing the adversary did not send.  The
branch has to happen anyway, because `mod_exp_consttime` requires its base
to be reduced.  HACL* returns an all-ones `uint64_t` mask; we return a
`bool`, because the value is public by construction and a mask that callers
have to remember to use in constant time is a footgun, not a feature.  On a
bad key the output is zeroed, so a caller who ignores the return value
still does not get a usable secret.

**`R^2 mod p` is recomputed on every call** rather than tabulated.  Since it
became a ladder it is a dozen multiplies and sixty-five doublings, against
an exponentiation of `bits` rungs each of which is a full multiply: a few
hundredths of a percent, for several kilobytes of table per group and no
precomputation context in the API.

The scratch is seven `nn`-limb arrays and one `2*nn`, on the *stack*, in
the per-group wrapper -- about 9 KB for FFDHE-8192.  An entry point named for its group
knows its size, which is precisely the condition under which a stack array
is legitimate; the generic layer underneath it still takes every temporary
from its caller.

`tests/test_ffdhe.c` checks all five groups against Python: both public
keys, the shared secret computed from either side, and the rejection of the
two boundary peer keys `1` and `p - 1`.

### RSA-PSS, where the key is just bytes

`code/rsapss/` is PKCS#1 v2.2 signing and verification: `Spec.RSAPSS` for
the encoding, `Hacl.RSAPSS.MGF` for MGF1, `Hacl.RSAPSS.PSS` for the EMSA-PSS
encoder and verifier, and `Hacl.RSAPSS` for the modular exponentiation and
the six entry points.

    bool Hacl_RSAPSS_sign_sha256(uint32_t modBits, uint8_t *nb,
                                 size_t dLen, uint8_t *db,
                                 size_t sLen, uint8_t *salt,
                                 size_t mLen, uint8_t *msg, uint8_t *sgnt);
    bool Hacl_RSAPSS_verify_sha256(uint32_t modBits, uint8_t *nb,
                                   size_t eLen, uint8_t *eb,
                                   size_t sLen, uint8_t *sgnt,
                                   size_t mLen, uint8_t *msg);
    /* and the same pair for sha384 and sha512 */

**The key is a byte string, and that is the whole key type.**  HACL* has a
`Hacl_RSAPSS_new_rsapss_load_pkey` that mallocs a flat `uint64_t` array
holding the modulus, `R^2 mod n` and the exponent at agreed offsets, hands
back a bare pointer with no type and no length, and leaves the caller to
free it; every operation then re-derives the bit lengths from the same
`modBits` that was already passed in.  Here the modulus is `ceil(modBits/8)`
big-endian bytes -- the form it arrives in, from a certificate or a
`SubjectPublicKeyInfo` -- and the exponent is however many bytes the caller
has.  There is no key object, no loader, and nothing for the caller to
free.  The conversion to limbs happens inside the call, which is also where
`R^2 mod n` is computed.  Unlike the Diffie-Hellman groups, the size is the
caller's `modBits`, so that scratch -- and the PSS encoding buffers, whose
size depends on the salt length -- comes from `Hacl.Mem.alloc` rather than
the stack, and is wiped before it is freed.

**Nothing is trusted.**  `rsa_exp`, the primitive both directions go
through, checks at run time that the modulus is odd, that it is greater than
one, that the base is below it and that the result fits the output width,
and returns `false` otherwise.  The last check reads the result, so it is
made only where the result is public: when signing, the output is as wide
as the modulus, the result is below the modulus, and the fit is proved
rather than tested.  A caller cannot reach Montgomery reduction
with an even modulus, which is the one way to make the bignum layer produce
nonsense rather than an error.  `tests/test_rsapss.c` clears the low bit of
each modulus and checks that both directions refuse it.

**Verification is a predicate, not a comparison.**  The postcondition is not
"the signature equals what signing would produce" -- that would be false,
because the salt is not recoverable from a signature by the verifier alone.
It is

    ok <==> 1 < n /\ n odd /\ s < n /\
            (exists em. be_nat em == s^e mod n /\ pss_valid p sLen msg em)

The existential is what avoids `nat_to_be`'s precondition, and `be_nat_inj`
-- a big-endian string of a given length is determined by the number it
denotes -- is what makes it as strong as naming the encoding outright.  The
six lemmas around it (`be_nat_zeros`, `be_nat_pad`, `be_nat_trunc`,
`be_nat_zeros_inv`, `be_nat_prefix_zero`, `be_nat_inj`) are the entire
bridge between "a number modulo `n`" and "a padded byte string", and they
are the only part of the spec that is not a direct transcription of the RFC.

**`modBits <= 65536` is a precondition**, and it is the one that makes every
`size_t` arithmetic obligation in the module discharge from `fits_u32`
alone, instead of threading explicit `SZ.fits` conjuncts through a dozen
signatures.  No real key is anywhere near it.

**The exponent is consumed as bytes, at full width.**  `mod_exp_be` passes
the exponent's whole bit length to the ladder rather than its significant
bit length, so nothing about a private exponent leaks through a loop bound;
the constant-time ladder is selected for signing and the variable-time one
for verification, where the exponent is public and is usually `65537`.
Only the variable-time ladder looks for the top set bit and skips the
zeros above it.

**One `if` in `pss_encode_impl` exists only for GCC.**  The scratch buffer
there is `emLen - hLen - 1` bytes, a difference of caller-supplied sizes,
and `-Werror=vla-larger-than=` fires on the path where it underflows or is
astronomically large.  `pss_ok` and the `modBits` bound rule both out, but
Custard emits each Pulse `fn` as its own C function, so the facts are not
visible at the point of the declaration.  The test is unreachable and proves
vacuously; it is cheaper than teaching the C compiler about the proof.

### SHA-1, where the interesting part is how little of it is SHA-1

SHA-1 is broken -- collisions since 2017, chosen-prefix collisions since
2020 -- and it is here for the same reason HACL\* has it: TLS 1.0/1.1
transcripts, PBKDF2, TOTP, Git object names and a great deal of deployed
X.509 have to be *read*.  HMAC-SHA1 additionally still has a security
proof, because HMAC rests on the compression function being a PRF rather
than on collision resistance.

What is worth writing down is how much of it was already there.  Outside
the compression function, SHA-1 and SHA-2-at-32-bits are the same
algorithm: sixty-four byte blocks, an `0x80`, zeros, a 64-bit big-endian
bit length, a `2^61` bound, and the same way of cutting blocks out of the
padded message.  `Spec.SHA1` states those definitions again rather than
instantiating `Spec.SHA2.params` -- a record covering a five-word state,
eighty rounds, a round function that changes every twenty and constants
indexed by quarter would describe neither algorithm -- but the definitions
are *equal*, and `Spec.SHA1.Lemmas` proves it in four lemmas that
discharge by computation, since both sides are `unfold`.

With `SMTPat`s on those equalities the implementation inherits the whole
of `Spec.SHA2.Lemmas` (`padded_index`, `padded_shape`, `pad_zeros_alt`,
`tail_bytes`, `padded_index_block_shift`) and calls SHA-2's
`write_len_be` and `build_tail` unchanged.  The same trick then covers
HMAC: `Spec.HMAC`'s `zeros`, `xor_byte`, `ipad`/`opad` and both pointwise
lemmas, and `Hacl.HMAC.Core`'s `fill_xor`, are all block-shaped and are
reused at `S32.t`.  The chunking lemmas behind the incremental interface
never needed a bridge at all -- `Hacl.Spec.Chunks` takes the block length
as an argument rather than a word type.

The genuinely SHA-1-specific code is the message schedule, the eighty
rounds, `key_block`, and a five-word digest that, unlike SHA-224 and
SHA-384, needs no truncating copy.  Two things are even simpler than
SHA-2's: there is no round-constant table, since `K` is one of four
values chosen by quarter, so `k_impl` branches on the round number and no
caller passes an array; and `f_impl`/`k_impl` test exactly the boundaries
`Spec.SHA1._f` and `k` use, so each branch's obligation closes by
unfolding rather than by a case split the solver has to invent.

Every module in the chain -- compression function, driver, streaming
layer, HMAC -- verified on the first attempt, which is the payoff for
having shaped `Spec.SHA1` on `Spec.SHA2` deliberately.

**SHA-1 on the SHA extensions.**  `SHA1RNDS4` does four rounds,
`SHA1MSG1`/`SHA1MSG2` four schedule slots, and `SHA1NEXTE` supplies the
fifth state word, which never has a register of its own: after four
rounds it is `ROTL^30` of the `a` that went in, so `SHA1NEXTE` recomputes
it from the previous `ABCD` and adds it to the next message word.
`spec/Spec.SHA1NI.fst` states each instruction in `Spec.SHA1`'s terms, as
`Spec.SHANI` does for SHA-256, and the axioms in `Hacl.Vec128` are tested
in `tests/test_vec128.c` against a scalar transcription.
`Hacl.Hash.SHA1.NI` has the same three-loop shape as SHA-256's NI block
(load, schedule into `wsb`, rounds).  Unlike SHA-256, the dispatch is
inside `Hacl.Hash.SHA1.Core.update_block_impl`, since SHA-1's core is not
generic in the word type, so every SHA-1 caller -- one-shot, streaming and
HMAC -- uses it.  SHA-1 over 256 KiB went from 1.62 ms to 165 us, against
AWS-LC's 146 us (`bench/REPORT.md` Part 87).

### MD5, and where the reuse runs out

MD5 is worse than broken -- collisions are minutes on a laptop, and
chosen-prefix collisions are a well-trodden attack on real certificate
chains -- but it is still what a protocol that predates 2004 says, so
HACL\* has it and so does this.  HACL\* gives it as a one-shot and as a
streaming state and *not* under HMAC; that is the parity target, and it is
met.

The same bridge lemmas work: MD5's padding is SHA-2's at 32 bits too, so
`Spec.MD5.Lemmas` opens with two `SMTPat` equalities and then inherits
`block_at_pointwise` and the shape lemmas.  Everything above the block --
`hash_blocks`, `tail_and_finish`, `hash_impl`, and the whole streaming
layer -- is SHA-1's code with the lemma module swapped.

Where it runs out is byte order.  MD5 is little-endian in three separate
places: the sixteen block words, the four digest words, and the 64-bit
length in the padding.  The first two were free, because
`Hacl.Spec.Bytes` was written symmetrically from the start and already had
`words_from_le`, `words_to_le` and `digest_step_le`.  The third needed
`write_len_le`, which differs from `write_len_be` in exactly one index --
byte *j* goes at `off + j` rather than `off + 7 - j` -- and a
`tail_generic_le` to match.  That lemma is *shorter* than the big-endian
one: SHA-2's length field can be sixteen bytes of which only the low eight
are written, so it carries an argument that the high bytes are zero, and
MD5's is eight bytes all of which are written.

Two smaller things.  MD5 has no message schedule; each of the sixty-four
rounds reads one of the sixteen block words through an index function, so
`g_impl` is a run-time `%` and the scratch buffer is sixteen words rather
than eighty.  And the rotation amounts come from a table, which means
`rotate_left` needs to know each one is in `(0, 32)`.  Rather than prove
that at the point of use, the table's *element type* is the refinement:
`s_arr : G.static_array rot` where `rot = r:U32.t{0 < v r /\ v r < 32}`.
Reading the array hands the caller the bound, the refinement erases, and
the C is still a `uint32_t[64]`.  The alternative -- an `assert_norm` of a
`forall` over a sixty-four-element `seq_of_list` -- times out.

### Salsa20, which is ChaCha20 with the wires crossed

Salsa20 is ChaCha20's predecessor, and the two are near enough that writing
the second one from the first is mostly a matter of being careful about
*where* things are rather than *what* they are.  The state is the same
sixteen words and the same four constants, but the constants sit at words
0, 5, 10 and 15 instead of 0 through 3, the key is split into two halves
around them, and the counter is at word 8 rather than 12.  The round
function is `m[a] ^= (m[b] + m[c]) <<< s` -- an add, a rotate and an xor,
exactly ChaCha20's, with the operands permuted -- and each quarter round
starts on the diagonal rather than at the top of a column.

So `code/salsa20/Hacl.Salsa20.Core.fst` is a hand port of the ChaCha20
core, and `code/salsa20/Hacl.Salsa20.fst` is ChaCha20's driver with `12`
changed to `8` and the names substituted.  The only part written from
scratch is the state setup, which is factored as `setup_base` -- the twelve
words Salsa20 and HSalsa20 agree on -- plus an `init_state` and an
`hinit_state` that fill words 6 through 9 differently.

The shared keystream writer moved to `lib/`.  `Hacl.Chacha20.Core` used to
own a `write_keystream`; it is now `Hacl.Impl.Bytes.store_words_le`, which
writes any `n` words little-endian, and both ciphers call it, so there is
one copy of that loop in the generated C rather than two.

**Vector Salsa20.**  The vector backends were ported the same way:
`Hacl.Salsa20.Vec512` (sixteen blocks, AVX-512F) and `Hacl.Salsa20.Vec256`
(eight, AVX2) are `Hacl.Chacha20.Vec512` and `Hacl.Chacha20.Vec256` with
Salsa20's `line`, quarter-round order, column and row rounds, and the counter
in word 8.  Everything after the rounds -- the transposes that turn lanes
back into blocks, the exclusive-or and the driver -- is ChaCha20's
unchanged, because both ciphers serialize the keystream as sixteen
little-endian words; both modules verified on the first attempt.
`Hacl.Salsa20.encrypt` calls `encrypt_vec` exactly as ChaCha20 does, so
XSalsa20, secretbox and box get it too.  Salsa20's rotations (7, 9, 13, 18)
are none of them whole bytes, so AVX2 needs a shift-shift-or for each where
ChaCha20 has two byte shuffles; AVX-512's `vprold` does every one in an
instruction.  On 256 KiB this took Salsa20 from 480 us to 45 us under gcc
and 43 us under clang (97 us with AVX-512 masked off), and secretbox from
542 us to 98 us, now mostly Poly1305 (`bench/REPORT.md` Part 61).

HSalsa20 is the piece NaCl needs.  It is twenty rounds on a state whose
nonce is sixteen bytes wide, with **no feedforward** -- the input is not
added back -- and its output is eight of the sixteen words, namely 0, 5,
10, 15, 6, 7, 8, 9: the four constant positions and the four nonce
positions, which are exactly the words the feedforward would have
contaminated.  Proving the implementation's output array equal to that
projection is where the one real fight was.  Stating it as
`Seq.init_ghost 8 (fun i -> Seq.index vs (hpick i))` does not work: the
solver will not identify that closure with the syntactically different one
inside the specification.  The fix was to give the projection a name in the
spec -- `hwords`, with an SMT-patterned index lemma -- so that the
implementation has a first-order term to prove itself equal to.  *Do not
ask SMT to identify two lambdas.*

One more spec-side lemma exists only to serve an implementation:
`keystream_init` says the counter in the *initial* state is dead, because
`keystream` overwrites word 8 on every block anyway.  NaCl needs it, for
the reason in the next section.

### NaCl, where the authenticator shares the cipher's keystream

`crypto_secretbox` and `crypto_box` are the original NaCl interface, and
the reason they get their own module rather than being a wrapper over
`Hacl.Chacha20Poly1305` is that the construction genuinely differs.
ChaCha20-Poly1305 generates a fresh block at counter zero for the one-time
key and starts the ciphertext at counter one.  NaCl does not restart
anything: it prepends thirty-two zero bytes to the message and encrypts the
padded whole in one XSalsa20 pass, so keystream bytes 0 through 31 come
back unchanged -- they *are* the Poly1305 key -- and the ciphertext begins
at keystream byte 32.  The authenticated input is the ciphertext alone: no
associated data, no padding, no length block.

`Spec.NaCl` states that pointwise and stays out of the way: `cipher k n m`
is `m[i] ^ sb_byte k n (32 + i)`.  The implementation cannot run it that
way, so five bridging lemmas cut the keystream into the pieces it does run.
`key_block0` produces the first sixty-four bytes; `otk_is_block0` says its
low half is the Poly1305 key, which is then handed to Poly1305 as a `Sub`
window rather than copied; `cipher_head` says the first `min(mlen, 32)`
ciphertext bytes come from its high half; and `cipher_tail` says the rest
is `Hacl.Salsa20.encrypt` at counter **one** on the message shifted by
thirty-two.  That last one is what needs `keystream_init`: the encryption
call builds its state with counter one where the specification's keystream
was built with counter zero, and the two states differ only at the word the
block function overwrites.

`crypto_box` is `crypto_secretbox` under a key derived by
`hsalsa20 (X25519 sk pk) (zeros 16)`.  `beforenm` returns that key together
with X25519's contributory-behaviour flag, and the key is written even when
the flag is false, which matches HACL\* and costs nothing since the caller
is required to check.  All thirteen entry points are exported: four
`crypto_secretbox_*`, `crypto_box_beforenm`, four `*_afternm`, and four
full `crypto_box_*` that do the agreement themselves.

One deliberate deviation, documented in the module header.  The names
are NaCl's, because a compatibility layer whose names do not match is not
one -- so `Hacl_NaCl_crypto_secretbox_easy`, not a HACL\*-style spelling.
As in HACL\*, the detached functions let `c` and `m` be the same buffer
(see the ChaCha20 section).  The combined ones do not, because the tag
comes first in `c`, so the two cannot coincide exactly.  Lengths are `size_t` rather than HACL\*'s `uint32_t`, which makes
`2^38 - 32` -- the largest message XSalsa20 can cover after the
thirty-two-byte prefix -- a real precondition rather than a vacuous one.

`tests/test_nacl.c` is anchored on libsodium's own files rather than on
recollection, which mattered: the nonce in `test/default/secretbox.c` is
not what memory said it was, and the resulting mismatch looked exactly like
a construction bug for a while.  Fetching the vector settled it in a
minute.

### FrodoKEM, where the matrix never exists

FrodoKEM is a lattice KEM with no structure in the lattice: the public
matrix `A` is an `n x n` matrix of sixteen-bit entries, drawn from a SHAKE
expansion of a sixteen-byte seed, and the security argument is plain LWE
rather than a ring or module variant.  The price is size -- at
FrodoKEM-1344 `A` is 3.6 megabytes -- and that size is the one interesting
implementation decision.

`A` is never assembled.  `Hacl.Frodo.Gen` expands one row at a time and
accumulates it into whichever of the two products the caller wants, so the
working set is a single row and the two small operands: about twenty-one
kilobytes at FrodoKEM-1344, instead of 3.6 megabytes, for exactly the same
arithmetic.  Row `i` is `shake128(le16(i) || seed, 2n)` -- SHAKE-128 in
every parameter set, including the two whose other hashing is SHAKE-256,
which is a detail of the specification that is easy to get wrong and that
the known-answer tests catch immediately.

One implementation serves all four parameter sets.  The parameters are a
record --- `n`, `log q`, the extracted bits, the shared-secret length, the
error table and the SHAKE choice --- passed as an ordinary argument and
tagged `[@@@monomorphize]`, and every buffer's width is computed from it.
The matrices are tens of kilobytes at FrodoKEM-1344 (a whole decapsulation
used to need a 173 KB stack frame), so every buffer sized by `n` comes from
`Hacl.Mem.alloc` and the rest are on the stack; see "Scratch memory".  `nbar`, the width of the small matrices, is a
constant rather than a field: it is eight in every parameter set ever
proposed, and making it one turns `publicmatrixbytes` into `log q * n`
rather than `log q * n * nbar / 8`, which removes a division the solver
would otherwise have to reason about at every use.  The four wrappers ---
`Hacl.Frodo64`, `Hacl.Frodo640`, `Hacl.Frodo976`, `Hacl.Frodo1344` --- are
a table and three one-line calls each, and Custard emits four separate sets
of C functions with the dimensions as literals.

The variant implemented is the one HACL\* implements, which the 2021
revision of the submission renamed **eFrodoKEM**: ephemeral, with no salt
in the ciphertext.  `Hacl.Frodo64` is in the public API because it is in
HACL\*'s, and it is a toy: sixty-four is not a security level, and the
module header says so.

*Randomness is the caller's.*  HACL\*'s `crypto_kem_keypair` and
`crypto_kem_enc` call a platform entropy shim internally, store the `bool`
it returns and discard it, and then `return 0U` unconditionally --- so an
entropy failure is invisible.  Here, as for HMAC-DRBG, the coins are an
argument: `keypair pk sk coins` takes `2 * crypto_bytes + 16` bytes and
`enc ct ss pk mu` takes the `bytes_mu` of the message.  Nothing returns a
status code, because with the randomness supplied nothing can fail.  It
also means the known-answer tests can drive the real entry points rather
than a deterministic back door.

Decapsulation is the FO transform, and its two halves are both
constant-time.  `Hacl.Frodo.KEM.eq_mask_arr` compares two matrices into a
mask rather than a `bool` --- secret integers have no decidable equality,
so the loop is stated against a ghost `agree` predicate and the mask is
related to it only at full length --- and `select_copy` then chooses
between the real key stream and the secret key's rejection value without a
branch.  The specification says the same thing with
`FStar.IndefiniteDescription.strong_excluded_middle`, so the postcondition
is an equality with a spec-level `if` whose scrutinee never exists at run
time.


### ML-KEM, where the ring does the work

ML-KEM is FIPS 203, the standardised Kyber, and it is what TLS actually
deploys: the hybrid groups everyone is turning on are X25519 plus
ML-KEM-768.  It is FrodoKEM's opposite number.  Frodo refuses structure and
pays three and a half megabytes for a public matrix; ML-KEM works in
`Z_3329[X]/(X^256 + 1)`, so the matrix is `k * k` polynomials of 256
coefficients, the largest key is a kilobyte and a half, and the arithmetic
is a number-theoretic transform rather than a schoolbook product.  There is
no ML-KEM in HACL\*; this is new code, not a port.

The modulus is 3329, which is `13 * 256 + 1`, and that is the whole reason
the scheme is fast: `Z_3329` has a primitive 256th root of unity (17), so
the transform is seven layers of butterflies over 128 pairs and polynomial
multiplication becomes 128 independent products of linear polynomials
modulo `X^2 - zeta`.  `Spec.MLKEM.NTT` says exactly
that and `Hacl.Impl.MLKEM.NTT` implements it in place, with the zeta table
a 128-entry constant.  Addition and subtraction reduce with a
conditional subtraction whose mask is the top bit of the sixteen-bit
difference `x - q`, added back as `s + (m & q)`, and multiplication with a Barrett step in
sixty-four bits, or, by a root of unity in the transform, with Shoup's
trick against a second table of `floor(zeta 2^16 / q)`, all branch-free, and the coefficient type is a refinement
--- `zqt = x: S16.t { S16.v x < q }` --- so every intermediate carries its
bound in its type instead of in a lemma.  The base-case products reduce
once per output coefficient rather than once per operation: each of
`a0 b0 + a1 b1 gamma_i` and `a0 b1 + a1 b0` is formed in sixty-four bits,
below `2^36`, and reduced by a single Barrett step with `m = floor(2^37 / q)`
(`zq_reduce`), with `gamma_i = zeta^(2 brv(i) + 1)` read from a third
128-entry table instead of computed as a product.  The matrix-vector
products do not add up `k` such products: `Hacl.Impl.MLKEM.Dot` sums, for
each pair, the `k` values of `a0 b0`, `a1 b1` and `a0 b1 + a1 b0` exactly in
thirty-two bits (at most `8 (q - 1)^2` for `k <= 4`), reduces the `a1 b1`
sum before it meets `gamma_i`, and reduces each output once
(`zq_reduce32`), which vectorises and is 3.5x faster than `k` products and
`k` additions.  The centred binomial
sampler reads its input a group at a time -- `eta` bytes are four
coefficients -- and adds up bits with constant shifts, rather than
locating each bit with a division.  The NTT, inverse NTT, pointwise product, dot product and CBD
sampler are each extracted twice from the same verified body, once under
`__attribute__((target("avx2")))` and once without, and a dispatcher with
the same specification picks one on `Hacl.Vec256.supported`: gcc and clang
then vectorize the butterflies sixteen coefficients wide instead of eight,
without a line of new proof.  The vectorizers are why the conditional
subtraction is shaped the way it is: a mask taken from a thirty-two-bit
borrow widens every lane to thirty-two bits, and gcc does not vectorize the
and-or blend of a `select` at all.

The correctness statement is that the implementation computes the
algorithms of FIPS 203, coefficient for coefficient, including that the NTT
is the specification's NTT.  Separately, `Spec.MLKEM.NTT.Lemmas` proves the
mathematical fact behind it: the specification's NTT is a ring isomorphism
`R_q ~ prod_i Z_q[X]/(X^2 - gamma_i)`, so `intt (multiply_ntts (ntt f)
(ntt g))` is the schoolbook product of `f` and `g` modulo `X^256 + 1`, and
`intt` and `ntt` are mutually inverse.  That is a finite-field argument
about roots of unity, independent of the implementation; the bit-reversal
facts about the twiddle tables are checked exhaustively by normalization.
On top of it, `Spec.MLKEM.Correctness` proves that decapsulation recovers
the encapsulated key whenever the decryption noise is below `q/4` (see
[Functional correctness](#functional-correctness)).  The spec is also
pinned by the published vectors, which is the bar the rest of this
repository meets.

One implementation serves all three parameter sets.  As with Frodo the
parameters are a `[@@@monomorphize]` record --- `k`, `eta1`, `eta2`, `du`,
`dv` --- and `Hacl.MLKEM512`, `Hacl.MLKEM768` and `Hacl.MLKEM1024` are a
table and three one-line calls each, so Custard emits three sets of C
functions with the dimensions as literals.  The matrix `A` *is* assembled
here, unlike Frodo's: at ML-KEM-1024 it is thirty-two kilobytes, which is a
stack allocation rather than a problem, and having it whole is what lets
`A^T s` and `A y` share one implementation.

Decapsulation is the part where the shape of the code is a security
property.  FIPS 203 decapsulates by decrypting, *re-encrypting* the
recovered message under the recovered randomness, and returning the real
shared secret if the re-encryption reproduces the ciphertext and
`J(z || c)` if it does not --- implicit rejection, so that a malformed
ciphertext yields a wrong-looking secret rather than an error the attacker
can see.  A branch on that comparison would leak, so there is none:
`lib/Hacl.Impl.Select` compares the two ciphertexts into a single all-ones
or all-zeros mask and selects the thirty-two output bytes through it, and
the lemma `decaps_eq` turns "mask, then pointwise selection" back into the
specification's `if Seq.equal c c'`.  It is the same idiom Frodo uses, but
in a shared module this time rather than open-coded in the KEM.

FIPS 203 section 7's two input checks are here as well, as
`Hacl_MLKEM768_ek_valid` and `Hacl_MLKEM768_dk_valid` and their siblings.
The standard keeps them outside the algorithms because they say where a
key came from rather than what encapsulation does with it, and a caller
that generated the key itself does not need them.  The modulus check is
written as the standard writes it --- re-encode what you decoded and
compare --- which is four lines and no bound proof over 256k coefficients,
and neither check pretends to run in constant time, because whether the
input was malformed is precisely the answer being returned.

`tests/test_mlkem.c` is the NIST ACVP vectors: the first keyGen seeds for
each set, digests of the encapsulation key, the decapsulation key and the
ciphertext, the shared secret, and --- the case worth having --- the
implicit-rejection secret for a ciphertext with one bit flipped, checked
against its published value rather than merely against "not the real one".
Both section 7 checks are exercised on a key that must pass and on one
corrupted so that it must not.
The generator re-validates its reference against all one hundred and eighty
published keyGen, encapsulation and decapsulation cases before it emits
anything.

### ML-DSA, where signing is a loop that is allowed to fail

ML-DSA is FIPS 204, the standardised Dilithium, and it is ML-KEM's
signature-scheme sibling: the same module-lattice idea, a different ring.
The modulus is `q = 8380417 = 2^23 - 2^13 + 1`, which has a primitive
512th root of unity (1753), so in `Z_q[X]/(X^256 + 1)` the transform goes
all the way down: eight layers of butterflies, and polynomial multiplication
in the NTT domain is 256 independent products of coefficients rather than
ML-KEM's products of linear polynomials.  There is no ML-DSA in HACL\*
either; this is new code.

The specification is `Spec.MLDSA` and its modules --- `Params`, `Zq`,
`NTT`, `Sample`, `Rounding`, `Encode` --- written from the standard's
algorithm listings, and the implementation is `code/mldsa/`.  The
correctness statement is the same shape as ML-KEM's: each entry point
computes the FIPS 204 algorithm byte for byte.

The specification is also proved correct as a signature scheme.
`Spec.MLDSA.Correctness.sign_verify` states that for every seed, message,
context and randomness, a signature produced by `sign` under the private
key from `keygen_internal` is accepted by `verify` under the matching
public key (and likewise for the `_internal` and `_mu` entry points).  The
proof rests on lemmas proved along the way: the NTT is a ring isomorphism
onto `Z_q[X]/(X^256 + 1)` (`Spec.MLDSA.Ring`, `Spec.MLDSA.NTT.Lemmas`); the
hint recovers the high bits, and high bits are stable under small
perturbations (`Spec.MLDSA.Rounding.Lemmas`); the key, signature and hint
encodings round-trip (`Spec.MLDSA.Encode.Lemmas`, `Spec.MLDSA.Hint.Lemmas`);
and the sampled secrets and challenge are short enough that `c s2` is
bounded by `beta` (`Spec.MLDSA.Sample.Lemmas`).
The coefficient type is again a refinement (`x: S32.t { S32.v x < q }`),
the transform multiplies by its roots with Shoup's trick against a
precomputed quotient table, and pointwise products use a Montgomery step.
On a processor with AVX2, `Hacl.Impl.MLDSA.Poly` sends the transforms and
the pointwise product to `Hacl.Impl.MLDSA.NTT.Vec256`, which does the same
arithmetic eight coefficients at a time against the same specification:
layers of half-width eight and more pair whole vectors; the last three work
on groups of sixteen coefficients, shuffled with the 128-bit, 64-bit and
32-bit unpacks so that each butterfly's ends meet in the same lane, and with
the roots gathered by a `VPERMD` of eight consecutive table entries.  Its
new instructions (`VPMULLD`, the high half of a product, `VPMINUD`,
`VPERMD`, and loads and stores of words at an offset) are in
`lib/Hacl.Vec256.Lane32.fst`.  Signing got about 2x faster, verification
1.5x and key generation 1.3x (Part 83 of `bench/REPORT.md`).

Signing is Fiat-Shamir with aborts: draw a mask `y`, commit to the high bits
of `A y`, hash to a challenge `c`, form `z = y + c s1`, and throw the
attempt away if `z`, the low bits of `w - c s2`, `c t0` or the hint leak
anything about the key.  The standard writes this as an unbounded loop; a
total specification cannot, so `Spec.MLDSA.Params.max_attempts` bounds it at
1024 attempts, and `sign` returns `None` (`false` in C) if every one is
rejected.  The expected number is four to five and running out has
probability far below `2^-256`, so this is a statement about the proof, not
about any observable behaviour.  The bound also keeps the 16-bit counter
`kappa` from wrapping.

The rejection loop is also the constant-time question.  The private key and
the mask are secret throughout, and each attempt declassifies exactly its
four verdicts, as section 3.6.3 of FIPS 204 and the reference
implementation do: whether an attempt is rejected, and by which test,
reveals nothing the accepted signature does not.  The hint is computed under
a secret mask; only its population count is declassified for the last test,
and its positions only once the signature is accepted and they are output.
Verification handles public data only.

`Hacl.MLDSA44`, `Hacl.MLDSA65` and `Hacl.MLDSA87` instantiate one
implementation at the three parameter records and export:

| function | FIPS 204 |
| --- | --- |
| `keypair(pk, sk, xi)` | `ML-DSA.KeyGen_internal`, from a 32-byte seed |
| `sign(sg, sk, msg, msg_len, ctx, ctx_len, rnd)` | `ML-DSA.Sign`, hedged, with a context string |
| `sign_deterministic(sg, sk, msg, msg_len, ctx, ctx_len)` | `ML-DSA.Sign` with `rnd` all zero |
| `verify(pk, msg, msg_len, ctx, ctx_len, sg)` | `ML-DSA.Verify` |
| `sign_internal`, `verify_internal` | algorithms 7 and 8 on a formatted message `M'` |
| `sign_mu`, `verify_mu` | algorithms 7 and 8 on a caller-computed 64-byte `mu` ("external mu") |

A context longer than 255 bytes makes `sign` and `verify` return `false`,
as the standard requires.  Pre-hashed HashML-DSA is not implemented.  The
caller supplies randomness, as everywhere else in this library: `xi` for
key generation and `rnd` for hedged signing.

`tests/test_mldsa.c` anchors each parameter set at the first NIST ACVP
keyGen seed and checks digests of the keys and of deterministic, hedged and
internal signatures, that `sign_mu` agrees with `sign_internal`, and that
verification rejects a flipped bit, a different context, a pure signature
presented to the internal interface and a modified `mu`.  Beyond the
checked-in test, the extracted C was run offline against all 480 ACVP
keyGen, sigGen and sigVer cases that do not use pre-hashing, with no
failures.

### HPKE, where the ciphersuite is a record rather than fifteen modules

RFC 9180 is an agility standard: a hybrid public-key encryption scheme
parameterised by a KEM, a KDF and an AEAD, any combination of which is a
ciphersuite.  HACL\* answers agility by generating a module per suite --
fifteen of them, plus a `Hacl.Meta.HPKE` to tie the knot -- because its
implementations are indexed by a `hash_alg` the extraction has to see
through.  Here the suite is a value:

```
type ciphersuite (t: Type0) {| word t |} = {
  kem: kem_alg;
  kdf: p: params t { hash_bytes p == 32 \/ hash_bytes p == 48 \/ hash_bytes p == 64 };
  aead: aead_alg;
}
```

and every function takes it as a `[@@@FStar.Attributes.monomorphize]`
argument, so there is exactly one implementation of `SetupBaseS`,
`KeySchedule`, `Seal` and the rest, and the extraction specialises them at
whichever suites the C surface pins.  `Hacl.HPKE.Suites` pins four --
X25519/SHA-256/ChaCha20-Poly1305, X25519/SHA-512/ChaCha20-Poly1305,
P-256/SHA-256/ChaCha20-Poly1305 and X25519/SHA-256/AES-128-GCM -- which are
the four combinations that actually change code; adding a fifth is three
lines and no proof.

Three things are more than HACL\* has.  All four modes are implemented --
Base, PSK, Auth and AuthPSK -- where the C distribution ships only Base.
All three RFC AEADs are wired up, where HACL\* offers only
ChaCha20-Poly1305 under HPKE.  And the labelled KDF is written once against
`Spec.HPKE.labeled_extract`/`labeled_expand` rather than open-coded per
suite.  Two things are deliberately different: fallible operations return
`bool` rather than a `uint32_t` that is only ever `0` or `1`, and the
ciphertext and the tag are separate buffers rather than a single
`len + 16` allocation the caller has to slice.  Export-only ciphersuites
are in the specification but not in the implementation.

The encryption context is not a type.  RFC 9180's context is a key, a base
nonce, a sequence number and an exporter secret; here those are four
caller-owned buffers, with the sequence number a one-element
`array uint64_t` so that `Seal` can advance it in place.  Nothing is
allocated on the caller's behalf, so nothing has to be freed, and a caller
that wants to keep a context in a struct can lay it out however it likes.
Running out of sequence numbers is a failure rather than a wrap, because a
repeated nonce loses the AEAD outright.

`ComputeNonce` is the one place where the proof shape mattered more than
the code.  The nonce is the base nonce exclusive-ored with the
sequence number in ninety-six-bit big-endian, which is four zero bytes and
then a `uint64`; writing those twelve bytes as straight-line code leaves
the solver twelve nested `Seq.upd`s to see through once per index, which is
quadratic, and at twelve it does not come back.  Writing them as an
allocation (whose contents are `Seq.create 12 0uy`, reachable by one
`SMTPat`), a `store_be`, and a loop with a pointwise invariant takes ten
seconds.

## Functional correctness

Everything above is a refinement proof: the C computes what the `Spec.*`
function says.  That leaves open whether the specification is the right
one, and the published test vectors are only part of the answer.  The
other part is a set of theorems about the specifications themselves, the
statements a cryptographer would write down first: decryption inverts
encryption, both parties of a key exchange agree, and an honest signature
verifies.  Each sits in a `*.Correctness` module next to the
specification it is about, is stated over exactly the functions the
implementation's postconditions name, and has no admits and no
assumptions beyond those listed here.

| scheme | module | theorem | hypotheses |
| --- | --- | --- | --- |
| ChaCha20-Poly1305 | `Spec.Chacha20Poly1305.Correctness` | `decrypt_encrypt`: the tag verifies and decryption returns the message | message length bound |
| AES-GCM (128, 256) | `Spec.GCM.Correctness` | `decrypt_encrypt`: `gcm_decrypt (gcm_encrypt m) == Some m` | the spec's length bounds |
| NaCl secretbox | `Spec.NaCl.Correctness` | `secretbox_open_secretbox`, `secretbox_open_easy` | message length bound |
| NaCl box | `Spec.NaCl.Correctness` | `beforenm_agree`; `box_open_box_agree`, `box_open_easy_agree`: the receiver, holding only the sender's public key, opens what the sender sealed | none |
| X25519 | `Spec.Curve25519.Correctness` | `ecdh_agree`: `ecdh a (pub b) == ecdh b (pub a)`, result and flag | none |
| P-256, secp256k1 ECDH | `Spec.{P256,K256}.ECDH.Correctness` | `dh_agree`; `dh_initiator_valid`: a generated public key passes validation | both private keys valid |
| FFDHE (all five groups) | `Spec.FFDHE.Correctness` | `ffdheN_agree`: both shared secrets are equal | both peers' public-key checks pass |
| Ed25519 | `Spec.Ed25519.Correctness` | `sign_verify`, `sign_expanded_verify`: `verify pub msg (sign sk msg) == true` | none (beyond the spec's message type) |
| P-256, secp256k1 ECDSA | `Spec.{P256,K256}.ECDSA.Correctness` | `verify_sign` and every hashed front end; for secp256k1 also the low-S signer and verifier | the signer returned `Some` |
| RSA-PSS | `Spec.RSAPSS.Correctness` | `sign_then_verify`: an honest signature verifies | `n = p q`, `p != q` prime, `e d = 1` mod `p-1` and `q-1`; `2^(modBits-1) <= n`; signing succeeded |
| HPKE (all modes, both KEMs, all AEADs) | `Spec.HPKE.Correctness` | `encap_decap`, `auth_encap_decap`, `setup_agree`, `context_open_seal`, `open_base_seal_base` | the public keys are those of the private keys; the sender succeeded |
| ML-KEM (all parameter sets) | `Spec.MLKEM.Correctness` | `mlkem_correct`: `decaps dk (encaps ek m) == k`; `kpke_correct` | decryption noise below `q/4` in every coefficient |
| FrodoKEM (all parameter sets) | `Spec.Frodo.Correctness` | `kem_correct`: `dec ct sk == ss`; `pke_correct` | every entry of `S'E + E'' - E'S` below `q/2^(B+1)` |

The supporting facts are proved, not assumed, along the way: that the
P-256 and secp256k1 group orders are prime (Pocklington certificates in
`Spec.Group.OrderPrimes`), that `n G` is the identity on all three curves
(by evaluation), that Ed25519 point compression round-trips, that the
X25519 Montgomery ladder computes the u-coordinate of a scalar multiple on
the proved Edwards group (`Spec.Curve25519.Montgomery`), RSA inversion
from Fermat's little theorem and Euclid's lemma
(`Spec.RSAPSS.Fermat`), the ML-KEM and FrodoKEM byte-encoding round trips,
and the ML-KEM NTT ring isomorphism (`Spec.MLKEM.NTT.Lemmas`).

Two kinds of statement are deliberately absent.  The lattice KEMs are
correct only with overwhelming probability, so their theorems take the
noise bound as a hypothesis and stop there; bounding the probability that
honestly sampled noise exceeds it (2^-138 to 2^-252 for FrodoKEM, 2^-139
to 2^-174 for ML-KEM) needs a probability framework, an idealised model of
the hashes and a numeric tail bound, and is future work.  And the
Diffie-Hellman theorems for FFDHE assume the peers' public-key checks
pass rather than proving that an honest key always does, since that needs
the primality of the RFC 7919 moduli, which this repository establishes
only by test.

## Performance

Measured on an AMD EPYC 7V13 (Zen 3; AVX2, ADX, SHA extensions, no AVX-512)
in a shared virtual machine, gcc 15.2.0 `-O3`, against HACL\* `504c298`,
pinned to one core, three rounds at two link-time code offsets, all three
contenders interleaved inside each round, per-benchmark minimum over the
runs (see [Measuring on a shared machine](#measuring-on-a-shared-machine)).
The previous table was measured on an Intel Xeon Gold 6140 (Skylake-SP,
AVX-512, no SHA extensions); ratios that moved between the two tables mostly
moved with the processor, and the ones that did not are discussed below.

The harness that produces this table lives in [`bench/`](../bench/), along with
[`bench/REPORT.md`](../bench/REPORT.md), which records every optimization in this
repository in the order it happened --- the measurement that motivated it, the
experiment that confirmed or killed the hypothesis, and the result.  The table
itself is regenerated by `bench/mktable.py` rather than typed by hand.
For a comparison with OpenSSL, AWS-LC, libsodium, libjade, Firedancer,
dalek and, for ML-DSA, libcrux, pq-crystals and mldsa-native, see
[Against other libraries](#against-other-libraries).

There are two reference columns, because there are two different questions.

**HACL\* best** is HACL\* configured for this machine and allowed everything it
has: EverCrypt's runtime multiplexing onto Vale's SHA-EXT assembly, the AVX2
ChaCha20 and Poly1305, the vectorized BLAKE2, and the BMI2/ADX Curve25519.
This is what a caller who reaches for HACL\* on this machine actually gets, so
it is the ratio the table is sorted by and the one in bold.  Where HACL\* has
no specialised backend for a primitive the two reference columns are the same
number.

**HACL\*** is HACL\*'s **portable scalar C** -- not its vector
variants -- except for AES-GCM, where HACL\* has no portable implementation at
all and the reference is EverCrypt dispatching to Vale assembly.  This is the
like-for-like comparison: same algorithm, same instruction set, two extraction
pipelines.  It is the column that isolates the extraction pipeline from the
instruction set, which is the only thing a reader can conclude about Pulse
from a benchmark; but it is not what a user would be choosing between, which
is why it is no longer the headline.

Ratios are hacl-pulse over the reference, so **below 1.00 is faster than the
reference**.

| primitive | size | hacl-pulse | HACL\* best | ratio | HACL\* | ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| SHA-1 | 256 KiB | 184 us | 1.6 ms | **0.11x** | 1.6 ms | 0.11x |
| Salsa20 | 256 KiB | 105 us | 433 us | **0.24x** | 433 us | 0.24x |
| NaCl secretbox | 256 KiB | 156 us | 616 us | **0.25x** | 616 us | 0.25x |
| SHA-512 | 256 KiB | 519 us | 1.3 ms | **0.39x** | 1.3 ms | 0.39x |
| HMAC-SHA-512 | 256 KiB | 526 us | 1.3 ms | **0.39x** | 1.3 ms | 0.39x |
| RSA-PSS-2048 verify | -- | 56 us | 130 us | **0.43x** | 130 us | 0.43x |
| P-256 ECDH | -- | 71 us | 151 us | **0.47x** | 151 us | 0.47x |
| SHAKE128 | 256 KiB | 606 us | 1.3 ms | **0.48x** | 1.3 ms | 0.48x |
| SHA3-256 | 256 KiB | 751 us | 1.5 ms | **0.49x** | 1.5 ms | 0.49x |
| P-256 ECDSA sign | -- | 83 us | 164 us | **0.51x** | 164 us | 0.51x |
| P-256 ECDSA verify | -- | 237 us | 414 us | **0.57x** | 414 us | 0.57x |
| Ed25519 sign | -- | 35 us | 56 us | **0.63x** | 56 us | 0.63x |
| BLAKE2b | 256 KiB | 369 us | 428 us | **0.86x** | 358 us | 1.03x |
| BLAKE2s | 256 KiB | 577 us | 615 us | **0.94x** | 610 us | 0.95x |
| FFDHE-2048 | -- | 4.1 ms | 4.2 ms | **0.96x** | 4.2 ms | 0.96x |
| RSA-PSS-2048 sign | -- | 4.1 ms | 4.3 ms | **0.96x** | 4.3 ms | 0.96x |
| Poly1305 | 256 KiB | 49 us | 51 us | **0.96x** | 182 us | 0.27x |
| RSA-2048 modexp | -- | 4.1 ms | 4.2 ms | **0.98x** | 4.1 ms | 0.99x |
| ChaCha20-Poly1305 | 256 KiB | 152 us | 139 us | **1.10x** | 1.1 ms | 0.14x |
| secp256k1 ECDSA sign | -- | 69 us | 63 us | **1.11x** | 63 us | 1.11x |
| AES-128-GCM | 256 KiB | 77 us | 67 us | **1.15x** | 67 us | 1.15x |
| HMAC-SHA-256 | 256 KiB | 205 us | 174 us | **1.18x** | 1.1 ms | 0.19x |
| ChaCha20 | 256 KiB | 103 us | 88 us | **1.18x** | 909 us | 0.11x |
| SHA-256 | 256 KiB | 204 us | 173 us | **1.18x** | 1.1 ms | 0.19x |
| MD5 | 256 KiB | 557 us | 432 us | **1.29x** | 431 us | 1.29x |
| X25519 | -- | 53 us | 40 us | **1.32x** | 40 us | 1.34x |

This table was re-measured after the master merge of October 2026 (`bench/REPORT.md`
Part 86).  The machine had become about 8% slower on both sides since the
previous table, so the absolute numbers rose while the ratios moved by a few
hundredths at most; the prose below quotes the earlier measurement where it
gives a ratio, and a few have shifted (SHAKE128 and SHA3-256 to 0.48x--0.49x,
secp256k1 signing to 1.11x, MD5 to 1.29x, X25519 to 1.32x).  The Ed25519
signing row is the Part 86 number scaled by `bench/REPORT.md` Part 89's
before-and-after measurement of the signed comb.

Against what HACL\* can actually do on this machine, eighteen rows are ahead
and every row is within 1.32x.  Ed25519 signing is at 0.63x since its
fixed-base multiplication became a signed comb over eight compiled-in
tables (`bench/REPORT.md` Part 89).  The furthest ahead are Salsa20 and
secretbox at 0.24x--0.25x, because HACL\* has no vector Salsa20; RSA
verification at 0.43x, whose ladder starts at the exponent's top set bit
(`bench/REPORT.md` Part 67); the three P-256 rows at 0.47x--0.57x;
SHA-3 and SHAKE at 0.48x--0.49x, where HACL\* has no vector sponge; and
SHA-1 at 0.11x and SHA-512 and HMAC-SHA-512 at 0.39x, where HACL\* has
neither a SHA-extensions SHA-1 nor a vector SHA-512 message schedule
(`bench/REPORT.md` Part 87; those three rows are the Part 86 numbers scaled
by Part 87's before-and-after measurement).  P-256 was at 0.64x--0.76x until
its field-element copy stopped being a loop: gcc vectorized the four-word
loop into 16-byte loads that missed store forwarding from the multiply's
8-byte stores, and every point operation copies after nearly every field
operation (`bench/REPORT.md` Part 72).  The BLAKE2 rows, Poly1305 and the
modular exponentiations are level or slightly ahead.

The stream-cipher rows lost their lead with the processor.  On the Skylake
machine ChaCha20 and ChaCha20-Poly1305 were at 0.53x and 0.67x because the
AVX-512F backend ran sixteen blocks to HACL\*'s eight (Part 60); this
processor has no AVX-512, so the comparison is now AVX2 against AVX2, at
1.15x and 1.08x (1.31x and 1.17x until Custard was stopped from compiling
the vector wipes for the wrong target; `bench/REPORT.md` Part 71).  It does
have SHA extensions, so SHA-256 and HMAC-SHA-256 are this repository's
intrinsics against Vale's SHA-EXT assembly, at 1.17x (and 0.19x of
HACL\*'s portable C).  AES-128-GCM is at 1.12x, MD5 at 1.27x, and X25519
at 1.28x: under gcc the radix-2^64 field (see
[Curve25519 again, four limbs of sixty-four bits](#curve25519-again-four-limbs-of-sixty-four-bits))
is a little slower than the radix-51 code it replaced; under clang it is
level with HACL\*'s BMI2/ADX assembly.

Ed25519 and secp256k1 signing, at 1.30x and 1.14x before the comb, were briefly at 1.71x
and 1.52x when the tables were first re-measured after secret temporaries
began to be wiped (issue #1).  Under gcc, a wipe whose length gcc cannot
see, or of 128 bytes or more, became `rep stosq`, whose start-up cost
dominates on a forty-byte field element, and the point additions and
doublings wipe six or seven of those each.  Small constant-length wipes
are now volatile word stores (`c/Hacl_Mem.h`; `bench/REPORT.md` Part 70),
which took Ed25519 signing from 85 us to 66 us and secp256k1 signing from
85 us to 65 us, and P-256 and SHA-512 a few percent with them.  Under clang
the wipes cost 2--3% either way.

Under clang 21, with HACL\* also built by clang, no row is above 1.32x
(HMAC-SHA-512) and eleven are ahead.  MD5 (0.92x), BLAKE2 (0.89x--0.90x),
Poly1305 (0.89x), ChaCha20 (0.94x) and ChaCha20-Poly1305 (0.92x) are ahead;
X25519 and P-256 are level at 1.00x--1.01x, with P-256 verification at
1.22x; Ed25519 and secp256k1 signing are at 1.19x and 1.28x (Ed25519's
before the comb, which halved signing under clang as well).  SHA-3 and
SHAKE are at 0.75x--0.80x rather than 0.54x--0.56x, and SHA-512 and
HMAC-SHA-512 were at 1.26x--1.32x rather than 0.52x--0.54x, because clang builds HACL\*'s sponge and SHA-512 about twice
as fast as gcc does.  That was before Part 87: clang's SHA-512 and
HMAC-SHA-512 went from 771 us and 777 us to 432 us and 430 us with the AVX2
message schedule, which puts them at about 0.71x--0.73x.

The rows that were the honest ceiling are not any more.  ChaCha20,
Poly1305 and ChaCha20-Poly1305 were at 5.31x, 4.13x and 5.13x four
tables ago, measured on an AMD EPYC 7662: they were what wide vector lanes
are worth on a stream cipher and a one-pass MAC, and no amount of work on
scalar C could close them.  All three now have verified vector backends
(see [ChaCha20, a keystream and nothing else](#chacha20-a-keystream-and-nothing-else)
and [Poly1305, five limbs of twenty-six bits](#poly1305-five-limbs-of-twenty-six-bits))
and sit at 1.19x, 0.97x and 1.10x under gcc, and 0.94x, 0.89x and 0.92x
under clang, against HACL\*'s AVX2 code.


The remainder of this section was written against the EPYC 7662 table, which
has SHA extensions; the numbers in it are from that machine.

Two rows were recently somewhere else.  HMAC-SHA-256 was the worst in the
table at 6.84x, because the SHA-EXT dispatch existed only in the one-shot
hash and HMAC goes through a *prefixed* hash that is generic in the word
type; generic code cannot branch into an implementation that exists only at
thirty-two-bit words, so HMAC ran scalar rounds on a machine already issuing
`sha256rnds2`.  A specialised `hash_prefixed_ni` and `hmac_impl_ni` took the
256 KiB case from 1,136 us to 227 us.

Then both SHA-256 rows moved again, from 227 us to 190, and under clang from
668 us to 179 -- 3.7x -- when a single stray `target` attribute was removed;
see [One attribute in the wrong place, and three quarters of the
time](#one-attribute-in-the-wrong-place-and-three-quarters-of-the-time).

That left SHA-256 and HMAC-SHA-256 tied at 1.16x against Vale's SHA-EXT
assembly, which is this repository's intrinsics against hand-written assembly
rather than scalar against vector, and is the narrowest of the remaining
gaps.  Every vectorized primitive still loses at 64 bytes, where the setup
outweighs the body.

Three things account for most of the spread against the scalar reference.

**Where the C is at parity or ahead, it is because the algorithm is the same
and the extraction is clean.**  SHA-256 is ahead because the SHA extensions
are wired in and HACL\*'s portable C does not use them; ChaCha20, SHA-512 and
SHA-3 are ahead because Custard's output unrolls and register-allocates at
least as well as karamel's and the specifications here permitted a flatter
implementation.  Nothing was hand-tuned.  SHA-3 is the one of these that was
returned to: the rate is now a literal in each of the six sponges and the
permutation sits inside them rather than behind a call, which is worth 2.4x
on a 64-byte digest and 1.13x on bulk.  A 64-byte SHA3-256 is 624 ns against
the reference's 985.

**Where it is behind by a quarter, it is the Montgomery multiply.**  RSA-PSS,
FFDHE and the generic modexp move together, because they are one cause and
not three: they are the same ladder.  That ladder used to be
square-and-multiply, two multiplications per exponent bit against HACL\*'s
five per four bits, and those three rows sat at 1.98x.  They now run the
same 4-bit window as the reference, which was worth 1.56x on gcc and 1.58x
on clang and brought them to about 1.25x.  Two changes to the inner loop
have since taken them past it, to 0.94x--0.97x under gcc and 0.92x--0.94x
under clang.

The first is that the row of an `n x n` multiply is now taken four columns
at a time, with a one-at-a-time tail, which is what HACL\*'s own inner loop
does: four independent `mulx` chains in one iteration have loads to overlap
with, where a single column has only the loop back-edge.  That alone took
`mont_mul` from 2,243 ns to 1,990, level with the reference's 1,986.

The second is a dedicated squaring.  A square has the same columns as a
general product, but the off-diagonal ones come in pairs -- `a_i a_j` occurs
at weight `i + j` once in each of two rows -- so `Hacl.Bignum.Base.sqr`
computes only the strict upper triangle, doubles the whole of it once, and
then adds the `n` diagonal terms `a_i^2` at weight `2i`.  That is `n(n-1)/2`
products against `n^2`: for the thirty-two limbs of a 2048-bit modulus, 496
against 1,024.  Measured, 579 ns against the full multiply's 931, and within
5% of HACL\*'s own `bn_sqr` at 550.  Since a 4-bit-window 2048-bit
exponentiation is about 2,048 squarings against 512 multiplies, four fifths
of the work is now going through the cheaper path.

The invariant that makes the triangle correct is `A_k^2 = 2 T_k + D_k`,
where `A_k` is the prefix of the input, `T_k` the triangle so far and `D_k`
the diagonal; it survives `A := A + a b^k` because `(x + a b^k)^2 = x^2 + 2 x
a b^k + a^2 b^{2k}`, which is one lemma.  The doubling cannot carry out,
because `2 T_n <= A_n^2 < b^{2n}`.

The verify row came down separately and much further.  It is a 2048-bit
exponentiation by 65537, seventeen bits, so the ladder is short and almost
all of it was the setup: computing `R^2 mod n` by a chain of 4,096 modular
doublings cost 361 us against a 155 us exponentiation.  That chain is now an
exponent ladder over the *Montgomery* exponent --- squaring doubles it, a
single modular doubling adds one --- seeded at the topmost limb of the
modulus rather than at one, which reaches the same value in about a dozen
squarings and sixty-five doublings: 32.5 us, 11.1x faster, and 2.9x faster
than HACL\*'s own 95 us.  `rsapss-2048-verify` went from 516 us to 198, and the squaring has since taken it to 166; starting the variable-time ladder at the exponent's top bit (Part 67) took it to 64 us under gcc and 60 under clang.

What is left on these rows is the reduction, not the multiply: a 32-limb
`reduction` costs 1,035 ns to the multiply's 931 and the squaring's 579, so
it is now the larger half of both `mont_mul` and `mont_sqr`.  HACL\* has an
*almost*-Montgomery variant that skips the final conditional subtraction
inside the ladder and corrects once at the end; that is the next thing to
try, and it is worth roughly the conditional subtraction per step.

An earlier version of this table put the modexp row at 0.70x and concluded
that the generic bignum was ahead.  That was wrong, and the way it was wrong
is worth recording: the benchmark's reference side called `Hacl_Bignum32`,
which is HACL\*'s **32-bit-limb** bignum, against hacl-pulse's 64-bit limbs.
`Hacl_Bignum64` on the same input is 4.5 ms rather than 12.9, and the row
that had looked like a 1.43x win is a 1.98x loss.  A reference is only a
reference if it is the same algorithm at the same width.

**Where it is behind by more, it is the higher-level algorithm.**  Curve25519
now runs at radix 2^51 like HACL\*'s `_51` with the same straight-line `fmul`,
so the field arithmetic is the same shape, and with the field marked
`CInline` X25519 is within 1.26x -- what is left there is the ladder itself,
which has had no attention.  Ed25519 is further behind, but much
less so than it was: both halves of its scalar multiplication have now been
windowed.  The variable-base half was worth 22% of key generation, 19% of
signing and 18% of verification; the fixed-base half, which splits the scalar
into four sixty-four-bit pieces and walks them together against [2^64] G,
[2^128] G and [2^192] G as well as G, was worth a further 28% of key
generation and 23% of signing; compiling in the four sixteen-entry tables of
multiples that the fixed-base half was building on entry -- sixty point
additions out of a hundred and eighty-eight -- was worth a further 25% of key
generation, 25% of signing and 10% of verification.  The scalar arithmetic
mod the group order,
which used to be done a bit at a time and cost more than a fifth of a
signature, is now four-limb Montgomery like every other curve here and costs
almost nothing.  Key generation went from 3.40x of the reference to
**1.46x** and signing from 3.82x to **1.46x**; verification is **1.98x**.  Under
clang the first two are **1.16x**.  secp256k1 and
P-256 have now had the same treatment, so no curve here walks its generator
bit by bit any more.  P-256 and secp256k1 were behind for three reasons, of
which secp256k1 now has none in particular and P-256 has one.  The plainest has been removed for both: the 256-bit core they share was
eight limbs of thirty-two bits, so a field multiply did sixty-four schoolbook
products and sixty-four reduction products, and it is now four limbs of
sixty-four, which does sixteen and sixteen.  Measured directly, our secp256k1
`fmul` went from 53.4 ns to 21.5 and our P-256 `fmul` from 42.2 to 19.7.
Second, secp256k1 no longer uses the shared general Montgomery core at all: it
has its own five-limb, radix-2^52, lazily reduced field, the same
representation HACL\* and libsecp256k1 use, with the special-prime fold
`2^256 = p + 2^32 + 977` in place of a Montgomery reduction.  A latency probe
of the two field multiplies side by side -- ours and HACL\*'s, each behind a
call, each fed its own previous output -- puts ours at 29.4 ns against 25.9,
so the secp256k1 field is within 14% of the reference and is no longer worth
attention.  P-256's prime has since had the same treatment, in its own
Montgomery form (see below).
Third, the scalar multiplication.  Both curves have now had that, on the
variable-base side: each walks the scalar four bits at a time against a
sixteen-entry table of small multiples of the input point, built at run time,
so a 256-bit multiplication costs sixty-four rungs of four doublings and one
addition plus sixteen to build the table -- 336 point operations against the
ladder's 512.  On secp256k1 it is worth about 26%: ECDH went from 213 us to
154 and its ratio against the reference from 2.40x to **1.73x**, ECDSA
signing from 227 to 169, verification from 428 to 313, and secret-to-public
from 213 to 153.  On P-256 it is worth about a third, because that curve's
addition formula is the more expensive of the two and so the saved operations
were worth more: ECDH as initiator went from 401 us to 271 and as responder
from 402 to 271, signing from 417 to 287 and verification from 812 to 545.
The responder row is the one to note -- variable-base ECDH on P-256 was 1.14x
the reference and is now **0.76x** it, the first asymmetric primitive here
that is faster than HACL\*'s portable C.  clang agrees within 3% on both
curves.  What remains is the *fixed*-base side, where HACL\* has a window
compiled in and this does not: signing, verification and secret-to-public all
start from a multiplication by the generator.  secp256k1 has now had that
too: `Hacl.K256.PointMulG` splits the scalar into four sixty-four-bit pieces
and walks them together against `G`, `2^64 G`, `2^128 G` and `2^192 G`, 184
point operations against 335, and its three fixed-base rows moved together
-- `secret-to-public` from 155 us to 111 and 3.16x to 2.27x, signing
from 172 to 126 and 2.63x to 1.91x, verification, which does one
fixed-base and one variable-base multiplication, from 319 to 271.
Compiling in the four sixteen-entry tables that this was building on entry --
sixty point additions out of a hundred and eighty-four, a third of the work --
moved the same three rows again, and by about the same proportion Ed25519
saw: `secret-to-public` from 111 us to **75** and 2.27x to **1.55x**, signing
from 126 to **91** and 1.91x to **1.40x**, verification from 271 to **234**
and 2.59x, ECDH, which is variable-base and only pays for the table build in
its key-generation half, from 173 to **154** and **1.75x**.  Under clang the
three fixed-base rows are **1.55x**, **1.50x** and **2.55x**.

P-256 has now had it too, and gained more from it than either of the others.
Its addition formula is the more expensive, so the eighty-two point
operations the window saves are worth more, and unlike the other two curves
it starts close enough to the reference that the saving takes it to parity:
ECDH as initiator went from 272 us to **165** and 1.73x to **1.04x**, signing
from 287 to **182** and 1.69x to **1.08x**, and verification from 545 to
**449** and 1.27x to **1.05x**.  ECDH as responder, which is variable-base
and is the control, is unchanged at 275 us and **0.77x**.  P-256 is
therefore within 10% of HACL\*'s portable C on every operation it offers and
ahead of it on one.  Under clang it is ahead on three of the four:
`dh-initiator` 151 us against 156 (**0.97x**), verification 393 against 429
(**0.91x**), `dh-responder` 241 against 355 (**0.68x**), with signing at
parity, 172 against 169 (**1.02x**).  That the two compilers disagree about
which side of 1.0x three of these rows fall on is the right way to read
them: the remaining difference is no longer algorithmic.  P-256 has since
had the special-prime field too (`Hacl.P256.Field64`, Part 62), which took
another 35-50% off every row: under gcc ECDH as initiator 176 us to **112**,
as responder 285 to **180**, signing 192 to **131** and verification 448 to
**292**; under clang 163 to **88**, 256 to **129**, 185 to **110** and 428
to **222**.  Compiled-in generator tables and an inversion on that field
(Parts 63 and 64) then took, in a second harness, ECDH as initiator from 97
us to **65** under gcc and from 77 to **49** under clang, signing from 119 to
**86** and 96 to **69**, and verification from 256 to **224** and 194 to
**166**.  A faster scalar multiplier and an addition-chain inversion (Part
65) then took signing to **75** and **57** and verification to **213** and
**154**.  Making the four-word field copy straight-line code instead of a
loop that gcc vectorized into store-forwarding stalls (Part 72) then took
every row a quarter faster under gcc and left clang unchanged: ECDH as
initiator 88 us to **64**, signing 98 to **76** and verification 290 to
**216**.  The table above includes all five: P-256 is now at 0.47x--0.57x
of HACL\* under gcc and 0.93x--1.16x under clang.

**`inline` is a global resource.**  The whole library is one translation unit,
so `FStar.Attributes.CInline` -- Custard's `static inline` request -- is spent
against gcc's `--param inline-unit-growth` budget for the unit as a whole.
Marking `Hacl.Impl.Bignum4`, the layer every P-256 and secp256k1 operation
goes through, is worth **1.9x** on both curves and costs nothing anywhere
else.  Marking the Montgomery and field wrappers above it as well, or
Poly1305 alongside, gains no more and costs 1.5x on BLAKE2, 1.4x on Salsa20
and 1.6x on Ed25519 -- primitives that share no code with any of it.  Raising
the budget on the command line restores them exactly, which confirms the
mechanism, but a library cannot dictate its consumers' flags.  So the
attribute goes only where it is paid for: Curve25519's field and the 256-bit
bignum core.  The `Hacl.Secret` arithmetic, 168 single-expression functions,
gains nothing at all -- gcc was already inlining every one.

**And so is interprocedural constant propagation.**  The same lesson arrived
a second time, less gently.  `Hacl.Impl.Mont4.amul` took its modulus and
its Montgomery constant as arguments so that the field and the scalar field
of both curves could share one multiplier, and the comment above it said that
specialising them would buy nothing.  gcc had in fact been specialising them
all along: it cloned `amul` once per modulus, four times, and the clones were
worth two and a half times on every P-256 and secp256k1 operation.  That is
also a budget -- `--param ipa-cp-large-unit-insns` defaults to sixteen
thousand -- and adding FrodoKEM and HPKE to the single translation unit spent
it.  The clones vanished, and every elliptic curve benchmark got two and a
half times slower without a single line of elliptic curve code changing.
`amul` is now `inline_for_extraction`, and so is the modular exponentiation
`Hacl.Impl.Exp4.mexp` above it, which gcc was cloning for the same reason:
each of their call sites carries its own copy with its own constants.  That
is a decision the library makes rather than one it hopes for, and it puts the
curves back at or slightly ahead of where they were before the merge.

**So the policy is to do this work ourselves.**  Every specialisation the C
compiler performs for us is one we do not control, and there are two
independent reasons not to want that.  It is spent against a budget for the
translation unit as a whole, so any new primitive can take it away without
touching the code it slows down.  And clang does no function specialisation
at all -- LLVM's pass is off by default -- so anything obtained this way is a
gcc-only speedup, and shows up as a gcc/clang gap rather than as a gap in the
library.  Splitting the distribution into several files does not fix either
one; it makes the units smaller, which moves the budget around and takes away
inlining opportunities elsewhere.  The fix is to say what we mean, and
there are two ways to say it.  `inline_for_extraction` puts the body at the
call site, which is right for a small function; for a large one, marking the
parameter `[@@@FStar.Attributes.monomorphize]` is right instead, because
Custard then emits one specialised *copy* per constant the callers pass.
ML-KEM is the cautionary tale: inlining its K-PKE layer into the three entry
points gave the constants to the same loops and was worth nothing, because
the C compiler stops inlining inside a function that large, while a copy per
parameter set was worth 1.31x on encapsulation.  Either way both compilers
see the same code.

`make clones` reports where we are still relying on the compiler's judgement:
it compiles the distribution with gcc, lists the functions it cloned, and
diffs them against `mk/clones.baseline`.  There are sixty-three today -- HMAC,
the SHA-2 cores, the MD5 and SHA-1 blocks, ML-KEM -- and the list is meant to
shrink.
`make clones-available` recompiles with the budget raised and prints what gcc
*would* have cloned given room.

It has already earned its place.  Specialising the SHA-3 sponge grew the
distribution by four thousand lines, and the check reported five clones lost
to that growth: the generic bignum's Montgomery reduction, its precomputation
and its constant-time exponentiation, a Frodo sampler and an HPKE label
expansion.  Every one of them turned out to be worth nothing -- RSA-PSS,
FFDHE and the bare modexp are unchanged to within a quarter of a percent.
Which is the other half of the lesson: a clone tells you the compiler found a
specialisation, not that the specialisation pays.  The way to find out is to
measure, and the way to keep the answer is to write it down.

Sometimes a clone is not a specialisation at all.  The survey once reported
`Hacl_Bignum_Exponentiation_mont_sq4` under `.isra`, the suffix gcc uses when
it rewrites a signature rather than a body, and the whole content of the
report was that `mont_sq` took a scratch array it had stopped using.  The
clone was gcc removing a dead argument on our behalf.  Deleting the parameter
in F\* removed the clone, which is the right outcome: an `.isra` entry is
usually a note that the C we emitted says something we did not mean.

The survey is also what caught a stale `dist/`.  Extraction is a
whole-program step whose real dependency is every `.checked` file, and the
makefile said so --- but it said so in a fragment included before the one
that defines that list, so the list was empty and `dist/` was only rebuilt
when the *root* module changed.  Nothing warns about this: `make extract`
exits zero and prints nothing, which is exactly what it prints when there
is genuinely nothing to do.  The committed C was two thousand lines out of
date before `make clones` disagreed with the baseline and gave it away.
The include order is now fixed, with a comment saying why it matters.

Regenerating against the current toolchain then moved the baseline from
sixty-five to sixty-three.  Three of HMAC's `hmac_cat` clones went away ---
specialised for us upstream, and absent from `clones-available`, so this is
a takeover and not a budget loss --- and the smaller translation unit left
enough interprocedural budget for one more of the Frodo entry points,
`keypair_coins__Mkparams_3`, to join the siblings of its own family that
were already there.

BLAKE2 is what the policy looks like when it is clang that was losing.  gcc
cloned the compression function and both half-rounds, once per width, on the
initialisation vector, the message schedule and the final-block flag; clang
cloned nothing, and that alone was most of a 13% gap between the two.  Making
the whole chain from `g_impl` up to `compress_impl` `inline_for_extraction`
leaves gcc exactly where it was -- it was already getting this -- and brings
clang up to meet it: BLAKE2b 640 to 562 microseconds, BLAKE2s 1,016 to 932.
The two compilers now agree on BLAKE2b to within one percent.

One function in that chain was deliberately left alone at the time, and it
was the interesting one.  Inlining `round_impl` into the round loop let clang
keep the sixteen-word working vector in registers and reach 441 microseconds,
a further 1.35x; the same change cost gcc 15%, because gcc spilled the vector
instead.  There was no annotation that satisfied both, which is the honest
signal that the code, not the annotation, was what needed to change.

So the round loop was unrolled.  It ran `16 * (i % 10)` rounds over a
hundred and sixty entry schedule table, and the modulus is there because
BLAKE2b's eleventh and twelfth rounds reuse the first and second
permutations.  Written out as ten straight-line round bodies plus two more
under a test on the round count -- a field that is a literal after
monomorphization, so exactly one arm survives -- every one of the hundred and
ninety-two schedule lookups has a constant subscript, and `round_impl` can
then be `inline_for_extraction` without either compiler having to guess
anything.  BLAKE2b went from 567 to 395 microseconds under gcc and 562 to 347
under clang; BLAKE2s from 849 to 595 and 932 to 571.  BLAKE2s is now at
parity with HACL\*'s reference on both compilers, and BLAKE2b is 1.27x rather
than 1.81x.

Two details made the difference between that and a much smaller win.  The
first is that unrolling *alone* is worth nothing at all -- measured at
exactly 1.00x on both compilers -- because with `round_impl` still a call the
literal base is just an argument.  The second is where the working vector
lives: moving its allocation out of the callers and into `compress_impl`, so
that it is a local array in the same function as the unrolled rounds rather
than a pointer parameter that might alias, is worth a further 1.15x to gcc
and 1.33x to clang, because that is what lets the sixteen words be promoted
to registers.  The cost is twelve thousand lines of generated C, and it is
bounded by keeping `compress_impl` itself *not* inlined: eight copies of the
unrolled rounds rather than the thirty-two the call sites would have given,
which also matters because gcc loses most of the win to code size at
thirty-two.

One thing the unrolled round exposed is that the schedule table was still
arriving as a *parameter*.  `sg` was threaded from the four entry points down
through six functions to the round body, and nothing ever passed anything
else -- there is one sigma table in BLAKE2 and both widths share it.  The
parameter existed only to be constant-propagated away, and whether it was
propagated away was the C compiler's decision rather than ours.  It is now
read from the global inside `compress_impl`, where the C is a local pointer
to a `static const` array and both compilers fold the hundred and ninety-two
literal subscripts at `-O1`.

That change is worth **nothing at all** at `-O3`, which is the point.  Both
compilers were already getting it -- gcc by cloning `compress_impl` against
the `ipa-cp-large-unit-insns` budget, clang by interprocedural constant
propagation into a `static` function -- and the measurement that matters is
what happens when they stop.  Compiling with `-fno-ipa-cp`, which is what an
exhausted budget looks like, used to cost BLAKE2 between 9% and 15%; it now
costs nothing measurable.  A speedup you are not in control of is a speedup
that can be taken away by an unrelated commit, and this one was the largest
left in the library.  Pricing the rest the same way: SHA-2 still owes 6%,
MD5 3%, NaCl's secretbox 8% at 64 bytes, and nothing else moves.

AES-GCM is the one row that was worked on.  It began at 875 microseconds on
256 KiB, twelve times the reference, and is now 140 -- four AES blocks in
flight at a time, eight GHASH blocks against the precomputed powers of the
hash key, a GF(2^128) reduction by shifts rather than by a second multiply,
that reduction now performed once for every eight blocks rather than once per
block, and the counter incremented in a vector lane rather than by a
constant-time carry chain through memory.  Deferring the reduction was worth
2.11 cycles a byte to 1.28 in GHASH alone, and widening the group from four
blocks to eight a further 1.22 to 1.03; putting the counter in a lane was
worth 1.55 to 0.49 in counter mode, and removed a hundred and thirty-nine of
the two hundred and twenty-five instructions a four-block turn was spending.
The remaining 1.98x is against hand-written assembly that interleaves
six blocks, and that is reachable from here.

Its *small*-message row was worked on separately and much later, after a
profile that should have been taken years earlier: the key schedule was
computing its S-box algebraically, which is three hundred and fifty
dependent operations a byte and fourteen thousand cycles a call, paid on
every AEAD call whatever the message length.  Binding `AESKEYGENASSIST` with
a zero round constant -- a single extern, because the round constant is
already carried in a register and exclusive-ored in by hand -- took that to a
thousand cycles, and sixty-four-byte AES-128-GCM from 77.45x of the reference
to **7.54x**.  The architecture section has the details.  The general lesson
is that a bulk throughput benchmark hides flat costs perfectly.

The benchmark harness and a long write-up of each optimization are kept
outside the repository; the numbers above are reproducible with any AEAD/hash
benchmark that links `dist/Hacl.c` on one side and HACL\*'s `dist/gcc-compatible`
on the other.

### A machine word is not eight bytes in a loop

`Hacl.Impl.Bytes.load_le` and `load_be` read a 32- or 64-bit word out of a
byte array, and for most of this repository's life they did it the obvious
way: one loop, one byte per iteration, `acc = acc * 256 + b`.  That is the
shortest code and the shortest proof -- one invariant, one `le_nat_cons` --
and it is the single most expensive line in the library.

Two things are wrong with it.  The first is that every iteration depends on
the previous one, so reading a sixty-four-bit word is eight serially
dependent shift-or pairs, something like twelve cycles, where the machine has
an instruction that does it in one.  The second is subtler and is the reason
no compiler rescued it: the trip count is `nbytes`, a *field* of the `word`
class, and Custard emits a class field as a C global.  `while (j < n)` with
`n` loaded from memory is not a loop any compiler will unroll, so the
eight-byte read never even got the chance to be recognized as a byte-gather
pattern.

The fix is to read four bytes with no loop at all --

```c
b[off] | (b[off+1] << 8) | (b[off+2] << 16) | (b[off+3] << 24)
```

-- and to make a sixty-four-bit read two of those joined by a shift.  Four is
the right width because `bits` is at least thirty-two for every instance of
the class, so the four-byte reader needs no precondition and both instances
can use it; `load_le` keeps its old signature and dispatches on `nbytes`,
with the original loop left behind as the branch for a width that is neither
four nor eight.  Nothing reaches that branch, because `word` has exactly two
instances, but leaving it there means the code does not depend on that fact.

What this costs in proof is two lemmas and a little bookkeeping.
`le_nat_prefix` says that extending a little-endian prefix by one byte adds
that byte scaled by `2^(8k)`, which is the term the straight-line code
contributes; `or_byte_le` says that `logor` of an accumulator below `2^(8k)`
and a byte placed at `8k` is their sum, which is `FStar.UInt.logor_disjoint`
with the operands in the right order.  Big-endian needs the mirror of each,
stated on the running accumulator `be_nat (prefix) * 2^(8(n-1-k))` so that
the equation is again "add one scaled byte".  The four steps themselves are
hoisted out of the Pulse code into `le4_ok` and `be4_ok`, pure lemmas whose
parameters are the four machine values the body computes and whose
hypotheses are the equations relating them -- the solver never has to look
inside a `logor` of a `shift_left` and reason about `le_nat` at the same
time.

It is worth **1.18x on Poly1305 under gcc and 1.54x under clang**, which
takes Poly1305 from 1.35x of HACL\* to 1.14x, and under clang past it.  The
same two loads per sixteen-byte block were a fifth of the entire running
time.  ChaCha20-Poly1305 gains 6%, NaCl's secretbox 19%, SHA-512 and
HMAC-SHA-512 4-5% under clang.  clang recognizes the four-way or-tree and
emits a single `movl`; gcc does not merge it, but four independent loads and
three `or`s still beat an eight-deep dependent chain.

**The matching change to `store_le` was measured and thrown away.**  It is
the same idea -- four independent right shifts and four byte stores instead
of a loop that shifts the word down eight bits at a time -- it verified, and
it cost ChaCha20 and Salsa20 12%.  The reason is the asymmetry hidden in the
paragraph above: a *store* loop writes to consecutive addresses with no
dependency between iterations, so gcc, which does know `nbytes` is four after
interprocedural constant propagation even though it will not unroll against
it, was already vectorizing ChaCha20's sixteen-word keystream store into SSE.
Writing the stores out by hand gave the vectorizer a shape it did not
recognize and lost more than the straight-line code won.  The load loop had
no such escape hatch, because a serial dependency cannot be vectorized at
all.  Keeping the loads and reverting the stores is the whole of this change.

### Twenty-one is not a field element

The complete addition formulas of Renes, Costello and Batina are stated
against a field, so they say `fmul b3 t` where they mean twenty-one times
`t`, and `fadd x x` where they mean twice `x`.  `Spec.K256` keeps the
published listings verbatim, which is the right thing for a specification
and the wrong thing for the code underneath it.  Taken literally,
`fmul b3 t` is a five-by-five schoolbook -- twenty-five word
multiplications and a carry pass one width up -- to multiply by a number
that fits in five bits, and the `8x` in the doubling is three carry
passes.

`Hacl.K256.Field52.fsmall` multiplies every limb by a small constant and
runs one carry pass: five word multiplications instead of twenty-five.  It
works because a limb is under `2^53` and the constants the formulas use
are at most thirty-two, so the product still fits in a word, and because
`carry_chain` is parameterised by the bound it is entering with rather
than hard-wired to one operation.  The bound is stated once at the largest
-- for every `n <= 32` at once -- rather than one shape per constant: the
pass that follows is the same either way and the slack costs nothing.

Four lemmas in `Spec.K256.Field52` do the whole translation between what
the formulas say and what the code does:

```fstar
let two_x   (x: K.felem) : Lemma (K.fadd x x == (2 * x) % prime) = ()
let three_x (x: K.felem) : Lemma (K.fadd (K.fadd x x) x == (3 * x) % prime)
  = Math.lemma_mod_add_distr x (x + x) prime
```

and two more for `8x` and for `b3`.  `fsmall` is in place on a single
array, which is what every one of the seven call sites wants and which
sidesteps the aliasing that `fsmall a2 a2 21` would otherwise force the
separation logic to argue about.  The `b3` constant table and the second
scratch element both became dead and are gone.

It is worth 1.15x to 1.24x on every secp256k1 operation under gcc and
1.07x to 1.13x under clang.  What is left of the secp256k1 gap is
algorithmic: HACL\*'s variable-base multiplication and its verification
use the GLV endomorphism and Shamir's trick, which this repository
declines for the reason given in `Hacl.K256.PointMulD`.

Six experiments were run at the C level before any of this was written in
Pulse, and three of them were worth exactly nothing, which is the more
useful half of the result.  gcc already CSEs `fmul(out, a, a)` down to the
fifteen distinct products, so a hand-written symmetric squaring buys
nothing and `fsqr` can go on being `fcopy` then `fmul`.  It already
unrolls the carry chain.  It already eliminates the `fcopy` churn around
aliased calls.  A full lazy-reduction rewrite -- dropping the carry pass
from `fadd` and `fsub` and reducing explicitly, which is what HACL\* does
-- measured six per cent on top of this, and was not worth the proof
cost.  The rule that falls out: only shapes the compiler *cannot* fix are
worth fixing by hand, and a twenty-five-multiplication product where a
five-multiplication one would do is such a shape.  Straight-lining `fadd`
and `fsub`, which were loops over the five limbs, is the other such shape
and is worth another three per cent.

### A bit string is a number

ML-KEM's `ByteEncode_d` packs 256 coefficients of `d` bits each into `32 d`
bytes, and `ByteDecode_d` unpacks them.  FIPS 203 states both of them one
bit at a time: bit `j` of the output is bit `j mod d` of coefficient
`j div d`.  `Spec.MLKEM.Encode` follows the standard, and the
implementation used to follow the specification, which means it computed a
division and a remainder by `d` for every bit it moved.  `d` is a
parameter rather than a constant, so those were real divisions --- three
thousand of them to encode one twelve-bit key polynomial.

gcc had been hiding how much that cost.  Its interprocedural constant
propagation would clone the encoder on `d`, which turns each division into
a multiply and a shift, and when the translation unit grew past the clone
budget the clone went away.  Bisecting the resulting slowdown with
`__attribute__((noclone))`, one candidate function at a time, showed the
encoder was the whole of it.

The fix is not to make a division cheaper but to notice that there is no
division in the problem.  Packing 256 `d`-bit values least significant
first is exactly writing down the integer

    N = sum_j f_j 2^(d j)

and reading a byte string least significant first is exactly
`Hacl.Spec.Bytes.le_nat`.  Both coders are the identity on one `256 d`-bit
number.  Once that is said, the implementation is free to move bits in and
out of `N` in whatever chunks suit the machine, because any two ways of
chopping up the same number agree.

So both are a sixty-four bit shift register.  The encoder holds the bits
packed so far and not yet written, pushes each coefficient in at the top,
and writes a byte off the bottom whenever eight have accumulated:

    acc += (f[i] & mask_d) << nb;  nb += d;
    while (nb >= 8) { out[o++] = acc;  acc >>= 8;  nb -= 8; }

The decoder runs the same register backwards, pulling a byte in whenever
fewer than `d` bits are left.  There is no division anywhere, and the
loops are the ones a C programmer would have written.

Written that way, though, the register carries from one coefficient to
the next across all 256, and the compiler cannot unroll anything.  Eight
coefficients of `d` bits are exactly `d` bytes, so the register is empty
at every multiple of eight: both coders run 32 groups (`enc_group`,
`dec_group`), each starting from an empty register at byte `d g`, and `d`
is monomorphized from `Codec` down.  With a constant `d` and eight steps
per group the compilers emit straight-line shifts and masks, and the
coders are 2--7x faster (Part 80).  Each group is its own function, taking
`i0` and `o0` with only `d i0 == 8 o0`: with the group index's products
`8 g` and `g d` in scope, the encoder's unchanged shift timed out.

`Spec.MLKEM.Pack` is the module that makes this legal.  It is pure
arithmetic --- it mentions neither `q` nor the NTT nor any parameter set
--- and says that `enc_num`'s bits are `coeff_bit`'s, that its bytes are
`byte_encode`'s, and that `bits_val` is a window of `le_nat`.  Two
decisions in it are worth copying elsewhere:

*The register is narrow, so use arithmetic rather than bits.*  It is never
wider than `8 + d <= 20` bits.  That makes each step's two operands
provably disjoint and their sum provably within range, so the bits can be
combined with `add_mod` instead of `logor`.  The generated code is
identical --- the compiler sees the same instruction either way --- and
the proof needs no bitwise reasoning at all, which is the part that is
expensive to automate.

*Mask rather than assume.*  `enc_num` takes each coefficient modulo `2^d`
rather than requiring the caller to have reduced it.  This costs one `AND`
per coefficient and removes a precondition from every caller, and it is
sound precisely because `coeff_bit` never reads above bit `d` either, so
the two agree on inputs that are not reduced as well as on inputs that
are.

Measured on ML-KEM-768, in microseconds:

| | gcc before | gcc after | | clang before | clang after | |
| --- | --- | --- | --- | --- | --- | --- |
| keypair | 116.8 | 98.1 | 1.19x | 192.1 | 95.4 | **2.01x** |
| encapsulate | 154.2 | 105.5 | **1.46x** | 171.6 | 124.7 | 1.38x |
| decapsulate | 199.5 | 137.0 | **1.46x** | 233.8 | 172.7 | 1.35x |

Decapsulation gains from the *encoder* as much as from the decoder,
because the Fujisaki-Okamoto transform re-encrypts in order to check.  The
clang key generation column is the one to dwell on: clang never cloned
anything, so it had been paying every division in full, and key generation
encodes two complete twelve-bit vectors.

### Measuring on a shared machine

A change confined to MD5 once appeared to cost BLAKE2b 62% and Ed25519 75%.
It did not.  Every text and data symbol in the fast and the slow binary was
at an identical address and every function was identical in size, so there
was no layout difference to blame; the slowness followed the *file*, and
deleting and rewriting it -- same name, same bytes -- made it go away.  The
same two byte-identical binaries were then 65% slower on one idle core than
on another idle core, and 20 minutes later that core was fast again.  This
box is a shared, dual-socket, 256-thread machine whose cores report clocks
anywhere between 2.0 and 3.3 GHz, and an individual core can be most of a
factor of two slow for tens of minutes for reasons invisible from inside the
container.

Chasing that as a code-layout problem would have been a long way to a wrong
answer, so the harness reports a **canary**: a fixed 200-million-iteration
serially dependent integer loop, run once before the suite and once after,
whose time is a direct reading of the core's clock and of whatever else is
competing for it.  It is emitted as an ordinary CSV row, with the before/after
ratio alongside, and the comparison script discards any run whose canary is
more than 2% above the best canary seen anywhere in the comparison -- such a
run measured a different machine, not a different library.  A/B runs are
interleaved A-B-B-A within a single window at two link-time code offsets, so
both sides see the same conditions and a residual layout sensitivity would
show up as disagreement between the offsets rather than as a result.

The general rule: a performance difference that is **large, localized in a
subsystem the change did not touch, and not accompanied by any difference in
the generated code** is a measurement artifact until proven otherwise, and
the cheapest proof is to diff `nm -S` output before reaching for a
microarchitectural explanation.

### Building the reference honestly

The reference numbers are only worth what the reference build is worth, and
HACL\*'s build has one trap that is silent in both directions.  `./configure`
must be run **with no arguments**: given `--enable-vale --enable-inline-asm`
it prints its help text and leaves `config.h` and `Makefile.config` empty,
after which everything still compiles and links, and `libevercrypt.a` simply
contains no assembly.  Worse, the objects from such a run are not rebuilt by a
later, correct `configure`, because their sources have not changed -- so a
tree that has ever been configured wrongly keeps producing a crippled library
until the objects are deleted.

The symptom is not a build failure but a plausible-looking number.  A library
built that way reports every CPU feature absent, which quietly costs the
reference its SHA-EXT, its AES-NI and its ADX; AES-GCM at 256 KiB drops from
71 microseconds to several hundred, and hacl-pulse appears to win a comparison
it loses by 4.5x.  The check is one line -- call
`EverCrypt_AutoConfig2_init()` and print `EverCrypt_AutoConfig2_has_shaext()`
and its siblings -- and it is worth running every time the reference tree is
rebuilt.

### ML-KEM, with no HACL\* to compare against

HACL\* has no ML-KEM, so the table below is absolute rather than relative,
measured the same way as the rest of this section, as gcc / clang.  Since
Part 86 each operation cycles through 64 seeds (and decapsulation through
the 64 matching ciphertexts) rather than repeating one, because the matrix
sampler's rejections make the time depend on the seed and a repeated seed
lets the branch predictor learn them:

| operation | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |
| --- | ---: | ---: | ---: |
| keypair | 15 us / 12 us | 22 us / 19 us | 33 us / 27 us |
| encapsulate | 17 us / 14 us | 26 us / 22 us | 36 us / 30 us |
| decapsulate | 21 us / 17 us | 31 us / 26 us | 42 us / 36 us |
| keypair | 54 us / 41 us | 92 us / 70 us | 145 us / 107 us |

These rows come from the same `bench.c` as everything else, guarded by
`BS_HAVE_MLKEM` because there is no HACL\* side to compile them against, and
the table is printed by `bench/mkkem.py` rather than typed.  So is the
ML-DSA table that follows it in the README; the comparison of ML-DSA
against other implementations is in the next section.

Decapsulation costs more than encapsulation everywhere because it *is*
encapsulation, plus a decryption: the Fujisaki-Okamoto transform
re-encrypts in order to check.  The numbers are a few times what a
hand-optimised reference implementation of Kyber gets on the same class of
machine.  The transform is no longer where the time goes: since Part 68
it is in-place butterflies whose inner loop has a constant trip count and
multiplies by the roots with Shoup's trick in sixteen and thirty-two bits,
which compilers vectorise, and the forward and inverse NTT together fell
from 42% of the instructions of an ML-KEM-768 run to 11%.  What is left
is mostly Keccak: the rejection sampler that expands the public matrix
(SHAKE128, one lane at a time) is now 39% and SHAKE256 15%, then the
base-case products (11% before the accumulating dot product of Part 79)
and the binomial sampler.

These numbers used to be half again as large, and the reason they are not
is *A bit string is a number* below.  There was a specialisation gap here
of exactly the kind the note below this table is about: `make
clones-available` said gcc would clone ML-KEM's polynomial encoder on the
bit width it is passed but that the interprocedural budget was spent, and
raising the budget was worth 1.32x on encapsulation.  That turned out to
be the compiler papering over a bit-serial coder, and the fix was to
rewrite the coder rather than to recover the clone.  Nothing in
`clones-available` is worth anything measurable on ML-KEM now.

The coder had also been specialised by hand, with `[@@monomorphize]` on
the bit width `d` threaded through `Hacl.Impl.MLKEM.{Encode,Codec}`, and
that annotation outlived its reason.  Once the shift-register coder
landed the specialisation was measured against its absence, on both
compilers, over all three parameter sets and all three operations: every
pair agrees to within one percent, which on this machine is noise, while
the annotation costs five hundred and twenty-six lines of C.  It has been
removed.  The remaining `[@@monomorphize]` annotations in ML-KEM -- on
the rank `k`, the noise parameters `eta1`/`eta2` and the compression
widths `du`/`dv` at the KPKE and KEM level -- are the ones that pay, and
they are the ones measured at 1.31x on encapsulation above.  The lesson
is the same one the clone survey teaches, applied to our own hand: a
specialisation is justified by a measurement, not by the fact that
something downstream of it used to be slow.

Part 80 put the annotation back, and the measurement is what justifies
it: once the coders run in groups of eight, a constant `d` lets each group
unroll, and the specialised coders are 2--7x faster than the generic ones.
Monomorphizing `d` without the grouping changes almost nothing, which is
what the earlier measurement saw.  Compression and decompression are
specialised along with the coders: no change under gcc, while clang's
`Compress_10` goes from 416 to 171 cycles, its vectoriser needing the
shift to be a constant.

### ML-DSA, against other implementations

HACL\* has no ML-DSA either, so it is measured against the ML-DSA
implementations people deploy: the pq-crystals reference C (`ref/`) and its
AVX2 build (`avx2/`), mldsa-native with its AVX2 arithmetic and Keccak
backends, AWS-LC (which imports mldsa-native with the arithmetic backend
only), OpenSSL 3.5's native ML-DSA, and Cryspen's libcrux in Rust with its
AVX2 backend.  The harness is the "others" one described below, with its
checks: every contender's public key must equal hacl-pulse's from the same
32-byte seed, and its signatures hacl-pulse's `sign_deterministic` on the
same 64 messages, byte for byte -- except AWS-LC, whose EVP interface only
signs hedged, so its signatures are cross-verified instead.  Signing cycles
through those 64 messages, because the number of rejection-sampling
attempts, and so the time, depends on the message.  Printed by
`bench/mkmldsa.py`:

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

hacl-pulse is between 1.8x and 2.1x behind the fastest implementation
(mldsa-native, or pq-crystals' AVX2 build on signing), 1.2x--1.5x behind
AWS-LC under clang, and 1.6x--2.9x ahead of the pq-crystals reference and
further ahead of OpenSSL.  The previous table had it at 5.0x--5.7x;
what closed most of the distance was the four-way Keccak in `ExpandA`
(Part 82), `ExpandMask` (Part 84) and `ExpandS` (Part 85), and the AVX2
transforms (Part 83).  Since Part 86 hacl-pulse's key generation also
cycles through 64 seeds, like signing through its 64 messages, and the
other libraries' key generation through the same 64 seeds; a single
repeated seed let the branch predictor learn `ExpandS`'s rejections and
flattered every contender, hacl-pulse most.

### Against other libraries

The table above answers how the Pulse pipeline compares with HACL\*'s.  This
one answers what a user gives up, in speed, by choosing a verified library
extracted from Pulse over the fast libraries people actually deploy:

- **OpenSSL** 3.5.5, the system `libcrypto`, through EVP with every algorithm
  pre-fetched and every key loaded outside the timed loop;
- **AWS-LC** (`ffca127`, October 2026), whose x86-64 X25519 and Ed25519
  are s2n-bignum's formally verified assembly;
- **libsodium** 1.0.22-stable;
- **libjade** (release 2023.05-2), Jasmin implementations, several with
  machine-checked correctness proofs, shipped as assembly; each row uses
  the best variant the release has for this CPU;
- **Firedancer**'s `ballet` (`849c582`), the Solana validator's crypto,
  built with clang because its makefile rejects gcc 15.2;
- **dalek** (curve25519-dalek 4.1.3, ed25519-dalek 2.2, x25519-dalek
  2.0.1), Rust, LTO, `target-cpu=native`;
- for the ML-DSA rows only, **pq-crystals** dilithium (`d35ba3f`), `ref/` and
  `avx2/`; **mldsa-native** (`6daba60`), with its x86-64 arithmetic and
  Keccak backends; and **libcrux-ml-dsa** 0.0.11, Rust, LTO, `simd256`.
  These have their own table in
  [ML-DSA, against other implementations](#ml-dsa-against-other-implementations)
  and no column here.

hacl-pulse appears twice, built by gcc 15.2 and by clang 21.1; the other C
libraries are built by gcc (Firedancer by clang).  Times are per operation,
fastest in bold, and the last column is the better hacl-pulse build divided
by the fastest other library.  Same machine and method as above
(three interleaved rounds, keeping only runs whose canary is within 6% of
the best one: this virtual machine's canary wanders by about 8%, and the
default 2% cut leaves some contenders with no run at all; on this run 5%
left none of hacl-pulse's gcc build).  The harness is
[`bench/others.sh`](../bench/others.sh), and the table is printed by
`bench/mkothers.py`.

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
| P-256 ECDH | -- | 149 us | 111 us | 50 us | **48 us** | -- | -- | -- | -- | 2.31x |
| Ed25519 verify | -- | 108 us | 126 us | 113 us | 39 us | 51 us | -- | 44 us | **37 us** | 2.91x |
| RSA-PSS-2048 verify | -- | 51 us | 59 us | 22 us | **17 us** | -- | -- | -- | -- | 2.99x |
| P-256 ECDSA verify | -- | 211 us | 162 us | 67 us | **54 us** | -- | -- | 62 us | -- | 3.00x |
| P-256 ECDSA sign | -- | 75 us | 61 us | 24 us | **16 us** | -- | -- | -- | -- | 3.85x |
| Ed25519 sign | -- | 34 us | 40 us | 41 us | 8.9 us | 16 us | -- | **8.7 us** | 18 us | 3.87x |

A dash means the library does not offer the operation through the API used:
AWS-LC has BLAKE2b only with a 256-bit output and no BLAKE2s; libsodium has no
MD5, SHA-1 or SHA-3 and only AES-256-GCM; Firedancer's P-256 is verify-only
and it has no SHA-3, BLAKE2 or ChaCha20 AEAD; libjade's Kyber is the round-3
scheme, not ML-KEM, and it has no ML-DSA; dalek is Curve25519 only.

**What makes the comparison fair.**  Each binary links hacl-pulse as well as
its contender, and before any row is timed the contender's output is
checked against hacl-pulse's on the same keys, message and nonce -- byte
for byte where the operation is deterministic, by cross-verification where
it is not -- and the binary aborts on a mismatch, so no cell can be measuring
a different key size, output length or variant from its label.  Bulk rows
are one-shot calls on 256 KiB.  P-256 ECDH here is a variable-base scalar
multiplication (the main table's is the fixed-base initiator); ECDSA rows
sign and verify SHA-256 of a 64-byte message.  RSA uses n, e and d only, no
CRT, for every library, because hacl-pulse's RSA has no CRT; hacl-pulse
also takes the key as bytes on every call, while OpenSSL and AWS-LC load it
once.  Ed25519 signs with a pre-expanded key everywhere except Firedancer,
whose API takes the seed and hashes it on every call.  OpenSSL's and
AWS-LC's ECDSA and ML-KEM, and AWS-LC's ML-DSA signing, draw from their
DRBGs where hacl-pulse takes explicit nonces and seeds (for ML-KEM, a new
one on every call).

**Reading it.**  hacl-pulse is the fastest library here for three rows.
secp256k1 is not a real contest: OpenSSL and AWS-LC run it through generic
curve code, and the library one would actually use, Bitcoin Core's
libsecp256k1, is not in the comparison.  The others are BLAKE2s and, built
by clang, Poly1305, each narrowly.  On the previous machine it also led on
ChaCha20, Salsa20, ChaCha20-Poly1305 and NaCl secretbox with its AVX-512F
backends (`bench/REPORT.md` Parts 60 and 61); this processor has no
AVX-512, and on AVX2 those rows are 1.05x--1.28x behind OpenSSL, AWS-LC and
libjade.  Elsewhere the gaps fall into two groups.

- *Within 1.4x* -- Salsa20, secretbox, SHA-1, SHA-256 and HMAC-SHA-256,
  both AES-GCMs, BLAKE2b, ChaCha20, SHA3-256, ChaCha20-Poly1305, MD5,
  SHAKE128, ML-DSA-65, SHA-512 and HMAC-SHA-512, and X25519.  Every one of
  these is a primitive where hacl-pulse already uses
  the same instruction-set extensions as the leader (AVX2, SHA-NI, AES-NI
  and PCLMUL, BMI2), and the remaining distance is hand-scheduled
  assembly: OpenSSL's and AWS-LC's SHA-1, SHA-256, ChaCha20 and Keccak,
  Firedancer's GCM and SHA-512, libjade's Salsa20, s2n-bignum's X25519.
  SHA-1 was at 6.2x and SHA-512 at 1.9x--2.0x until Part 87 gave them a
  SHA-extensions block and an AVX2 message schedule.
- *1.4x--4x* -- ML-KEM, RSA, FFDHE, P-256 and Ed25519.
  ML-KEM-768, at 1.4x--1.5x of AWS-LC, already runs its matrix sampler and
  noise PRF four streams at a time and its transforms on AVX2; what is
  left is AWS-LC's hand-written x86-64 backend.  ML-DSA-65 was at 3.7x--3.8x
  of AWS-LC in the previous table and is now at 1.3x--1.4x (1.8x--2.1x of
  mldsa-native, which has no column here), mostly from the four-way Keccak
  and the AVX2 transforms (`bench/REPORT.md` Parts 82--85).  Since Part 86
  hacl-pulse's ML-KEM key generation and encapsulation take a fresh seed
  per call, as OpenSSL's and AWS-LC's always did; every library's ML-DSA
  key generation cycles through 64 seeds, and decapsulation, signing and
  verification through 64 inputs, so no row reflects a branch predictor
  that has learnt one input's rejections.
  RSA and FFDHE are portable 64-bit Montgomery multiplication against
  OpenSSL's MULX/ADX assembly, at 1.7x.  P-256
  is at 2.3x--3.9x against `nistz256`'s assembly field, its 150 KB of
  generator multiples and its double-scalar verification.  Ed25519, at
  2.9x--3.9x, is portable radix-2^51 C against s2n-bignum's assembly.

Verification does not by itself put a library at the back of a row:
libjade and the s2n-bignum routines in AWS-LC and Firedancer are verified
too, and they lead or nearly lead theirs.  The gaps are mostly backends that
have not been written yet, and this table, rather than the HACL\* one, is
the better guide to which matter most: P-256 and RSA's multiplication, and
Ed25519's field.

## Proof engineering notes

Non-obvious things that cost time here, recorded so they cost less next time:

* **Nonlinear arithmetic is off.**  `n * m >= 0`, `(j+1)*b == j*b + b` and
  `j*b <= n*b` are all *not* automatic, and the failure is usually reported as
  "the SMT query timed out" rather than as an unproved goal.  Reach for
  `FStar.Math.Lemmas.{distributivity_add_left, lemma_mult_le_right,
  multiple_division_lemma, multiple_modulo_lemma, euclidean_division_definition}`
  before reaching for `--z3rlimit`.
* **Keep carry-chain arithmetic out of the Pulse context.**  Under
  `--smtencoding.nl_arith_repr wrapped`, a linear equality over a dozen
  `S64.v` values and a `u * p`-sized numeral hung Z3 for minutes far past the
  rlimit (`Hacl.P384.Field64`).  The same fact as a pure lemma over `nat`s,
  called with the `S64.v`s and every carry named, proves in milliseconds.
  Likewise, a postcondition such as `fev vo' == P.fadd (fev va) (fev vb)`
  goes through instantly when restated with `assert (pure ...)` right after
  the bridge lemma, and hangs otherwise; and a precondition like
  `pow2 384 * rinv % p == 1` belongs inside the bridge lemma (by
  `assert_norm`), not at the call site.
* **A product or a quotient of two variables under a quantifier poisons the
  whole query.**  It does not merely fail to prove its own conjunct: every
  other fact in the same query becomes unprovable too, including goals as
  trivial as `i == j` from `i < j + 1 /\ ~(i < j)`.  The symptom is a query
  that runs for hours without tripping the rlimit and then blames something
  absurd.  Both halves of Frodo's message packing hit it --- encoding named
  the cell with two loop indices, so the invariant carried `i * nbar` under a
  `forall`; decoding mentioned `Spec.Frodo.key_decode`, whose `Seq.init_ghost`
  body divides the flat index by `bits p`, so the `Seq.index` trigger put a
  division by a variable there instead.  Encoding took over four hours and
  decoding never finished at all.  The cure is to say only that the flat
  prefix written so far agrees with the specification sequence, keeping the
  write position in a real mutable variable so the prefix bound stays linear,
  and to supply the specification's value at one *concrete* index with a
  lemma, where the product is harmless.  Where the specification function
  itself is the problem, verify against an `[@@"opaque_to_smt"]` copy of it
  and reconcile the two once, at the end.  Encoding now takes ninety-nine
  seconds.  To find the culprit, reproduce the failing goal in a scratch file
  and replace the suspect specification function with an `assume val`: if the
  goal becomes instant, that term is the poison.
* **`--admit_except` admits everything when the name does not match.**  The
  run then returns success in seconds and verifies nothing.  Never read an
  `--admit_except` pass without a baseline that fails.
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
* **Give a lemma the offset the caller is looking at.**  E-matching is
  syntactic: a hypothesis triggered on `Seq.index (Seq.append pre s)
  (Seq.length pre + k)` will not fire on a goal about
  `Seq.index (Seq.append pre s) (base + k)`, however obviously the two indices
  are equal.  `Spec.SHA2.Lemmas.append_index_at` takes the absolute offset as
  its own argument for exactly this reason.
* **A `while` invariant must carry every resource the body touches, not just
  the ones it changes.**  Leaving one out (or leaving it out of an explicit
  `if ... ensures`) fails with "leftover resources" at the end of the
  function, far from the cause.
* **A `decreases` expression has to be a `nat` at every iteration.**  A loop
  that advances by a fixed stride past a limit cannot measure `limit - i`;
  measure the iteration count instead.  The symptom is a timeout on
  `... << meas`, which looks like a crowding problem and is not.
* **Split, do not raise the rlimit.**  Every "the SMT query timed out" in
  `update_impl` was on a goal like `nb + 1 <= |seen| + |data|`.  Moving the
  block-full case out into `update_full` made all of them go away at once; no
  amount of rlimit would have.
* **Extract one whole program, not sixteen.**  Custard emits everything an
  entry point reaches, so a per-family unit carried its own copy of the
  secret-integer layer and of SHA-2, and two of them could not be linked into
  one binary at all.  Collapsing the sixteen roots into one `code/Hacl.fst`
  that names every entry module halved the generated code -- 25,200 lines to
  11,200 -- and made the library linkable with itself.  The only cost is that
  `--custard_entry` moved from a per-unit variable to one list, which is a
  better place for it: that list is the public API.
* **Mark big `Seq.init` definitions `opaque_to_smt`.**  A spec function that
  builds a 25-element sequence is, unfolded, 25 copies of its body in every
  query that mentions it.  Make it opaque and give it an index lemma that
  `reveal_opaque`s it; that one change is what made Keccak provable.
* **A trailing `Seq.lemma_eq_elim` does not discharge a Pulse `ensures`.**  The
  idiom that works is to name the witness and assert the goal:
  `with v. assert (A.pts_to x v); assert (pure (reveal v \`Seq.equal\` rhs));`.
  More generally, a lemma call whose conclusion the postcondition needs must be
  followed by an `assert (pure ...)` restating that conclusion.
* **`let ... in` is a syntax error inside a Pulse block**, and so is
  `let ghost x = ...`.  A lemma that wants a local definition has to be hoisted
  to module level — which is why `squeeze_bytes_eq` and `squeeze_range_eq` live
  in `Spec.SHA3` rather than next to the loop that uses them.
* **Bind the initial value of a stack array first.**
  `let mut a = [| S8.classify 0uy; 200sz |]` gives the array the *refined*
  element type `x:S8.t{S8.v x == 0}`, which then fails to match
  `A.array S8.t` with an unreadable error.  `let z8 = S8.classify 0uy;`
  first, then `[| z8; 200sz |]`.
* **Do not multiply in a loop guard.**  `SZ.mul i r` carries a
  `SZ.fits (v i * v r)` obligation that is not provable from the invariant.
  Carry the product as its own variable, advanced by `r` each iteration and
  never past the limit, and recover the index with `SZ.div` where it is needed.
  For the same reason, hoist `SZ.div`/`SZ.rem` into real `let`s: even
  `SZ.v b / SZ.v r >= 0` times out as an inline argument in a large context.
* **Shape the lemma like the loop, not like the spec.**  When the goal indexes
  at `base + i*r + k` and the hypothesis at `Seq.index msg (base + k)`,
  no amount of rewriting will make E-matching bridge the two.  What works is a
  spec lemma that takes the whole run -- the number of blocks, the block index
  and the base offset -- as arguments and does the instantiation in a small
  context, ending in the caller's exact syntactic shape
  (`Spec.SHA3.Streaming.block_eq_slice_at`).
* **Hand out a window of an array with `Hacl.Impl.Sub`, not by hand.**
  `Sub.sub a i j` gives back an array over `a[i..j)` carrying a plain `pts_to`
  plus a `rest` token for everything outside; `Sub.unsub` trades the two back.
  Two details make it usable: `sub` has to re-export Pulse's
  `ensures rewrites_to b (A.gsub a i j)`, because the resource matcher is
  syntactic and a refinement `b == gsub a i j` is not enough on its own; and
  `unsub` only returns the contents *pointwise*, so the common read-only case
  gets its own `Sub.unsub_id`, which does the pointwise-to-`Seq.equal` step
  once inside the module instead of in every caller's (huge) context.  Omitting
  that shows up as a resource-matching timeout, not as a clean failure.
* **A callee's `ensures` is all you get.**  `squeeze_impl` does not promise
  anything about the length of the scratch buffers it was handed, so a caller
  whose own postcondition mentions them has to re-establish it -- one
  `S.pts_to_len` at each end of the function, since a slice's length never
  changes.
* **Give a branch a written-down postcondition.**  Pulse will check both arms
  of an `if` against an annotated goal, but it will not invent the join: an
  `if` whose two arms leave different values in the same slice fails with
  "cannot prove `match ... with`".  Lifting the branch into its own function
  whose `ensures` is itself an `if` -- `read_block_of` -- makes it go through.
  For branches that only choose a *value*, use an ordinary F\* function
  (`step_of`, `final_off`, `koff_sz`) and keep the Pulse code straight-line.
* **A `while` needs a `decreases`.**  Without one the loop is `stt_div`, and
  the error surfaces far away as "cannot compose computations in this divergent
  block", naming the effect rather than the missing clause.
* **A `decreases` measure must stay non-negative *after* the body.**  A fill
  loop running `while (nb < d) { nb += 8; }` has the obvious measure `d - nb`,
  which is positive on entry to the body and negative on the way out of it.
  `<<` on `int` is well-founded only on the non-negative part, so this fails
  at the loop's last iteration with a `_ << meas` goal that looks arithmetic
  and is not.  `d + 8 - nb`, with `nb < d + 8` carried in the invariant, is
  the same measure shifted into range.
* **Lead a hard linear goal up a staircase.**  After a loop on `i`, proving
  `SZ.v i == 256` from `~(SZ.v i < 256)` and `SZ.v i <= 256` timed out at
  rlimit 600 --- not because it is hard, but because the loop invariant
  leaves a quantified frame condition and a `pow2`-laden equation in scope
  for Z3 to flail at.  Writing `assert (256 <= SZ.v i); assert (SZ.v i <=
  256); assert (SZ.v i == 256)` makes all three discharge instantly at rlimit
  40.  Each `assert` is its own query with its own, much smaller, set of
  relevant facts.
* **Hoist each nonlinear step into a lemma whose arguments are the machine
  values.**  Inside a Pulse loop body the context is enormous; `d * (i + 1) <=
  256 * d` asked there can cost the whole rlimit, and asked in a four-line
  top-level lemma it costs nothing.  `Spec.MLKEM.Pack.enc_room` and `dec_room`
  exist only for this.  The rule of thumb that fell out: if a goal mentions a
  product of two variables, it does not belong in Pulse code.
* **`by` is a reserved word.**  `let by = ...` is a syntax error reported at
  the column of the `=`, with no mention of the name.
* **`--split_queries` is not a pragma.**  When a four-conjunct postcondition
  times out, the lever available is `--fuel`/`--ifuel` and splitting the
  function, not splitting the query.
* **Guard a lemma call, do not case-split the caller.**  `nlast - koff` is not
  a natural number when the last block is the key block.  Wrapping the lemma in
  another whose conclusion is an implication (`msg_blocks_bound_opt`) keeps the
  Pulse code free of ghost branches.

* **Keep a hypothesis set small, everywhere.**  This is the single most
  expensive lesson in the repository, and it recurred at three different
  levels.  In `Spec.SHA2.Lemmas`, `tail_generic` timed out not because any
  one step was hard but because its ten-conjunct `requires` was in scope for
  every sub-query; extracting the last step into `slices_of_bytes`, with the
  three hypotheses it actually needs, fixed it instantly.  In
  `Spec.Poly1305.Field`, the multiply-and-carry lemma stated in one piece ran
  for over twenty minutes without an answer, and split into a congruence
  half and a bounds half -- neither of which mentions what the other is
  about -- the whole module verifies in seventy-seven seconds.  In
  `Hacl.Poly1305.Field`, the twenty-five products and the carry chain in one
  Pulse `fn` did not finish, and split in two, with a scratch slice between
  them, each half takes seconds.  Prefer many small lemmas to one big one,
  always.
* **Name a postcondition that mentions arithmetic.**  A contract written out
  in full is in scope for every query in the caller.  `fmul`'s
  postcondition, written as `feval vh' % prime == ...`, made the solver
  unfold five `as_nat5` limbs and `pow2 130` in a query that also carried the
  heap, and timed out; named `fmul_post`, the match between the lemma's
  conclusion and the function's contract is syntactic and the query is
  trivial.  The same applies to `is_product`, and it is why `chain` is a
  plain `let` and not an `unfold`.
* **A Pulse `fn` must not end with a lemma call.**  The function's `ensures`
  is checked at the last statement, and a trailing lemma's conclusion is not
  yet in scope there.  The failure is not a clean "could not prove" either --
  the solver flails and reports a timeout on a goal that is syntactically one
  of its own hypotheses.  Any statement after the lemma will do; `fmul` ends
  with a redundant `S.pts_to_len`.
* **`canon_semiring` has three sharp edges.**  It does not scale: the
  twenty-five-term Poly1305 identity does not finish, though each of the five
  per-limb identities it decomposes into closes in under a second.  It does
  not unfold: an `unfold` definition still appears in the goal the tactic
  receives, and an application it does not recognise is treated as an opaque
  atom, whereupon the tactic gives up quietly and hands the whole goal to Z3.
  Norm the definitions away first.  And it will not distribute a subtraction
  that sits inside a product, so `(b^5 - 5) * c` stays stuck; state the
  lemmas additively and do the one subtraction by hand.
* **`assert_norm` the small powers.**  At `--fuel 0` the solver cannot see
  that twenty-one times `2^53` is under `2^58` from `pow2_plus 5 53` alone --
  it also has to be told that `pow2 5` is thirty-two.
* **A type-class value method used to cost a startup pass.**  `word.zero` and
  `word.nbytes` specialize to a parameterless definition per instance, and one
  global naming another is not a constant expression in C, so the whole chain
  was assigned in a `custard_init_globals` that every `main` had to call
  first — and a test that forgot got a BLAKE2 block length of zero and a
  division by zero.  Custard now folds a constant global into the initializer
  of the global that reads it, so the library does not emit that function at
  all.
  Recorded because the failure mode was so quiet.
* **`Seq.index` does not reduce through `Seq.seq_of_list`.**  The sequence
  type is abstract, so `assert_norm (Seq.index (seq_of_list l) i == ...)`
  fails.  Bridge with `Seq.lemma_seq_of_list_index`; `List.Tot.index` on a
  literal spine does reduce.
* **A bounded `forall` over 160 ground facts is not an SMT job.**  At
  twenty-five entries (Keccak's rho offsets) a case split at `--z3rlimit 200
  --fuel 1 --ifuel 1` still closes.  At a hundred and sixty (BLAKE2's message
  schedule) it does not, at any budget.  What works is to make the check
  *computational*: a recursive `bool` over `List.Tot.index`, one
  `assert_norm` that it is `true` -- a normalizer job, not a solver one --
  and a recursive lemma that unfolds it exactly once per step to produce the
  quantified form.  Thirteen seconds.  `FStar.SizeT.v` is `Pure nat` and not
  `GTot`, which is what lets the check be a `bool` at all.
* **Put a list's length in its type.**  `let l : m: list t {List.Tot.length m
  == 160} = assert_norm (...); l0` costs one `assert_norm` once, instead of
  one at every use.
* **Custard eta-renames trivial wrappers.**  A Pulse `fn` whose body is just
  a call to another `fn` extracts with its parameters named `eta`, `eta1`,
  ...  Inline the body instead; that is why `Hacl.Chacha20.decrypt`
  repeats `encrypt`'s body rather than calling it.

* **Spell powers of two out as decimal literals.**  An identity about limbs
  that mentions `pow2 26`, `pow2 12` and `pow2 64` looks nonlinear and stays
  stuck; four `assert_norm (pow2 26 == 67108864)` lines turn it into linear
  arithmetic that Z3 closes with no further help.  Used for both the block
  load and the tag repack.
* **Trivia does not always close inside a Pulse verification condition.**
  `assert (as_nat5 x 0 0 0 0 == x)` is immediate on its own and fails inside a
  separation-logic query, where the context is a few hundred hypotheses.  Give
  it a name at the top level and call it.
* **Keep divisions out of separation-logic queries.**  Poly1305's `block_at`
  unfolds to `(len + 15) / 16`; instantiating a lemma stated in terms of it,
  inside a loop body, times out at any budget.  Stated instead over `16 * i`
  and `len % 16`, with the division discharged once in a lemma that holds
  nothing else, the same proof is instant.
* **Where a lemma sits in a file can break an unrelated one.**  Inserting
  three lemmas in the middle of `Hacl.Spec.Bytes` made a later, untouched
  lemma time out; appending them at the end fixed it.  The solver sees earlier
  definitions of the same module as ambient facts.
* **Pulse silently drops a pure statement in final position.**  A `fn` body,
  or a branch of an `if`, that ends with a lemma call simply does not make that
  call; the postcondition then fails with no indication why.  End such a body
  with `()`.  This is worth knowing before a large mechanical edit: removing a
  trailing statement from sixty-six functions left sixty-six silently broken
  proofs.
* **A Pulse `ensures` does not see the `requires`.**  Any refinement a
  postcondition needs in order to typecheck -- a length, a bound -- has to be
  restated as one of its own earlier conjuncts.
* **A Pulse `if` needs a written-down postcondition.**  Two branches that
  leave the heap in the same shape still do not join; make the `if` the last
  statement of a function whose `ensures` covers both cases, and let that
  `ensures` be an `if` too.
* **`repeati_g n f acc` does not identify `f` with an eta-expansion of it.**
  A specification that writes its step as a lambda and an implementation whose
  invariant names it are different arguments to the same fold, and only a
  pointwise-extensionality lemma proved by induction relates them.
* **Write folds over named step functions, never lambdas.**  Two lambdas that
  are not the same source occurrence are two distinct opaque constants to the
  solver, so an equation between two folds will not close no matter what
  fuel it is given.  Every fold in `Spec.Poly1305` goes through a named
  `pstep` or `bstep` for this reason alone.
* **A `while` loop with no `decreases` is `stt_div`, and a divergent block
  cannot be followed by a non-divergent one.**  The symptom is "cannot compose
  computations in this divergent block" pointing at the whole function, not at
  the loop.
* **A lemma call cannot be the last statement of a Pulse block.**  Its
  postcondition is added for the *continuation*, so if there is none, the
  function's own postcondition is checked without it.  End with an `assert`
  of what the lemma gave you.
* **Ghost implicits that only appear in a `pure` refinement are not
  inferred.**  An accumulator threaded through several calls has to be passed
  explicitly at every one of them; the error is "unexpected unresolved uvars",
  naming the application rather than the argument.
* **An annotated `if` must list every resource in scope, not just the ones it
  touches.**  The postcondition written on an `if` is the whole state after
  it, with no framing; omitting an untouched slice is reported as "leftover
  resources: did you forget to free these?" against the last statement of a
  branch.
* **An `if` with a postcondition is often worth deleting.**  Both BLAKE2
  branches of "does this update fill the buffer?" ended up as one lemma call
  once the lemma was generalized to allow the empty case, and the proof got
  faster as well as shorter.
* **Push index arithmetic out of Pulse and into pure lemmas.**  Three
  timeouts in a row -- a block offset inside a loop, the bounds of an
  overflowing update, the whole easy branch of `update` -- were fixed not by
  raising `z3rlimit` but by moving the reasoning into `Spec.Blake2.Streaming`
  as `pad_block_run`, `update_split` and `update_small`, where the solver sees
  arithmetic and nothing else.  A lemma stated in exactly the shape the call
  site needs is worth more than any budget.
* **A disjunction in a record field's refinement is a case split in every
  proof that mentions the record.**  Telling the type system that BLAKE2 has
  either ten rounds or twelve -- `nrounds: n: SZ.t { SZ.v n == 10 \/ SZ.v n
  == 12 }` -- is exactly the fact the unrolled round loop needs, and it took
  `mix_columns`, which does not care how many rounds there are, from twenty
  seconds to a timeout at three times the resource limit.  Behind an opaque
  predicate (`[@@"opaque_to_smt"] let nrounds_ok`) with the positivity the
  specifications actually use spelled out beside it, the hypothesis is an
  uninterpreted atom until the one function that wants it asks, and the
  module checks in twenty-five seconds.  The general rule: a refinement on a
  field is a hypothesis in *every* query about a value of that type, so it
  should be as close to atomic as the proofs that do not use it can bear.
* **`FStar.SizeT.fits` obligations do not follow from `< pow2 64`.**  A
  counter that a ghost sequence bounds needs a real `size_t` to descend from:
  passing the byte offset in as an argument, with `SZ.v ctr0 == n0 * block_len`
  as its specification, is easier than proving `fits` for every intermediate
  product.
* **A Pulse `fn` must not end with a pure or ghost statement.**  A trailing
  lemma call is silently dropped, and the fact it was meant to establish
  simply is not there; the error appears at the function's postcondition with
  no indication of the cause.  End with something stateful -- `S.pts_to_len
  st;` or `S.to_array scratch;` will do.  The same applies to each branch of
  an `if`: move the loop-counter update into the branches rather than leaving
  a lemma call last.
* **A `while` with no `decreases` has effect `stt_div`, and nothing after it
  composes.**  Make the measure a `nat` under the invariant: a loop that steps
  by sixteen past `n` needs `SZ.v n + 16 - SZ.v (!j)`, with `SZ.v vj <= SZ.v n
  + 16` carried in the invariant.
* **`opaque_to_smt` is a proof tool, not an optimization.**  Three separate
  blow-ups in `code/aes` were fixed by it: the 256-element `sbox_list`, the
  large bodies of `ginv_impl` and `sbox_impl`, and `key_expansion`, whose
  unfolding is a `Seq.init` with a division in the body, so that every
  `forall j < b` hypothesis spawned a fresh `ks_word (j/4)` term.  Pair each
  opaque definition with exactly one `*_index` lemma and nothing else can
  reach inside it.
* **Repeat the `requires` inside the `ensures`.**  A postcondition that
  mentions a specification function with a refined argument -- `gcm_encrypt`
  needs `msg_ok`, `blk` needs a bound -- is typechecked without the
  precondition in scope, and fails as "ill-typed term" at the `ensures`
  clause rather than anywhere useful.
* **When a proof is slow, take the reasoning out of the context.  Do not
  raise the rlimit.**  This is the same lesson as "keep a hypothesis set
  small", and optimizing `code/aes` produced four more instances of it in a
  row, each one sharper than the last.  Anchoring the Keccak indices; lifting
  the four-block composition out of the counter-mode loop into a pure
  `ctr4_step`; moving six vector shifts out of `mul_r_vec` into four helpers
  with tight specifications, which took the module from a two-and-a-half
  minute timeout to sixteen seconds; and splitting the four-way GHASH into
  `ghash_loop4_ni`, `ghash_start`, `step4_bounds` and `step1_bounds`, which
  took it from *not closing at `--z3rlimit 400`* to twenty-five seconds.
  Nothing about the mathematics changed in any of the four.  If a goal is
  trivial on its own and times out in place, the answer is never a bigger
  budget.
* **A shift count has to reach the intrinsic as a literal.**  Computing
  `64 - n` inside the Pulse function defeats it, so `full_shr` takes both `n`
  and `m` with a refinement `U32.v m == 64 - U32.v n` and lets the caller pass
  two constants.
* **Match the specification's syntax, not just its meaning, under a binder.**
  `Spec.GF128.Algebra.conv_comm` needs its reversed summand written
  `fun i -> pget b i && pget a (k - i)`, with the operands of `&&` in that
  order, because that is how `conv b a k` is written.  Swap them and the proof
  fails with every fact it needs in context: functions under a summation are
  opaque and the solver will not commute `&&` inside a lambda.
* **Do not guess where the time goes.**  Two predictions during the AES work
  were badly wrong in opposite directions -- a change forecast at 1.4x
  delivered 1.11x, and one forecast at 1.3x delivered 1.03x.  Reading the
  generated assembly, and stubbing a function out to difference the benchmark,
  were right every time.

* **Twelve straight-line writes are quadratic.**  A postcondition that
  reads every index of a buffer written by `n` consecutive `upd`s costs
  `O(n^2)` in the solver, and no `z3rlimit` rescues it -- `ComputeNonce`
  did not return in a quarter of an hour at twelve writes and takes ten
  seconds as a loop with a pointwise invariant.  Preferring a loop to
  straight-line code is usually a readability choice; past about four
  writes it is a feasibility one.
* **A `pure` conjunct in an invariant may not mix `seq` with `lseq`.**
  `reveal w == B.nat_to_be 12 n` where `w: Seq.seq t` sends F\* off to prove
  `l_True == (Seq.length s == 12)`, which takes about fifteen minutes to
  fail and reports nothing useful.  State the pointwise form in the
  invariant and do the extensionality afterwards.
* **Restrict the facts when a module has pointwise `SMTPat`s.**
  `Spec.HPKE`'s `catN_pointwise` lemmas fire on every `Seq.index` in scope;
  `--using_facts_from '* -Spec.HPKE +Spec.HPKE.xor_bytes'` took one
  `ComputeNonce` lemma from over fifteen minutes to fifty-four seconds.
  The filter is a prefix match, so `+Spec.HPKE.xor_bytes` readmits
  `xor_bytes_index` too.
* **`introduce forall ... with ...` is not free.**  In a query already
  carrying many `Seq.index` terms it was dramatically slower than an inner
  `aux` lemma passed to `Classical.forall_intro`.  Conversely, merely
  writing `module Classical = FStar.Classical` loads that module's axioms
  into every query in the file, which is enough to tip a marginal one.
* **Assert the lemma's conclusion after calling it.**  A pure lemma whose
  conclusion is exactly the Pulse `ensures` is often not enough on its own;
  restating it as `assert (pure ...)` immediately after the call splits one
  hopeless query into two cheap ones.
* **`--admit_except` admits the callers too.**  It admits the SMT of every
  other definition in the file, so a green run says only that the named
  definition is fine in isolation, not that anything downstream of it
  still typechecks.
* **Never `open` a large Pulse implementation module; wrap it.**  The cost
  of an `open` is not the definitions used but the whole module's
  elaboration context, and a module full of Pulse `fn`s is enormous.
  ML-KEM's K-PKE went from eight minutes to sixteen seconds by replacing
  four `open`s with four thin wrapper modules --- `Hacl.Impl.MLKEM.Poly`
  over `NTT`, `Sampler` over `Sample`, `Codec` over `Encode`, `Hash` over
  `Hacl.Hash.SHA3` --- each an `.fsti` with two or three `val`s and an
  `.fst` that forwards.  Giving the big module its own `.fsti` instead is
  the wrong fix, and an expensive one: it made `NTT`'s own implementation
  go from two and a half minutes to twenty-three.  The diagnosis is
  `--query_stats`: total Z3 time far below wall-clock time means the cost
  is elaboration, not solving.
* **Thread the offending term into the lemma.**  When the goal is
  `f a == f b` and `a`, `b` are expensive ghost terms --- an ML-KEM matrix
  seed under an `if`, say --- the congruence step alone can time out.
  Passing the sequence in as an extra lemma argument, so that the call
  site matches its hypotheses syntactically, and restating the surrounding
  `assert` in *exactly* the goal's syntax (`SZ.v vc / SZ.v k`, not
  `SZ.v ci` for a `ci` defined to be that) took one ML-KEM function from
  eight minutes of failure to forty-six seconds of success.

## Roadmap

Following `design/reimplementation.md` §9, the minimum viable subset is
complete: the hashes and their streaming layers, HMAC one-shot and
incremental, HKDF, ChaCha20-Poly1305, X25519, Ed25519, P-256, HMAC-DRBG with
an OS entropy shim, and AES-GCM.  secp256k1 sits beside P-256 on the
shared 256-bit Montgomery layer, with the low-S rule Bitcoin needs.  Past it, the generic bignum has its
arithmetic, its conversions, its Montgomery layer and its modular
exponentiation -- both ladders and Fermat inversion -- and on top of those
the five RFC 7919 finite-field Diffie-Hellman groups and PKCS#1 v2.2
RSA-PSS signing and verification.

The two legacy hashes are there too: SHA-1 one-shot, incremental and under
HMAC, and MD5 one-shot and incremental, which is everything HACL\* offers
for it.

AES-NI, the carry-less-multiply GHASH and the `AESKEYGENASSIST` key schedule
all sit under AES-GCM, and the Intel SHA extensions sit under SHA-256 and
SHA-224, each chosen at run time.

Beyond the subset, Salsa20 is there with HSalsa20 and XSalsa20 under it,
and so is the whole of the original NaCl interface: `crypto_secretbox`,
`crypto_box`, and the `beforenm`/`afternm` split for callers that talk to
the same peer more than once.

FrodoKEM closes the primitives HACL\* has: all four parameter sets, with
the public matrix streamed a row at a time rather than assembled.  Past
them is one HACL\* does not have at all --- ML-KEM, FIPS 203, all three
parameter sets, with constant-time implicit rejection --- which is what
the hybrid key exchanges now being turned on in TLS need.

Above them all sits HPKE, RFC 9180, with all four modes, all three AEADs
and four ciphersuites pinned for C -- more than the HACL\* distribution
exposes, from a single implementation parameterised by a ciphersuite
record.

One thing is left, and it is deliberate: there is no agile provider in the
shape of EverCrypt.  Multiplexing between implementations happens inside
the algorithm -- AES-NI under AES-GCM, the SHA extensions under SHA-256 --
rather than behind a separate dispatch layer with its own state type, so a
caller that wants to choose an algorithm at run time does so by choosing a
function.  Whether a general agile surface is worth the indirection it
costs is still open.

Beyond feature parity, the performance work above has a queue of its own, in
rough order of value:

1. **Windowed scalar multiplication for Ed25519**, which is most of the
   remaining gap now that the field is at radix 2^51 and `fmul` is a straight
   line: signing is 3.7x the reference where X25519 is 1.25x, and the whole of
   the difference is HACL\*'s precomputed base-point window against a
   bit-at-a-time double-and-add here.  Fixed-base, so it pays on keygen and
   signing both, and the constant-time table lookup it needs already exists:
   `Hacl.Bignum.Base.table_select`, written for the modexp window.  It needs
   associativity of the twisted Edwards addition law in extended coordinates,
   which is now proved.

   That obligation, and the same one for the two Weierstrass curves, is
   written down: `spec/Spec.Ed25519.Group.fsti`, `spec/Spec.P256.Group.fsti`
   and `spec/Spec.K256.Group.fsti` state curve membership, projective
   equality, closure of the addition law, and the group axioms, and all
   three are now proved, with no `admit` and no `assume`, so the library
   still assumes nothing mathematical.  The proofs reduce every statement
   to polynomial identities modulo the affine curve equations, which a
   small verified polynomial arithmetic (`spec/Spec.Group.Poly.fst`) checks
   by normalisation; completeness additionally uses Pocklington primality
   certificates for the field primes (`spec/Spec.Group.Primes.fst`), a
   no-roots certificate on the Weierstrass curves, and non-squareness of
   `d` on Ed25519.  Worth saying that HACL\* proves none of them: in
   `specs/lemmas/Spec.K256.Lemmas.fst` and its Ed25519 and P-256 twins the
   corresponding lemmas are `admit()`, so HACL\*'s windowed Ed25519, its
   windowed P-256 and its GLV secp256k1 all rest on the same admitted
   facts.  The measured shape of the gap says what they are worth: on
   variable-base ECDH, where HACL\* has no table either, P-256 is within
   1.15x; on fixed-base it is 2.59x.
2. **One GF(2^128) reduction per four GHASH blocks**, **done**.  The four-way
   loop used to compute four full products, reducing each 256-bit product to
   128 bits before adding it to the accumulator, so the reduction ran four
   times per sixty-four bytes even though it is linear and could run once.
   It now accumulates the four raw 256-bit products and folds a single time.
   Three specification facts were needed and none of them says anything new
   about the reduction polynomial: `Spec.GF128.Poly.mul_r_two`, factored out
   of the existing `gmul_three`, which lets one fold serve a doubled
   argument; `Spec.CLMUL.bswap_gadd`, additivity of the byte reversal, one
   line by extensionality; and `Spec.GF128.Algebra.gmul_defer4`, which is
   `gmul_split` four times, a regrouping of the eight resulting half-products
   into a low sum and a high sum, and `gmul_gadd_left` three times to pull
   the multiplication by `r` out of the high sum.  The code is
   `Hacl.AES.GF128.NI.gmul4_vec`, whose postcondition is exactly
   `Spec.GF128.Algebra.sum4` of the four products -- the shape `horner4`
   already wanted -- so it dropped into `ghash_loop4_ni` with no glue.
   GHASH alone went from 2.11 cycles a byte to **1.28**, whole-primitive
   AES-128-GCM from 3.68 to **2.88**, and the benchmark row from 4.48x of
   EverCrypt to **3.52x**, past a gigabyte a second for the first time.  The
   CTR half did not move, which is the control.  The eight-block window this
   item suggested as future work has since been done, and is item 4 below.
3. **The counter block incremented in a vector lane**, **done**.  A
   four-block turn of `Hacl.AES.NI.ctr_block4_ni` was 225 instructions for
   sixty-four bytes, and only about seventy-eight of them were AES; a
   hundred and thirty-nine were four copies of the constant-time byte carry
   chain of `Hacl.AES.Counter.inc32_impl`, each ending in a four-byte store
   to the counter array that the next iteration immediately reloaded
   sixteen bytes wide -- a narrow store under a wide load, which stalls, and
   the four chains were serial through it.  Reversing all sixteen bytes puts
   the counter's four in lane zero *and* turns their big-endian reading into
   a little-endian one, so a packed thirty-two bit add of one is exactly
   `Spec.AES.inc32`, carrying nothing into the twelve bytes above it, and
   reversing again puts it back.  No new instruction was needed: `PADDD` was
   already bound for SHA-256 and only had to move out of the SHA target
   group, `_mm_add_epi32` being SSE2 and part of the baseline; the one new
   extern is the constant one-in-lane-zero.  The proof is
   `Hacl.Spec.Bytes.le_nat_byte` (read a byte back out of a little-endian
   number), `Spec.SHANI.lane_byte` (connect the lane the `PADDD` axiom
   states itself over to the bytes underneath it),
   `Hacl.AES.Counter.inc32_lanes` (sixteen concrete byte instances, twelve
   saying the byte did not move and four that it is a digit of the
   incremented counter) and `Hacl.AES.NI.inc32_vec`.  225 instructions to
   **114**, counter mode from 1.55 cycles a byte to **0.49**, whole
   AES-128-GCM from 2.78 to **1.71**, and the benchmark row from 3.52x of
   EverCrypt to **2.24x** under gcc and **1.80x** under clang.  The GHASH
   half did not move, which is the control.
4. **Eight GHASH blocks to a reduction**, **done**.  Item 2 left the fold as
   a fixed cost per group rather than per block, and the deferral argument
   never cared that the group was four.  `Hacl.AES.GF128.NI.gmul8_vec` runs
   eight carry-less products against eight powers of the hash key and folds
   once for a hundred and twenty-eight bytes; eight independent `PCLMULQDQ`s
   also give the multiplier twice as much to work on at once.  None of the
   algebra is new: `Spec.GF128.Algebra.sum8` is two `sum4`s added, `regroup8`
   is `regroup4` twice and one pairing lemma, `mul_r_sum8` is `mul_r_sum4`
   twice, and `gmul_defer8` is `gmul_defer4` with four replaced by eight.
   Only the Horner side needed thought: `horner8` is `horner4` applied twice
   with a multiplication by `H^4` pushed through the first group's four
   terms, and because the powers are generated one multiplication at a time,
   `pow_mul4` has to walk up the chain to show that `H^4` times each of `H`
   to `H^4` is `H^5` to `H^8`.  The four-way loop stayed, because the
   eight-way pass leaves at most one group of four behind: `ghash_loop4_ni`
   gained a starting offset and picks up where the eight-way pass stopped,
   and the one-block loop takes the rest.  The extra powers are computed
   inside the same test as before, so a message short of a hundred and
   twenty-eight bytes pays for none of them.  GHASH went from 1.22 cycles a
   byte to **1.03** under gcc and 0.92 to **0.82** under clang, and the
   benchmark row from 2.24x of EverCrypt to **1.98x** under gcc and 1.80x to
   **1.68x** under clang -- inside a factor of two of hand-written assembly
   for the first time.  The CTR half did not move, which is the control.
   What is left is register pressure: eight powers, eight data blocks and
   sixteen product halves do not fit in sixteen registers, and forty-one of
   the eight-way turn's 363 instructions are spills.  Accumulating the halves
   as they are produced rather than in a tree was tried, to keep fewer live,
   and made gcc a third slower -- it serialises the products when the sum is
   a chain.  A sixteen-way window would make that worse, not better, so this
   is probably the end of the line for the reduction, and what is left in
   AES-GCM is the interleaving of the two halves that EverCrypt's assembly
   does and this code does not.
5. **Special-prime reduction for P-256**, in place of the shared general
   Montgomery core.  secp256k1's half of this is **done**: `code/k256` now
   runs on a five-limb, radix-2^52, lazily reduced field with the fold
   `2^256 = p + 2^32 + 977` in place of a Montgomery reduction, which is the
   representation HACL\* and libsecp256k1 use.  `spec/Spec.Bignum52.fst` is
   the prime-free radix-52 core, `spec/Spec.K256.Field52.fst` the
   prime-specific arithmetic, `spec/Spec.K256.Columns.fst` the bridge that
   turns the nine-column product and its fold into the straight line the code
   runs, `spec/Spec.K256.Freeze.fst` the canonical form, and
   `spec/Spec.K256.Repack.fst` the bit repacking between five fifty-two-bit
   limbs and the four sixty-four-bit ones whose byte layer was already proved.
   `code/k256/Hacl.K256.Field52.fst` is the code, `Hacl.K256.Exp52` the
   exponentiation ladder without the Montgomery apparatus, and
   `Hacl.Impl.Lit52` and `Hacl.K256.Tables52` the four curve constants, which
   are now the numbers themselves rather than multiples of `R`.  The old
   `Hacl.K256.Field` is deleted.  It was worth 313 us to 227 on ECDSA sign and
   291 to 213 on ECDH, and it puts our `fmul` at 29.4 ns against HACL\*'s
   25.9, so the field is no longer the gap.  P-256's half is **done** too,
   in its own Montgomery form rather than a fold: `code/p256/Hacl.P256.Field64.fst`
   reduces with `mu == 1` and `p + 1 = 2^96 + 2^192 * 0xffffffff00000001`, so
   each of the four steps is two shifts and one multiplication, on top of
   X25519-64's `mul8`.  `fmul` went from 34 ns to 25 (gcc) and 47 to 18
   (clang), and every P-256 operation 35-50% faster (Part 62).  The two
   scalar fields followed with a generic word-by-word Montgomery multiply,
   `Hacl.Impl.Mont64`, and an addition-chain inversion, 11-16% off signing
   on both curves (Part 65).

6. **The fixed-base window**, **done on all three curves**.
   `code/ed25519/Hacl.Ed25519.PointMulG.fst` splits the scalar into four
   sixty-four-bit pieces and walks them together against `G`, `2^64 G`,
   `2^128 G` and `2^192 G`, so that one doubling chain serves all four and
   sixteen rungs suffice.  184 point operations against 335: key generation
   from 84.8 us to **60.7** (gcc) and 77.8 to **51.3** (clang), 3.40x of
   HACL\* to **1.91x** and 2.45x to **1.61x**; signing from 200.0 to
   **153.9** and 191.3 to **139.0**; verification, which does one fixed-base
   and one variable-base multiplication, from 202.7 to **187.5** and 188.6 to
   **165.1**.  The three extra base points are compiled in as nine field
   constants; `spec/Spec.Ed25519.Base.fst` says what they are by a doubling
   chain the normaliser evaluates, and `Spec.Group.Smul.dblk_ok` turns that
   into a statement about `smul`.  **On Ed25519 the four tables of sixteen
   entries are now compiled in too**, rather than built on entry: that was
   sixty point additions out of 188, and removing them took key generation to
   **45.7** us (gcc) and **36.0** (clang), 1.91x of HACL\* to **1.46x** and
   1.61x to **1.16x**; signing to **93.4** and **73.5**, 1.92x to **1.46x**
   and 1.62x to **1.15x**; verification to **150.8** and **127.6**, 2.22x to
   **1.98x** and 1.88x to **1.69x**.  The price is 256 field constants
   instead of 9, about ten kilobytes of `.rodata`.  `spec/Spec.Ed25519.Win0`
   .. `Win3` name the sixty-four points and prove each is the multiple it
   claims to be, one addition at a time from the scale point;
   `code/ed25519/Hacl.Ed25519.Win0` .. `Win3` hold the limbs;
   `Hacl.Impl.Lit51` cuts a literal list the way `entry` slices the sequence;
   and `Hacl.Ed25519.WinTable` turns four limb facts into the window's `ent`.
   **Ed25519 has since replaced the window with a signed radix-16 comb**,
   `code/ed25519/Hacl.Ed25519.PointMulComb.fst` over thirty-two compiled-in
   Niels tables (see "The generator has its own comb"), and the window's
   modules above are gone: sixty-four mixed additions and four doublings
   instead of sixty-four of each, key generation from 31.6 us to **14.9**
   and signing from 64.8 to **31.1** (gcc, `Hacl_Ed25519_sign`, which
   multiplies by the generator twice), verification from 107.1 to **88.1**;
   under clang 37.3 to **18.9**, 78.1 to **39.1** and 122.7 to **103.8**
   (`bench/REPORT.md` Part 89).  The price is 34 KB of `.rodata`.
   secp256k1 has had the same fixed-base split, in
   `code/k256/Hacl.K256.PointMulG.fst`, with six field constants rather than
   nine because a projective point has three coordinates where an extended
   one has four: `secret-to-public` went from 155 us to **111** and 3.16x to
   **2.27x**, signing from 172 to **126** and 2.63x to **1.91x**, and
   verification from 319 to **271**.  P-256 has had it third, in
   `code/p256/Hacl.P256.PointMulG.fst`, and gained the most from it, because
   its addition formula is the more expensive and it began closest to the
   reference: `dh-initiator` went from 272 us to **165** and 1.73x to
   **1.04x**, signing from 287 to **182** and 1.69x to **1.08x**, and
   verification from 545 to **449** and 1.27x to **1.05x**, with variable-base
   `dh-responder` unmoved at **0.77x** as the control.  Its six constants are
   Montgomery forms, since that is the representation P-256's field runs in
   (they have since been replaced by compiled-in tables; see below).  The scalar arithmetic all three
   share is `spec/Spec.Group.Split4.fst`.  The variable-base
   half is **done on all three curves**: `code/k256/Hacl.K256.PointWin.fst`,
   `code/p256/Hacl.P256.PointWin.fst` and
   `code/ed25519/Hacl.Ed25519.PointWin.fst` walk the scalar four bits at a
   time
   against a sixteen-entry table of small multiples of the input point, built
   at run time, with `Hacl.Bignum.Base.table_select` for the constant-time
   lookup and `Hacl.Impl.Mont4.adigit` for the nibble.  336 point operations
   against the ladder's 512: about 26% off every secp256k1 operation,
   about a third off every P-256 one and about a fifth off every Ed25519
   one, taking secp256k1's variable-base ECDH
   from 2.40x to **1.73x**, P-256's from 1.14x to **0.76x**, the first
   asymmetric primitive here that is ahead of the reference, and Ed25519
   signing from 3.82x to **3.11x** under gcc and 4.21x to **2.94x** under
   clang.  Its table layer now carries a scale, which is what lets the
   fixed-base window above reuse all of it.

   The proof is reusable and that was the point.  `spec/Spec.Group.Smul.fst`
   is a commutative group as an abstract record -- the operation, the
   membership predicate and the equivalence are opaque function fields -- and
   everything inductive lives there: scalar multiplication, its congruences,
   the double-and-add ladder, and the theorem that the ladder computes it.
   2.5 seconds.  `spec/Spec.K256.Smul.fst` instantiates it from
   `Spec.K256.Group` and connects `Spec.K256.point_mul` by a definitional
   equality of step functions, which mentions no equivalence and so is free:
   0.9 seconds, against an eight-minute timeout for the same statement proved
   directly.  `spec/Spec.P256.Smul.fst` is the same file with the P-256
   lemmas substituted in and verified in a second on the first attempt, which
   is exactly the return the abstraction was built for.  `spec/Spec.Ed25519.Smul.fst`
   is the third instance and took five seconds; it is the only one that needed
   anything new, because Ed25519's ladder is indexed by thirty-two *bytes* and
   reads bit `i` out of byte `i / 8` where the abstract one divides by `2^i`,
   so it proves `ith_bit_gbit` and its four-bit analogue `nibble_of_bytes`.
   Both are arithmetic about byte strings, mention no curve, and are cheap.

   The lesson generalizes past the specs: `on_curve` and `peq` unfold into
   field equations modulo a seventy-eight-digit prime, so any query that
   merely has them in scope pays for the whole field.  Keep them out of every
   induction, out of every bookkeeping predicate (`opaque_to_smt`), and above
   all out of every Pulse precondition, since a precondition is in scope for
   the entire body.  P-256 added a fourth case: its field is Montgomery, so
   even `pt_ok` and the coordinate projection are expensive -- the latter is
   `eval v * R^-1 mod p`, two seventy-eight-digit literals per coordinate.
   The invariant therefore takes the three limb *sequences*, not the point,
   and the module went from a forty-minute timeout to ninety seconds.
   `--query_stats` is the tool that finds this: when every reported query
   reads 0.00 seconds and the module still runs twenty minutes, the time is
   one *failing* query burning its whole rlimit.  Ed25519 added a fifth case,
   one level down: `decompress_on_curve` is four lines of algebra, and
   written over `fadd`, `fsub` and `fmul` it put `prime` in scope of a
   degree-four nonlinear goal and ran for twenty minutes.  Restated over an
   arbitrary positive modulus `n`, with only the last two lemmas mentioning
   the curve, it takes fifteen seconds.  Keep the seventy-eight-digit
   literal out of the query, whatever the query is about.

   Signing, verification and key agreement
   all begin with a multiplication by the generator, where HACL\* has a
   table compiled in, and all three curves here now have one too.  The
   three moved by amounts that track how expensive their addition formulae
   are and how close to the reference they started: Ed25519 key generation
   from 3.40x to 1.91x, secp256k1 `secret-to-public` from 3.16x to 2.27x,
   P-256 signing from 1.69x to 1.08x.  The hard part was proving a
   compiled-in multiple of the generator correct, since `smul (2^64) g`
   cannot simply be unfolded; the answer all three use is to state it as a
   doubling *chain* (`Spec.Group.Smul.dblk`), which the normaliser
   evaluates on concrete field elements at typechecking time, and convert
   with `dblk_ok`.  The third copy cost an afternoon and verified on the
   first attempt at every step, which is what writing the same four modules
   twice buys.

   Plan A -- compiling in the four tables of sixteen entries rather than
   building them -- **has now been done on Ed25519 and on secp256k1**.  It
   took Ed25519 key generation from 1.91x to **1.46x** and signing from 1.92x
   to **1.46x**, with clang at **1.16x** and **1.15x**, and secp256k1
   `secret-to-public` from 2.27x to **1.55x** and signing from 1.91x to
   **1.40x**, with clang at **1.55x** and **1.50x**.  The proof obligation grows from three points to
   sixty-four, but it does not get harder: each entry is one `assert_norm`
   that it equals the previous entry plus the scale point, lifted to `smul`
   by `Spec.Group.smul_add_congr`, and the entries are stored affine so the
   normaliser is always comparing small numbers.  What made it awkward was
   Pulse rather than F\*: sixteen `Table.table` calls yield sixteen
   *different* existential permissions, and a permission can be halved but
   never weakened to a stated target, so `win_add` had to be generalised from
   one permission to four and sixteen binders threaded through the window
   loop.  secp256k1's copy is `spec/Spec.K256.Win0` .. `Win3`,
   `code/k256/Hacl.K256.Win0` .. `Win3` (twelve `static const uint64_t [80]`
   arrays in radix 2^52, a hundred and ninety-two field constants), the
   chunking half of `Hacl.Impl.Lit52` and `Hacl.K256.WinTable`; it cost an
   afternoon, verified at every step on the first attempt, and let
   `Hacl.K256.Tables52G` be deleted.  P-256 has **now had it too**, at 192
   field constants in Montgomery form (`Hacl.P256.Win0` .. `Win3`,
   `Hacl.P256.WinTable`), which let `Hacl.P256.TablesG` be deleted and took
   ECDH as initiator from 97 us to 69 under gcc and 77 to 59 under clang
   (Part 63).
7. **Ed25519's group-order arithmetic on the four-limb Montgomery core**,
   **done**.  `Hacl.Ed25519.Scalar` was the last bit-at-a-time arithmetic in
   the repository and the last user of the eight-limb, thirty-two-bit
   `Spec.Bignum256` stack: reducing a SHA-512 digest was 512 rounds of
   double-and-conditionally-subtract and multiplying two scalars was 256
   more.  Its header explained the choice -- "here there is no `uint128`" --
   which stopped being true with the first item of this list.  It now uses
   `Hacl.Impl.Mont4` with the order as data, exactly as `Hacl.K256.Scalar`
   does, and reduces a digest by cutting it into four 128-bit chunks (each
   below `q`, so a residue for free) and folding them with three constant
   Montgomery multiplies against `2^384 mod q`, `R^2 mod q` and `2^640 mod
   q`; a Montgomery multiply by `R k mod q` is a plain multiply by `k`, so
   no Barrett step and no second representation are needed.  The scalar
   arithmetic in a signature -- `sign_expanded` less the fixed-base
   multiplication it also does -- went from 31 us to 1.8, signing from
   2.35x of the reference to **1.92x** with gcc and **1.62x** with clang,
   key generation to **1.94x**/1.63x and verification to **2.22x**/1.88x.
   What is left of the Ed25519 gap is entirely the scalar multiplication,
   and item 6's Plan A has since taken another quarter off it: signing and
   key generation are now **1.46x** under gcc and **1.16x** under clang.
8. **The inner loop of the Montgomery multiply**, **done**.  The four modexp
   rows -- RSA-PSS signing, FFDHE, the generic 2048-bit modexp and RSA-PSS
   verification -- had come down to about 1.25x on the window alone, and
   what was left was the `n x n` multiply itself.  Two changes took them
   past the reference.  `Hacl.Bignum.Base.mul_row` now runs four columns to
   an iteration with a one-at-a-time tail, which is worth 11% of the
   multiply and took `mont_mul` to 1,990 ns against HACL\*'s 1,986; and
   `Hacl.Bignum.Base.sqr` is now a real squaring -- strict upper triangle,
   one doubling, then the `n` diagonal terms -- at 579 ns against the full
   multiply's 931 and HACL\*'s `bn_sqr` at 550.  Four fifths of the
   multiplications in a 4-bit-window exponentiation are squarings, so
   `Hacl.Bignum.Montgomery.mont_sqr` is the one that matters and
   `Hacl.Bignum.Exponentiation.mont_sq` now calls it instead of copying the
   accumulator and going through `mont_mul`.  RSA-PSS signing 1.23x to
   **0.94x**, FFDHE 1.25x to **0.96x**, the generic modexp 1.26x to
   **0.97x**, RSA-PSS verification 1.38x to **1.14x**; under clang,
   **0.92x**, **0.92x**, **0.94x** and **1.12x**.  What is left is the
   reduction rather than the multiply, and the next thing to try is HACL\*'s
   almost-Montgomery variant, which skips the conditional subtraction inside
   the ladder and corrects once at the end.

   The proof cost of this was not the algebra, which is three lemmas, but a
   solver behaviour worth writing down: F\* proves the loop body's
   postcondition at `j + 1` and then has to accept it as the invariant at
   `SZ.v (SZ.add j 1sz)`, and merging two integer terms that are equal by
   arithmetic underneath an uninterpreted `pre` or `wt` is a propagation
   from the arithmetic theory into congruence closure that Z3, in a body
   carrying three arrays, will not make -- it burns the whole rlimit and
   fails.  Stated as its own lemma with the equation as a hypothesis
   (`idx_subst`, `tri_subst`, `dg_subst`, `pw_ext`) it is instant.  The same
   shape was already lurking in `Hacl.Bignum.Montgomery.ladder_step`, whose
   two branches reach `2 e + SZ.v bit` and are asked for `2 e` and `2 e +
   1`: that query had been running for over ninety minutes without
   returning.  Splitting the conditional half out as `ladder_bit`, with a
   contract naming only the two arrays it touches, took the whole module
   from not terminating to **two minutes**.

9. **Taking over the remaining sixty-three compiler specialisations**, the
   ones `make clones` lists: HMAC, the SHA-2 cores, the MD5 and SHA-1 blocks,
   ML-KEM.
   Each is a speedup that gcc currently grants us at its own discretion and
   clang does not grant at all.  The SHA-3 sponge and permutation were the
   first, and were worth 2.4x on a short digest; BLAKE2's compression chain
   was the second, and was worth 14% to clang before the unrolled round took
   it further; ML-KEM's parameter sets were the third, and were worth 1.31x
   on encapsulation and 1.26x on decapsulation.  Pricing the ones gcc still
   performs, all at once, with `-fno-ipa-cp-clone` says they are worth
   nothing measurable, so taking *those* over is a tidying exercise rather
   than a performance one.

   The ones gcc would perform and cannot *looked* like a different matter,
   and ML-KEM looked like where it bit: `make clones-available` wanted to
   clone the noise sampler on eta, the polynomial encoder on the bit width,
   key generation on the parameter set, and SHA3-512 on its constant call
   lengths, and the budget was spent.  Raising it was worth 1.32x on
   encapsulation and 1.24x on decapsulation.  Bisecting that number with
   `__attribute__((noclone))`, one candidate at a time, showed it was
   entirely the encoder -- and that the right fix was not to get the clone
   back but to stop needing it, which is what *A bit string is a number*
   above does.  The other twelve entries in `clones-available` were then
   measured to be worth nothing on ML-KEM, so what remains of this item is
   the tidying exercise after all.  Splitting the distribution into several
   translation units is still *not* the fix -- it moves the budget rather
   than removing the dependency on it, and costs inlining across the new
   boundaries.

   The lesson generalises, and is worth stating plainly: a specialisation
   the compiler grants at its own discretion is usually hiding an
   algorithmic problem that it is papering over.  `clones-available` is
   better read as a list of places to look than as a list of speedups
   owed.

   Part of this is a mechanical sweep: a table that never varies should not
   be a parameter at all.  BLAKE2's schedule, BLAKE2's initialisation vector
   and MD5's two tables are done; SHA-2's round constants and initial states,
   SHA-3's round constants, Ed25519's curve constants, ML-KEM's twiddle
   factors, the FFDHE primes and the HPKE labels are not.  Measured with
   `-fno-ipa-cp`, what is left is SHA-2 6% and NaCl's secretbox 8% on short
   inputs.  The awkward case -- a table that genuinely differs between
   instantiations, as BLAKE2's initialisation vector does between the two
   widths -- is solved rather than open: the binder becomes a
   `Pulse.Lib.GlobalArray` `static_array` marked `[@@@monomorphize]`, and the
   global it is applied to carries `[@@FStar.Custard.no_specialize]` so that
   Custard's specialization key stops at the name instead of unfolding to the
   initializer.  SHA-2 is the next one to take that shape.

10. ~~**An expanded-key context for AES-GCM**~~ --- done; see *An
    expanded-key context for AES-GCM* above.  The estimate here was 29 ns
    and the measurement was 35.6, the difference being the key division
    roadmap item 11 added after this entry was written.  Sixty-four-byte
    AES-128-GCM went from 2.92x of EverCrypt to **2.11x** and AES-256-GCM
    to **1.90x**.  The remaining half of the idea --- caching the GHASH key
    powers in the context, which would make the aggregation thresholds
    irrelevant and turn a sixty-four-byte GHASH into one group of four ---
    is done too; see *The powers of the key belong with the key* above.
    Sixty-four-byte AES-128-GCM is now **1.87x** and AES-256-GCM **1.71x**.

11. ~~**Deferring the one-bit shift in GHASH**~~ --- done, and in a stronger
    form than this entry proposed.  The plan was to hoist the one-bit shift
    out of `raw_product` and do it once per aggregated group.  The shift can
    be removed outright instead: see *Removing the one-bit shift from
    GHASH* above.  Bulk AES-GCM gained 29%.

12. **The GLV endomorphism and Shamir's trick for secp256k1.**  With the
    small multiples of *Twenty-one is not a field element* in, secp256k1
    signing is within **1.19x** of HACL\* and `secret-to-public` within
    **1.28x**, but verification is still **2.12x** under gcc and 2.29x
    under clang.  What is left is entirely algorithmic, and it is two
    things.  First, verification computes `u1 G + u2 P` as two independent
    scalar multiplications; Shamir's trick interleaves them against a
    joint table and does one pass of doublings instead of two.
    `Hacl.K256.PointMulD` currently declines it, with a docstring saying
    why, and that docstring is the thing to revisit.  Second, secp256k1
    has an efficiently computable endomorphism: `lambda * (x, y) ==
    (beta x, y)`, which splits a 256-bit scalar into two 128-bit halves
    and halves the number of doublings again.  HACL\* does both.  Together
    they are roughly a factor of two on verification and about 30% on
    variable-base ECDH, and neither is small: the scalar splitting needs
    its own correctness proof, and the joint table needs the
    constant-time lookup to range over sixteen combined points rather
    than sixteen multiples of one.  Ed25519 verification has
    since taken the Shamir half (`Hacl.Ed25519.Straus`, variable time,
    since all its inputs are public); it has no endomorphism to go with it.

13. ~~**Karatsuba in the bulk GHASH multiplier**~~ --- done; see
    *Karatsuba, and what a group of blocks may put off* above.  The entry
    proposed trading one of the four carry-less multiplies a block for the
    Karatsuba fold, which on its own is a loss; what makes it pay is that
    both the squares correction and the assembly of the halves are linear
    and so may be deferred to the end of an aggregated group, the same
    argument that defers the reduction.  Twenty-four multiplies a group of
    eight instead of thirty-two, and the loop body down from 247
    instructions to 194.  Bulk AES-GCM gained 9% under gcc and 14% under
    clang; 256 KiB AES-128-GCM is now **1.43x** of EverCrypt under gcc and
    **1.22x** under clang.

14. ~~**A dedicated squaring for the field**~~ --- done; see *A square is
    not a product* above.  Every field in the library squared by copying
    its argument and calling the multiply, which for five limbs is
    twenty-five wide multiplies where fifteen suffice.  Pairing the
    off-diagonal products of the symmetric schoolbook and carrying the
    factor of two in the word rather than in the 128-bit accumulator
    leaves the column bounds inside what the multiply's carry chain is
    already proved to accept, so the chain, the wrap and the narrowing are
    reused unchanged and the whole proof is five lemmas derived from the
    existing column lemmas with `b := a`.  X25519 gained 10-12% under gcc
    and 11% under clang, Ed25519 verification 14% and 7%, signing 12% and
    6%.  Ed25519's `point_double` squared inline rather than through the
    field's `fsqr` and had to be rewritten site by site; while there,
    `2 z1^2` became a square followed by a doubling.  The same rewrite for
    secp256k1's radix-2^52 field verified just as easily and was reverted:
    it is 32% faster in isolation under clang and still made
    `k256-ecdsa-verify` 3% slower there while gaining 5% under gcc, which
    is the measurement saying that k256's time is not in the multiply.
    Item 12 is where it is.

15. ~~**Audit the remaining masked selections against the compiler**~~ ---
    done for six of them; see *The compiler is allowed to undo a
    constant-time algorithm* above.  The secret-indexed table read was
    found by accident to compile, under clang `-O3`, into a sixteen-way
    branch cascade on the secret digit, so the question had to be asked of
    everything else.  `tests/test_consttime.c` now asks it as a standing
    test: the table read at P-256's four-limb width, the whole X25519
    ladder over scalars of all-zero, all-one and alternating bits, the two
    bignum comparisons by position of the first differing limb, ML-KEM's
    Fujisaki--Okamoto ciphertext comparison the same way, and the AES
    S-box over all 256 input bytes.  All six are flat to 3.5% under both
    compilers.  What remains is the long tail: ML-KEM's compression and
    sampling, which compare against the fixed modulus 3329 rather than
    against a range of literals and are therefore a weaker candidate, the
    conditional subtractions in the Montgomery reduction, and the
    `Hacl.Secret` selects inside the point formulas.  The method is the
    one the test uses, and the two levers where a leak is found are the
    value barrier `Hacl.Launder.launder` and restructuring the loop so the
    optimizer cannot see a constant trip count over the secret's range.

16. ~~**Why is clang's SHA-EXT code three times gcc's?**~~ --- answered, and
    it was not code generation at all; see *One attribute in the wrong
    place, and three quarters of the time* above.  A pointer-arithmetic
    helper shared by nothing but SHA-256 had been stamped with the AES
    feature set, and clang will not inline across a `target` mismatch, so
    thirty-nine `a + i` per block became thirty-nine calls.  `sub` is now
    `inline_for_extraction`.  clang's SHA-256 went from 668 us to 179 on
    256 KiB, gcc's from 227 to 190, and both SHA-256 and HMAC-SHA-256 now
    sit at 1.16x of HACL\* best under gcc and about 1.10x under clang.
    What remains of that row is this repository's intrinsics against Vale's
    hand-written assembly, which is a much smaller thing to chase.

17. **A vector backend -- done.**  ChaCha20 at 5.31x, Poly1305 at 4.18x
    and ChaCha20-Poly1305 at 5.14x against HACL\* best were the three rows
    that no further work on scalar C could reach; they are now 1.09x, 0.97x
    and 1.04x.  **ChaCha20 is done**: `lib/Hacl.Vec256.fst`
    is the AVX2 counterpart of `Hacl.Vec128`, fifteen axioms each tested by
    `tests/test_vec256.c`, and `Hacl.Chacha20.Vec256` is an eight-lane
    vertical ChaCha20 proved lane by lane against the scalar specification
    (4.7x on 256 KiB, see `bench/REPORT.md` Part 54).  **Poly1305 is done
    too**: `Hacl.Poly1305.Vec256` runs four Horner chains in *r^4*, one per
    64-bit lane, and `Spec.Poly1305.Vec` proves them the specification's one
    chain in *r* (4.4x on 256 KiB, Part 55); `lib/Hacl.Vec256.fst` grew to
    twenty-three axioms.  **AVX-512 ChaCha20 is done** as well:
    `lib/Hacl.Vec512.fst` (seventeen axioms, `tests/test_vec512.c`) and the
    sixteen-lane `Hacl.Chacha20.Vec512`, another 1.9x on 256 KiB (Part 60).
    **Salsa20 has both** (`Hacl.Salsa20.Vec512`, `Hacl.Salsa20.Vec256`,
    10.6x on 256 KiB, Part 61), ported from ChaCha20's with only the rounds
    changed.  What remains is AVX-512 Poly1305 (eight lanes), on the same
    pattern; it is now most of secretbox's time.

18. **One hash core, two block implementations.**  Partly done.
    `Hacl.Hash.SHA2.Core.blocks_t` is the type of a block function, the
    incremental hash (`update_with`) and `Hacl.HMAC.Cat.hmac_cat` take one
    as a `[@@@monomorphize]` argument, and `Hacl.HKDF.Core.expand_impl` is
    one generic copy that runs on SHA-EXT through it; `expand_impl_ni` is
    gone.  `hash_blocks_ni` and `hmac_impl_ni` are still transcriptions at
    `S32.t`, and `Hacl.HMAC.DRBG.Core`, `Hacl.HPKE.Labeled` and
    `Hacl.Streaming.HMAC` still pass `blocks_scalar`.  Moving the one-shot
    hash and HMAC onto the same argument would remove the remaining copies.
