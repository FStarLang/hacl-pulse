# hacl-pulse

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
(FIPS 203) is here in all three parameter sets, which HACL\* does not have
at all.  The one deliberate omission
is an agile provider in the shape of EverCrypt; see the roadmap below.
Everything listed there is specified, implemented, verified, extracted and
tested against the published vectors -- FIPS 180-4, FIPS 202, RFC 4231,
RFC 5869, RFC 7748, RFC 8032, RFC 7919, RFC 9180, FIPS 186-4, PKCS#1 v2.2,
the NIST CAVP sets for AES-GCM and HMAC-DRBG, the FrodoKEM known-answer
tests, the NIST ACVP vectors for ML-KEM, and the NaCl vectors --
thirty-four C test harnesses in `tests/`.

Performance ranges from ahead of HACL\*'s portable C -- SHA-256, SHA-512,
SHA-3, SHAKE, ChaCha20, ChaCha20-Poly1305, HMAC-SHA-512 and the generic
bignum are all faster -- to behind it on the elliptic curves, where what is
left is the scalar multiplication rather than the field: X25519 is within
1.26x, but Ed25519, P-256 and secp256k1 still multiply one bit at a time where
HACL\* uses a precomputed window.  See [Performance](#performance).

```
make            verify, extract, compile, test
make verify     verify everything
make extract    (re)generate dist/
make test       build and run the C tests
```

You need an F\* built from `master`, through `stage3` (that is, with the Pulse
plugin and libraries installed).  Point the build at it:

```
make FSTAR_ROOT=$HOME/tools/fstar
```

## Layout

| directory | contents |
| --- | --- |
| `lib/` | the secret-integer layer, the `word` type class, generic byte serialization, compile-time tables |
| `spec/` | pure specifications: `Spec.MD5`, `Spec.SHA1`, `Spec.SHA2`, `Spec.SHA3`, `Spec.Blake2`, `Spec.Chacha20`, `Spec.Salsa20`, `Spec.Poly1305`, `Spec.Curve25519`, `Spec.Ed25519`, `Spec.P256`, `Spec.K256`, `Spec.AES`, `Spec.GF128`, `Spec.GF128.Algebra`, `Spec.GCM`, `Spec.CarryLess`, `Spec.CLMUL`, `Spec.Chacha20Poly1305`, their constants and lemmas, `Spec.HMAC`, `Spec.HMAC.SHA1`, `Spec.HKDF`, `Spec.HMAC_DRBG`, `Spec.FFDHE`, `Spec.RSAPSS`, `Spec.NaCl`, `Spec.Frodo` and its matrix and parameter modules, `Spec.HPKE`, `Spec.MLKEM` and its NTT, sampling and encoding modules |
| `code/` | Pulse implementations, one directory per family (`code/hash/`, `code/chacha/`, `code/salsa20/`, `code/poly1305/`, `code/curve25519/`, `code/ed25519/`, `code/field256/`, `code/p256/`, `code/k256/`, `code/drbg/`, `code/aes/`, `code/bignum/`, `code/ffdhe/`, `code/rsapss/`, `code/aead/`, `code/nacl/`, `code/frodo/`, `code/mlkem/`, `code/hpke/`) |
| `c/` | handwritten C, and the whole of the trusted computing base on the C side: the platform entropy shim and the 128-bit vector intrinsics |
| `tests/` | C test harnesses |
| `dist/` | generated C: one `Hacl.c`, one `Hacl.h` |
| `design/` | the inventory of HACL\* that this library is measured against |

## The four design commitments

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
code and tested against an independent transcription of the standard: AES-NI
and `PCLMULQDQ` under AES-GCM (`lib/Hacl.Vec128.fst`), the Intel SHA
extensions under SHA-256 and SHA-224.  Each is selected at run time by
`__builtin_cpu_supports`.  See `design/vale-migration`.

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

### HKDF's one scratch buffer

`expand` hashes `T(i-1) || info || i` once per round.  `Hacl.HKDF.Core` lays
that out in a single buffer

```
[ T(i-1) |   info   | i ]
   hb       |info|    1
```

writes `info` into it exactly once, and then each round overwrites only the
leading digest and the trailing counter byte.  Round 1 is the exception --
`T(0)` is empty -- and is handled by hashing the `info || i` *window* of the
buffer, using `Hacl.Impl.Sub`.

The loop invariant never mentions `expand_all` at the round count reached so
far; it is stated against the *final* count, so that on exit it is literally
the postcondition.  `Spec.HKDF.expand_all_index_le` -- `expand_all` at `n`
agrees with `expand_all` at any `m <= n` on the first `m` digests -- is what
lets a round establish it.  The loop measure is the round counter, not the
bytes remaining: the last round overshoots the requested length, so
`len - base` is not a `nat`.

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
the spec's flattening; scratch is 25 lanes for the pi/rho result and 5 for the
theta parities.

Absorb xors whole message blocks straight out of the caller's buffer, and
stages only the last, padded, block in a 200-byte stack buffer — 200 rather
than the rate because the rate is not known at compile time.  Squeeze emits
`min(rate, remaining)` bytes per permutation, so a SHAKE call shorter than the
rate does exactly one permutation and a long one does not overrun.

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
`load_le #uint64` calls give the low and high halves; four of the five limbs
are a shift and a mask of one of them, and limb two is the only one that
straddles the boundary -- twelve bits from the low word, fourteen from the
high.  There is no `logor` anywhere: the operands are disjoint by size, so a
plain addition is equal to the disjunction and avoids `logor_disjoint`
entirely.

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

### Ed25519, on top of Curve25519's field

Ed25519 lives on the same prime as X25519, so it reuses
`Hacl.Curve25519.Field` unchanged -- the same five limbs of fifty-one bits,
the same `fmul`, the same inversion chain.  Nothing in the signature scheme
needed a second field implementation, which is the main reason the whole of
`code/ed25519` is six modules.

Its *scalar* arithmetic, mod the group order `q`, is a different matter: it
is eight limbs of thirty-two bits and always was, and for a while it shared
the field's names because the field happened to use the same radix.  The move
to 2^51 forced the split.  `Hacl.Ed25519.Scalar` now sits on
`Hacl.Impl.Limb` and `Spec.Bignum256` and owns its own `copy`, `load_le`,
`store_le`, `limbs_eq` and `reduce32`; `Hacl.Ed25519` deliberately mixes the
two, five-limb arrays for coordinates and eight-limb arrays for scalars.

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
operations already use.  One consequence: `point_add` and `point_mul` demand
all four coordinates of an input at a *single shared* permission, so the
read-only base-point table has to be copied into owned buffers before
`point_mul_g` can use it -- `Table.table` hands back an existential
permission per array, and four existentials are not one.

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
form over eight 32-bit limbs by one shared layer in `code/field256/`:
`Spec.Bignum256` fixes the representation, `Hacl.Impl.Mont256` does
Coarsely-Integrated Operand Scanning, and `Hacl.P256.Field` and
`Hacl.P256.Scalar` are two instantiations that never meet.  **That layer
takes its modulus as data**, a record of the modulus, its two's complement
and the Montgomery constants, passed at run time.  Nothing in it mentions a
curve, which is what made secp256k1 almost free.

**Keeping them apart is a performance decision, not a taste one.**  The field
modulus `p` and the order `q` are both 78-digit literals, and a goal that
mentions both takes minutes.  So `code/p256` is twenty modules: the on-curve
test and the scalar reduction never appear in the same verification context,
and `Hacl.P256.Key` (private keys, the scalar field) and
`Hacl.P256.Key.Public` (public keys, the field) are separate files for no
other reason.  `code/k256` is the same twenty for the same reason.

**`Spec.P256.point_add` and `point_double` are `opaque_to_smt`.**  The
addition formulas are Renes-Costello-Batina, twelve field multiplications
with no special cases -- and about forty lines of nested `fmul`/`fadd` when
unfolded.  Once, in the scalar-multiplication loop, that is fine; on every
iteration of a 256-step ladder it is fatal.  Sealing them means the loop
invariant talks about `point_add` the symbol.

**Scalar multiplication reads bits, so it does not use Montgomery form.**
`Hacl.P256.Key.load_scalar` produces sixteen plain limbs with `load_be`;
`qload` is used only where the scalar enters the order field (signing).  The
ladder itself is a plain 256-iteration double-and-add with the addend
selected by a constant-time swap, in its own module
(`Hacl.P256.PointStep`) so that one step's proof does not carry the
loop's.

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
`code/p256` in which only three files differ in substance.

**`Hacl.K256.Tables` is the whole of the difference for the field.**  The
two moduli, their complements, the four Montgomery constants, the three
exponents and the curve constants in Montgomery form -- about three hundred
lines of generated literals, and the only place in the implementation where
secp256k1's actual numbers appear.  `Hacl.K256.Field`, `Hacl.K256.Scalar`
and `Hacl.K256.Inverse` are then the P-256 modules with those tables
underneath, and **none of them adds a line to the emitted C**: the
Montgomery layer takes its modulus as an argument, so the two curves share
every field operation and differ only in the table they pass.

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
every other test in this library is an equality.  `Hacl.Impl.Mont256.ageq`
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
rotations and a xor.  `Spec.AES.sbox_is_algebraic` is the lemma that this
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
ignores the return value still never sees forged plaintext, because the buffer
still holds the ciphertext it passed in.  The comparison itself folds sixteen
`eq_mask`s with `logand` and declassifies one bit at the end -- no early exit,
nothing that depends on where the first difference is.

    void Hacl_AES_GCM_Ptr_aes128_encrypt(uint8_t *tag, uint8_t *msg, size_t msg_len,
                                         uint8_t *key, uint8_t *iv, size_t iv_len,
                                         uint8_t *aad, size_t aad_len);
    bool Hacl_AES_GCM_Ptr_aes128_decrypt(uint8_t *msg, size_t msg_len, uint8_t *tag,
                                         uint8_t *key, uint8_t *iv, size_t iv_len,
                                         uint8_t *aad, size_t aad_len);

and the same pair for `aes256`.  Both are in place on `msg`.  The nonce may be
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
string on a declaration and `custard_c_closure_prologue` puts one on
everything that declaration *exclusively* reaches, which is exactly the set
that needs it -- a helper the baseline path also calls is deliberately left
alone.  So `cipher_ni` and its subtree get
`__attribute__((target("aes,pclmul,ssse3,sse4.1")))` and the dispatcher, one
call up, does not.  Feature detection is `__builtin_cpu_supports`.

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

The key schedule is still the portable one.  It runs once per message rather
than once per block, and `AESKEYGENASSIST` takes a round constant as an
immediate, so it would need one extern per round.

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
    void Hacl_Bignum_Montgomery_precomp     (uint64_t *res, uint64_t *n, size_t nn);
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
form -- entering is `mont_mul` against it, so there is no separate
`to_mont`.  HACL* starts the doubling chain at a power of two just below the
modulus; here it starts at one and doubles all the way, which costs the same
asymptotically and needs neither a bit-length nor a set-bit primitive.

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

`code/bignum/Hacl.Bignum.Exponentiation.fst` is the square-and-multiply
ladder that RSA and finite-field Diffie-Hellman are built out of.  It runs
entirely in Montgomery form: the base goes in once, the accumulator comes
out once, and every rung in between is two `mont_mul`s.

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

**The constant-time one always multiplies.**  It computes both candidates
and picks with `cselect`, a branch-free masked copy, so the instruction
trace does not depend on the exponent.  The mask comes from `get_bit`,
which returns a secret all-ones or all-zeroes word and offers no way to
turn one into a `bool`.  The variable-time one branches instead, and is
correspondingly only for public exponents -- which is why it is the one
`mod_inv_prime_vartime` calls: the exponent there is `n - 2`, and the
modulus is public.

Inversion is Fermat's little theorem, `a^(n-2) = a^-1 mod n` when `n` is
prime.  The specification does not mention primality -- it says only that
the result is `a^(n-2) mod n`, which is true unconditionally and is what
the code actually establishes.  Claiming an inverse would require a
primality hypothesis the caller cannot discharge and the library does not
check, so, like HACL*, we do not claim it.

**Nothing allocates**, here least of all: the length is a run-time value,
so every temporary is a caller-supplied array.  A ladder needs three `nn`
words of scratch plus one `2*nn` for the products, and `res` serves as a
fourth while the loop runs.

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

**`R^2 mod p` is recomputed on every call** rather than tabulated.  It is a
doubling chain of `2 * bits` steps, against an exponentiation of `bits`
rungs each of which is a full multiply: a few tenths of a percent, for
several kilobytes of table per group and no precomputation context in the
API.

This is also the one place in the library that allocates.  The scratch is
seven `nn`-limb arrays and one `2*nn`, on the *stack*, in the per-group
wrapper -- about 9 KB for FFDHE-8192.  An entry point named for its group
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
has.  There is no key object, no loader, no allocation and no free.  The
conversion to limbs happens on the stack inside the call, which is also
where `R^2 mod n` is computed, exactly as in the Diffie-Hellman groups and
for the same reason.

**Nothing is trusted.**  `rsa_exp`, the primitive both directions go
through, checks at run time that the modulus is odd, that it is greater than
one, that the base is below it and that the result fits the output width,
and returns `false` otherwise.  A caller cannot reach Montgomery reduction
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

Two deliberate deviations, both documented in the module header.  The names
are NaCl's, because a compatibility layer whose names do not match is not
one -- so `Hacl_NaCl_crypto_secretbox_easy`, not a HACL\*-style spelling.
And **`c` and `m` may not alias**: HACL\* permits it, separation logic
forbids it, and every other input/output pair in this library is disjoint
already.  Lengths are `size_t` rather than HACL\*'s `uint32_t`, which makes
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
tagged `[@@@monomorphize]`, and every buffer is a stack allocation whose
width is computed from it.  `nbar`, the width of the small matrices, is a
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
conditional-subtract mask and multiplication with a Barrett step in
sixty-four bits, all branch-free, and the coefficient type is a refinement
--- `zqt = x: S16.t { S16.v x < q }` --- so every intermediate carries its
bound in its type instead of in a lemma.

The correctness statement is that the implementation computes the
algorithms of FIPS 203, coefficient for coefficient, including that the NTT
is the specification's NTT.  What is *not* proved, and is honest to say so,
is the mathematical fact that the specification's NTT is multiplication in
the ring: that is a finite-field argument about roots of unity, not a
memory-safety or refinement argument, and it is future work.  The spec is
pinned instead by the published vectors, which is the same bar the rest of
this repository meets.

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

## Performance

Measured on an AMD EPYC 7662 (Zen 2), gcc 15.2.0 `-O3`, pinned to one core,
three rounds at two link-time code offsets, all three contenders interleaved
inside each round, per-benchmark minimum over the runs whose canary says the
core was healthy (see
[Measuring on a shared machine](#measuring-on-a-shared-machine)).

There are two reference columns, because there are two different questions.

**HACL\*** is HACL\*'s **portable scalar C** -- not its AVX2 or AVX-512
variants -- except for AES-GCM, where HACL\* has no portable implementation at
all and the reference is EverCrypt dispatching to Vale assembly.  This is the
like-for-like comparison: same algorithm, same instruction set, two extraction
pipelines.  It is the column that says anything about Pulse.

**HACL\* best** is HACL\* configured for this machine and allowed everything
it has: EverCrypt's runtime multiplexing onto Vale's SHA-EXT assembly, the
AVX2 ChaCha20 and Poly1305, the vectorized BLAKE2, and the BMI2/ADX
Curve25519.  hacl-pulse has no vectorized or assembly backend, so this column
is not a fair fight and is not meant to be one; it is there to size the gap
that a future vectorization effort would have to close.  It is shown only
where it differs from the scalar reference by more than 3%.

Ratios are hacl-pulse over the reference, so **below 1.00 is faster than the
reference**.

| primitive | size | hacl-pulse | HACL\* | ratio | HACL\* best | ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| SHA-256 | 256 KiB | 227 us | 1,098 us | **0.21x** | 164 us | 1.39x |
| SHA3-256 | 256 KiB | 985 us | 1,839 us | **0.54x** |  |  |
| SHA-512 | 256 KiB | 770 us | 1,364 us | **0.57x** |  |  |
| HMAC-SHA-512 | 256 KiB | 770 us | 1,361 us | **0.57x** |  |  |
| ChaCha20 | 256 KiB | 494 us | 854 us | **0.58x** | 93 us | 5.30x |
| SHAKE128 | 256 KiB | 883 us | 1,489 us | **0.59x** |  |  |
| RSA-2048 modexp | -- | 9.0 ms | 12.9 ms | **0.70x** |  |  |
| ChaCha20-Poly1305 | 256 KiB | 808 us | 1,059 us | **0.76x** | 148 us | 5.46x |
| SHA-1 | 256 KiB | 1,514 us | 1,484 us | **1.02x** |  |  |
| HMAC-SHA-256 | 256 KiB | 1,131 us | 1,102 us | **1.03x** | 163 us | 6.94x |
| BLAKE2s | 256 KiB | 595 us | 572 us | **1.04x** |  |  |
| Salsa20 | 256 KiB | 528 us | 435 us | **1.22x** |  |  |
| NaCl secretbox | 256 KiB | 809 us | 645 us | **1.26x** |  |  |
| X25519 | -- | 55 us | 44 us | **1.26x** | 36 us | 1.52x |
| BLAKE2b | 256 KiB | 395 us | 312 us | **1.27x** | 438 us | 0.90x |
| Poly1305 | 256 KiB | 281 us | 208 us | **1.35x** | 57 us | 4.93x |
| MD5 | 256 KiB | 616 us | 431 us | **1.43x** |  |  |
| RSA-PSS-2048 sign | -- | 9.3 ms | 4.7 ms | **1.98x** |  |  |
| FFDHE-2048 | -- | 9.4 ms | 4.6 ms | **2.04x** |  |  |
| Ed25519 sign | -- | 238 us | 64 us | **3.72x** |  |  |
| AES-128-GCM | 256 KiB | 325 us | 71 us | **4.58x** |  |  |
| P-256 ECDSA verify | -- | 2.4 ms | 426 us | **5.74x** |  |  |
| secp256k1 ECDSA sign | -- | 1,055 us | 65 us | **16.16x** |  |  |

The last two columns say what vector code is worth, and it is worth a great
deal: 5.3x for ChaCha20, 4.9x for Poly1305, 5.5x for ChaCha20-Poly1305, 6.9x
for HMAC-SHA-256 once EverCrypt reaches the SHA-EXT assembly.  Those are the
four places where a portable scalar implementation, however well extracted,
simply cannot compete, and they are the honest ceiling on what the work in
this repository can reach without a vector backend.  Two of the entries go the
other way and are worth recording: HACL\*'s AVX2 BLAKE2b is *slower* than its
own scalar C on this machine (438 us against 312), and every vectorized
primitive loses at 64 bytes, where the setup outweighs the body.  SHA-EXT
beats hacl-pulse's SHA-256 by only 1.39x, which is the narrowest of these
margins, and for a different reason: both sides are already issuing
`sha256rnds2`, so that row is this repository's intrinsics against Vale's
hand-written assembly rather than scalar against vector.

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

**Where it is behind by a factor of two, it is the exponent, not the
arithmetic.**  RSA-PSS and FFDHE use square-and-multiply; HACL\* uses a 4-bit
window.  The generic bignum itself is *faster* than HACL\*'s, which is what
the modexp row shows.

**Where it is behind by more, it is the higher-level algorithm.**  Curve25519
now runs at radix 2^51 like HACL\*'s `_51` with the same straight-line `fmul`,
so the field arithmetic is the same shape, and with the field marked
`CInline` X25519 is within 1.26x -- what is left there is the ladder itself,
which has had no attention.  Ed25519 is further behind because it multiplies
one bit at a time where HACL\* uses a precomputed window.  P-256 and secp256k1
use the shared general Montgomery core rather than the special-prime reductions
those two primes admit, and multiply scalars one bit at a time rather than
through a precomputed window.  These are known,
localized and unstarted; none of them requires new proof technique, only work.

**`inline` is a global resource.**  The whole library is one translation unit,
so `FStar.Attributes.CInline` -- Custard's `static inline` request -- is spent
against gcc's `--param inline-unit-growth` budget for the unit as a whole.
Marking `Hacl.Impl.Bignum256`, the layer every P-256 and secp256k1 operation
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
a second time, less gently.  `Hacl.Impl.Mont256.amul` took its modulus and
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
`Hacl.Impl.Exp256.mexp` above it, which gcc was cloning for the same reason:
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
inlining opportunities elsewhere.  The fix is to say what we mean:
`inline_for_extraction` where a caller's constant matters, and let both
compilers see the same code.

`make clones` reports where we are still relying on the compiler's judgement:
it compiles the distribution with gcc, lists the functions it cloned, and
diffs them against `mk/clones.baseline`.  There are sixty-seven today -- HMAC,
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
256 KiB, twelve times the reference, and is now 325 -- four AES blocks in
flight at a time, four GHASH blocks against the precomputed powers of the hash
key, and a GF(2^128) reduction by shifts rather than by a second multiply.
The remaining 4.5x is against hand-written assembly that interleaves six
blocks and aggregates the GHASH reduction across them, and both of those are
reachable from here.

The benchmark harness and a long write-up of each optimization are kept
outside the repository; the numbers above are reproducible with any AEAD/hash
benchmark that links `dist/Hacl.c` on one side and HACL\*'s `dist/gcc-compatible`
on the other.

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
measured the same way as the rest of this section:

| operation | 512 | 768 | 1024 |
| --- | --- | --- | --- |
| keypair | 77 us | 122 us | 179 us |
| encapsulate | 105 us | 160 us | 232 us |
| decapsulate | 138 us | 205 us | 290 us |

Decapsulation costs more than encapsulation everywhere because it *is*
encapsulation, plus a decryption: the Fujisaki-Okamoto transform
re-encrypts in order to check.  The numbers are a few times what a
hand-optimised reference implementation of Kyber gets on the same class of
machine, and the gap is not in the transform: a large share of every
operation is Keccak, where this library is already ahead of HACL\*'s
portable C, and the rest is the NTT and the rejection sampler, neither of
which has been tuned at all --- the NTT is the specification's seven
layers written out, with a Barrett reduction on every product and no
lazy-reduction or Montgomery-domain tricks.  That is the obvious place to
look first if these ever need to be faster.

## Proof engineering notes

Non-obvious things that cost time here, recorded so they cost less next time:

* **Nonlinear arithmetic is off.**  `n * m >= 0`, `(j+1)*b == j*b + b` and
  `j*b <= n*b` are all *not* automatic, and the failure is usually reported as
  "the SMT query timed out" rather than as an unproved goal.  Reach for
  `FStar.Math.Lemmas.{distributivity_add_left, lemma_mult_le_right,
  multiple_division_lemma, multiple_modulo_lemma, euclidean_division_definition}`
  before reaching for `--z3rlimit`.
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

AES-NI and the carry-less-multiply GHASH both sit under AES-GCM, and the
Intel SHA extensions sit under SHA-256 and SHA-224, each chosen at run time.

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
   line: signing is 4.0x the reference where X25519 is 1.27x, and the whole of
   the difference is HACL\*'s precomputed base-point window against a
   bit-at-a-time double-and-add here.
2. **One GF(2^128) reduction per four GHASH blocks**, accumulating the four
   256-bit products before reducing rather than after.  Needs one new
   specification fact: additivity of `Spec.GF128.Poly.halves`.
3. **Special-prime reduction for P-256 and secp256k1** in place of the shared
   general Montgomery core.
4. **Windowed modular exponentiation** (4-bit) in
   `Hacl.Bignum.Exponentiation`, which is the whole of the RSA-PSS and FFDHE
   gap.
5. **Windowed scalar multiplication** for P-256 and secp256k1, which is most
   of what is left after (3).
6. **Taking over the remaining sixty-seven compiler specialisations**, the
   ones `make clones` lists: HMAC, the SHA-2 cores, the MD5 and SHA-1 blocks,
   ML-KEM.
   Each is a speedup that gcc currently grants us at its own discretion and
   clang does not grant at all.  The SHA-3 sponge and permutation were the
   first, and were worth 2.4x on a short digest; BLAKE2's compression chain
   was the second, and was worth 14% to clang before the unrolled round took
   it further.  Pricing them all at once with
   `-fno-ipa-cp-clone` says the rest are worth nothing measurable, so this is
   a tidying exercise rather than a performance one.  Splitting the
   distribution into several translation units is *not* the fix here -- it
   moves the budget rather than removing the dependency on it, and costs
   inlining across the new boundaries.

   Part of this is a mechanical sweep: a table that never varies should not
   be a parameter at all.  BLAKE2's schedule was the big one and is done, but
   its initialisation vector still is, and so are SHA-2's round constants,
   MD5's two tables and ML-KEM's twiddle factors.  Measured with
   `-fno-ipa-cp`, what is left is SHA-2 6%, MD5 3% and NaCl's secretbox 8% on
   short inputs.  The initialisation vector is the awkward case, because it
   genuinely differs between the two widths and the word type is abstract at
   the point where it would have to be chosen -- that wants either a
   `monomorphize` binder that Custard honours for array arguments or a
   type class carrying the table, and neither exists yet.
