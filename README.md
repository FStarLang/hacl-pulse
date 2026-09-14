# hacl-pulse

A reimplementation of [HACL\*](https://github.com/hacl-star/hacl-star) in
modern F\*/Pulse, extracted straight to C by
[Custard](https://github.com/FStarLang/FStar/blob/gebner_custard/doc/ref/custard.md).

The goal is feature parity with HACL\*'s C and F\* APIs.  The design is not a
port: where HACL\* had to work around the absence of a language feature, this
library uses the feature.  `design/` records what HACL\* does and
`design/changes.md` the four commitments this reimplementation starts from.

Status: the SHA-2 family (SHA-224/256/384/512) one-shot and incremental, HMAC
over it, HKDF over that, and the SHA-3 family (SHA3-224/256/384/512 and
SHAKE128/256) one-shot and incremental, are specified, implemented, verified,
extracted, and tested against the FIPS 180-4, FIPS 202, RFC 4231 and RFC 5869
vectors.  BLAKE2b and BLAKE2s are specified, implemented, verified, extracted
and tested at all eight standard digest lengths, keyed and unkeyed.

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
| `lib/` | the secret-integer layer, the `word` type class, generic byte serialization, compile-time tables |
| `spec/` | pure specifications: `Spec.SHA2`, `Spec.SHA3`, `Spec.Blake2`, `Spec.Chacha20`, `Spec.Poly1305`, `Spec.Curve25519`, `Spec.Ed25519`, `Spec.P256`, `Spec.AES`, `Spec.GF128`, `Spec.GCM`, their constants and lemmas, `Spec.HMAC`, `Spec.HKDF`, `Spec.HMAC_DRBG` |
| `code/` | Pulse implementations, one directory per family (`code/hash/`, `code/chacha/`, `code/poly1305/`, `code/curve25519/`, `code/ed25519/`, `code/p256/`, `code/drbg/`, `code/aes/`) |
| `c/` | handwritten C, and the whole of the trusted computing base on the C side: currently the platform entropy shim |
| `tests/` | C test harnesses |
| `dist/` | generated C: one `Hacl.c`, one `Hacl.h` |
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

### Curve25519, sixteen limbs because there is no `uint128`

Every fast X25519 in existence represents a field element in radix 2^51,
five limbs, because the product of two limbs fits in a 128-bit integer.
Custard's builtins are `FStar.UInt8/16/32/64`, `FStar.Int8/16/32/64` and
`FStar.SizeT`; there is no `FStar.UInt128`, and unlike karamel there is no
compiler-side emulation of one.  Radix 2^51 is therefore not available.

So this implementation uses **sixteen limbs of sixteen bits** in
`Hacl.Secret.UInt64.t`.  A limb product is at most `(2^17)^2 = 2^34`, and a
column of the schoolbook product accumulates sixteen of them plus carries,
which is comfortably inside 64 bits -- no intermediate reduction inside
`mul_columns` at all, which is what makes the proof tractable.  The price is
256 word multiplies per `fmul` against 25 for HACL*'s `_51`, so this is an
order of magnitude slower than the C fast path; a scalar multiplication runs
in roughly 470 microseconds here.  That is honest arithmetic, not a
competitive one, and the reduction `2^256 = 2 * prime + 38` is done once at
the end of `fmul` rather than woven through it.

**Inversion is an addition chain, not square-and-multiply.**  `x^(p-2)` by
scanning the 255 bits of `p-2` would need a lemma about every one of those
bits; the classical chain needs only `fexp_add` and `fexp_mul`, applied to
`x^2, x^8, x^9, x^11, x^22` and then the runs `E5, E10, E20, E40, E50, E100,
E200, E250`.  It is expressed as three in-place moves -- `a := a^2`,
`a := a*b`, `a := a^(2^n)` -- each implemented by copying into scratch and
calling the out-of-place `fmul`.  A sixteen-word copy against 256 multiplies
is not worth avoiding.

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
`Hacl.Curve25519.Field` unchanged -- the same sixteen limbs of sixteen bits,
the same `fmul`, the same inversion chain.  Nothing in the signature scheme
needed a second field implementation, which is the main reason the whole of
`code/ed25519` is six modules.

**A point is four arrays, not a record.**  Extended coordinates `(x, y, z,
t)` are passed as four separate 16-limb arrays side by side, because a
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
form over sixteen 16-bit limbs by one shared `Hacl.P256.Mont`:
`Spec.Bignum256` fixes the representation, `mont_mul` does
Coarsely-Integrated Operand Scanning, and `Hacl.P256.Field` and
`Hacl.P256.Scalar` are two instantiations that never meet.

**Keeping them apart is a performance decision, not a taste one.**  The field
modulus `p` and the order `q` are both 78-digit literals, and a goal that
mentions both takes minutes.  So `code/p256` is twenty modules: the on-curve
test and the scalar reduction never appear in the same verification context,
and `Hacl.P256.Key` (private keys, the scalar field) and
`Hacl.P256.Key.Public` (public keys, the field) are separate files for no
other reason.

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

GHASH is the literal 128-step algorithm 1 of SP 800-38D, with both branches of
each step turned into a mask rather than taken.  A field multiplication is
about a hundred instructions per bit of input; the result is roughly a
megabyte a second.  That is slow, and deliberately so: carry-less multiply
(`PCLMULQDQ`, `PMULL`) is the real answer on hardware that has it and is the
documented upgrade path, as bitslicing is for the cipher.  A correct, portable
and constant-time implementation comes first.

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


### The generic bignum, where the length is a run-time value

Everything above works at a fixed width.  RSA and finite-field
Diffie-Hellman do not: the modulus is whatever the key says it is.
`code/bignum/` is arithmetic on arrays of `uint32_t` limbs, least
significant first, with the limb count passed in.

**The radix is 2^32.**  It is the widest radix for which a
multiply-accumulate is exact in a double word: `(2^32-1)^2 + 2*(2^32-1)` is
`2^64-1`, using every bit and no more.  Custard has no `uint128`, so 2^64 is
not available, and 2^16 -- what Curve25519 and P-256 use -- would double the
memory and the loop counts for no gain, because those two want room to
accumulate a whole product before carrying and this does not.  It also
happens to be the limb type of HACL*'s `Hacl_Bignum32`.

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

    uint32_t Hacl_Bignum_Base_add    (uint32_t *res, uint32_t *a, uint32_t *b, size_t n);
    uint32_t Hacl_Bignum_Base_sub    (uint32_t *res, uint32_t *a, uint32_t *b, size_t n);
    void     Hacl_Bignum_Base_add_mod(uint32_t *res, uint32_t *a, uint32_t *b,
                                      uint32_t *m, size_t n);
    void     Hacl_Bignum_Base_sub_mod(uint32_t *res, uint32_t *a, uint32_t *b,
                                      uint32_t *m, size_t n);
    void     Hacl_Bignum_Base_mul    (uint32_t *res, uint32_t *a, uint32_t *b, size_t n);
    void     Hacl_Bignum_Base_sqr    (uint32_t *res, uint32_t *a, size_t n);
    uint32_t Hacl_Bignum_Base_lt_mask(uint32_t *a, uint32_t *b, size_t n);
    uint32_t Hacl_Bignum_Base_eq_mask(uint32_t *a, uint32_t *b, size_t n);
    void     Hacl_Bignum_Base_zero   (uint32_t *res, size_t n);

`add` and `sub` return the carry or borrow; `mul` and `sqr` write `2n`
limbs; `add_mod` and `sub_mod` require their inputs already reduced, as
HACL* does.  The two comparisons return an all-ones or all-zero mask and
look at every limb whatever the answer is.

Conversion is four functions, both byte orders both ways:

    void Hacl_Bignum_Convert_from_bytes_be(uint32_t *res, size_t n, uint8_t *b);
    void Hacl_Bignum_Convert_from_bytes_le(uint32_t *res, size_t n, uint8_t *b);
    void Hacl_Bignum_Convert_to_bytes_be  (uint8_t *b, uint32_t *a, size_t n);
    void Hacl_Bignum_Convert_to_bytes_le  (uint8_t *b, uint32_t *a, size_t n);

each on exactly `4n` bytes.  HACL* takes a byte count and left-pads to a
whole number of limbs; here that rounding is the caller's, who has to own a
buffer of the right size anyway, and no key length in any standard this
library implements fails to be a multiple of four.

`tests/test_bignum.c` checks all of it against values computed in Python,
which shares no code with the implementation.

### Montgomery arithmetic

Reducing modulo an arbitrary `n` costs a trial division per limb.
Montgomery's observation is that if you carry `a * R mod n` instead of `a`,
where `R` is `2^(32n)` -- a power of the radix, so that dividing by it is
dropping limbs -- the reduction becomes a multiply and a shift.
`code/bignum/Hacl.Bignum.Montgomery.fst` is that.

    uint32_t Hacl_Bignum_Montgomery_mont_mu (uint32_t m0);
    void Hacl_Bignum_Montgomery_precomp     (uint32_t *res, uint32_t *n, size_t nn);
    void Hacl_Bignum_Montgomery_reduction   (uint32_t *res, uint32_t *c,
                                             uint32_t *n, size_t nn, uint32_t mu);
    void Hacl_Bignum_Montgomery_mont_mul    (uint32_t *res, uint32_t *a, uint32_t *b,
                                             uint32_t *tmp, uint32_t *n, size_t nn,
                                             uint32_t mu);
    void Hacl_Bignum_Montgomery_from_mont   (uint32_t *res, uint32_t *a,
                                             uint32_t *tmp, uint32_t *n, size_t nn,
                                             uint32_t mu);
    void Hacl_Bignum_Montgomery_modulo      (uint32_t *res, uint32_t *a, uint32_t *acc,
                                             uint32_t *r2, uint32_t *n, size_t nn,
                                             uint32_t mu);

`mu` is a single limb with `mu * m0 + 1 = 0 mod 2^32`, `m0` being the lowest
limb of the modulus; it exists exactly when the modulus is odd.  HACL*
computes it with a thirty-two iteration bit loop.  Here it is five steps of
Hensel lifting from one, `x := x * (2 - m0 * x)`, which doubles the number
of correct bits each time: one, two, four, eight, sixteen, thirty-two.
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
        uint32_t *res, uint32_t *a, uint32_t *bb, size_t bbits,
        uint32_t *r2, uint32_t *n, size_t nn, uint32_t mu,
        uint32_t *aM, uint32_t *acc, uint32_t *t, uint32_t *wide);
    void Hacl_Bignum_Exponentiation_mod_exp_vartime(/* the same arguments */);
    void Hacl_Bignum_Exponentiation_mod_inv_prime_vartime(
        uint32_t *res, uint32_t *a, uint32_t *r2, uint32_t *n,
        size_t nn, uint32_t mu, uint32_t *e,
        uint32_t *aM, uint32_t *acc, uint32_t *t, uint32_t *wide);

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
group, that limb `0` and the top limb are both `2^32 - 1`.  The first says
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

## Roadmap

Following `design/reimplementation.md` §9, the minimum viable subset is
complete: the hashes and their streaming layers, HMAC one-shot and
incremental, HKDF, ChaCha20-Poly1305, X25519, Ed25519, P-256, HMAC-DRBG with
an OS entropy shim, and AES-GCM.  Past it, the generic bignum has its
arithmetic, its conversions, its Montgomery layer and its modular
exponentiation -- both ladders and Fermat inversion -- and on top of those
the five RFC 7919 finite-field Diffie-Hellman groups and PKCS#1 v2.2
RSA-PSS signing and verification.

Beyond the subset, in rough order of how often they are asked for: AES-NI and
carry-less-multiply intrinsics under the portable AES-GCM, secp256k1,
Salsa20/NaCl, FrodoKEM, and the legacy hashes.
