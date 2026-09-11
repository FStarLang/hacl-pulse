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
| `spec/` | pure specifications: `Spec.SHA2`, `Spec.SHA3`, `Spec.Blake2`, `Spec.Chacha20`, `Spec.Poly1305`, `Spec.Curve25519`, `Spec.Ed25519`, their constants and lemmas, `Spec.HMAC`, `Spec.HKDF` |
| `code/` | Pulse implementations, one directory per family (`code/hash/`, `code/chacha/`, `code/poly1305/`, `code/curve25519/`, `code/ed25519/`) |
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
turn one into a slice, and `drop_table` is the counterpart of the `S.to_array`
a stack buffer needs.

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
HMAC of a byte, with no state machine.  The same generalization is what a
streaming interface will be built on.

### HKDF's one scratch buffer

`expand` hashes `T(i-1) || info || i` once per round.  `Hacl.HKDF.Core` lays
that out in a single buffer

```
[ T(i-1) |   info   | i ]
   hb       |info|    1
```

writes `info` into it exactly once, and then each round overwrites only the
leading digest and the trailing counter byte.  Round 1 is the exception --
`T(0)` is empty -- and is handled by hashing the `info || i` *subslice*, using
`Pulse.Lib.Slice.subslice` and giving the permission back with two `join`s.

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
HMAC uses: `absorb_blocks` hands `hash_blocks` a prefix length and a subslice,
and `Spec.SHA2.Streaming.absorb_congr` -- absorbing `n` blocks only looks at
the first `n * bl` bytes, so two messages that agree that far absorb alike --
is what bridges "the bytes in this slice" to "the bytes of `seen`".

`digest` copies the accumulator to the stack and finishes there, so the state
survives: digesting twice gives the same answer, and updating after a digest
continues the same message.  `tests/test_streaming.c` checks both, and checks
the FIPS 180-4 messages fed in nine different chunk sizes chosen to straddle
the block boundary from both sides.

`Hacl.Streaming.SHA2` names the four algorithms and `Hacl.Streaming.SHA2.Ptr`
is the C ABI.  One wart: `total` is a `size_t`, so on a 32-bit target a single
state tops out at four gigabytes.  That follows from using `FStar.SizeT` for
every length (see `design/changes.md`); the one-shot interface has the same
limit, and HACL* does not.

### The sponge

SHA-3 shares almost nothing with SHA-2, so it gets its own stack:
`Spec.SHA3.Constants` (the round constants and rotation offsets),
`Spec.SHA3` (the spec), `Hacl.Hash.SHA3.Core` (Keccak-f[1600]),
`Hacl.Hash.SHA3.Sponge` (absorb and squeeze), `Hacl.Hash.SHA3` (the six named
algorithms) and `Hacl.Hash.SHA3.Ptr` (the C ABI).

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
wrappers.  The state is a 25-lane `S.slice S64.t` indexed `x + 5*y`, matching
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
the copy, so the real state is untouched.  That is what lets a SHAKE state be
squeezed at 16 bytes and then at 200 and get the same stream twice, and lets
an `update` after a `digest` carry on with the same message.
`tests/test_sha3_streaming.c` checks all three, plus the FIPS 202 messages fed
in nineteen chunk sizes that straddle every one of the five rates from both
sides.

One copy of the code serves all six algorithms, since the rate and the
domain-separation byte are ordinary runtime arguments; `Hacl.Streaming.SHA3`
names the six and `Hacl.Streaming.SHA3.Ptr` is the C ABI.  The cost is that
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

**A point is four slices, not a record.**  Extended coordinates `(x, y, z,
t)` are passed as four separate 16-limb slices side by side, because a
struct of slices would need its own separation discipline and Custard would
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
* **A `while` invariant must carry the non-`pts_to` resources too.**  A slice
  obtained from a stack array owns an `is_from_array`; leaving it out of an
  invariant (or out of an explicit `if ... ensures`) fails with "leftover
  resources" at the end of the function, far from the cause.
* **A `decreases` expression has to be a `nat` at every iteration.**  A loop
  that advances by a fixed stride past a limit cannot measure `limit - i`;
  measure the iteration count instead.  The symptom is a timeout on
  `... << meas`, which looks like a crowding problem and is not.
* **Split, do not raise the rlimit.**  Every "the SMT query timed out" in
  `update_impl` was on a goal like `nb + 1 <= |seen| + |data|`.  Moving the
  block-full case out into `update_full` made all of them go away at once; no
  amount of rlimit would have.
* **A unit is a whole program.**  Two extracted units each contain everything
  their entry points reach, and each defines it, so they cannot be linked into
  one binary.  One test binary per unit.
* **Mark big `Seq.init` definitions `opaque_to_smt`.**  A spec function that
  builds a 25-element sequence is, unfolded, 25 copies of its body in every
  query that mentions it.  Make it opaque and give it an index lemma that
  `reveal_opaque`s it; that one change is what made Keccak provable.
* **A trailing `Seq.lemma_eq_elim` does not discharge a Pulse `ensures`.**  The
  idiom that works is to name the witness and assert the goal:
  `with v. assert (S.pts_to x v); assert (pure (reveal v \`Seq.equal\` rhs));`.
  More generally, a lemma call whose conclusion the postcondition needs must be
  followed by an `assert (pure ...)` restating that conclusion.
* **`let ... in` is a syntax error inside a Pulse block**, and so is
  `let ghost x = ...`.  A lemma that wants a local definition has to be hoisted
  to module level — which is why `squeeze_bytes_eq` and `squeeze_range_eq` live
  in `Spec.SHA3` rather than next to the loop that uses them.
* **Bind the initial value of a stack array first.**
  `let mut a = [| S8.classify 0uy; 200sz |]` gives the array the *refined*
  element type `x:S8.t{S8.v x == 0}`, and the slice taken from it then fails to
  match `S.slice S8.t` with an unreadable error.  `let z8 = S8.classify 0uy;`
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
* **`unfold S.subslice_rest` is ambiguous when two subslices are live.**
  `subslice_rest` is a plain `let`, so it can be unfolded at explicit
  arguments: `unfold (S.subslice_rest tail buf 1.0R 0sz blen vbuf);`.  Full
  permission is written `1.0R`.
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
  of the global that reads it, so no unit here emits that function at all.
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
  ...  Inline the body instead; that is why `Hacl.Chacha20.Ptr.decrypt`
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
* **`Pulse.Lib.Slice.len` shadows a parameter named `len`** inside an
  `S.(...)` block, and the error is the baffling "Expected expression of type
  `FStar.SizeT.t`, got `Pulse.Lib.Slice.len`".
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

## Roadmap

Following `design/reimplementation.md` §9, in dependency order: P-256, then
the DRBG.  Curve25519 and Ed25519 are done.
