# The F\* API: memory model, effects, and contracts

HACL\*/EverCrypt has **two** public APIs, not one:

- the **C API**, documented in the `api-*.md` chapters — a set of `extern`
  declarations with contracts that live only in comments and in this
  documentation;
- the **F\* API**, documented in this chapter and the `fstar-api-*.md`
  chapters — a set of `val` declarations whose contracts are *machine-checked*,
  and against which a verified client can prove its own theorems.

For a C client, "the API" is a name and a signature. For an F\* client, the API
*is* the pre/post-condition: a verified caller cannot compile without
discharging the preconditions, and gets the postcondition as a usable fact.
This is the difference that makes statements like

```fstar
decrypt k n aad (encrypt k n aad p) == Some p
```

available to a client rather than merely believed by one. That specific theorem
is `Spec.Agile.AEAD.correctness` (`specs/Spec.Agile.AEAD.fsti:125-126`); see
[fstar-specs.md](fstar-specs.md) for the full catalogue and
[fstar-api-aead-ciphers.md](fstar-api-aead-ciphers.md) for how to lift it to
the stateful level.

This chapter covers the shared vocabulary. The per-family chapters assume it.

| Chapter | Covers |
|---|---|
| [fstar-specs.md](fstar-specs.md) | The pure spec layer and the theorems it exports |
| [fstar-api-hashes-macs.md](fstar-api-hashes-macs.md) | Hashes, the streaming functor, HMAC, HKDF, Poly1305 |
| [fstar-api-aead-ciphers.md](fstar-api-aead-ciphers.md) | AEAD, ciphers, NaCl |
| [fstar-api-curves-bignum.md](fstar-api-curves-bignum.md) | Curves, signatures, bignum, RSA-PSS, FFDHE |
| [fstar-api-provider.md](fstar-api-provider.md) | AutoConfig2, TargetConfig, Vale interop, randomness, DRBG, HPKE, Frodo |
| [fstar-client-guide.md](fstar-client-guide.md) | Worked examples, proof idioms, pitfalls, build setup |

---

## 1. Why the `.fsti` files are the real documentation

`providers/Documentation.md` says it directly:

> Our C code is generated; as such, some information is lost in the translation
> process. Instead of looking at C header files, we strongly advise prospective
> users to read the original F\* interface files (`.fsti`). These have the most
> up-to-date comments, as well as a wealth of information regarding
> preconditions, such as length of arrays, disjointness, etc. that C clients
> MUST obey.

Everything a C client must obey *by discipline* is written down formally in the
`.fsti` and checked *by the compiler* for an F\* client. The mapping is
mechanical: a function declared in `Foo.Bar.fsti` is emitted as `Foo_Bar_baz`.

There is one further asymmetry worth stating up front, because it recurs
throughout: **some usage protocols are enforced only for verified clients.**
`EverCrypt.AEAD.fsti` opens with

> The expected usage for this module is as follows:
> - client expands key, obtaining an `expanded_key a`
> - client uses `encrypt`/`decrypt` with the same `expanded_key a` repeatedly.
>
> This usage protocol is enforced for verified F\* clients but, naturally,
> isn't for C clients.

---

## 2. The memory model

### 2.1 HyperStack

Low\* programs manipulate `FStar.HyperStack.mem`, a *region-based* model of
memory. Regions form a tree; some are stack frames, some are "eternal" (heap)
regions that outlive any particular frame. The pieces a client meets:

| Name | Meaning |
|---|---|
| `HS.mem` | A whole memory snapshot. Pre/postconditions are predicates over `h0`, `h1 : HS.mem`. |
| `HS.rid` | A region identifier. |
| `ST.is_eternal_region r` | `r` is a heap region — a precondition of every `create_in`-style allocator. |
| `HS.get_tip h` | The current stack frame in `h`. |
| `ST.push_frame ()` / `ST.pop_frame ()` | Open/close a stack frame; extract to C scoping. |

The client-visible consequence: **allocation functions take the region they
allocate into**, so the client controls lifetime and can prove disjointness
from its own data.

```fstar
let create_in_st (a: alg) =
  r:HS.rid ->
  dst:B.pointer (B.pointer_or_null (state_s a)) ->
  k:B.buffer uint8 { B.length k = key_length a } ->
  ST error_code
    (requires fun h0 ->
      ST.is_eternal_region r /\
      B.live h0 k /\ B.live h0 dst)
    ...
```
<sub>`providers/evercrypt/EverCrypt.AEAD.fsti:148-158`</sub>

### 2.2 Locations and `modifies`

Framing — knowing that a call did *not* disturb your data — is done with
`LowStar.Buffer` locations:

| Construct | Meaning |
|---|---|
| `B.loc` | An abstract set of memory locations. |
| `B.loc_buffer b`, `B.loc_addr_of_buffer b`, `B.loc_region_only b r`, `B.loc_none` | Ways to build a `loc`. |
| `B.loc_union`, `B.loc_includes`, `B.loc_disjoint` | Set algebra over locations. |
| `B.modifies l h0 h1` | Going from `h0` to `h1`, only `l` changed. |
| `B.fresh_loc l h0 h1` | `l` was not allocated in `h0` and is in `h1`. |
| `B.live h b`, `B.freeable b` | Liveness; the buffer is heap-allocated and can be freed. |

Every stateful `val` in the library has a `modifies` clause in its
postcondition. That clause is the client's framing tool: anything disjoint from
it is provably unchanged.

### 2.3 Two buffer dialects

The codebase uses **two** buffer libraries, and a client must be able to move
between them.

- `LowStar.Buffer` (from F\*'s ulib), abbreviated `B`. Used by EverCrypt
  interfaces. `B.buffer a`, `B.length`, `B.as_seq h b`, `B.live`, `B.disjoint`.
- `Lib.Buffer` (from `lib/`), used by HACL\* interfaces. Length is carried *in
  the type*:

```fstar
type buftype =
  | MUT
  | IMMUT
  | CONST

inline_for_extraction
let lbuffer_t (t:buftype) (a:Type0) (len:size_t) =
  b:buffer_t t a{length #t #a b == v len}

unfold let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
unfold let ilbuffer (a:Type0) (len:size_t) = lbuffer_t IMMUT a len
unfold let clbuffer (a:Type0) (len:size_t) = lbuffer_t CONST a len
unfold let glbuffer (a:Type0) (len:size_t) = c:clbuffer a len{CB.qual_of #a c == CB.IMMUTABLE}
```
<sub>`lib/Lib.Buffer.fsti:20-72`</sub>

`Lib.Buffer` also provides `modifies0`…`modifies6` as conveniences for "this
call modified exactly these *n* buffers", and `loc`, `live`, `disjoint`,
`as_seq` mirroring the ulib names. Under the hood `Lib.Buffer.modifies` is
literally `B.modifies` (`lib/Lib.Buffer.fsti:140`), so the two dialects
interoperate — but the *type* `lbuffer uint8 32ul` is not syntactically
`B.buffer uint8`, and clients must coerce.

Why two? The comment in `EverCrypt.Curve25519.fsti` explains:

> We can't re-export this signature with a standard ulib type because of secret
> integers. So, for now, the type is done using HACL\* types.

`Lib.IntTypes` secret integers (`uint8` = `int_t U8 SEC`) are not
`FStar.UInt8.t`, so an interface that mentions secret bytes cannot use plain
ulib buffer types. The practical rule: **EverCrypt interfaces are mostly
`LowStar.Buffer`-flavoured, HACL\* interfaces are `Lib.Buffer`-flavoured, and
`EverCrypt.Curve25519` is an EverCrypt module that uses HACL\* types.** A
reimplementation should pick *one* dialect.

### 2.4 Secret vs public integers

`Lib.IntTypes` indexes machine integers by width *and* secrecy
(`SEC`/`PUB`). Secret integers support arithmetic and bitwise operations but
**not** comparison, division, modulus, or use as an index or branch condition.
`Lib.RawIntTypes` provides the explicit, auditable declassification functions.

For a client this means the type system will stop you from writing
`if secret_byte = 0uy then ...`. It also means secrecy is visible in
signatures: `lbuffer uint8 32ul` is a buffer of *secret* bytes, and mixing it
with a public-byte buffer requires an explicit coercion.

See [fstar-specs.md](fstar-specs.md) §2 for the spec-level counterparts
(`Lib.Sequence.lseq`, `Lib.ByteSequence.lbytes`).

---

## 3. Effects

| Effect | Meaning for a client |
|---|---|
| `Tot` / pure | Total function, no memory. Specs live here. |
| `GTot` / `Ghost` | Proof-only; erased at extraction. Ghost accessors (`as_seq`, `footprint`, `as_kv`, `seen`) live here — you may mention them in your own specs but never compute with them at runtime. |
| `Stack` | Stateful, may allocate only in the current frame; the frame is unchanged on exit. Extracts to a plain C function. Most one-shot crypto operations. |
| `StackInline` | Like `Stack`, but the result may live in the *caller's* frame — used by `alloca`-style allocators, which must be inlined into the caller. |
| `ST` | Stateful, may allocate in eternal (heap) regions. Used by `create_in`/`malloc`-style allocators and by anything that frees. |

Two consequences a client feels immediately:

- **`Stack` is a stronger contract than `ST`.** Library functions are given the
  weakest effect that suffices, so a `Stack` function can be called from a
  wider range of contexts. This is why `EverCrypt.AEAD` provides `alloca`
  (`StackInline`) alongside `create_in` (`ST`) — the comment says it exists "so
  that it is possible to use AES GCM while staying in the `Stack` effect"
  (`EverCrypt.AEAD.fsti:176-179`).
- **Ghost values cost nothing.** `G.erased alg`, `GTot B.loc`, ghost sequences
  — none of these exist at run time. This is what makes it affordable for the
  API to carry rich specification state such as `seen` (the entire history of
  bytes fed into a streaming state).

---

## 4. Anatomy of a `val`

A representative HACL\*-style signature, with everything a client needs:

```fstar
inline_for_extraction noextract
let scalarmult_st (s:field_spec) (p: Type0) =
    o:lbuffer uint8 32ul
  -> k:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      p /\
      live h0 o /\ live h0 k /\ live h0 i /\
      disjoint o i /\ disjoint o k)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.scalarmult (as_seq h0 k) (as_seq h0 i))
```
<sub>`code/curve25519/Hacl.Impl.Curve25519.Generic.fsti:13-23`</sub>

Read it in five parts:

1. **Lengths are in the types.** `lbuffer uint8 32ul` — there is no separate
   length argument to get wrong, and no length precondition to state.
2. **Liveness.** `live h0 o /\ live h0 k /\ live h0 i`.
3. **Disjointness.** `disjoint o i /\ disjoint o k`. Note what is *absent*:
   `k` and `i` are not required to be disjoint from each other, because both
   are read-only. The disjointness requirements are exactly the ones needed,
   not a blanket "all buffers distinct" — which is why reading the `.fsti` is
   strictly more informative than assuming.
4. **Framing.** `modifies (loc o) h0 h1` — the *only* thing that changed is the
   output buffer.
5. **Functional correctness.** `as_seq h1 o == S.scalarmult (as_seq h0 k) (as_seq h0 i)`
   — the contents of the output, viewed as a pure sequence, are *equal* to the
   spec applied to the pure views of the inputs. This is the universal shape:
   **`as_seq (result) == Spec.f (as_seq (arguments))`**, with `as_seq` the
   ghost bridge from stateful memory to pure specification.

Notice also that the signature is a *type abbreviation* parameterized by an
index `s:field_spec` and a proposition `p:Type0`. Concrete modules instantiate
it:

```fstar
val scalarmult: scalarmult_st M51 True        (* Hacl.Curve25519_51.fsti:11 *)
```

```fstar
let p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)
val scalarmult: scalarmult_st M64 p           (* Hacl.Curve25519_64.fsti:7,14 *)
```

This is the third key idea, and it deserves its own section.

---

## 5. Preconditions as propositions: CPU features in the type system

`Hacl.Curve25519_64.scalarmult` cannot be called unless the caller can *prove*
`adx_enabled /\ bmi2_enabled`. Those are not runtime booleans; they are pure
propositions describing the machine, declared in
`vale/specs/hardware/Vale.X64.CPU_Features_s.fst`.

A client obtains such a proof by *calling a detection function whose
postcondition is an implication*:

```fstar
unfold
inline_for_extraction noextract
let getter (flag: bool) = unit -> Stack bool
  (requires (fun _ -> true))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> flag)))

val has_adx: getter Vale.X64.CPU_Features_s.adx_enabled
val has_bmi2: getter Vale.X64.CPU_Features_s.bmi2_enabled
```
<sub>`providers/evercrypt/EverCrypt.AutoConfig2.fsti:19-33`</sub>

So:

```fstar
let adx = EverCrypt.AutoConfig2.has_adx () in
let bmi2 = EverCrypt.AutoConfig2.has_bmi2 () in
if adx && bmi2 then
  Hacl.Curve25519_64.scalarmult out priv pub   (* precondition discharged here *)
else
  Hacl.Curve25519_51.scalarmult out priv pub
```

Inside the `then` branch, F\* knows `adx = true`, hence `adx_enabled`, which is
exactly the precondition. The implication is deliberately **one-directional**:
`b ==> flag`, not `b <==> flag`. A `false` result tells you nothing (the
feature may exist but be disabled via `disable_adx`), which is sound — you
merely take the slower path.

The same idiom carries compile-time configuration, via
`EverCrypt.TargetConfig` booleans marked `[@@ CIfDef ]` so KaRaMeL renders them
as `#if`. See [fstar-api-provider.md](fstar-api-provider.md) §2 for the
ordering constraint (`hacl_can_compile_vec128 && has_vec128 ()`) and why
getting it wrong breaks the link step.

### Multiplexed frontends have *weaker* preconditions

This is the payoff of the whole EverCrypt design, and it is visible in the
types. Compare:

| Function | Precondition |
|---|---|
| `Hacl.Curve25519_51.scalarmult` | `True` |
| `Hacl.Curve25519_64.scalarmult` | `adx_enabled /\ bmi2_enabled` |
| `EverCrypt.Curve25519.scalarmult` | *(no CPU precondition at all)* |

```fstar
val scalarmult:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 _ h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == Spec.Curve25519.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub))
```
<sub>`providers/evercrypt/EverCrypt.Curve25519.fsti:35-46`</sub>

Same postcondition, no feature obligation: EverCrypt discharges it internally
by doing the detection for you. **Multiplexing, expressed in types, is
precondition weakening with the postcondition preserved.** That is a clean,
language-independent design idea worth carrying into any reimplementation.

Note that some EverCrypt entry points deliberately keep the precondition and
skip the check — those are the ones extracted as `_no_check` in C (see
[fstar-api-aead-ciphers.md](fstar-api-aead-ciphers.md) §4).

---

## 6. The stateful abstraction pattern

Every object with mutable state in this library — AEAD keys, hash states, DRBG
states — follows one pattern. Learn it once and every module reads the same.
`EverCrypt.AEAD` is the canonical instance
(`providers/evercrypt/EverCrypt.AEAD.fsti:44-144`); the streaming functor is
the most elaborate one.

### 6.1 The pieces

```fstar
[@@ CAbstractStruct; Comment "..."]
val state_s: alg -> Type0

inline_for_extraction noextract
let state alg = B.pointer (state_s alg)
```

- **`state_s`** is abstract: clients know nothing about the representation.
  `[@@ CAbstractStruct]` is what makes KaRaMeL emit an *incomplete* struct type
  in C, so C clients are equally unable to inspect it.
- **`state`** is a pointer to it. Handing out a pointer (rather than the struct)
  is what allows the state to be reallocated/updated in place.

```fstar
val footprint_s: #a:alg -> state_s a -> GTot B.loc
let footprint (#a:alg) (m: HS.mem) (s: state a) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))
```

- **`footprint`** is the ghost set of memory the state owns. A client uses it
  to state disjointness from its own buffers.

```fstar
inline_for_extraction noextract
val invariant_s: (#a:alg) -> HS.mem -> state_s a -> Type0

inline_for_extraction noextract
let invariant (#a:alg) (m: HS.mem) (s: state a) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s m (B.get m s 0)
```

- **`invariant h s`** is the "this state is well-formed in memory `h`"
  predicate. It is a precondition of every operation and re-established by
  every operation. Clients never unfold it; they only carry it around.

```fstar
val freeable_s: #(a: alg) -> state_s a -> Type0
let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)
let preserves_freeable #a (s: state a) (h0 h1: HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s
```

- **`freeable`** distinguishes heap-allocated states (which may be `free`d)
  from stack-allocated ones (which may not). `preserves_freeable` appears in
  postconditions so the property survives across calls.

- **Ghost accessor(s)** expose the logical contents. For AEAD it is the key:

```fstar
val as_kv: (#a: alg) -> state_s a -> GTot (kv a)
```

  For a streaming state it is `seen` (everything fed so far) plus `reveal_key`.
  This is the bridge to the pure spec, playing the role `as_seq` plays for
  plain buffers.

### 6.2 The framing lemmas

Two lemmas make the pattern usable, and both carry SMT patterns so they fire
automatically:

```fstar
val invariant_loc_in_footprint
  (#a: alg) (s: state a) (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

val frame_invariant: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]
```
<sub>`providers/evercrypt/EverCrypt.AEAD.fsti:105-125`</sub>

`frame_invariant` is the workhorse: *if you modify something disjoint from the
state's footprint, the state is still valid and its footprint is unchanged.*
Without it, a client could not do anything between two crypto calls. With the
SMT pattern, the client usually does not have to invoke it explicitly.

There is also a hand-written pattern-management lemma:

```fstar
let loc_includes_union_l_footprint_s
  (l1 l2: B.loc) (#a: alg) (s: state_s a)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s s) \/ B.loc_includes l2 (footprint_s s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s s))]
```
<sub>`providers/evercrypt/EverCrypt.AEAD.fsti:74-83`</sub>

whose accompanying comment explains it exists purely to keep SMT from blowing
up on nested `loc_union`s. This is proof-engineering plumbing, not semantics —
the kind of thing a reimplementation in another language simply would not have.

### 6.3 The lifecycle contract

| Operation | Effect | Contract sketch |
|---|---|---|
| `create_in r dst k` | `ST` | requires `is_eternal_region r`; ensures fresh footprint inside `r`, `invariant`, `freeable`, and `as_kv (deref h1 s) == as_seq h0 k` |
| `alloca k` | `StackInline` | same but in the caller's frame; `modifies loc_none`; not `freeable` |
| operations | `Stack` | require `invariant h0 s` and disjointness; ensure `invariant h1 s`, `footprint h0 s == footprint h1 s`, `preserves_freeable`, plus the functional postcondition |
| `free s` | `ST` | requires `invariant` and `freeable`; ensures `modifies (footprint h0 s) h0 h1` |

Note the recurring `footprint h0 s == footprint h1 s`: operations never grow or
move the state. That is what lets a client establish disjointness once and
rely on it for the rest of the program.

---

## 7. Index and erased arguments

Two argument kinds appear in signatures but not in the C prototype:

- **Implicit/erased indices.** `#a:G.erased alg` — the algorithm is known
  statically to the proof but carried at runtime only where necessary. In
  `EverCrypt.AEAD`, `encrypt` takes `#a:G.erased (supported_alg)` while
  `alg_of_state` *recovers* the algorithm at runtime from the state
  (`val alg_of_state (a: G.erased alg) (s: state (G.reveal a)): Stack alg`).
- **Proposition parameters.** The `p: Type0` in `scalarmult_st s p` (§5).

For a reimplementer: erased arguments are the reason the F\* signature and the
C prototype have different arities. Do not expect a 1:1 correspondence.

---

## 8. Refinement types replace runtime checks

Where a C client must remember "the modulus must be odd" or "`ad_len <= 2^31`",
the F\* client gets a refinement:

```fstar
ad:ad_p a ->
ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
```

and cannot call the function without proving it. Note the idiom
`len:UInt32.t { v len = B.length b }`: because `LowStar.Buffer` does not carry
its length in the type (unlike `Lib.Buffer`), EverCrypt signatures *tie* the
runtime length argument to the ghost buffer length with a refinement. That
redundancy is exactly the class of bug ("passed the wrong length") that the C
API cannot rule out.

This is the single most valuable thing to carry into a reimplementation: in a
language with length-carrying slices, most of these refinements become free.

---

## 9. Building a verified client

An F\* client needs `.checked` files and include paths, not just headers.

- **Include paths.** `Makefile.include` exports `ALL_HACL_SOURCE_DIRS`
  (`LIB_DIR`, `SPECS_DIR`, `CODE_DIRS`, `EVERCRYPT_DIRS`, `VALE_DIRS`, plus
  `$(KRML_HOME)/runtime`) precisely so client projects can include it. The same
  list is mirrored in `Hacl.fst.config.json` for the VS Code extension —
  the file comments ask that the two be kept in sync.
- **F\* flags** used by this repo (`Makefile.common`, `Hacl.fst.config.json`):
  `--cmi`, `--use_hints --use_hint_hashes --record_hints`, `--hint_dir hints`,
  `--already_cached 'Prims FStar LowStar C Spec.Loops TestLib WasmSupport'`,
  `--z3version 4.8.5`, and a specific `--warn_error` string. A client that
  wants reproducible verification should match the Z3 version.
- **KaRaMeL flags.** `Makefile.include` exports `VALE_BUNDLES` so a client
  extracting its own code can successfully bundle the Vale interop modules.
- **Hints.** `hints/` contains one `.hints` file per source module. They are
  proof-replay data, not part of the trusted base, but they make verification
  fast and deterministic.

See [fstar-client-guide.md](fstar-client-guide.md) for a worked setup.

---

## 10. Notes for reimplementers

What of this survives a port to a non-F\* language?

| F\* mechanism | Portable counterpart |
|---|---|
| Pure spec + `as_seq` bridge | An executable reference implementation plus a "view" function; the basis of differential testing |
| `requires`/`ensures` | Documented contracts, runtime `assert`s in debug builds, or a refinement/contract system if available |
| Length-in-type (`lbuffer a len`) | Length-carrying slices — free in most modern languages, and removes a whole class of preconditions |
| `disjoint` / `modifies` | Ownership and borrow checking, where available; otherwise documented aliasing rules |
| Abstract `state_s` + `footprint` + `invariant` | An opaque handle type with a private representation; the invariant becomes a type invariant maintained by construction |
| `frame_invariant` and SMT patterns | Nothing — this is proof plumbing that exists because the logic needs help. Do not port it. |
| `getter (flag: bool)` with `b ==> flag` | Feature detection returning a *capability token* / typestate, so that only code holding the token can call the intrinsic-using function |
| Precondition weakening for multiplexed frontends | A safe wrapper that performs detection and dispatches, with the same output contract as the specialized versions |
| `G.erased` arguments | Compile-time generic parameters / phantom types |

The two ideas most worth stealing are in §5 and §6: **capabilities for CPU
features**, and **an opaque state with an explicit ownership footprint and a
maintained invariant**. Both are expressible without a theorem prover, and both
eliminate categories of misuse that the C API leaves wide open.
