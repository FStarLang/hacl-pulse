# F* API surface for curves, signatures, bignum, RSA-PSS, and FFDHE

This note complements [design/fstar-api.md](fstar-api.md), which covers the
Low*/F* memory model, `Stack`/`ST` effects, `live`, `disjoint`, `modifies`, and
`as_seq`. It also complements [design/fstar-specs.md](fstar-specs.md),
[design/api-curves.md](api-curves.md), [design/api-bignum.md](api-bignum.md),
[design/implementation.md](implementation.md), and
[design/surprises.md](surprises.md). The focus here is the F* interface surface:
`val` declarations, refinements, preconditions, postconditions, and the way the
postconditions connect the Low* code to pure specs.

The C API is intentionally not repeated. Many public `.fsti` files contain C
comments because they drive extraction, but verified F* clients should read the
F* types first: buffer lengths, secrecy-indexed machine integers, aliasing
constraints, and pure-spec postconditions are the real API.

## 1. Orientation and module layering

### 1.1 What a verified client should depend on

For most clients, the best dependencies are the top-level HACL*/EverCrypt
modules, not the internal `Hacl.Impl.*` modules.

| Area | Preferred client module(s) | Why |
| --- | --- | --- |
| X25519 | `EverCrypt.Curve25519`, or fixed `Hacl.Curve25519_51` / `Hacl.Curve25519_64` | These expose byte-buffer contracts against `Spec.Curve25519`. |
| Ed25519 | `EverCrypt.Ed25519` or `Hacl.Ed25519` | These expose byte-buffer contracts against `Spec.Ed25519`. |
| P-256 | `Hacl.P256` | Public F* surface covers ECDSA, key validation, public-key encodings, and ECDH. |
| secp256k1/K-256 | `Hacl.K256.ECDSA` | Public F* surface covers ECDSA, low-S normalization, public-key encodings, key validation, and ECDH. |
| Bignum | `Hacl.Bignum32`, `Hacl.Bignum64`, `Hacl.GenericField32`, `Hacl.GenericField64`; lower-level clients may use `Hacl.Bignum`, `Hacl.Bignum.Montgomery`, `Hacl.Bignum.Exponentiation` | The exported modules instantiate the limb type; the lower-level modules expose type classes indexed by limb type and length. |
| RSA-PSS | `Hacl.RSAPSS` | It fixes `U64` limbs and exposes key-loading, sign/verify, and MGF wrappers. |
| FFDHE | `Hacl.FFDHE` | It fixes `U64` limbs and exposes RFC7919 group operations. |

The internal curve modules (`Hacl.Impl.P256.*`, `Hacl.Impl.K256.*`,
`Hacl.Impl.Curve25519.*`) are valuable for reimplementers and for verified
clients that intentionally manipulate field or point representations, but they
are dangerous as application-level APIs: callers must maintain representation
invariants that are not visible in a C header.

### 1.2 Layering by family

**Curve25519/X25519.** The public byte-buffer functions are in
`Hacl.Curve25519_51`, `Hacl.Curve25519_64`, `Hacl.Curve25519_64_Slow`,
`Hacl.Curve25519_64_Local`, and `EverCrypt.Curve25519`. Their shared F* type is
factored in `Hacl.Impl.Curve25519.Generic` (path:line
`code/curve25519/Hacl.Impl.Curve25519.Generic.fsti:12`, `:25`, `:36`). The
field interface is factored in `Hacl.Impl.Curve25519.Fields.Core` and indexed by
`field_spec = M51 | M64` (path:line
`code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:22`). Both the 51-bit and
64-bit representations implement the same core signatures. The M64 signature is
implemented by HACL* C code and by Vale assembly, with the Vale implementation
adding the CPU-feature precondition `adx_enabled /\ bmi2_enabled`.

**Ed25519.** `Hacl.Ed25519` and `EverCrypt.Ed25519` expose signing,
verification, public-key derivation, and expanded-key signing. The pure spec is
`Spec.Ed25519`; implementation internals live under `Hacl.Impl.Ed25519.*`.
The interface postconditions are direct equalities to `Spec.Ed25519.*`.

**P-256.** `Hacl.P256` is the high-level surface for ECDSA, key validation,
point encodings, and ECDH. Internals are in `Hacl.Impl.P256.Field`,
`Hacl.Impl.P256.Point`, `Hacl.Impl.P256.PointMul`, etc. The low-level point and
field modules use 4 64-bit limbs for field elements and keep coordinates in
Montgomery form for many operations; ghost functions such as `as_nat`,
`fmont_as_nat`, `as_point_nat`, and `from_mont_point` state the connection to
`Spec.P256`.

**K-256/secp256k1.** `Hacl.K256.ECDSA` is the public surface. Internals use a
radix-2^52 representation in `Hacl.K256.Field` and point buffers in
`Hacl.Impl.K256.Point`. Ghost functions such as `as_felem5`, `as_nat`, `feval`,
`aff_point_eval`, and `point_eval` connect buffers to `Spec.K256`.

**Bignum.** The generic bignum development is intentionally type-class based.
`Hacl.Spec.Bignum.Definitions` defines `limb_t`, `limb`, `lbignum`, and the pure
interpretation `bn_v` (path:line `code/bignum/Hacl.Spec.Bignum.Definitions.fst:15`).
`Hacl.Bignum.Definitions` lifts them to Low* buffers and memory-dependent
`bn_v` (path:line `code/bignum/Hacl.Bignum.Definitions.fst:14`).
`Hacl.Bignum` defines class `bn`; `Hacl.Bignum.Montgomery` defines class
`mont`; `Hacl.Bignum.Exponentiation` defines class `exp`. Runtime C-facing
modules instantiate them for `U32` and `U64`.

**RSA-PSS and FFDHE.** Both reuse bignum exponentiation. `Hacl.RSAPSS` fixes
`U64` limbs and constructs a runtime exponentiation instance from `modBits`.
`Hacl.FFDHE` fixes `U64` limbs and constructs a runtime exponentiation instance
from the RFC7919 group size.

## 2. Curve25519/X25519 in F*

### 2.1 Shared stateful signatures

The shared signatures are F*-only abbreviations (`inline_for_extraction
noextract`) in `Hacl.Impl.Curve25519.Generic`. They do not produce separate C
functions; they give multiple public modules the same verified type.

Path:line `code/curve25519/Hacl.Impl.Curve25519.Generic.fsti:12`:

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

Path:line `code/curve25519/Hacl.Impl.Curve25519.Generic.fsti:25`:

```fstar
inline_for_extraction noextract
let secret_to_public_st (s: field_spec) (p: Type0) =
    o:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      p /\
      live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.secret_to_public (as_seq h0 i))
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Generic.fsti:36`:

```fstar
inline_for_extraction noextract
let ecdh_st (s:field_spec) (p: Type0) =
    o:lbuffer uint8 32ul
  -> k:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack bool
    (requires fun h0 ->
      p /\
      live h0 o /\ live h0 k /\ live h0 i /\
      disjoint o i /\ disjoint o k)
    (ensures  fun h0 r h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.scalarmult (as_seq h0 k) (as_seq h0 i)
      /\ (not r == Lib.ByteSequence.lbytes_eq #32 (as_seq h1 o) (Lib.Sequence.create 32 (u8 0))))
```

The postcondition for `scalarmult` is the simplest complete contract: after the
call, only `o` is modified, and `o` equals the pure
`Spec.Curve25519.scalarmult` applied to the pre-state bytes of `k` and `i`.
`ecdh` has the same output equality and returns `true` exactly when the output
is not the all-zero 32-byte string.

### 2.2 Public instantiations

The public modules only instantiate these shared signatures.

Path:line `code/curve25519/Hacl.Curve25519_51.fsti:11`:

```fstar
val scalarmult: scalarmult_st M51 True
```

Path:line `code/curve25519/Hacl.Curve25519_51.fsti:19`:

```fstar
val secret_to_public: secret_to_public_st M51 True
```

Path:line `code/curve25519/Hacl.Curve25519_51.fsti:26`:

```fstar
val ecdh: ecdh_st M51 True
```

Path:line `code/curve25519/Hacl.Curve25519_64.fsti:7` and `:14`:

```fstar
inline_for_extraction noextract
let p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

val scalarmult: scalarmult_st M64 p
```

Path:line `code/curve25519/Hacl.Curve25519_64.fsti:22` and `:29`:

```fstar
val secret_to_public: secret_to_public_st M64 p
val ecdh: ecdh_st M64 p
```

Path:line `code/curve25519/Hacl.Curve25519_64_Slow.fsti:11`, `:19`, `:26`:

```fstar
val scalarmult: scalarmult_st M64 True
val secret_to_public: secret_to_public_st M64 True
val ecdh: ecdh_st M64 True
```

Path:line `code/curve25519/Hacl.Curve25519_64_Local.fsti:6`:

```fstar
val scalarmult: scalarmult_st M64 True
val secret_to_public: secret_to_public_st M64 True
val ecdh: ecdh_st M64 True
```

`Hacl.Curve25519_64` is the assembly-gated instance: a verified caller must prove
or carry the precondition `p`, which is a CPU-feature predicate. The `_Slow` and
`_Local` variants use `True`. `Hacl.Curve25519_51` uses `M51` and `True`.

### 2.3 EverCrypt Curve25519

EverCrypt exposes the same byte-level spec without the `field_spec` index.
Path:line `providers/evercrypt/EverCrypt.Curve25519.fsti:21`:

```fstar
val secret_to_public:
    pub:lbuffer uint8 32ul
  -> priv:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 pub /\ live h0 priv /\ disjoint pub priv)
    (ensures  fun h0 _ h1 -> modifies (loc pub) h0 h1 /\
      as_seq h1 pub == Spec.Curve25519.secret_to_public (as_seq h0 priv))
```

Path:line `providers/evercrypt/EverCrypt.Curve25519.fsti:37`:

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

Path:line `providers/evercrypt/EverCrypt.Curve25519.fsti:55`:

```fstar
val ecdh:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul
  -> Stack bool
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 r h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == Spec.Curve25519.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub)
      /\ (not r == Lib.ByteSequence.lbytes_eq #32 (as_seq h1 shared) (Lib.Sequence.create 32 (u8 0))))
```

### 2.4 Field representation abstraction

`Hacl.Impl.Curve25519.Fields.Core` is the clearest “one signature, two
implementations” example in the tree.

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:22`:

```fstar
type field_spec =
  | M51
  | M64
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:27`:

```fstar
unfold noextract
let limb (s:field_spec) =
  match s with
  | M51 -> uint64
  | M64 -> uint64
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:39`:

```fstar
unfold noextract
let nlimb (s:field_spec) : size_t =
  match s with
  | M51 -> 5ul
  | M64 -> 4ul
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:45`:

```fstar
unfold noextract
let wide (s:field_spec) =
  match s with
  | M51 -> uint128
  | M64 -> uint64
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:57`:

```fstar
unfold noextract
let nwide (s:field_spec) : size_t =
  match s with
  | M51 -> 5ul
  | M64 -> 8ul
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:62`:

```fstar
inline_for_extraction noextract
let felem (s:field_spec) = lbuffer (limb s) (nlimb s)
inline_for_extraction noextract
let felem2 (s:field_spec) = lbuffer (limb s) (nlimb s +. nlimb s)
inline_for_extraction noextract
let felem_wide (s:field_spec) = lbuffer (wide s) (nwide s)
inline_for_extraction noextract
let felem_wide2 (s:field_spec) = lbuffer (wide s) (nwide s +. nwide s)
```

`M51` and `M64` both use `uint64` limbs at the Low* level, but `M51` uses 5
limbs with `uint128` wide temporaries, while `M64` uses 4 limbs and 8 `uint64`
wide temporaries.

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:109`:

```fstar
noextract
let as_nat (#s:field_spec) (h:mem) (e:felem s): GTot nat =
  match s with
  | M51 -> f51_as_nat h e
  | M64 -> f64_as_nat h e
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:115`:

```fstar
noextract
let feval (#s:field_spec) (h:mem) (e:felem s): GTot P.elem =
  (as_nat h e) % P.prime
```

The `as_nat` and `feval` functions are ghost interpretation functions. They do
not extract, but they are the bridge from a concrete limb buffer in a heap to the
mathematical field element used in `Spec.Curve25519`.

### 2.5 Field operation signatures and limb-bound refinements

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:122`:

```fstar
let fadd_fsub_pre (#s:field_spec) (h:mem) (f1:felem s) (f2:felem s): Type0 =
  match s with
  | M51 ->
      f51_felem_fits h f1 (1, 2, 1, 1, 1) /\
      f51_felem_fits h f2 (1, 2, 1, 1, 1)
  | M64 -> True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:135`:

```fstar
inline_for_extraction
let fadd_t (s:field_spec) (p: Type0) =
    out:felem s
  -> f1:felem s
  -> f2:felem s
  -> Stack unit
    (requires fun h ->
      p /\
      live h out /\ live h f1 /\ live h f2 /\
      (disjoint out f1 \/ out == f1) /\
      (disjoint out f2 \/ out == f2) /\
      (disjoint f1 f2 \/ f1 == f2) /\
      fadd_fsub_pre h f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\ fadd_post h1 out /\
      feval h1 out == P.fadd (feval h0 f1) (feval h0 f2))
[@ Meta.Attribute.specialize]
val fadd: #s:field_spec -> fadd_t s True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:177`:

```fstar
let fmul_pre (#s:field_spec) (h:mem) (f1:felem s) (f2:felem s): Type0 =
  match s with
  | M51 ->
      f51_felem_fits h f1 (9, 10, 9, 9, 9) /\
      f51_felem_fits h f2 (9, 10, 9, 9, 9)
  | M64 -> True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:202`:

```fstar
inline_for_extraction
let fmul_t (s:field_spec) (p: Type0) =
    out:felem s
  -> f1:felem s
  -> f2:felem s
  -> tmp:felem_wide2 s
  -> Stack unit
    (requires fun h ->
      p /\
      live h out /\ live h f1 /\ live h f2 /\ live h tmp /\
      fmul_disjoint out f1 f2 tmp /\
      fmul_pre h f1 f2)
    (ensures fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\ state_inv_t h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f2))
[@ Meta.Attribute.specialize ]
val fmul: #s:field_spec -> fmul_t s True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:296`:

```fstar
let fsqr_pre (#s:field_spec) (h:mem) (f:felem s): Type0 =
  match s with
  | M51 -> f51_felem_fits h f (9, 10, 9, 9, 9)
  | M64 -> True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Fields.Core.fsti:310`:

```fstar
inline_for_extraction
let fsqr_t (s:field_spec) (p: Type0) =
    out:felem s
  -> f1:felem s
  -> tmp:felem_wide s
  -> Stack unit
    (requires fun h ->
      p /\
      live h out /\ live h f1 /\ live h tmp /\
      fsqr_disjoint out f1 tmp /\
      fsqr_pre h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out |+| loc tmp) h0 h1 /\
      state_inv_t h1 out /\
      feval h1 out == P.fmul (feval h0 f1) (feval h0 f1))

[@ Meta.Attribute.specialize ]
val fsqr: #s:field_spec -> fsqr_t s True
```

The important discipline is not just “arrays of limbs”. For `M51`, `fadd` and
`fsub` require scaled limb bounds such as `(1,2,1,1,1)` and establish new bounds;
`fmul` and `fsqr` require wider lazy bounds `(9,10,9,9,9)` and re-establish a
state invariant. `M64` hides fewer limb-bound facts in these preconditions, but
it imposes stricter disjointness on temporaries through `fmul_disjoint` and
`fsqr_disjoint`.

### 2.6 One signature, multiple implementations

Path:line `code/curve25519/Hacl.Impl.Curve25519.Field64.Hacl.fsti:5`:

```fstar
val add1_: add1_t True
val fadd_: fadd_t M64 True
val fsub_: fsub_t M64 True
val fmul_: fmul_t M64 True
val fmul2_: fmul2_t M64 True
val fmul1_: fmul1_t M64 True
val fsqr_: fsqr_t M64 True
val fsqr2_: fsqr2_t M64 True
val cswap2_: cswap2_t M64 True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Field64.Local.fsti:9`:

```fstar
val add1: add1_t True
val fadd: fadd_t M64 True
val fsub: fsub_t M64 True
val fmul: fmul_t M64 True
val fmul2: fmul2_t M64 True
val fmul1: fmul1_t M64 True
val fsqr: fsqr_t M64 True
val fsqr2: fsqr2_t M64 True
val cswap2: cswap2_t M64 True
```

Path:line `code/curve25519/Hacl.Impl.Curve25519.Field64.Vale.fsti:5`:

```fstar
let p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

val add_scalar: add1_t p
val fadd: fadd_t M64 p
val fsub: fsub_t M64 p
val fmul: fmul_t M64 p
val fmul2: fmul2_t M64 p
val fmul_scalar: fmul1_t M64 p
val fsqr: fsqr_t M64 p
val fsqr2: fsqr2_t M64 p
val cswap2: cswap2_t M64 p
```

The generic ladder code can be instantiated with either HACL* C field operations
or Vale field operations because both satisfy the same `fadd_t`, `fmul_t`,
`fsqr_t`, etc. The assembly implementation simply carries the extra precondition
`p`; the pure postconditions are identical.

## 3. Ed25519 in F*

### 3.1 HACL* Ed25519 contracts

Path:line `code/ed25519/Hacl.Ed25519.fsti:19`:

```fstar
val secret_to_public:
    public_key:lbuffer uint8 32ul
  -> private_key:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h public_key /\ live h private_key /\ disjoint public_key private_key)
    (ensures  fun h0 _ h1 -> modifies (loc public_key) h0 h1 /\
      as_seq h1 public_key == Spec.Ed25519.secret_to_public (as_seq h0 private_key))
```

Path:line `code/ed25519/Hacl.Ed25519.fsti:36`:

```fstar
val expand_keys:
    expanded_keys:lbuffer uint8 96ul
  -> private_key:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h expanded_keys /\ live h private_key /\ disjoint expanded_keys private_key)
    (ensures  fun h0 _ h1 -> modifies (loc expanded_keys) h0 h1 /\
     (let public_key, s, prefix = Spec.Ed25519.expand_keys (as_seq h0 private_key) in
      as_seq h1 (gsub expanded_keys 0ul 32ul) == public_key /\
      as_seq h1 (gsub expanded_keys 32ul 32ul) == s /\
      as_seq h1 (gsub expanded_keys 64ul 32ul) == prefix))
```

Path:line `code/ed25519/Hacl.Ed25519.fsti:58`:

```fstar
val sign_expanded:
    signature:lbuffer uint8 64ul
  -> expanded_keys:lbuffer uint8 96ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h expanded_keys /\
      disjoint signature msg /\ disjoint signature expanded_keys)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub expanded_keys 0ul 32ul))
        (as_seq h0 (gsub expanded_keys 32ul 32ul))
        (as_seq h0 (gsub expanded_keys 64ul 32ul))
        (as_seq h0 msg))
```

Path:line `code/ed25519/Hacl.Ed25519.fsti:86`:

```fstar
val sign:
    signature:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h private_key /\
      disjoint signature msg /\ disjoint signature private_key)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 private_key) (as_seq h0 msg))
```

Path:line `code/ed25519/Hacl.Ed25519.fsti:107`:

```fstar
val verify:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h public_key /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
      b == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))
```

`expand_keys` splits its 96-byte output into three 32-byte slices: public key,
secret scalar, and prefix. The expanded signing contract deliberately refers to
those slices in the pre-state. This lets a verified caller cache expanded keys
and prove repeated signing against `Spec.Ed25519.sign_expanded`.

### 3.2 EverCrypt Ed25519

`EverCrypt.Ed25519` repeats the same contracts (path:line
`providers/evercrypt/EverCrypt.Ed25519.fsti:8`, `:20`, `:35`, `:54`, `:68`).
For example, the verification contract is verbatim:

```fstar
val verify:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h public_key /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
      b == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))
```

### 3.3 Sign-then-verify correctness lemma

I found implementation lemmas connecting the Low* code to the spec, for example
verification uses `Spec.Ed25519.Lemmas.point_decompress_lemma` in
`code/ed25519/Hacl.Impl.Ed25519.Verify.fst:117` and `:140`, and ladder code uses
`Spec.Exponentiation` lemmas. I did not find a public `val` lemma in the
Ed25519 `.fsti` surface stating that `verify (secret_to_public sk) msg (sign sk
msg)` returns `true`. Therefore, for the F* API documented here, a
sign-then-verify correctness lemma is **unconfirmed** at both the public spec
interface level and the stateful `Hacl.Ed25519`/`EverCrypt.Ed25519` level. The
stateful contracts are nevertheless sufficient to reduce such a proof obligation
to whatever pure `Spec.Ed25519` property a client imports or proves.

## 4. P-256 and K-256 in F*

### 4.1 P-256 high-level signatures

The P-256 ECDSA types are factored through two F*-only stateful abbreviations.
Path:line `code/ecdsap256/Hacl.P256.fsti:20`:

```fstar
inline_for_extraction noextract
let ecdsa_sign_p256_st (alg:S.hash_alg_ecdsa) =
    signature:lbuffer uint8 64ul
  -> msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> private_key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h signature /\ live h msg /\ live h private_key /\ live h nonce /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 flag h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_signature_agile alg (v msg_len)
      (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
     (flag <==> Some? sgnt) /\ (flag ==> (as_seq h1 signature == Some?.v sgnt))))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:37`:

```fstar
inline_for_extraction noextract
let ecdsa_verify_p256_st (alg:S.hash_alg_ecdsa) =
    msg_len:size_t{v msg_len >= S.min_input_length alg}
  -> msg:lbuffer uint8 msg_len
  -> public_key:lbuffer uint8 64ul
  -> signature_r:lbuffer uint8 32ul
  -> signature_s:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h signature_r /\ live h signature_s /\ live h msg)
  (ensures fun h0 res h1 -> modifies0 h0 h1 /\
    res == S.ecdsa_verification_agile alg (v msg_len) (as_seq h0 msg)
      (as_seq h0 public_key) (as_seq h0 signature_r) (as_seq h0 signature_s))
```

Instantiations (path:line `code/ecdsap256/Hacl.P256.fsti:81`, `:95`, `:109`,
`:133`, `:150`, `:162`, `:174`, `:191`):

```fstar
val ecdsa_sign_p256_sha2: ecdsa_sign_p256_st (S.Hash SHA2_256)
val ecdsa_sign_p256_sha384: ecdsa_sign_p256_st (S.Hash SHA2_384)
val ecdsa_sign_p256_sha512: ecdsa_sign_p256_st (S.Hash SHA2_512)
val ecdsa_sign_p256_without_hash: ecdsa_sign_p256_st (S.NoHash)
val ecdsa_verif_p256_sha2: ecdsa_verify_p256_st (S.Hash SHA2_256)
val ecdsa_verif_p256_sha384: ecdsa_verify_p256_st (S.Hash SHA2_384)
val ecdsa_verif_p256_sha512: ecdsa_verify_p256_st (S.Hash SHA2_512)
val ecdsa_verif_without_hash: ecdsa_verify_p256_st S.NoHash
```

Path:line `code/ecdsap256/Hacl.P256.fsti:211`:

```fstar
val validate_public_key: public_key:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h public_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.validate_public_key (as_seq h0 public_key))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:225`:

```fstar
val validate_private_key: private_key:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h private_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let s = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    r <==> (0 < s && s < S.order)))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:253`:

```fstar
val uncompressed_to_raw: pk:lbuffer uint8 65ul -> pk_raw:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:268`:

```fstar
val compressed_to_raw: pk:lbuffer uint8 33ul -> pk_raw:lbuffer uint8 64ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:281`:

```fstar
val raw_to_uncompressed: pk_raw:lbuffer uint8 64ul -> pk:lbuffer uint8 65ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:293`:

```fstar
val raw_to_compressed: pk_raw:lbuffer uint8 64ul -> pk:lbuffer uint8 33ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:313`:

```fstar
val dh_initiator:
    public_key:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\ disjoint public_key private_key)
  (ensures fun h0 r h1 -> modifies (loc public_key) h0 h1 /\
    (let pk = S.secret_to_public (as_seq h0 private_key) in
    (r <==> Some? pk) /\ (r ==> (as_seq h1 public_key == Some?.v pk))))
```

Path:line `code/ecdsap256/Hacl.P256.fsti:334`:

```fstar
val dh_responder:
    shared_secret:lbuffer uint8 64ul
  -> their_pubkey:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (let ss = S.ecdh (as_seq h0 their_pubkey) (as_seq h0 private_key) in
    (r <==> Some? ss) /\ (r ==> (as_seq h1 shared_secret == Some?.v ss))))
```

### 4.2 P-256 representation invariants

Path:line `code/ecdsap256/Hacl.Impl.P256.Bignum.fsti:14`:

```fstar
inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction
let widefelem = lbuffer uint64 (size 8)

unfold
let as_nat (h:mem) (e:felem) : GTot nat =
  BD.bn_v (as_seq h e)
```

Path:line `code/ecdsap256/Hacl.Impl.P256.Field.fsti:14`:

```fstar
let fmont_as_nat (h:mem) (a:felem) = SM.from_mont (as_nat h a)
```

Path:line `code/ecdsap256/Hacl.Impl.P256.Field.fsti:53`:

```fstar
val fadd: res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == S.fadd (as_nat h0 x) (as_nat h0 y) /\
    fmont_as_nat h1 res == S.fadd (fmont_as_nat h0 x) (fmont_as_nat h0 y))
```

Path:line `code/ecdsap256/Hacl.Impl.P256.Field.fsti:88`:

```fstar
val fmul: res:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 x * as_nat h0 y * SM.fmont_R_inv) % S.prime /\
    fmont_as_nat h1 res = S.fmul (fmont_as_nat h0 x) (fmont_as_nat h0 y))
```

Path:line `code/ecdsap256/Hacl.Impl.P256.Point.fsti:20`:

```fstar
let from_mont_point (a:tuple3 nat nat nat) : S.proj_point =
  let x, y, z = a in SM.from_mont x, SM.from_mont y, SM.from_mont z
```

Path:line `code/ecdsap256/Hacl.Impl.P256.Point.fsti:26`:

```fstar
inline_for_extraction noextract
let aff_point_seq = LSeq.lseq uint64 8

let as_aff_point_nat_seq (p:aff_point_seq) =
  BD.bn_v (LSeq.sub p 0 4),
  BD.bn_v (LSeq.sub p 4 4)

let aff_point_inv_seq (p:aff_point_seq) =
  let x, y = as_aff_point_nat_seq p in
  x < S.prime /\ y < S.prime
```

Path:line `code/ecdsap256/Hacl.Impl.P256.Point.fsti:46`:

```fstar
inline_for_extraction noextract
let point_seq = LSeq.lseq uint64 12

let as_point_nat_seq (p:point_seq) =
  BD.bn_v (LSeq.sub p 0 4),
  BD.bn_v (LSeq.sub p 4 4),
  BD.bn_v (LSeq.sub p 8 4)

let point_inv_seq (p:point_seq) =
  let x, y, z = as_point_nat_seq p in
  x < S.prime /\ y < S.prime /\ z < S.prime
```

The low-level P-256 point API is not merely `uint64[8]` or `uint64[12]`. An
affine point is two 4-limb integers, each `< prime`. A projective point is three
4-limb integers, each `< prime`, and many point postconditions compare
`from_mont_point (as_point_nat h p)` to `Spec.P256` points.

### 4.3 K-256 public signatures

Path:line `code/k256/Hacl.K256.ECDSA.fsti:45`:

```fstar
val ecdsa_sign_hashed_msg (signature:lbytes 64ul)
  (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))
```

Path:line `code/k256/Hacl.K256.ECDSA.fsti:66`:

```fstar
val ecdsa_sign_sha256 (signature:lbytes 64ul)
  (msg_len:size_t) (msg:lbytes msg_len) (private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))
```

Path:line `code/k256/Hacl.K256.ECDSA.fsti:86`:

```fstar
val ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))
```

Path:line `code/k256/Hacl.K256.ECDSA.fsti:103`:

```fstar
val ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 signature))
```

Low-S variants and predicates (path:line `code/k256/Hacl.K256.ECDSA.fsti:117`,
`:129`, `:147`, `:168`, `:188`, `:205`):

```fstar
val secp256k1_ecdsa_signature_normalize: signature: lbytes 64ul -> Stack bool
  (requires fun h -> live h signature)
  (ensures  fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_signature_normalize (as_seq h0 signature) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))

val secp256k1_ecdsa_is_signature_normalized: signature: lbytes 64ul -> Stack bool
  (requires fun h -> live h signature)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_is_signature_normalized (as_seq h0 signature))

val secp256k1_ecdsa_sign_hashed_msg (signature:lbytes 64ul)
  (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))

val secp256k1_ecdsa_sign_sha256 (signature:lbytes 64ul)
  (msg_len:size_t) (msg:lbytes msg_len) (private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))

val secp256k1_ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))

val secp256k1_ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 signature))
```

Key encoding and validation (path:line `code/k256/Hacl.K256.ECDSA.fsti:233`,
`:246`, `:260`, `:273`, `:296`, `:310`, `:331`, `:350`):

```fstar
val public_key_uncompressed_to_raw: pk_raw:lbytes 64ul -> pk:lbytes 65ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))

val public_key_uncompressed_from_raw: pk:lbytes 65ul -> pk_raw:lbytes 64ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))

val public_key_compressed_to_raw: pk_raw:lbytes 64ul -> pk:lbytes 33ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))

val public_key_compressed_from_raw: pk:lbytes 33ul -> pk_raw:lbytes 64ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))

val is_public_key_valid: public_key:lbytes 64ul -> Stack bool
  (requires fun h -> live h public_key)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b <==> S.validate_public_key (as_seq h0 public_key))

val is_private_key_valid: private_key:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h private_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let s = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    r <==> (0 < s && s < S.q)))

val secret_to_public: public_key:lbytes 64ul -> private_key:lbytes 32ul -> Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\
    disjoint public_key private_key)
  (ensures fun h0 b h1 -> modifies (loc public_key) h0 h1 /\
    (let public_key_s = S.secret_to_public (as_seq h0 private_key) in
    (b <==> Some? public_key_s) /\ (b ==> (as_seq h1 public_key == Some?.v public_key_s))))

val ecdh:
    shared_secret:lbuffer uint8 64ul
  -> their_pubkey:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (let ss = S.ecdh (as_seq h0 their_pubkey) (as_seq h0 private_key) in
    (r <==> Some? ss) /\ (r ==> (as_seq h1 shared_secret == Some?.v ss))))
```

### 4.4 K-256 representation invariants

Path:line `code/k256/Hacl.K256.Field.fsti:17`:

```fstar
inline_for_extraction noextract
let nlimb = 5ul

inline_for_extraction noextract
let felem = lbuffer uint64 nlimb
```

Path:line `code/k256/Hacl.K256.Field.fsti:23`:

```fstar
noextract
let as_felem5 (h:mem) (e:felem) : GTot felem5 =
  let open Lib.Sequence in
  let s = as_seq h e in
  (s.[0], s.[1], s.[2], s.[3], s.[4])

noextract
let as_nat (h:mem) (e:felem) : GTot nat =
  as_nat5 (as_felem5 h e)

noextract
let feval (h:mem) (e:felem) : GTot S.felem = as_nat h e % S.prime
```

Path:line `code/k256/Hacl.K256.Field.fsti:34`:

```fstar
noextract
let inv_fully_reduced5 (f:felem5) =
  felem_fits5 f (1,1,1,1,1) /\
  as_nat5 f < S.prime

noextract
let inv_fully_reduced (h:mem) (e:felem) =
  inv_fully_reduced5 (as_felem5 h e)
```

Path:line `code/k256/Hacl.K256.Field.fsti:200`:

```fstar
val fmul (out f1 f2: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    felem_fits5 (as_felem5 h f1) (64,64,64,64,64) /\
    felem_fits5 (as_felem5 h f2) (64,64,64,64,64))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    feval h1 out == feval h0 f1 * feval h0 f2 % S.prime /\
    inv_lazy_reduced2 h1 out)
```

Path:line `code/k256/Hacl.Impl.K256.Point.fsti:21`:

```fstar
inline_for_extraction noextract
let aff_point_seq = LSeq.lseq uint64 10

let aff_point_inv_seq (p:aff_point_seq) =
  inv_fully_reduced5 (as_felem5_lseq (LSeq.sub p 0 5)) /\
  inv_fully_reduced5 (as_felem5_lseq (LSeq.sub p 5 5))

let aff_point_eval_seq (p:aff_point_seq{aff_point_inv_seq p}) : S.aff_point =
  as_nat5 (as_felem5_lseq (LSeq.sub p 0 5)),
  as_nat5 (as_felem5_lseq (LSeq.sub p 5 5))
```

Path:line `code/k256/Hacl.Impl.K256.Point.fsti:52`:

```fstar
// (_X, _Y, _Z)
inline_for_extraction noextract
let point = lbuffer uint64 15ul
```

Path:line `code/k256/Hacl.Impl.K256.Point.fsti:76`:

```fstar
inline_for_extraction noextract
let point_inv_lseq (p:LSeq.lseq uint64 15) =
  inv_lazy_reduced2_5 (as_felem5_lseq (LSeq.sub p 0 5)) /\
  inv_lazy_reduced2_5 (as_felem5_lseq (LSeq.sub p 5 5)) /\
  inv_lazy_reduced2_5 (as_felem5_lseq (LSeq.sub p 10 5))

inline_for_extraction noextract
let point_inv (h:mem) (p:point) =
  inv_lazy_reduced2 h (gsub p 0ul 5ul) /\
  inv_lazy_reduced2 h (gsub p 5ul 5ul) /\
  inv_lazy_reduced2 h (gsub p 10ul 5ul)
```

Path:line `code/k256/Hacl.Impl.K256.Point.fsti:89`:

```fstar
inline_for_extraction noextract
let point_eval_lseq (p:LSeq.lseq uint64 15) : GTot S.proj_point =
  feval5 (as_felem5_lseq (LSeq.sub p 0 5)),
  feval5 (as_felem5_lseq (LSeq.sub p 5 5)),
  feval5 (as_felem5_lseq (LSeq.sub p 10 5))

inline_for_extraction noextract
let point_eval (h:mem) (p:point) : GTot S.proj_point =
  feval h (gsub p 0ul 5ul),
  feval h (gsub p 5ul 5ul),
  feval h (gsub p 10ul 5ul)
```

K-256 low-level callers must distinguish fully reduced field elements from lazy
reduced ones. Affine points require fully reduced coordinates; projective points
permit `inv_lazy_reduced2` coordinates. Forgetting that distinction is the main
hazard when calling `Hacl.Impl.K256.Point` directly.

## 5. Bignum as an F* API

### 5.1 Definitions: limb type, buffer type, and interpretation

Path:line `code/bignum/Hacl.Spec.Bignum.Definitions.fst:15`:

```fstar
inline_for_extraction noextract
let limb_t = t:inttype{t = U32 \/ t = U64}
inline_for_extraction noextract
let limb (t:limb_t) = uint_t t SEC
let lbignum (t:limb_t) len = lseq (limb t) len
```

Path:line `code/bignum/Hacl.Spec.Bignum.Definitions.fst:19`:

```fstar
val eval_: #t:limb_t -> len:size_nat -> s:lbignum t len -> i:nat{i <= len} -> nat
let rec eval_ #t len s i =
  if i = 0 then 0
  else eval_ #t len s (i - 1) + v s.[i - 1] * pow2 (bits t * (i - 1))

let bn_v (#t:limb_t) (#len:size_nat) (s:lbignum t len) = eval_ #t len s len
```

Path:line `code/bignum/Hacl.Bignum.Definitions.fst:20`:

```fstar
inline_for_extraction noextract
let limb_t = S.limb_t

inline_for_extraction noextract
let limb (t:limb_t) = S.limb t

inline_for_extraction noextract
let lbignum (t:limb_t) len = lbuffer (limb t) len

noextract
val bn_v: #t:limb_t -> #len:size_t -> h:mem -> b:lbignum t len -> GTot nat
let bn_v #t #len h b = S.bn_v #t #(v len) (as_seq h b)
```

At the F* API level, `bn_v h b` is the mathematical value of a live bignum
buffer in heap `h`, using little-endian limbs of size `bits t`. It is a ghost
function and does not extract. `as_seq h b` remains the exact byte/limb sequence
postcondition used by most core APIs.

### 5.2 Core add/sub/mul/sqr shapes

Path:line `code/bignum/Hacl.Bignum.fsti:18`:

```fstar
inline_for_extraction noextract
val bn_add1:
    #t:limb_t
  -> aLen:size_t{0 < v aLen}
  -> a:lbignum t aLen
  -> b1:limb t
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (let c, r = S.bn_add1 (as_seq h0 a) b1 in
    c_out == c /\ as_seq h1 res == r))
```

Path:line `code/bignum/Hacl.Bignum.fsti:47`:

```fstar
inline_for_extraction noextract
let bn_add_eq_len_st (t:limb_t) (len:size_t) =
     a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_add (as_seq h0 a) (as_seq h0 b))
```

Path:line `code/bignum/Hacl.Bignum.fsti:62`:

```fstar
inline_for_extraction noextract
let bn_sub_eq_len_st (t:limb_t) (len:size_t) =
     a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
   (c_out, as_seq h1 res) == S.bn_sub (as_seq h0 a) (as_seq h0 b))
```

Path:line `code/bignum/Hacl.Bignum.fsti:135`:

```fstar
inline_for_extraction noextract
let bn_add_mod_n_st (t:limb_t) (len:size_t{v len > 0}) =
    n:lbignum t len
  -> a:lbignum t len
  -> b:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint n a /\ disjoint n b /\ disjoint n res /\
    eq_or_disjoint a b /\ eq_or_disjoint a res /\ eq_or_disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_add_mod_n (as_seq h0 n) (as_seq h0 a) (as_seq h0 b))
```

Path:line `code/bignum/Hacl.Bignum.fsti:169`:

```fstar
inline_for_extraction noextract
val bn_mul1:
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> l:limb t
  -> res:lbignum t aLen ->
  Stack (limb t)
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint res a)
  (ensures  fun h0 c_out h1 -> modifies (loc res) h0 h1 /\
    (c_out, as_seq h1 res) == S.bn_mul1 (as_seq h0 a) l)
```

Path:line `code/bignum/Hacl.Bignum.fsti:183`:

```fstar
inline_for_extraction noextract
let bn_karatsuba_mul_st (t:limb_t) (len:size_t{0 < v len /\ 4 * v len <= max_size_t}) (a:lbignum t len) =
    b:lbignum t len
  -> res:lbignum t (len +! len) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b))
```

Path:line `code/bignum/Hacl.Bignum.fsti:221`:

```fstar
inline_for_extraction noextract
let bn_sqr_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) (a:lbignum t len) =
  res:lbignum t (len +! len) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 a))
```

The core API is mostly unchecked: the caller proves lengths, liveness, aliasing,
and arithmetic preconditions statically. For modular add/sub, the core function
postcondition is given as a spec sequence equality; lemmas in `Hacl.Spec.Bignum`
can be used to derive `bn_v` equalities.

### 5.3 Type classes rather than specialize/inline tactics

The comments in `Hacl.Bignum.fsti` explicitly say this is type-class based. The
key index is both the limb type and the limb count.

Path:line `code/bignum/Hacl.Bignum.fsti:342`:

```fstar
inline_for_extraction noextract
let meta_len (t:limb_t) = len:size_t{0 < v len /\ 2 * bits t * v len <= max_size_t}
```

Path:line `code/bignum/Hacl.Bignum.fsti:348`:

```fstar
inline_for_extraction noextract
class bn (t:limb_t) = {
  len: meta_len t;
  add: bn_add_eq_len_st t len;
  sub: bn_sub_eq_len_st t len;
  add_mod_n: bn_add_mod_n_st t len;
  sub_mod_n: bn_sub_mod_n_st t len;
  mul: a:lbignum t len -> bn_karatsuba_mul_st t len a;
  sqr: a:lbignum t len -> bn_karatsuba_sqr_st t len a;
}
```

Path:line `code/bignum/Hacl.Bignum.fsti:361`:

```fstar
inline_for_extraction noextract
val mk_runtime_bn: t:limb_t -> len:meta_len t -> bn t

val mk_runtime_bn_len_lemma: t:limb_t -> len:meta_len t ->
  Lemma ((mk_runtime_bn t len).len == len) [SMTPat (mk_runtime_bn t len)]
```

A verified client that wants a length-specialized implementation can require an
implicit or explicit `BN.bn t` instance and use `x.len` to index all buffers.
A client that merely calls runtime code can use `mk_runtime_bn U64 len` or the
public `Hacl.Bignum64` wrappers.

### 5.4 Montgomery context and modular arithmetic

Path:line `code/bignum/Hacl.Bignum.Montgomery.fsti:16`:

```fstar
inline_for_extraction noextract
let bn_check_modulus_st (t:limb_t) (len:BN.meta_len t) =
  n:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_modulus (as_seq h0 n))
```

Path:line `code/bignum/Hacl.Bignum.Montgomery.fsti:50`:

```fstar
inline_for_extraction noextract
let bn_mont_precomp_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t
  -> n:lbignum t len
  -> r2:lbignum t len
  -> Stack (limb t)
  (requires fun h ->
    live h n /\ live h r2 /\ disjoint n r2 /\

    1 < bn_v h n /\ bn_v h n % 2 = 1 /\
    pow2 (v nBits) < bn_v h n /\ v nBits / bits t < v len)
  (ensures  fun h0 mu h1 -> modifies (loc r2) h0 h1 /\
    (as_seq h1 r2, mu) == S.bn_mont_precomp (v nBits) (as_seq h0 n))
```

Path:line `code/bignum/Hacl.Bignum.Montgomery.fsti:70`:

```fstar
inline_for_extraction noextract
let bn_mont_reduction_st (t:limb_t) (len:size_t{0 < v len /\ v len + v len <= max_size_t}) =
    n:lbignum t len
  -> mu:limb t
  -> c:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h c /\ live h res /\
    disjoint res n /\ disjoint res c /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc c) h0 h1 /\
    as_seq h1 res == S.bn_mont_reduction (as_seq h0 n) mu (as_seq h0 c))
```

Path:line `code/bignum/Hacl.Bignum.Montgomery.fsti:151`:

```fstar
inline_for_extraction noextract
let bn_mont_mul_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> aM:lbignum t len
  -> bM:lbignum t len
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h aM /\ live h bM /\ live h resM /\ live h n /\
    disjoint resM n /\ eq_or_disjoint aM bM /\
    eq_or_disjoint aM resM /\ eq_or_disjoint bM resM)
  (ensures  fun h0 _ h1 -> modifies (loc resM) h0 h1 /\
    as_seq h1 resM == S.bn_mont_mul (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM))
```

Path:line `code/bignum/Hacl.Bignum.Montgomery.fsti:178`:

```fstar
inline_for_extraction noextract
class mont (t:limb_t) = {
  bn: BN.bn t;
  mont_check: bn_check_modulus_st t bn.BN.len;
  precomp: bn_precomp_r2_mod_n_st t bn.BN.len;
  reduction: bn_mont_reduction_st t bn.BN.len;
  to: bn_to_mont_st t bn.BN.len;
  from: bn_from_mont_st t bn.BN.len;
  mul: bn_mont_mul_st t bn.BN.len;
  sqr: bn_mont_sqr_st t bn.BN.len;
}
```

Path:line `code/bignum/Hacl.Bignum.Montgomery.fsti:191`:

```fstar
/// Encoding type-class hierarchies via a hook for type class resolution.
inline_for_extraction noextract
instance bn_of_mont (t:limb_t) (x:mont t) : BN.bn t = x.bn
```

The unchecked Montgomery core expects proofs such as odd modulus, modulus
non-zero and greater than one, a valid `mu`, and a correct `r2`. The public field
contexts in `Hacl.Bignum.MontArithmetic`, `Hacl.GenericField32`, and
`Hacl.GenericField64` package those values.

### 5.5 Exponentiation type class and modular exponentiation

Path:line `code/bignum/Hacl.Bignum.Exponentiation.fsti:16`:

```fstar
inline_for_extraction noextract
let bn_check_mod_exp_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{bits t * v (blocks0 bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks0 bBits (size (bits t))) ->
  Stack (limb t)
  (requires fun h ->
    live h n /\ live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_mod_exp (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))
```

Path:line `code/bignum/Hacl.Bignum.Exponentiation.fsti:34`:

```fstar
inline_for_extraction noextract
let bn_mod_exp_precomp_st (t:limb_t) (len:BN.meta_len t) =
     n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t
  -> b:lbignum t (blocks0 bBits (size (bits t)))
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2 /\

    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n /\
    (1 + bn_v h n * v mu) % pow2 (bits t) == 0)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    S.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res))
```

Path:line `code/bignum/Hacl.Bignum.Exponentiation.fsti:149`:

```fstar
inline_for_extraction noextract
let bn_mod_exp_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t
  -> n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{bits t * v (blocks0 bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks0 bBits (size (bits t)))
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\

    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    v nBits / bits t < v len /\ pow2 (v nBits) < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    S.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res))
```

Path:line `code/bignum/Hacl.Bignum.Exponentiation.fsti:182`:

```fstar
inline_for_extraction noextract
class exp (t:limb_t) = {
  bn: BN.bn t;
  mod_check: BM.bn_check_modulus_st t bn.BN.len;
  exp_check: bn_check_mod_exp_st t bn.BN.len;
  precompr2: BM.bn_precomp_r2_mod_n_st t bn.BN.len;
  exp_vt_precomp: bn_mod_exp_precomp_st t bn.BN.len;
  exp_ct_precomp: bn_mod_exp_precomp_st t bn.BN.len;
  exp_vt: bn_mod_exp_st t bn.BN.len;
  exp_ct: bn_mod_exp_st t bn.BN.len;
}
```

Here `_vt` means variable-time and `_ct` means constant-time. Both variants have
the same functional postcondition `S.bn_mod_exp_post`; the distinction is not a
semantic refinement in the postcondition.

### 5.6 SafeAPI: runtime-checked wrappers

The `SafeAPI` functions return booleans or nullable pointers after checking
conditions at runtime. They are also F*-only wrappers/factories marked
`inline_for_extraction noextract` at the signature level, but their bodies
extract into wrappers.

Path:line `code/bignum/Hacl.Bignum.SafeAPI.fst:24`:

```fstar
inline_for_extraction noextract
let new_bn_from_bytes_be_st (t:limb_t) =
    r:HS.rid
  -> len:size_t
  -> b:lbuffer uint8 len ->
  ST (B.buffer (limb t))
  (requires fun h ->
    live h b /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t /\
      B.len res == blocks len (size (numbytes t)) /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t (blocks len (size (numbytes t)))) == SC.bn_from_bytes_be (v len) (as_seq h0 b)))
```

Path:line `code/bignum/Hacl.Bignum.SafeAPI.fst:123`:

```fstar
inline_for_extraction noextract
let bn_mod_slow_safe_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SM.bn_check_modulus (as_seq h0 n)) /\
    (r ==> bn_v h1 res == bn_v h0 a % bn_v h0 n))
```

Path:line `code/bignum/Hacl.Bignum.SafeAPI.fst:154`:

```fstar
inline_for_extraction noextract
let bn_mod_exp_safe_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{bits t * v (blocks0 bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks0 bBits (size (bits t)))
  -> res:lbignum t len ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SE.bn_check_mod_exp (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b)) /\
    (r ==> SE.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res)))
```

Path:line `code/bignum/Hacl.Bignum.SafeAPI.fst:188`:

```fstar
inline_for_extraction noextract
let bn_mod_inv_prime_safe_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> res:lbignum t len ->
  Stack bool
  (requires fun h -> FStar.Math.Euclid.is_prime (bn_v h n) /\
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SI.bn_check_mod_inv_prime (as_seq h0 n) (as_seq h0 a)) /\
   (r ==> bn_v h1 res * bn_v h0 a % bn_v h0 n = 1))
```

SafeAPI differs from the unchecked core by moving many proof obligations into a
runtime boolean. It still keeps non-runtime mathematical assumptions when the
library cannot check them cheaply or at all: `bn_mod_inv_prime_safe_st` still
requires `FStar.Math.Euclid.is_prime (bn_v h n)` statically.

### 5.7 Public U32/U64 bignum and generic-field modules

`Hacl.Bignum32` and `Hacl.Bignum64` instantiate `t_limbs` and expose wrappers
such as:

```fstar
val add: len:BN.meta_len t_limbs -> BN.bn_add_eq_len_st t_limbs len
val sub: len:BN.meta_len t_limbs -> BN.bn_sub_eq_len_st t_limbs len
val add_mod: len:BN.meta_len t_limbs -> BN.bn_add_mod_n_st t_limbs len
val sub_mod: len:BN.meta_len t_limbs -> BN.bn_sub_mod_n_st t_limbs len
val mul: len:BN.meta_len t_limbs -> a:lbignum t_limbs len -> BN.bn_karatsuba_mul_st t_limbs len a
val sqr: len:BN.meta_len t_limbs -> a:lbignum t_limbs len -> BN.bn_karatsuba_sqr_st t_limbs len a
val mod: len:BN.meta_len t_limbs -> BS.bn_mod_slow_safe_st t_limbs len
val mod_exp_vartime: len:BN.meta_len t_limbs -> BS.bn_mod_exp_safe_st t_limbs len
val mod_exp_consttime: len:BN.meta_len t_limbs -> BS.bn_mod_exp_safe_st t_limbs len
val mod_inv_prime_vartime: len:BN.meta_len t_limbs -> BS.bn_mod_inv_prime_safe_st t_limbs len
```

These lines occur in `code/bignum/Hacl.Bignum32.fsti` starting at line 43 and in
`code/bignum/Hacl.Bignum64.fsti` starting at line 36. The shapes are identical
except for `t_limbs = U32` versus `t_limbs = U64`.

`Hacl.GenericField32` and `Hacl.GenericField64` use Montgomery contexts. Path:line
`code/bignum/Hacl.GenericField64.fsti:16`:

```fstar
inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64
```

Representative field operations (path:line `code/bignum/Hacl.GenericField64.fsti:34`,
`:56`, `:65`, `:72`, `:79`, `:86`, `:93`, `:108`, `:125`, `:136`):

```fstar
val field_modulus_check: len:BN.meta_len t_limbs -> MA.bn_field_check_modulus_st t_limbs len
val field_init: len:BN.meta_len t_limbs -> MA.bn_field_init_st t_limbs len
val field_free: MA.bn_field_free_st t_limbs
val field_get_len: MA.bn_field_get_len_st t_limbs
val to_field: len:Ghost.erased _ -> MA.bn_to_field_st t_limbs len
val from_field: len:Ghost.erased _ -> MA.bn_from_field_st t_limbs len
val add: len:Ghost.erased _ -> MA.bn_field_add_st t_limbs len
val sub: len:Ghost.erased _ -> MA.bn_field_sub_st t_limbs len
val mul: len:Ghost.erased _ -> MA.bn_field_mul_st t_limbs len
val sqr: len:Ghost.erased _ -> MA.bn_field_sqr_st t_limbs len
val one: len:Ghost.erased _ -> MA.bn_field_one_st t_limbs len
val exp_consttime: len:Ghost.erased _ -> MA.bn_field_exp_consttime_st t_limbs len
val exp_vartime: len:Ghost.erased _ -> MA.bn_field_exp_vartime_st t_limbs len
val inverse: len:Ghost.erased _ -> MA.bn_field_inv_st t_limbs len
```

## 6. RSA-PSS and FFDHE F* interfaces

### 6.1 RSA-PSS top-level module

`Hacl.RSAPSS` has `.fst` rather than `.fsti`, but it contains explicit `val`
declarations. It fixes `U64` limbs.

Path:line `code/rsapss/Hacl.RSAPSS.fst:12`:

```fstar
inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let modBits_t = RI.modBits_t t_limbs

inline_for_extraction noextract
let ke (modBits:modBits_t) =
  BE.mk_runtime_exp #t_limbs (BD.blocks modBits (size (bits t_limbs)))
```

Top-level declarations (path:line `code/rsapss/Hacl.RSAPSS.fst:42`, `:65`,
`:82`, `:96`, `:119`, `:144`, `:156`):

```fstar
val rsapss_sign:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_sign_st t_limbs (ke modBits) a modBits

val rsapss_verify:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_verify_st t_limbs (ke modBits) a modBits

val new_rsapss_load_pkey: modBits:modBits_t -> RK.new_rsapss_load_pkey_st t_limbs (ke modBits) modBits

val new_rsapss_load_skey: modBits:modBits_t -> RK.new_rsapss_load_skey_st t_limbs (ke modBits) modBits

val rsapss_skey_sign:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_skey_sign_st t_limbs (ke modBits) a modBits

val rsapss_pkey_verify:
    a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t ->
  RI.rsapss_pkey_verify_st t_limbs (ke modBits) a modBits

val mgf_hash: a:Hash.hash_alg{S.hash_is_supported a} -> Hacl.Impl.RSAPSS.MGF.mgf_hash_st a
```

The `modBits_t` refinement comes from `Hacl.Impl.RSAPSS`. Path:line
`code/rsapss/Hacl.Impl.RSAPSS.fst:24`:

```fstar
inline_for_extraction noextract
let modBits_t (t:limb_t) = modBits:size_t{1 < v modBits /\ 2 * bits t * SD.blocks (v modBits) (bits t) <= max_size_t}
```

The main sign and verify contracts link to `Hacl.Spec.RSAPSS`/`Spec.RSAPSS`.
Path:line `code/rsapss/Hacl.Impl.RSAPSS.fst:214`:

```fstar
inline_for_extraction noextract
let rsapss_sign_st (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
    let len = blocks modBits (size (bits t)) in
     eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> saltLen:size_t
  -> salt:lbuffer uint8 saltLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\ disjoint sgnt skey /\
    disjoint salt msg /\

    LS.rsapss_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey))
  (ensures  fun h0 b h1 -> modifies (loc sgnt) h0 h1 /\
    (b, as_seq h1 sgnt) == LS.rsapss_sign a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) (as_seq h0 sgnt))
```

Path:line `code/rsapss/Hacl.Impl.RSAPSS.fst:391`:

```fstar
inline_for_extraction noextract
let rsapss_verify_st (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
   let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> saltLen:size_t
  -> sgntLen:size_t
  -> sgnt:lbuffer uint8 sgntLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h msg /\ live h sgnt /\ live h pkey /\
    disjoint msg sgnt /\ disjoint msg pkey /\

    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_verify a (v modBits) (v eBits) (as_seq h0 pkey)
      (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))
```

Key representation refinements are in `Hacl.Impl.RSAPSS.Keys`. A public key is
stored as `[n; r2; e]`; a secret key as `[pkey; d]`.

Path:line `code/rsapss/Hacl.Impl.RSAPSS.Keys.fst:157`:

```fstar
//pkey = [n; r2; e]
inline_for_extraction noextract
let rsapss_load_pkey_st (t:limb_t) (ke:BE.exp t) (modBits:size_t) =
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> pkey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t))) ->
  Stack bool
  (requires fun h ->
    blocks modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h nb /\ live h eb /\ live h pkey /\
    disjoint pkey nb /\ disjoint pkey eb)
  (ensures  fun h0 b h1 -> modifies (loc pkey) h0 h1 /\
   (b, as_seq h1 pkey) == LS.rsapss_load_pkey (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb))
```

Path:line `code/rsapss/Hacl.Impl.RSAPSS.Keys.fst:223`:

```fstar
//skey = [pkey; d]
inline_for_extraction noextract
let rsapss_load_skey_st (t:limb_t) (ke:BE.exp t) (modBits:size_t) =
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> db:lbuffer uint8 (blocks dBits 8ul)
  -> skey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t))) ->
  Stack bool
  (requires fun h ->
    blocks modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h nb /\ live h eb /\ live h db /\ live h skey /\
    disjoint skey nb /\ disjoint skey eb /\ disjoint skey db)
  (ensures  fun h0 b h1 -> modifies (loc skey) h0 h1 /\
    (b, as_seq h1 skey) == LS.rsapss_load_skey (v modBits) (v eBits) (v dBits)
      (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db))
```

### 6.2 FFDHE top-level module

`Hacl.FFDHE` also has `.fst` rather than `.fsti`, with explicit `val`s. It fixes
`U64` limbs.

Path:line `code/ffdhe/Hacl.FFDHE.fst:10`:

```fstar
inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let ke (a:S.ffdhe_alg) =
  BE.mk_runtime_exp #t_limbs (BD.blocks (DH.ffdhe_len a) (size (numbytes t_limbs)))
```

Top-level declarations (path:line `code/ffdhe/Hacl.FFDHE.fst:32`, `:37`, `:43`,
`:49`, `:55`):

```fstar
let ffdhe_len (a:S.ffdhe_alg) : DH.size_pos = DH.ffdhe_len a

val new_ffdhe_precomp_p: a:S.ffdhe_alg ->
  DH.new_ffdhe_precomp_p_st t_limbs a (ffdhe_len a) (ke a)

val ffdhe_secret_to_public_precomp: a:S.ffdhe_alg ->
  DH.ffdhe_secret_to_public_precomp_st t_limbs a (DH.ffdhe_len a) (ke a)

val ffdhe_secret_to_public: a:S.ffdhe_alg ->
  DH.ffdhe_secret_to_public_st t_limbs a (DH.ffdhe_len a) (ke a)

val ffdhe_shared_secret_precomp: a:S.ffdhe_alg ->
  DH.ffdhe_shared_secret_precomp_st t_limbs a (DH.ffdhe_len a) (ke a)

val ffdhe_shared_secret: a:S.ffdhe_alg ->
  DH.ffdhe_shared_secret_st t_limbs a (DH.ffdhe_len a) (ke a)
```

Implementation-level contracts link to `Spec.FFDHE`.
Path:line `code/ffdhe/Hacl.Impl.FFDHE.fst:288`:

```fstar
inline_for_extraction noextract
let ffdhe_secret_to_public_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
    sk:lbuffer uint8 len
  -> pk:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h sk /\ live h pk /\ disjoint sk pk /\

    v len == S.ffdhe_len a /\
    ke.BE.bn.BN.len == blocks len (size (numbytes t)) /\
    1 < Lib.ByteSequence.nat_from_bytes_be (as_seq h sk))
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.ffdhe_secret_to_public a (as_seq h0 sk))
```

Path:line `code/ffdhe/Hacl.Impl.FFDHE.fst:401`:

```fstar
inline_for_extraction noextract
let ffdhe_shared_secret_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
    sk:lbuffer uint8 len
  -> pk:lbuffer uint8 len
  -> ss:lbuffer uint8 len ->
  Stack (limb t)
  (requires fun h ->
    live h sk /\ live h pk /\ live h ss /\
    disjoint sk pk /\ disjoint sk ss /\ disjoint pk ss /\

    v len = S.ffdhe_len a /\
    ke.BE.bn.BN.len == blocks len (size (numbytes t)) /\
    1 < Lib.ByteSequence.nat_from_bytes_be (as_seq h sk))
  (ensures  fun h0 m h1 -> modifies (loc ss) h0 h1 /\
   (let ss_s = S.ffdhe_shared_secret a (as_seq h0 sk) (as_seq h0 pk) in
    if v m = v (ones t SEC) then Some? ss_s /\ as_seq h1 ss == Some?.v ss_s else None? ss_s))
```

The precomputed representation stores `[p_n; r2_n]` as a bignum buffer twice the
modulus length. Path:line `code/ffdhe/Hacl.Impl.FFDHE.fst:111`:

```fstar
inline_for_extraction noextract
let ffdhe_precomp_inv (#t:limb_t) (#len:size_nat{0 < len /\ len + len <= max_size_t})
  (a:S.ffdhe_alg) (p_r2_n:SD.lbignum t (len + len))
 =
  let p_n = LSeq.sub p_r2_n 0 len in
  let r2_n = LSeq.sub p_r2_n len len in
  SD.bn_v p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\
  0 < SD.bn_v p_n /\ SD.bn_v r2_n == pow2 (2 * bits t * len) % SD.bn_v p_n
```

## 7. Constant-time versus variable-time at the F* level

The API names mark variable-time functions with `_vartime` or `_vt`, e.g.
`bn_mod_exp_vartime`, `exp_vartime`, `is_point_at_inf_vartime`,
`aff_point_load_vartime`, `load_point_vartime`, `fnegate_conditional_vartime`,
and K-256/P-256 point decompression. Their F* types still use ordinary `Stack`
contracts and functional postconditions. The type system does not, by itself,
forbid passing secrets to a function named `_vartime`.

The relevant integer secrecy mechanism is in `Lib.IntTypes`. Path:line
`lib/Lib.IntTypes.fsti:136`:

```fstar
type secrecy_level =
  | SEC
  | PUB
```

Path:line `lib/Lib.IntTypes.fsti:148`:

```fstar
inline_for_extraction
let int_t (t:inttype) (l:secrecy_level) =
  match l with
  | PUB -> pub_int_t t
  | SEC -> sec_int_t t
```

Path:line `lib/Lib.IntTypes.fsti:174`:

```fstar
unfold
type uint8 = uint_t U8 SEC
```

Path:line `lib/Lib.IntTypes.fsti:207`:

```fstar
unfold
type size_t = uint_t U32 PUB
```

Path:line `lib/Lib.IntTypes.fsti:250`:

```fstar
inline_for_extraction
val secret: #t:inttype -> x:int_t t PUB -> y:int_t t SEC{v x == v y}
```

Bignum limbs are secret by default (`limb t = uint_t t SEC`), and byte buffers in
these APIs are generally `lbuffer uint8 ...`, i.e. secret bytes. The `_vartime`
functions do not have a refinement saying their inputs are public. Therefore,
the secrecy index supports constant-time programming internally, but at the
public F* API boundary it is the caller's responsibility not to feed secrets to
variable-time functions unless the leakage is acceptable.

## 8. Generic exponentiation reuse

`Lib.Exponentiation` is a pure monoid exponentiation library. It serves modular
exponentiation and elliptic-curve scalar multiplication.

Path:line `lib/Lib.Exponentiation.fsti:10`:

```fstar
let get_ith_bit (bBits:nat) (b:nat{b < pow2 bBits}) (i:nat{i < bBits}) =
  b / pow2 i % 2
```

Path:line `lib/Lib.Exponentiation.fsti:18`:

```fstar
let exp_rl (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (acc, c) = Loops.repeati bBits (exp_rl_f k bBits b) (one, a) in
  acc

val exp_rl_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_rl k a bBits b == pow k a b)
```

Path:line `lib/Lib.Exponentiation.fsti:93`:

```fstar
let exp_fw (#t:Type) (k:comm_monoid t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : t =
  let acc0 = if bBits % l = 0 then one else exp_fw_acc0 k a bBits b l in
  let res = Loops.repeati (bBits / l) (exp_fw_f k a bBits b l) acc0 in
  res

val exp_fw_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (exp_fw k a bBits b l == pow k a b)
```

`Spec.Exponentiation` refines this pure library with a `concrete_ops` class,
which relates concrete representations to a commutative monoid.
Path:line `specs/Spec.Exponentiation.fsti:33`:

```fstar
inline_for_extraction
class to_comm_monoid (t:Type) = {
  a_spec: Type;
  comm_monoid: S.comm_monoid a_spec;
  refl: x:t -> a_spec;
}
```

Path:line `specs/Spec.Exponentiation.fsti:54`:

```fstar
inline_for_extraction
class concrete_ops (t:Type) = {
  to: to_comm_monoid t;
  one: one_st t to;
  mul: mul_st t to;
  sqr: sqr_st t to;
}
```

Path:line `specs/Spec.Exponentiation.fsti:149`:

```fstar
val exp_fw_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (k.to.refl (exp_fw k a bBits b l) == S.exp_fw k.to.comm_monoid (k.to.refl a) bBits b l)
```

This is why the same proof pattern appears in bignum modular exponentiation and
EC scalar multiplication: instantiate a monoid, instantiate concrete operations,
prove the implementation loop reflects the pure exponentiation loop, then reuse
the exponentiation lemma.

## 9. Notes for verified clients and reimplementers

1. **Prefer byte-level public modules.** If your proof goal is about an X25519,
   Ed25519, ECDSA, RSA-PSS, or FFDHE result, the top-level modules already expose
   postconditions in terms of pure specs.
2. **Do not erase representation invariants.** Low-level field and point modules
   are only safe when the caller preserves limb bounds, full/lazy reduction, and
   Montgomery-domain invariants. In F*, these are refinements such as
   `as_nat h x < S.prime`, `inv_fully_reduced h x`, `point_inv h p`, and
   `aff_point_inv h p`; in another language they would likely become abstract
   types, typestates, dependent records, or runtime-checked constructors.
3. **Use `bn_v`/`as_seq` deliberately.** Core bignum functions often state exact
   sequence equality to a spec function; SafeAPI and field contexts often state
   `bn_v` arithmetic facts. Reimplementers should maintain both levels: exact
   limb layout and mathematical interpretation.
4. **Type classes are the specialization mechanism.** The bignum development
   specializes by passing records of operations indexed by limb type and length
   (`bn`, `mont`, `exp`), not by relying only on the specialize/inline tactic.
5. **Runtime wrappers are not proof-free.** SafeAPI checks modulus/exponent/input
   bounds at runtime and returns `bool` or `NULL`, but properties such as primality
   for modular inverse remain logical assumptions in the F* contract.
6. **Variable-time is a naming convention plus implementation discipline, not a
   public type prohibition.** The F* types I found do not reject secret buffers at
   `_vartime` call sites.
7. **One signature can serve C and assembly.** Curve25519 Field64 demonstrates
   the pattern: HACL* C and Vale assembly satisfy the same `fadd_t`/`fmul_t`/
   `fsqr_t` signatures, with assembly adding a CPU-feature precondition.
8. **For a different language**, expose the safe public operations as ordinary
   byte APIs, but hide low-level field and point buffers behind constructors that
   enforce reduction and curve membership. For performance-critical code, model
   `mont` and `exp` contexts as capability objects that carry precomputed `r2`,
   `mu`, limb size, and length.

## 10. Items explicitly unconfirmed

* A public Ed25519 sign-then-verify correctness lemma was not found in the F*
  interface surface reviewed here. It may exist elsewhere, but it is unconfirmed
  for this document.
* I did not find `code/rsapss/*.fsti` or `code/ffdhe/*.fsti` files; the F* API
  declarations documented for RSA-PSS and FFDHE are explicit `val`s in `.fst`
  files.
* I did not find a separate `Hacl.Bignum.GenericField.fsti`; the present tree has
  `Hacl.GenericField32.fsti` and `Hacl.GenericField64.fsti`.
