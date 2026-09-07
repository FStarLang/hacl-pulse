# Guide for verified F\* clients

This chapter is practical: how to set up a project that verifies against
HACL\*/EverCrypt, what a real client looks like, which idioms recur, and which
mistakes cost the most time. It assumes [fstar-api.md](fstar-api.md).

---

## 1. Project setup

### 1.1 Include paths

`Makefile.include` exists specifically for this purpose — its first lines say

> This Makefile can be included by client projects; it exports the set of
> include directories relative to HACL_HOME and exports the set of needed
> [bundles].

The two exports that matter:

```make
ALL_HACL_SOURCE_DIRS = \
  $(LIB_DIR) $(SPECS_DIR) $(CODE_DIRS) $(VALE_DIRS) \
  $(EVERCRYPT_DIRS) \
  $(KRML_HOME)/runtime

ALL_HACL_DIRS ?= $(ALL_HACL_SOURCE_DIRS) $(HACL_HOME)/obj
```
<sub>`Makefile.include:53-58`</sub>

- Use `ALL_HACL_SOURCE_DIRS` if you are verifying from source.
- Use `ALL_HACL_DIRS` (which adds `obj/`) if you want to consume **pre-built
  `.checked` files** — strongly recommended, since re-verifying HACL\* takes
  hours.
- `VALE_BUNDLES` (`Makefile.include:4`) is the list of `-bundle` arguments your
  own KaRaMeL invocation needs so that the Vale interop modules land in the
  right C files. If you extract your own code and link against a HACL\*
  distribution, you must pass these or you will get duplicate/missing symbols.

### 1.2 F\* flags

Match the repository's own flags, from `Hacl.fst.config.json`:

```json
"options": [
  "--use_hints",
  "--use_hint_hashes",
  "--record_hints",
  "--odir", "obj",
  "--cmi",
  "--already_cached", "Prims FStar LowStar C Spec.Loops TestLib WasmSupport",
  "--warn_error", "@240+241@247-272-274@319@328@331@332@337",
  "--trivial_pre_for_unannotated_effectful_fns", "false",
  "--hint_dir", "hints",
  "--z3version", "4.8.5"
]
```

Notes for a client:

- **`--z3version 4.8.5`.** Proof stability is tied to the SMT solver version.
  If your client verifies with a different Z3, expect to re-tune `z3rlimit`s.
- **`--cmi`** (cross-module inlining) is required: much of HACL\* relies on
  `inline_for_extraction` definitions being visible across module boundaries.
- **`--already_cached`** tells F\* not to re-verify the standard library. Add
  `*,-YourNamespace` style patterns to also treat HACL\* as trusted-and-cached.
- **`--use_hints`** replays recorded proofs from `hints/`. Hints are not part of
  the trusted base — they only make verification fast and repeatable.

`Hacl.fst.config.json` is also what the VS Code F\* extension reads, so a
client project should ship its own analogous file.

### 1.3 Which modules to open

| You want | Open |
|---|---|
| Agile, CPU-dispatching crypto | `EverCrypt.*` |
| A specific algorithm/implementation | `Hacl.*` |
| Pure specifications and theorems | `Spec.*` |
| Buffers, sequences, integers | `Lib.Buffer`, `Lib.Sequence`, `Lib.IntTypes` (HACL\* style) or `LowStar.Buffer`, `FStar.Seq` (EverCrypt style) |
| Stateful effect | `FStar.HyperStack.ST` |

Beware: `Lib.IntTypes` and `FStar.UInt32` both define `v`, `+.`-style
operators, and literals. Most HACL\* files `open Lib.IntTypes` and then use
`FStar.UInt32` qualified, or vice versa. Pick a convention early.

---

## 2. A real verified client, annotated

`providers/test/Test.fst` contains a genuine verified use of
`EverCrypt.AEAD`. Reduced to its skeleton (`providers/test/Test.fst:125-209`):

```fstar
#push-options "--z3rlimit 700 --fuel 0 --ifuel 0"

let test_aead_st alg key key_len iv iv_len aad aad_len tag tag_len
                 plaintext plaintext_len ciphertext ciphertext_len
: ST unit
  (requires (fun _ ->
    B.recallable key /\ B.recallable iv /\ B.recallable aad /\
    B.recallable tag /\ B.recallable plaintext /\ B.recallable ciphertext /\
    B.len key == key_len /\ ... /\
    B.disjoint plaintext aad // required by EverCrypt.AEAD.encrypt_st
  ))
  (ensures (fun _ _ _ -> True))
=
  ...
  push_frame();
  B.recall key; B.recall iv; B.recall aad; B.recall plaintext;
  let st = B.alloca B.null 1ul in
  let e = EverCrypt.AEAD.create_in #alg HyperStack.root st key in
  begin match e with
  | UnsupportedAlgorithm -> ()   // non-fatal: CI machines may lack AES-NI
  | Success ->
    let h1 = HST.get () in
    let st = B.index st 0ul in
    assert (B.loc_disjoint (B.loc_buffer iv) (EverCrypt.AEAD.footprint h1 st));
    push_frame ();
    let ciphertext' = B.alloca 0uy ciphertext_blen in
    ...
    let h2 = HST.get () in
    EverCrypt.AEAD.frame_invariant B.loc_none st h1 h2;
    if EverCrypt.AEAD.(encrypt #(G.hide alg) st iv iv_len aad aad_len
                       plaintext plaintext_len ciphertext' tag' <> Success)
    then LowStar.Failure.failwith "Failure AEAD encrypt\n";
    ...
```

Seven things to learn from it:

1. **`HST.get ()` names the memory.** Every time you want to talk about "the
   heap right now", bind `let h = HST.get () in`. It is ghost and free.
2. **Preconditions of the callee become preconditions of your function.** The
   comment `// required by EverCrypt.AEAD.encrypt_st` marks a disjointness
   obligation that had to be propagated all the way out to the caller. Expect
   this; design your own signatures to accept it.
3. **`frame_invariant` sometimes must be called explicitly.** Even though it
   carries an `SMTPat`, after a sequence of `B.alloca`s the pattern may not
   trigger; the explicit call `EverCrypt.AEAD.frame_invariant B.loc_none st h1 h2`
   is the fix. Note the location is `B.loc_none`: allocation modifies nothing.
4. **`UnsupportedAlgorithm` is a real, reachable outcome.** A verified client
   must handle it — `create_in` returns it when the CPU lacks the required
   features. Do not assume `Success`.
5. **Zero-length buffers need care.** `let plaintext_blen = if plaintext_len = 0ul then 1ul else plaintext_len in`
   then `B.sub ... 0ul plaintext_len` — you cannot `alloca` zero bytes, so
   allocate one and take an empty sub-buffer.
6. **Global data must be recalled.** `B.recall key` re-establishes liveness of
   a `recallable` (top-level, immutable) buffer in the current heap. Without
   it, `live h key` is not known. See §4.3.
7. **Resource limits are explicit and large.** `--z3rlimit 700 --fuel 0 --ifuel 0`.
   Turning fuel off (no recursive unrolling, no inversion) and raising the
   rlimit is the standard tactic for buffer-heavy code.

---

## 3. Proving a round trip

The user-facing question "can I prove `decrypt (encrypt p) == p`?" has a precise
answer. The pieces:

**Spec level** (`specs/Spec.Agile.AEAD.fsti:125-126`):

```fstar
val correctness: #a:supported_alg -> k:kv a -> n:iv a -> aad:ad a -> p:plain a ->
  Lemma (decrypt k n aad (encrypt k n aad p) == Some p)
```

**Stateful level.** `encrypt` gives you (`EverCrypt.AEAD.fsti:327-328`):

```fstar
S.equal (S.append (B.as_seq h1 cipher) (B.as_seq h1 tag))
  (Spec.encrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain))
```

and `decrypt` reasons about (`EverCrypt.AEAD.fsti:478,485`):

```fstar
let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
...
let plain = Spec.decrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) cipher_tag in
```

**The argument.** Encryption's postcondition says the concatenation
`cipher ++ tag` *is* `Spec.encrypt k iv ad p`. Decryption's postcondition is
phrased in terms of `Spec.decrypt k iv ad (cipher ++ tag)`. Substituting and
applying `correctness`:

```fstar
Spec.decrypt k iv ad (Spec.encrypt k iv ad p) == Some p
```

Two consequences you can prove in your own client:

- **Decryption cannot fail.** The `AuthenticationFailure` branch asserts
  `None? plain` (`EverCrypt.AEAD.fsti:500`), which contradicts `Some p`.
  So on a genuine round trip, `decrypt` provably returns `Success`. You can
  discharge the error branch as dead code rather than propagating it.
- **The output is the original plaintext.** The `Success` branch gives
  `Some? plain /\ S.equal (Some?.v plain) (B.as_seq h1 dst)`, hence
  `B.as_seq h1 dst == B.as_seq h0 plain`.

The obligations you must meet to make the substitution go through:

1. The same state `s` is used for both calls, and `as_kv` is preserved — both
   `encrypt` and `decrypt` ensure `as_kv (B.deref h1 s) == as_kv (B.deref h0 s)`,
   so the key is provably the same one.
2. The `iv` and `ad` buffers are unmodified between the two calls. Since both
   calls only modify `footprint ∪ cipher ∪ tag`, framing gives this — provided
   `iv` and `ad` are disjoint from those, which the preconditions already
   require.
3. `cipher` and `tag` are unmodified between the calls (same argument).

This is exactly the reasoning a C client cannot perform, and it is the concrete
answer to "why bother with the F\* API".

See [fstar-specs.md](fstar-specs.md) for which other families have an
analogous correctness lemma — and, importantly, which do not.

---

## 4. Recurring idioms

### 4.1 Framing across your own code

The pattern is always:

```fstar
let h0 = HST.get () in
Hacl.Foo.op out inp;            (* ensures modifies (loc out) h0 h1 *)
let h1 = HST.get () in
(* now: as_seq h1 other == as_seq h0 other, for any `other` disjoint from `out` *)
```

If F\* does not see it, the missing ingredient is almost always a
*disjointness* fact, not a framing lemma. Add `assert (B.loc_disjoint ...)` and
see which one fails.

### 4.2 Stack discipline

```fstar
push_frame ();
let tmp = B.alloca 0uy 32ul in
...
pop_frame ()
```

`push_frame`/`pop_frame` must be balanced on every path for the function to be
in the `Stack` effect. A common failure is an early `return`-like branch that
skips `pop_frame`.

`B.alloca` returns a buffer live only until the matching `pop_frame`. If you
need the data to survive, allocate in an eternal region with
`B.malloc r init len` (and remember `B.free`).

### 4.3 Recallable global tables

Precomputed tables are top-level `let`-bound buffers. Their liveness is not
automatic in an arbitrary heap; the client must call `B.recall b` (or, in the
HACL\* dialect, `Lib.Buffer.recall_contents b s` which recovers *both*
liveness and the contents). Symptom of forgetting: an unprovable `live h b`
that "obviously" holds.

### 4.4 Erased and implicit arguments

`encrypt #(G.hide alg) st ...` — the algorithm index is `G.erased`, so pass
`G.hide alg`. If you have a `G.erased alg` and need the value in a proof, use
`G.reveal`. At run time, use `alg_of_state` (`EverCrypt.AEAD.fsti:136`),
which recovers the algorithm from the state in the `Stack` effect.

### 4.5 Following `_st` abbreviations

When you read

```fstar
val scalarmult: scalarmult_st M51 True
```

the contract is *not* in this file. Chase `scalarmult_st` to
`Hacl.Impl.Curve25519.Generic.fsti:13`. This indirection is pervasive in
`code/`; budget for it. Grepping for `let <name>_st` is the fastest route.

### 4.6 Discharging CPU-feature preconditions

```fstar
if EverCrypt.AutoConfig2.has_adx () && EverCrypt.AutoConfig2.has_bmi2 () then
  Hacl.Curve25519_64.scalarmult out priv pub
else
  Hacl.Curve25519_51.scalarmult out priv pub
```

Or avoid the issue entirely by calling `EverCrypt.Curve25519.scalarmult`, which
has no CPU precondition. Also remember `EverCrypt.AutoConfig2.init ()` must
have been called (all flags default to `false` otherwise; see
[fstar-api-provider.md](fstar-api-provider.md)).

### 4.7 Resource-limit hygiene

```fstar
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let my_function ... = ...
#pop-options
```

Always scope options with `#push-options`/`#pop-options` rather than
`#set-options`, so one hard function does not slow the whole file.
`#reset-options "--using_facts_from '* -Test.Vectors'"`
(`providers/test/Test.fst:121`) shows the other lever: prune the context when a
module pulls in large irrelevant definitions.

---

## 5. Pitfalls

| Symptom | Cause | Fix |
|---|---|---|
| `live h b` unprovable for a top-level buffer | Recallable global | `B.recall b` / `Lib.Buffer.recall_contents` |
| Invariant lost after unrelated allocation | `frame_invariant` SMT pattern did not trigger | Call `frame_invariant B.loc_none s h1 h2` explicitly |
| "Assertion failed" on a disjointness goal you believe | Two buffers derived by `B.sub` from the same parent | Use `B.loc_disjoint` on the *sub-buffers*; `B.sub` disjointness needs the index ranges |
| Cannot `alloca` when length may be 0 | Zero-length allocation is disallowed | Allocate `max 1 len` then `B.sub b 0ul len` |
| Timeout that goes away with `--fuel 4` | Recursive spec being unrolled | Prefer `--fuel 0 --ifuel 0` plus explicit `assert_norm`/lemma applications |
| `pow2 31` not reduced | Kept symbolic | `assert_norm (pow2 31 == 2147483648)` (`providers/test/Test.fst:145`) |
| Type error mixing `uint8` and `FStar.UInt8.t` | Secret vs public integers | Use `Lib.RawIntTypes` to declassify explicitly, or stay in one dialect |
| Cannot compare two secret integers | By design | Use `Lib.ByteSequence.lbytes_eq` / a constant-time comparison primitive |
| Verification succeeds locally, fails in CI | Z3 version or hint mismatch | Pin `--z3version 4.8.5`; regenerate hints with `--record_hints` |
| Extraction produces duplicate symbols | Missing `VALE_BUNDLES` in your KaRaMeL invocation | Include `Makefile.include` and pass `$(VALE_BUNDLES)` |
| `create_in` returns `UnsupportedAlgorithm` at run time | CPU lacks required features | Handle the branch; it is not dead code |

---

## 6. Choosing between the layers

| Situation | Use |
|---|---|
| You want the best implementation on the current CPU, and don't want to reason about features | `EverCrypt.*` |
| You need a specific implementation (e.g. for reproducibility, or a target without AES-NI) | `Hacl.<Alg>_<repr>` |
| You need agility over algorithms at run time | `EverCrypt.Hash`, `EverCrypt.AEAD` |
| You need incremental/streaming input | The streaming functor instances — see [fstar-api-hashes-macs.md](fstar-api-hashes-macs.md) |
| You only need to state a property, not run code | `Spec.*` — pure, no memory reasoning at all |

A useful discipline: write your protocol logic against `Spec.*` first and prove
it there, where there are no buffers, no framing, and no CPU features. Then
implement it with `EverCrypt.*`/`Hacl.*` and connect the two through the
`as_seq`/`as_kv` postconditions. The stateful proof then reduces to memory
management, which is mechanical.

---

## 7. What a verified client gains over a C client

To close the loop with [fstar-api.md](fstar-api.md) §1:

1. **Usage protocols are enforced.** The key-expansion-then-reuse protocol of
   `EverCrypt.AEAD` "is enforced for verified F\* clients but, naturally, isn't
   for C clients" (`EverCrypt.AEAD.fsti:10-11`).
2. **Lengths cannot be wrong.** Every length argument is tied to the buffer by
   a refinement, or carried in the type.
3. **Aliasing cannot be wrong.** Disjointness is a proof obligation, and the
   precise permitted overlaps (e.g. in-place encryption via
   `B.disjoint plain cipher \/ plain == cipher`) are stated exactly.
4. **Uninitialized/stale state cannot be used.** `invariant` is a precondition
   of every operation; you cannot call `encrypt` on a state you did not
   successfully create.
5. **Spec-level theorems are available**, e.g. the AEAD round trip of §3.
6. **Framing is free.** You get to prove that a crypto call did not disturb the
   rest of your program's memory — something no C API can offer.

The cost is real (proof effort, build complexity, Z3 pinning), which is why
both APIs are supported. But for a client that is itself verified, layers 1–6
are not conveniences; they are the whole point.
