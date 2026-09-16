(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** Salsa20 encryption.

    One loop over blocks, one loop over the bytes of a block; the second is
    what makes the implementation indifferent to a partial last block, and it
    is why [Spec.Salsa20] states encryption pointwise.

    The block counter is kept in a [FStar.UInt32.t] and incremented with
    [add_mod].  Wrapping is not a correctness worry -- the loop invariant only
    claims the counter is right {i while there are bytes left}, and there are
    bytes left only as long as the true counter is below [2^32] -- so no branch
    is needed to guard the last increment.

    [core_impl] clobbers word eight of the state, which is where the counter
    lives.  Rather than restoring it, the invariant only remembers that the
    state agrees with the initial state {i off} word eight, which is all
    [core] depends on. *)
module Hacl.Salsa20

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Hacl.Impl.Bytes
open Hacl.Impl.Copy
open Spec.Salsa20
open Hacl.Salsa20.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module A = Pulse.Lib.Array
module U32 = FStar.UInt32
module G = FStar.Ghost

(** {2 Two facts about the state} *)

(** [core] reads word eight only through [with_counter], which overwrites it,
    so two states that agree elsewhere have the same block function. *)
let core_agree (st st': state) (c: U32.t)
  : Lemma
      (requires forall (i: nat). i < 16 ==> i <> 8 ==> Seq.index st i == Seq.index st' i)
      (ensures core st c == core st' c)
  = Seq.lemma_eq_elim (with_counter st c) (with_counter st' c)

(** Overwriting word eight preserves that agreement. *)
let with_counter_agree (st st': state) (c: U32.t)
  : Lemma
      (requires forall (i: nat). i < 16 ==> i <> 8 ==> Seq.index st i == Seq.index st' i)
      (ensures forall (i: nat). i < 16 ==> i <> 8 ==>
                 Seq.index (with_counter st c) i == Seq.index st' i)
  = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** The byte the implementation is about to write is the byte the
    specification asks for.  [b] is the start of the current block, [k] the
    offset within it, and [vs] the -- possibly counter-clobbered -- state. *)
let out_byte (st0: state) (ctr0: U32.t)
             (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
             (vs: state) (c: U32.t) (b k: nat)
  : Lemma
      (requires
        b % size_block == 0 /\ k < size_block /\ b + k < Seq.length msg /\
        U32.v c == U32.v ctr0 + b / size_block /\
        (forall (i: nat). i < 16 ==> i <> 8 ==> Seq.index vs i == Seq.index st0 i))
      (ensures
        Seq.index (encrypt_bytes st0 ctr0 msg) (b + k) ==
        S8.logxor (Seq.index msg (b + k))
                  (Seq.index (words_to_le #S32.t 16 (core vs c)) k))
  = let p = b + k in
    Math.euclidean_division_definition b size_block;
    Math.lemma_div_plus k (b / size_block) size_block;
    Math.lemma_mod_plus k (b / size_block) size_block;
    Math.small_div k size_block;
    Math.small_mod k size_block;
    div_lt size_block p (pow2 32 - U32.v ctr0);
    assert (p / size_block == b / size_block);
    assert (p % size_block == k);
    assert (ctr_at ctr0 p == c);
    core_agree vs st0 c

#pop-options

(** The step of the driver's loop, guarded: nothing is claimed about the
    counter once the message has run out, because there is no next block to
    claim it for.  This is what lets the counter be bumped with [add_mod] and
    without a branch. *)
let step_ok (ctr0: U32.t) (len: nat) (b n: nat)
  : Lemma
      (requires
        len <= max_len ctr0 /\ b % size_block == 0 /\ b + n <= len /\
        n == (if size_block <= len - b then size_block else len - b))
      (ensures
        b + n < len ==>
          ((b + n) % size_block == 0 /\ (b + n) / size_block == b / size_block + 1 /\
           U32.v ctr0 + (b + n) / size_block < pow2 32))
  = if b + n < len then begin
      Math.lemma_mod_plus b 1 size_block;
      Math.lemma_div_plus b 1 size_block;
      div_lt size_block (b + n) (pow2 32 - U32.v ctr0)
    end

(** {2 The initial state}

    Salsa20 does not lay its state out in blocks, so the setup is written as
    the twelve words that Salsa20 and HSalsa20 agree on -- the four constants
    on the diagonal and the key either side of them -- followed by whatever
    goes in the hole at words six to nine. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn setup_base (st: A.array S32.t) (key: A.array S8.t)
              (#v0: erased (Seq.seq S32.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to key #pk vkey **
         pure (Seq.length v0 == 16 /\ Seq.length vkey == 32)
ensures exists* (vs: Seq.seq S32.t).
  A.pts_to st vs ** A.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vs == 16 /\
        (forall (i: nat). i < 16 ==> (i < 6 \/ 9 < i) ==>
           Seq.index vs i == base (words_from_le #S32.t 8 vkey) i))
{
  A.pts_to_len st;
  A.pts_to_len key;

  A.((st.(0sz)  <- c0));
  A.((st.(5sz)  <- c1));
  A.((st.(10sz) <- c2));
  A.((st.(15sz) <- c3));

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (vs: Seq.seq S32.t).
    pts_to i vi ** A.pts_to st vs ** A.pts_to key #pk vkey **
    pure (SZ.v vi <= 4 /\ Seq.length vkey == 32 /\ Seq.length vs == 16 /\
          Seq.index vs 0 == c0 /\ Seq.index vs 5 == c1 /\
          Seq.index vs 10 == c2 /\ Seq.index vs 15 == c3 /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vs (1 + j) == Seq.index (words_from_le #S32.t 8 (reveal vkey)) j))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right 4 (SZ.v vi + 1) 8;
    let x = load_le #S32.t key (SZ.mul vi 4sz);
    word_u32.v_extensional x (Seq.index (words_from_le #S32.t 8 (reveal vkey)) (SZ.v vi));
    A.((st.(SZ.add 1sz vi) <- x));
    i := SZ.add vi 1sz;
  };

  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 4sz)
  invariant exists* (vn: SZ.t) (vs: Seq.seq S32.t).
    pts_to n vn ** A.pts_to st vs ** A.pts_to key #pk vkey **
    pure (SZ.v vn <= 4 /\ Seq.length vkey == 32 /\ Seq.length vs == 16 /\
          Seq.index vs 0 == c0 /\ Seq.index vs 5 == c1 /\
          Seq.index vs 10 == c2 /\ Seq.index vs 15 == c3 /\
          (forall (j: nat). j < 4 ==>
             Seq.index vs (1 + j) == Seq.index (words_from_le #S32.t 8 (reveal vkey)) j) /\
          (forall (j: nat). j < SZ.v vn ==>
             Seq.index vs (11 + j) == Seq.index (words_from_le #S32.t 8 (reveal vkey)) (4 + j)))
  decreases (4 - SZ.v (!n))
  {
    let vn = !n;
    Math.lemma_mult_le_right 4 (SZ.v vn + 5) 8;
    let x = load_le #S32.t key (SZ.mul (SZ.add 4sz vn) 4sz);
    word_u32.v_extensional x (Seq.index (words_from_le #S32.t 8 (reveal vkey)) (4 + SZ.v vn));
    A.((st.(SZ.add 11sz vn) <- x));
    n := SZ.add vn 1sz;
  }
}

(** Salsa20's own state: the eight-byte nonce at words six and seven, the
    counter at eight, and word nine -- the top half of what the design says
    is a 64-bit counter -- permanently zero. *)
fn init_state (st: A.array S32.t) (key: A.array S8.t) (nonce: A.array S8.t) (ctr0: U32.t)
              (#v0: erased (Seq.seq S32.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length v0 == 16 /\ Seq.length vkey == 32 /\ Seq.length vnon == 8)
ensures exists* (vs: Seq.seq S32.t).
  A.pts_to st vs ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 8 /\ Seq.length vs == 16 /\
        vs == init vkey vnon ctr0)
{
  A.pts_to_len st;
  A.pts_to_len key;
  A.pts_to_len nonce;

  setup_base st key;

  let n0 = load_le #S32.t nonce 0sz;
  word_u32.v_extensional n0 (Seq.index (words_from_le #S32.t 2 (reveal vnon)) 0);
  A.((st.(6sz) <- n0));
  let n1 = load_le #S32.t nonce 4sz;
  word_u32.v_extensional n1 (Seq.index (words_from_le #S32.t 2 (reveal vnon)) 1);
  A.((st.(7sz) <- n1));

  A.((st.(8sz) <- S32.classify ctr0));
  A.((st.(9sz) <- S32.classify 0ul));

  with vs. assert (A.pts_to st vs);
  Seq.lemma_eq_intro vs (init vkey vnon ctr0);
  Seq.lemma_eq_elim vs (init vkey vnon ctr0);
}

(** HSalsa20's: a sixteen-byte nonce fills the hole outright. *)
fn hinit_state (st: A.array S32.t) (key: A.array S8.t) (nonce: A.array S8.t)
               (#v0: erased (Seq.seq S32.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
               (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length v0 == 16 /\ Seq.length vkey == 32 /\ Seq.length vnon == 16)
ensures exists* (vs: Seq.seq S32.t).
  A.pts_to st vs ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 16 /\ Seq.length vs == 16 /\
        vs == hinit vkey vnon)
{
  A.pts_to_len st;
  A.pts_to_len key;
  A.pts_to_len nonce;

  setup_base st key;

  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 4sz)
  invariant exists* (vn: SZ.t) (vs: Seq.seq S32.t).
    pts_to n vn ** A.pts_to st vs ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
    pure (SZ.v vn <= 4 /\ Seq.length vkey == 32 /\ Seq.length vnon == 16 /\
          Seq.length vs == 16 /\
          (forall (i: nat). i < 16 ==> (i < 6 \/ 9 < i) ==>
             Seq.index vs i == base (words_from_le #S32.t 8 vkey) i) /\
          (forall (j: nat). j < SZ.v vn ==>
             Seq.index vs (6 + j) == Seq.index (words_from_le #S32.t 4 (reveal vnon)) j))
  decreases (4 - SZ.v (!n))
  {
    let vn = !n;
    Math.lemma_mult_le_right 4 (SZ.v vn + 1) 4;
    let x = load_le #S32.t nonce (SZ.mul vn 4sz);
    word_u32.v_extensional x (Seq.index (words_from_le #S32.t 4 (reveal vnon)) (SZ.v vn));
    A.((st.(SZ.add 6sz vn) <- x));
    n := SZ.add vn 1sz;
  };

  with vs. assert (A.pts_to st vs);
  Seq.lemma_eq_intro vs (hinit vkey vnon);
  Seq.lemma_eq_elim vs (hinit vkey vnon);
}

#pop-options

(** {2 One block's worth of output} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Xor [n] keystream bytes into the output, starting at [b].  Split out of
    the driver so that the driver's own obligations stay about block
    arithmetic and this one's stay about bytes. *)
fn xor_chunk (out: A.array S8.t) (msg: A.array S8.t) (kb: A.array S8.t)
             (b: SZ.t) (n: SZ.t)
             (st0: G.erased state) (ctr0: U32.t) (c: U32.t)
             (vs: G.erased (Seq.seq S32.t))
             (#vout: erased (Seq.seq S8.t))
             (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
             (#pb: perm) (#vkb: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to msg #pm vmsg ** A.pts_to kb #pb vkb **
         pure (Seq.length vout == Seq.length vmsg /\ Seq.length vkb == 64 /\
               Seq.length vs == 16 /\
               Seq.length vmsg <= max_len ctr0 /\
               SZ.v b % size_block == 0 /\ SZ.v n <= size_block /\
               SZ.v b + SZ.v n <= Seq.length vmsg /\
               U32.v c == U32.v ctr0 + SZ.v b / size_block /\
               (forall (i: nat). i < 16 ==> i <> 8 ==>
                  Seq.index (reveal vs) i == Seq.index (reveal st0) i) /\
               reveal vkb == words_to_le #S32.t 16 (core (reveal vs) c) /\
               (forall (p: nat). p < SZ.v b ==>
                  Seq.index vout p == Seq.index (encrypt_bytes st0 ctr0 vmsg) p))
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to msg #pm vmsg ** A.pts_to kb #pb vkb **
  pure (Seq.length vmsg <= max_len ctr0 /\ Seq.length vo == Seq.length vmsg /\
        SZ.v b + SZ.v n <= Seq.length vmsg /\
        (forall (p: nat). p < SZ.v b + SZ.v n ==>
           Seq.index vo p == Seq.index (encrypt_bytes st0 ctr0 vmsg) p))
{
  A.pts_to_len out;
  A.pts_to_len msg;
  A.pts_to_len kb;
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk n)
  invariant exists* (vk: SZ.t) (vo: Seq.seq S8.t).
    pts_to k vk ** A.pts_to out vo ** A.pts_to msg #pm vmsg ** A.pts_to kb #pb vkb **
    pure (SZ.v vk <= SZ.v n /\ Seq.length vmsg <= max_len ctr0 /\
          Seq.length vo == Seq.length vmsg /\
          SZ.v b + SZ.v n <= Seq.length vmsg /\
          (forall (p: nat). p < SZ.v b + SZ.v vk ==>
             Seq.index vo p == Seq.index (encrypt_bytes st0 ctr0 vmsg) p))
  decreases (SZ.v n - SZ.v (!k))
  {
    let vk = !k;
    let x = A.(msg.(SZ.add b vk));
    let y = A.(kb.(vk));
    out_byte (reveal st0) ctr0 (reveal vmsg) (reveal vs) c (SZ.v b) (SZ.v vk);
    A.((out.(SZ.add b vk) <- S8.logxor x y));
    k := SZ.add vk 1sz;
  }
}

#pop-options

(** {2 The driver} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** The C entry point.

      void Hacl_Salsa20_encrypt(uint8_t *out,
                                 uint8_t *msg, size_t mlen,
                                 uint8_t *key, uint8_t *nonce, uint32_t ctr);

    [out] and [msg] must not overlap, [key] is 32 bytes and [nonce] is 8.
    The message length is bounded by [(2^32 - ctr) * 64], which is what it
    takes for the 32-bit block counter not to wrap; on any real platform the
    bound is only reachable with [ctr] very close to [2^32]. *)
fn encrypt (out: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
                 (key: A.array S8.t) (nonce: A.array S8.t) (ctr0: U32.t)
                 (#vout: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
                 (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                 (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to msg #pm vmsg **
         A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vout == Seq.length vmsg /\
               Seq.length vmsg == SZ.v mlen /\
               Seq.length vkey == 32 /\ Seq.length vnon == 8 /\
               Seq.length vmsg <= max_len ctr0)
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to msg #pm vmsg **
  A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 8 /\
        Seq.length vmsg <= max_len ctr0 /\
        vo == salsa20 vkey vnon ctr0 vmsg)
{
  A.pts_to_len out;
  A.pts_to_len msg;
  A.pts_to_len key;
  A.pts_to_len nonce;

  let z32 = S32.zero;
  let z8 = S8.classify 0uy;

  let mut starr = [| z32; 16sz |];
  A.pts_to_len starr;
  let mut ksarr = [| z32; 16sz |];
  A.pts_to_len ksarr;
  let mut kbarr = [| z8; 64sz |];
  A.pts_to_len kbarr;
  A.pts_to_len starr;
  A.pts_to_len ksarr;
  A.pts_to_len kbarr;

  init_state starr key nonce ctr0;
  let st0 : G.erased state = G.hide (init (reveal vkey) (reveal vnon) ctr0);

  let mut base = 0sz;
  let mut ctr = ctr0;

  while (let b = !base; SZ.lt b mlen)
  invariant exists* (b: SZ.t) (c: U32.t) (vo: Seq.seq S8.t)
                    (vs: Seq.seq S32.t) (vk: Seq.seq S32.t) (vkb: Seq.seq S8.t).
    pts_to base b ** pts_to ctr c **
    A.pts_to out vo ** A.pts_to msg #pm vmsg **
    A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
    A.pts_to starr vs ** A.pts_to ksarr vk ** A.pts_to kbarr vkb **
    pure (Seq.length vmsg <= max_len ctr0 /\ Seq.length vo == Seq.length vmsg /\
          Seq.length vs == 16 /\ Seq.length vk == 16 /\ Seq.length vkb == 64 /\
          SZ.v b <= Seq.length vmsg /\
          (SZ.v b < Seq.length vmsg ==>
             SZ.v b % size_block == 0 /\
             U32.v c == U32.v ctr0 + SZ.v b / size_block) /\
          (forall (i: nat). i < 16 ==> i <> 8 ==>
             Seq.index vs i == Seq.index (reveal st0) i) /\
          (forall (p: nat). p < SZ.v b ==>
             Seq.index vo p == Seq.index (encrypt_bytes st0 ctr0 vmsg) p))
  decreases (Seq.length vmsg - SZ.v (!base))
  {
    let b = !base;
    let c = !ctr;
    let n = szmin 64sz (SZ.sub mlen b);

    with vs0. assert (A.pts_to starr vs0);
    core_impl ksarr starr c;
    store_words_le #S32.t kbarr ksarr 16sz;

    xor_chunk out msg kbarr b n st0 ctr0 c (G.hide vs0);

    step_ok ctr0 (Seq.length vmsg) (SZ.v b) (SZ.v n);

    base := SZ.add b n;
    ctr := U32.add_mod c 1ul;
  };

  with vo. assert (A.pts_to out vo);
  Seq.lemma_eq_intro vo (encrypt_bytes st0 ctr0 vmsg);
  Seq.lemma_eq_elim vo (encrypt_bytes st0 ctr0 vmsg);

  ()
}

#pop-options

(** Decryption is the same function -- Salsa20 is additive -- and is exported
    under its own name so that callers read the way they mean. *)
fn decrypt (out: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
           (key: A.array S8.t) (nonce: A.array S8.t) (ctr0: U32.t)
           (#vout: erased (Seq.seq S8.t))
           (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to msg #pm vmsg **
         A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vout == Seq.length vmsg /\
               Seq.length vmsg == SZ.v mlen /\
               Seq.length vkey == 32 /\ Seq.length vnon == 8 /\
               Seq.length vmsg <= max_len ctr0)
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to msg #pm vmsg **
  A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 8 /\
        Seq.length vmsg <= max_len ctr0 /\
        vo == salsa20 vkey vnon ctr0 vmsg)
{
  encrypt out msg mlen key nonce ctr0;
}

(** {2 The first keystream block}

      void Hacl_Salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n);

    [out] is 64 bytes.  This exists because NaCl's secretbox wants the first
    thirty-two bytes of block zero as a Poly1305 key and throws the rest
    away; nothing else in the library has a use for it. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn key_block0 (out: A.array S8.t) (key: A.array S8.t) (nonce: A.array S8.t)
              (#vout: erased (Seq.seq S8.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vout == 64 /\ Seq.length vkey == 32 /\ Seq.length vnon == 8)
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 8 /\
        vo == Spec.Salsa20.key_block0 vkey vnon)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len nonce;

  let z32 = S32.zero;
  let mut starr = [| z32; 16sz |];
  A.pts_to_len starr;
  let mut ksarr = [| z32; 16sz |];
  A.pts_to_len ksarr;
  A.pts_to_len starr;

  init_state starr key nonce 0ul;
  core_impl ksarr starr 0ul;
  store_words_le #S32.t out ksarr 16sz;
  ()
}

#pop-options

(** {2 HSalsa20}

      void Hacl_Salsa20_hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n);

    [key] is 32 bytes, [n] is 16 and [out] is 32.  The twenty rounds are the
    same ones; what is left out is the feedforward, and what comes back is
    the eight words that were not the key going in -- the diagonal and the
    nonce. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn hsalsa20 (out: A.array S8.t) (key: A.array S8.t) (nonce: A.array S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vout == 32 /\ Seq.length vkey == 32 /\ Seq.length vnon == 16)
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 16 /\
        vo == Spec.Salsa20.hsalsa20 vkey vnon)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len nonce;

  let z32 = S32.zero;
  let mut starr = [| z32; 16sz |];
  A.pts_to_len starr;
  let mut hw = [| z32; 8sz |];
  A.pts_to_len hw;
  A.pts_to_len starr;

  hinit_state starr key nonce;
  rounds_impl starr;

  let x0 = A.(starr.(0sz));  A.((hw.(0sz) <- x0));
  let x1 = A.(starr.(5sz));  A.((hw.(1sz) <- x1));
  let x2 = A.(starr.(10sz)); A.((hw.(2sz) <- x2));
  let x3 = A.(starr.(15sz)); A.((hw.(3sz) <- x3));
  let x4 = A.(starr.(6sz));  A.((hw.(4sz) <- x4));
  let x5 = A.(starr.(7sz));  A.((hw.(5sz) <- x5));
  let x6 = A.(starr.(8sz));  A.((hw.(6sz) <- x6));
  let x7 = A.(starr.(9sz));  A.((hw.(7sz) <- x7));

  with vh. assert (A.pts_to hw vh);
  Seq.lemma_eq_intro vh (hwords (rounds (hinit vkey vnon)));
  Seq.lemma_eq_elim vh (hwords (rounds (hinit vkey vnon)));

  store_words_le #S32.t out hw 8sz;
  assert (pure (Seq.length vkey == 32));
  ()
}

#pop-options
