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

(** ChaCha20 encryption.

    One loop over blocks, one loop over the bytes of a block; the second is
    what makes the implementation indifferent to a partial last block, and it
    is why [Spec.Chacha20] states encryption pointwise.

    The block counter is kept in a [FStar.UInt32.t] and incremented with
    [add_mod].  Wrapping is not a correctness worry -- the loop invariant only
    claims the counter is right {i while there are bytes left}, and there are
    bytes left only as long as the true counter is below [2^32] -- so no branch
    is needed to guard the last increment.

    [core_impl] clobbers word twelve of the state, which is where the counter
    lives.  Rather than restoring it, the invariant only remembers that the
    state agrees with the initial state {i off} word twelve, which is all
    [core] depends on. *)
module Hacl.Chacha20

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Hacl.Impl.Bytes
open Hacl.Impl.Copy
open Spec.Chacha20
open Hacl.Chacha20.Core

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

(** [core] reads word twelve only through [with_counter], which overwrites it,
    so two states that agree elsewhere have the same block function. *)
let core_agree (st st': state) (c: U32.t)
  : Lemma
      (requires forall (i: nat). i < 16 ==> i <> 12 ==> Seq.index st i == Seq.index st' i)
      (ensures core st c == core st' c)
  = Seq.lemma_eq_elim (with_counter st c) (with_counter st' c)

(** Overwriting word twelve preserves that agreement. *)
let with_counter_agree (st st': state) (c: U32.t)
  : Lemma
      (requires forall (i: nat). i < 16 ==> i <> 12 ==> Seq.index st i == Seq.index st' i)
      (ensures forall (i: nat). i < 16 ==> i <> 12 ==>
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
        (forall (i: nat). i < 16 ==> i <> 12 ==> Seq.index vs i == Seq.index st0 i))
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

(** {2 The initial state} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn init_state (st: A.array S32.t) (key: A.array S8.t) (nonce: A.array S8.t) (ctr0: U32.t)
              (#v0: erased (Seq.seq S32.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length v0 == 16 /\ Seq.length vkey == 32 /\ Seq.length vnon == 12)
ensures exists* (vs: Seq.seq S32.t).
  A.pts_to st vs ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\ Seq.length vs == 16 /\
        vs == init vkey vnon ctr0)
{
  A.pts_to_len st;
  A.pts_to_len key;
  A.pts_to_len nonce;

  A.((st.(0sz) <- c0));
  A.((st.(1sz) <- c1));
  A.((st.(2sz) <- c2));
  A.((st.(3sz) <- c3));

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vs: Seq.seq S32.t).
    pts_to i vi ** A.pts_to st vs ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
    pure (SZ.v vi <= 8 /\ Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
          Seq.length vs == 16 /\
          (forall (j: nat). j < 4 + SZ.v vi ==>
             Seq.index vs j == Seq.index (init vkey vnon ctr0) j))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right 4 (SZ.v vi + 1) 8;
    let x = load_le #S32.t key (SZ.mul vi 4sz);
    word_u32.v_extensional x (Seq.index (words_from_le #S32.t 8 (reveal vkey)) (SZ.v vi));
    A.((st.(SZ.add 4sz vi) <- x));
    i := SZ.add vi 1sz;
  };

  A.((st.(12sz) <- S32.classify ctr0));

  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 3sz)
  invariant exists* (vn: SZ.t) (vs: Seq.seq S32.t).
    pts_to n vn ** A.pts_to st vs ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
    pure (SZ.v vn <= 3 /\ Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
          Seq.length vs == 16 /\
          (forall (j: nat). j < 13 + SZ.v vn ==>
             Seq.index vs j == Seq.index (init vkey vnon ctr0) j))
  decreases (3 - SZ.v (!n))
  {
    let vn = !n;
    Math.lemma_mult_le_right 4 (SZ.v vn + 1) 3;
    let x = load_le #S32.t nonce (SZ.mul vn 4sz);
    word_u32.v_extensional x (Seq.index (words_from_le #S32.t 3 (reveal vnon)) (SZ.v vn));
    A.((st.(SZ.add 13sz vn) <- x));
    n := SZ.add vn 1sz;
  };

  with vs. assert (A.pts_to st vs);
  Seq.lemma_eq_intro vs (init vkey vnon ctr0);
  Seq.lemma_eq_elim vs (init vkey vnon ctr0);
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
               (forall (i: nat). i < 16 ==> i <> 12 ==>
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

      void Hacl_Chacha20_encrypt(uint8_t *out,
                                 uint8_t *msg, size_t mlen,
                                 uint8_t *key, uint8_t *nonce, uint32_t ctr);

    [out] and [msg] must not overlap, [key] is 32 bytes and [nonce] is 12.
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
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               Seq.length vmsg <= max_len ctr0)
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to msg #pm vmsg **
  A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vmsg <= max_len ctr0 /\
        vo == chacha20 vkey vnon ctr0 vmsg)
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

  (* Eight blocks at a time while that is possible and the processor
     allows; the loop below finishes up one block at a time. *)
  let nb = Hacl.Chacha20.Vec256.encrypt_vec out msg mlen starr ctr0 st0;

  let mut base = nb;
  let mut ctr = U32.add_mod ctr0 (SZ.sizet_to_uint32 (SZ.div nb 64sz));

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
          (forall (i: nat). i < 16 ==> i <> 12 ==>
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

(** Decryption is the same function -- ChaCha20 is additive -- and is exported
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
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               Seq.length vmsg <= max_len ctr0)
ensures exists* (vo: Seq.seq S8.t).
  A.pts_to out vo ** A.pts_to msg #pm vmsg **
  A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vmsg <= max_len ctr0 /\
        vo == chacha20 vkey vnon ctr0 vmsg)
{
  encrypt out msg mlen key nonce ctr0;
}
