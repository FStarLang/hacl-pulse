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

(** The incremental hash.

    The state is three pieces of memory -- an eight-word accumulator, one
    block of buffered bytes, and the total length -- and one piece of ghost
    state, [seen], the concatenation of everything fed in so far.  The
    invariant is [Spec.SHA2.Streaming.state_ok]: the accumulator has absorbed
    [|seen| / block_len] blocks and the buffer holds the [|seen| % block_len]
    bytes that are left over.

    [update] therefore keeps the buffer strictly partial: as soon as it fills,
    it is absorbed.  [digest] does not disturb the state -- it copies the
    accumulator, and hands the partial buffer to the same
    [Hacl.Hash.SHA2.Core.tail_and_finish] the one-shot hash uses, with the
    already-absorbed bytes as its ghost prefix. *)
module Hacl.Hash.SHA2.Streaming

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Loops
open Spec.SHA2
open Spec.SHA2.Streaming
open Hacl.Hash.SHA2.Core
open Hacl.Impl.Copy
open Hacl.Spec.Chunks

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module Classical = FStar.Classical

(** {2 The state invariant} *)

unfold let acc_ok (#t: Type0) {| word t |} (p: params t)
                  (vacc: Seq.seq t) (vbuf: Seq.seq S8.t) (seen: Seq.seq S8.t) =
  Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
  vacc == absorb p seen (Seq.length seen / block_len #t) /\
  (forall (k: nat). k < Seq.length seen % block_len #t ==>
     Seq.index vbuf k ==
       Seq.index seen (Seq.length seen / block_len #t * block_len #t + k))

unfold let stream_ok (#t: Type0) {| word t |} (p: params t)
                     (vacc: Seq.seq t) (vbuf: Seq.seq S8.t) (vtot: Seq.seq SZ.t)
                     (seen: Seq.seq S8.t) =
  Seq.length seen < pow2 61 /\ Seq.length seen < max_input #t /\
  Seq.length vtot == 1 /\ SZ.v (Seq.index vtot 0) == Seq.length seen /\
  acc_ok p vacc vbuf seen

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Eight words, the size of an accumulator. *)
fn copy8 (#t: Type0) (dst: A.array t) (src: A.array t)
         (#vd: erased (Seq.seq t)) (#ps: perm) (#vs: erased (Seq.seq t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (Seq.length vd == 8 /\ Seq.length vs == 8)
ensures exists* vd'. A.pts_to dst vd' ** A.pts_to src #ps vs **
        pure (Seq.length vd' == 8 /\ vd' == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vd': Seq.seq t).
    pts_to i vi ** A.pts_to dst vd' ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 8 /\ Seq.length vd' == 8 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vd'. assert (A.pts_to dst vd');
  assert (pure (reveal vd' `Seq.equal` reveal vs));
}

#pop-options

(** {2 Absorbing blocks into the accumulator}

    This is the only place the streaming state meets [Spec.SHA2.padded].
    [hash_blocks] states its contract against the padding of the whole
    message; [absorb_congr] says that is the same thing as the [n]-block fold
    of [seen], since the two agree on the bytes that have been absorbed. *)

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

fn absorb_blocks (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (kt: A.array t) (wsb: A.array t) (acc: A.array t)
                 (input: A.array S8.t) (base_in: SZ.t) (nfull: SZ.t) (nb: SZ.t)
                 (seen: erased (Seq.seq S8.t))
                 (#pk: perm) (#vk: erased (Seq.seq t))
                 (#vw0: erased (Seq.seq t)) (#vacc: erased (Seq.seq t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to acc vacc **
         A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length vacc == 8 /\
               SZ.v base_in + SZ.v nfull * block_len #t <= Seq.length vin /\
               (SZ.v nb + SZ.v nfull) * block_len #t <= Seq.length seen /\
               Seq.length seen < max_input #t /\
               reveal vacc == absorb p seen (SZ.v nb) /\
               (forall (k: nat). k < SZ.v nfull * block_len #t ==>
                  Seq.index vin (SZ.v base_in + k) ==
                    Seq.index seen (SZ.v nb * block_len #t + k)))
ensures exists* (vw: Seq.seq t) (vacc': Seq.seq t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to acc vacc' **
  A.pts_to input #pin vin **
  pure (Seq.length vw == (rounds p) /\ Seq.length vacc' == 8 /\
        vacc' == absorb p seen (SZ.v nb + SZ.v nfull))
{
  A.pts_to_len input;
  A.pts_to_len acc;
  let bl = block_len_sz #t #w;

  Math.lemma_mult_le_right (block_len #t) (SZ.v nb) (SZ.v nb + SZ.v nfull);
  Math.distributivity_add_left (SZ.v nb) (SZ.v nfull) (block_len #t);
  SZ.fits_lte (SZ.v nfull * block_len #t) (Seq.length vin);
  let hi = SZ.add base_in (SZ.mul nfull bl);
  assert (pure (SZ.v base_in <= SZ.v hi /\ SZ.v hi <= Seq.length vin));
  split3 (reveal vin) (SZ.v base_in) (SZ.v hi);
  let sub = Sub.sub input base_in hi;
  with vsub. assert (A.pts_to sub #pin vsub);
  assert (pure (Seq.length vsub == SZ.v nfull * block_len #t));
  Math.multiple_division_lemma (SZ.v nfull) (block_len #t);
  assert (pure (SZ.v nfull == Seq.length vsub / block_len #t));

  let pre = G.hide (Seq.slice (reveal seen) 0 (SZ.v nb * block_len #t));
  let whole = G.hide (Seq.append (reveal pre) (reveal vsub));
  Seq.lemma_len_append (reveal pre) (reveal vsub);
  assert (pure (Seq.length whole == (SZ.v nb + SZ.v nfull) * block_len #t));
  assert (pure (Seq.length whole <= Seq.length seen));

  (* [whole] and [seen] agree on every byte [whole] has. *)
  Seq.lemma_eq_intro (reveal whole) (Seq.slice (reveal seen) 0 (Seq.length whole));

  absorb_padded p (reveal whole) (SZ.v nb);
  absorb_congr p (reveal whole) (reveal seen) (SZ.v nb);
  assert (pure (reveal vacc ==
                repeati_g (SZ.v nb) (update_step p (padded #t (Seq.append pre vsub)))
                  (reveal p.iv)));

  hash_blocks p kt wsb acc sub bl nb nfull pre;

  absorb_padded p (reveal whole) (SZ.v nb + SZ.v nfull);
  absorb_congr p (reveal whole) (reveal seen) (SZ.v nb + SZ.v nfull);

  Sub.unsub input (SZ.v base_in) (SZ.v hi) sub;
  with vin1. assert (A.pts_to input #pin vin1);
  assert (pure (Seq.equal vin1 vin));
  ()
}

#pop-options

(** {2 The three operations} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Reset to the empty message. *)
fn init_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (ivt: A.array t) (acc: A.array t) (buf: A.array S8.t) (tot: A.array SZ.t)
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vacc: erased (Seq.seq t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
             (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to ivt #pi vi ** A.pts_to acc vacc ** A.pts_to buf #pb vbuf **
         A.pts_to tot vtot **
         pure (reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
               Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq t) (vtot': Seq.seq SZ.t).
  A.pts_to ivt #pi vi ** A.pts_to acc vacc' ** A.pts_to buf #pb vbuf **
  A.pts_to tot vtot' **
  pure (stream_ok p vacc' vbuf vtot' (Seq.empty #S8.t))
{
  A.pts_to_len ivt;
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  copy8 acc ivt;
  A.((tot.(0sz) <- 0sz));
  absorb_zero p (Seq.empty #S8.t);
  assert (pure (Seq.length (Seq.empty #S8.t) / block_len #t == 0));
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** The case of [update] in which the buffer has just been filled: absorb it,
    then absorb whatever whole blocks of [data] follow, then keep the trailing
    bytes.  Split out of [update_impl] because the two cases together make a
    verification condition large enough that even linear arithmetic times out.

    On entry [buf] already holds block [nb0] of [seen1] in full, and [seen1] is
    [seen] followed by the caller's data. *)
fn update_full (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (wsb: A.array t) (acc: A.array t)
               (buf: A.array S8.t) (data: A.array S8.t) (dlen: SZ.t)
               (blen: SZ.t) (nb0: SZ.t) (fill: SZ.t)
               (seen: erased (Seq.seq S8.t)) (seen1: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t)) (#vacc: erased (Seq.seq t))
               (#vbuf: erased (Seq.seq S8.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to acc vacc **
         A.pts_to buf vbuf ** A.pts_to data #pd vdata **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
               reveal seen1 == Seq.append (reveal seen) (reveal vdata) /\
               Seq.length seen == SZ.v nb0 * block_len #t + SZ.v blen /\
               SZ.v blen + SZ.v fill == block_len #t /\
               SZ.v fill <= Seq.length vdata /\
               Seq.length seen1 < max_input #t /\
               SZ.fits (Seq.length seen1) /\
               reveal vacc == absorb p seen1 (SZ.v nb0) /\
               (forall (k: nat). k < block_len #t ==>
                  Seq.index vbuf k == Seq.index seen1 (SZ.v nb0 * block_len #t + k)))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vw: Seq.seq t) (vacc': Seq.seq t) (vbuf': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to acc vacc' **
  A.pts_to buf vbuf' ** A.pts_to data #pd vdata **
  pure (Seq.length vw == (rounds p) /\ acc_ok p vacc' vbuf' (reveal seen1))
{
  A.pts_to_len kt;
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len data;
  let bl = block_len_sz #t #w;
  Seq.lemma_len_append (reveal seen) (reveal vdata);

  Math.distributivity_add_left (SZ.v nb0) 1 (block_len #t);
  assert (pure ((SZ.v nb0 + 1) * block_len #t == Seq.length seen + SZ.v fill));
  assert (pure ((SZ.v nb0 + 1) * block_len #t <= Seq.length seen1));
  absorb_blocks p kt wsb acc buf 0sz 1sz nb0 seen1;

  let restlen = SZ.sub dlen fill;
  let nfull = SZ.div restlen bl;
  let tl = SZ.rem restlen bl;
  Math.euclidean_division_definition (SZ.v restlen) (block_len #t);
  Math.distributivity_add_left (SZ.v nb0 + 1) (SZ.v nfull) (block_len #t);
  Math.multiple_division_lemma (SZ.v nb0 + 1 + SZ.v nfull) (block_len #t);
  Math.multiple_modulo_lemma (SZ.v nb0 + 1 + SZ.v nfull) (block_len #t);
  Math.lemma_div_plus (SZ.v tl) (SZ.v nb0 + 1 + SZ.v nfull) (block_len #t);
  Math.lemma_mod_plus (SZ.v tl) (SZ.v nb0 + 1 + SZ.v nfull) (block_len #t);
  tail_agrees (block_len #t) (reveal seen) (reveal vdata)
              (SZ.v nb0 + 1) (SZ.v fill) (SZ.v nfull * block_len #t);
  Math.lemma_mult_le_left (SZ.v nb0 + 1) 1 (block_len #t);
  SZ.fits_lte (SZ.v nb0 + 1) (Seq.length seen1);
  absorb_blocks p kt wsb acc data fill nfull (SZ.add nb0 1sz) seen1;

  tail_agrees (block_len #t) (reveal seen) (reveal vdata)
              (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v dlen - SZ.v tl) (SZ.v tl);
  assert (pure (Seq.length seen1 ==
                (SZ.v nb0 + 1 + SZ.v nfull) * block_len #t + SZ.v tl));
  assert (pure (Seq.length seen1 / block_len #t == SZ.v nb0 + 1 + SZ.v nfull));
  assert (pure (Seq.length seen1 % block_len #t == SZ.v tl));
  copy_range buf 0sz data (SZ.sub dlen tl) tl;
  with vbuf2. assert (A.pts_to buf vbuf2);
  assert (pure (forall (k: nat). k < SZ.v tl ==>
                  Seq.index vbuf2 k ==
                  Seq.index seen1 ((SZ.v nb0 + 1 + SZ.v nfull) * block_len #t + k)));
}

#pop-options

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

(** Absorb [data]. *)
fn update_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (wsb: A.array t) (acc: A.array t)
               (buf: A.array S8.t) (tot: A.array SZ.t) (data: A.array S8.t) (dlen: SZ.t)
               (seen: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t)) (#vacc: erased (Seq.seq t))
               (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to acc vacc **
         A.pts_to buf vbuf ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               stream_ok p vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               Seq.length seen + Seq.length vdata < max_input #t /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vw: Seq.seq t) (vacc': Seq.seq t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to acc vacc' **
  A.pts_to buf vbuf' ** A.pts_to tot vtot' ** A.pts_to data #pd vdata **
  pure (Seq.length vw == (rounds p) /\
        stream_ok p vacc' vbuf' vtot' (Seq.append seen vdata))
{
  A.pts_to_len kt;
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len data;
  let bl = block_len_sz #t #w;
  let tlen = A.(tot.(0sz));
  let blen = SZ.rem tlen bl;
  let nb0 = SZ.div tlen bl;
  let fill = szmin (SZ.sub bl blen) dlen;
  let seen1 = G.hide (Seq.append (reveal seen) (reveal vdata));
  Seq.lemma_len_append (reveal seen) (reveal vdata);
  Math.euclidean_division_definition (SZ.v tlen) (block_len #t);

  absorb_congr p (reveal seen) (reveal seen1) (SZ.v nb0);

  copy_range buf blen data 0sz fill;
  with vbuf1. assert (A.pts_to buf vbuf1);
  buf_agrees (block_len #t) (reveal seen) (reveal vdata) (reveal vbuf) (reveal vbuf1)
             (SZ.v nb0) (SZ.v blen) (SZ.v fill);

  if (SZ.eq (SZ.add blen fill) bl)
  ensures exists* (vw: Seq.seq t) (vacc': Seq.seq t) (vbuf': Seq.seq S8.t).
    A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to acc vacc' **
    A.pts_to buf vbuf' ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
    pure (Seq.length vw == (rounds p) /\ acc_ok p vacc' vbuf' (reveal seen1))
  {
    update_full p kt wsb acc buf data dlen blen nb0 fill seen seen1;
  }
  else
  {
    (* All of [data] fitted in the buffer. *)
    Math.small_division_lemma_1 (SZ.v blen + SZ.v dlen) (block_len #t);
    Math.lemma_div_plus (SZ.v blen + SZ.v dlen) (SZ.v nb0) (block_len #t);
    Math.lemma_mod_plus (SZ.v blen + SZ.v dlen) (SZ.v nb0) (block_len #t);
    ()
  };

  A.((tot.(0sz) <- SZ.add tlen dlen));
}

#pop-options

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

(** The digest of everything seen so far.  The state is left usable. *)
fn digest_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (wsb: A.array t) (acc: A.array t)
               (buf: A.array S8.t) (tot: A.array SZ.t) (out: A.array S8.t)
               (seen: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t)) (#pa: perm) (#vacc: erased (Seq.seq t))
               (#vbuf: erased (Seq.seq S8.t)) (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
               (#vout: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to acc #pa vacc **
         A.pts_to buf vbuf ** A.pts_to tot #ptot vtot ** A.pts_to out vout **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length vout == (hash_bytes p) /\
               stream_ok p vacc vbuf vtot seen)
ensures exists* (vw: Seq.seq t) (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to acc #pa vacc **
  A.pts_to buf vbuf' ** A.pts_to tot #ptot vtot ** A.pts_to out vout' **
  pure (Seq.length vw == (rounds p) /\ Seq.length seen < max_input #t /\
        vout' == hash p seen)
{
  A.pts_to_len kt;
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len out;
  let bl = block_len_sz #t #w;
  let tlen = A.(tot.(0sz));
  let blen = SZ.rem tlen bl;
  let nb0 = SZ.div tlen bl;
  Math.euclidean_division_definition (SZ.v tlen) (block_len #t);

  let z0: t = zero #t #w;
  let mut starr = [| z0; 8sz |];
  A.pts_to_len starr;
  A.pts_to_len starr;
  copy8 starr acc;

  split3 (reveal vbuf) 0 (SZ.v blen);
  let sub = Sub.sub buf 0sz blen;
  with vsub. assert (A.pts_to sub vsub);
  let pre = G.hide (Seq.slice (reveal seen) 0 (SZ.v nb0 * block_len #t));
  Seq.lemma_len_append (reveal pre) (reveal vsub);
  buf_is_tail (block_len #t) (reveal seen) (reveal vbuf) (SZ.v nb0) (SZ.v blen);
  absorb_padded p (reveal seen) (SZ.v nb0);

  tail_and_finish p kt wsb starr out sub tlen nb0 0sz blen pre;

  Sub.unsub buf 0 (SZ.v blen) sub;
  ()
}

#pop-options
