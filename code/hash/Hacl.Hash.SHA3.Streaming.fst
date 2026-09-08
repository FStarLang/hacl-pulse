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

(** The incremental sponge.

    The state is the same shape as the incremental SHA-2: three flat pieces of
    memory the caller owns -- twenty-five lanes of Keccak state, one rate's
    worth of buffered bytes, and the total length -- plus, ghostly, the message
    [seen] so far.  There is no allocation and so no allocation failure.

    The invariant, [Spec.SHA3.Streaming.state_ok], is that the Keccak state has
    absorbed the first [|seen| / r] blocks of [seen] and the buffer holds the
    [|seen| % r] bytes past them.  [update] keeps the buffer strictly partial:
    the moment it fills it is absorbed, so the invariant stays a single
    equation.

    [digest] does not disturb the state.  It copies the twenty-five lanes to
    the stack, builds the padded last block out of the buffered tail, absorbs
    it into the copy, and squeezes from there -- so digesting twice gives the
    same answer, and a SHAKE state can be digested at one length and then fed
    more data. *)
module Hacl.Hash.SHA3.Streaming

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3.Constants
open Spec.SHA3
open Spec.SHA3.Streaming
open Hacl.Hash.SHA3.Core
open Hacl.Hash.SHA3.Sponge
open Hacl.Hash.SHA3
open Hacl.Impl.Copy
open Hacl.Spec.Chunks

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module G = FStar.Ghost


(** {2 The state invariant} *)

unfold let rate_ok (r: SZ.t) =
  SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200

unfold let stream_ok (r: SZ.t) (vst: Seq.seq S64.t) (vbuf: Seq.seq S8.t)
                     (vtot: Seq.seq SZ.t) (seen: Seq.seq S8.t) =
  rate_ok r /\ SZ.fits (Seq.length seen) /\
  Seq.length vtot == 1 /\ SZ.v (Seq.index vtot 0) == Seq.length seen /\
  state_ok (SZ.v r) seen vst vbuf


#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Twenty-five lanes, the size of a Keccak state. *)
fn copy25 (dst: S.slice S64.t) (src: S.slice S64.t)
          (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires S.pts_to dst vd ** S.pts_to src #ps vs **
         pure (Seq.length vd == 25 /\ Seq.length vs == 25)
ensures exists* vd'. S.pts_to dst vd' ** S.pts_to src #ps vs **
        pure (Seq.length vd' == 25 /\ vd' == reveal vs)
{
  S.pts_to_len dst;
  S.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S64.t).
    pts_to i vi ** S.pts_to dst vd' ** S.pts_to src #ps vs **
    pure (SZ.v vi <= 25 /\ Seq.length vd' == 25 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(src.(vi));
    S.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vd'. assert (S.pts_to dst vd');
  assert (pure (reveal vd' `Seq.equal` reveal vs));
}

#pop-options


(** {2 Absorbing blocks into the state}

    The one-shot [absorb_full] starts from [zero_state] and talks about the
    padded message.  Streaming needs neither: it absorbs [nfull] blocks out of
    an arbitrary offset of the caller's buffer into whatever state it has, and
    states the result against the unpadded [seen]. *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

fn absorb_blocks (st: S.slice S64.t) (b: S.slice S64.t) (c: S.slice S64.t)
                 (rotc_tbl: S.slice U32.t) (rc_tbl: S.slice S64.t)
                 (input: S.slice S8.t) (base: SZ.t) (nfull: SZ.t) (nb: SZ.t) (r: SZ.t)
                 (seen: erased (Seq.seq S8.t))
                 (#vst0: erased (Seq.seq S64.t))
                 (#vb0: erased (Seq.seq S64.t)) (#vc0: erased (Seq.seq S64.t))
                 (#pr: perm) (#vr: erased (Seq.seq U32.t))
                 (#prc: perm) (#vrc: erased (Seq.seq S64.t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to st vst0 ** S.pts_to b vb0 ** S.pts_to c vc0 **
         S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc ** S.pts_to input #pin vin **
         pure (rate_ok r /\ Seq.length vst0 == 25 /\
               Seq.length vb0 == 25 /\ Seq.length vc0 == 5 /\ Seq.length vr == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j) /\
               SZ.v base + SZ.v nfull * SZ.v r <= Seq.length vin /\
               (SZ.v nb + SZ.v nfull) * SZ.v r <= Seq.length seen /\
               reveal vst0 == sabsorb (SZ.v r) seen (SZ.v nb) /\
               (forall (k: nat). k < SZ.v nfull * SZ.v r ==>
                  Seq.index vin (SZ.v base + k) ==
                    Seq.index seen (SZ.v nb * SZ.v r + k)))
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t).
  S.pts_to st vst ** S.pts_to b vb ** S.pts_to c vc **
  S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc ** S.pts_to input #pin vin **
  pure (rate_ok r /\ Seq.length vst == 25 /\
        Seq.length vb == 25 /\ Seq.length vc == 5 /\
        vst == sabsorb (SZ.v r) seen (SZ.v nb + SZ.v nfull))
{
  S.pts_to_len st;
  S.pts_to_len input;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi nfull)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t).
    pts_to i vi ** S.pts_to st vst ** S.pts_to b vb ** S.pts_to c vc **
    S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc ** S.pts_to input #pin vin **
    pure (rate_ok r /\ Seq.length vst == 25 /\
          Seq.length vb == 25 /\ Seq.length vc == 5 /\ Seq.length vr == 25 /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j) /\
          SZ.v base + SZ.v nfull * SZ.v r <= Seq.length vin /\
          (SZ.v nb + SZ.v nfull) * SZ.v r <= Seq.length seen /\
          (forall (k: nat). k < SZ.v nfull * SZ.v r ==>
             Seq.index vin (SZ.v base + k) ==
               Seq.index seen (SZ.v nb * SZ.v r + k)) /\
          SZ.v vi <= SZ.v nfull /\
          vst == sabsorb (SZ.v r) seen (SZ.v nb + SZ.v vi))
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (SZ.v r) (SZ.v vi + 1) (SZ.v nfull);
    Math.lemma_mult_le_right (SZ.v r) (SZ.v vi) (SZ.v nfull);
    Math.distributivity_add_left (SZ.v vi) 1 (SZ.v r);
    Math.distributivity_add_left (SZ.v nb) (SZ.v vi) (SZ.v r);
    Math.lemma_mult_le_right (SZ.v r) (SZ.v nb + SZ.v vi + 1) (SZ.v nb + SZ.v nfull);
    Math.distributivity_add_left (SZ.v nb + SZ.v vi) 1 (SZ.v r);
    SZ.fits_lte (SZ.v vi * SZ.v r) (Seq.length vin);
    let off = SZ.add base (SZ.mul vi r);
    assert (pure (SZ.v off + SZ.v r <= Seq.length vin));
    assert (pure ((SZ.v nb + SZ.v vi) * SZ.v r + SZ.v r <= Seq.length seen));
    block_eq_slice_at (SZ.v r) seen (SZ.v nb) (SZ.v vi) vin (SZ.v base) (SZ.v nfull);
    assert (pure (block_at (SZ.v r) seen (SZ.v nb + SZ.v vi) ==
                  Seq.slice vin (SZ.v off) (SZ.v off + SZ.v r)));
    sabsorb_unfold (SZ.v r) seen (SZ.v nb + SZ.v vi);
    xor_block_at st input off r;
    permute_impl st b c rotc_tbl rc_tbl;
    i := SZ.add vi 1sz;
  };
}

#pop-options


(** {2 The three operations} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Reset to the empty message.  The buffer is left alone: nothing reads past
    [tot % r] bytes of it. *)
fn init_impl (st: S.slice S64.t) (tot: S.slice SZ.t) (r: SZ.t)
             (#vst0: erased (Seq.seq S64.t)) (#vtot: erased (Seq.seq SZ.t))
requires S.pts_to st vst0 ** S.pts_to tot vtot **
         pure (rate_ok r /\ Seq.length vst0 == 25 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  S.pts_to st vst ** S.pts_to tot vtot' **
  pure (rate_ok r /\ Seq.length vst == 25 /\ Seq.length vtot' == 1 /\
        SZ.v (Seq.index vtot' 0) == 0 /\
        vst == sabsorb (SZ.v r) (Seq.empty #S8.t) 0)
{
  S.pts_to_len st;
  S.pts_to_len tot;
  zero_state_impl st;
  S.((tot.(0sz) <- 0sz));
}

#pop-options


#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

(** The case of [update] in which the buffer has just been filled: absorb it,
    then absorb whatever whole blocks of [data] follow straight out of the
    caller's buffer, then keep the trailing bytes.  Split out of [update_impl]
    because the two cases together are more than one query can carry. *)
fn update_full (st: S.slice S64.t) (b: S.slice S64.t) (c: S.slice S64.t)
               (rotc_tbl: S.slice U32.t) (rc_tbl: S.slice S64.t)
               (buf: S.slice S8.t) (data: S.slice S8.t)
               (blen: SZ.t) (nb0: SZ.t) (fill: SZ.t) (r: SZ.t)
               (seen: erased (Seq.seq S8.t)) (seen1: erased (Seq.seq S8.t))
               (#vst0: erased (Seq.seq S64.t))
               (#vb0: erased (Seq.seq S64.t)) (#vc0: erased (Seq.seq S64.t))
               (#pr: perm) (#vr: erased (Seq.seq U32.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
               (#vbuf: erased (Seq.seq S8.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to st vst0 ** S.pts_to b vb0 ** S.pts_to c vc0 **
         S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
         S.pts_to buf vbuf ** S.pts_to data #pd vdata **
         pure (rate_ok r /\ Seq.length vst0 == 25 /\
               Seq.length vb0 == 25 /\ Seq.length vc0 == 5 /\ Seq.length vr == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j) /\
               Seq.length vbuf == SZ.v r /\
               reveal seen1 == Seq.append (reveal seen) (reveal vdata) /\
               Seq.length seen == SZ.v nb0 * SZ.v r + SZ.v blen /\
               SZ.v blen + SZ.v fill == SZ.v r /\
               SZ.v fill <= Seq.length vdata /\
               SZ.fits (Seq.length seen1) /\
               reveal vst0 == sabsorb (SZ.v r) seen1 (SZ.v nb0) /\
               (forall (k: nat). k < SZ.v r ==>
                  Seq.index vbuf k == Seq.index seen1 (SZ.v nb0 * SZ.v r + k)))
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t)
                (vbuf': Seq.seq S8.t).
  S.pts_to st vst ** S.pts_to b vb ** S.pts_to c vc **
  S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
  S.pts_to buf vbuf' ** S.pts_to data #pd vdata **
  pure (rate_ok r /\ Seq.length vb == 25 /\ Seq.length vc == 5 /\
        state_ok (SZ.v r) (reveal seen1) vst vbuf')
{
  S.pts_to_len st;
  S.pts_to_len buf;
  S.pts_to_len data;
  let dlen = S.len data;
  Seq.lemma_len_append (reveal seen) (reveal vdata);

  Math.distributivity_add_left (SZ.v nb0) 1 (SZ.v r);
  assert (pure ((SZ.v nb0 + 1) * SZ.v r == Seq.length seen + SZ.v fill));
  assert (pure ((SZ.v nb0 + 1) * SZ.v r <= Seq.length seen1));
  absorb_blocks st b c rotc_tbl rc_tbl buf 0sz 1sz nb0 r seen1;

  let restlen = SZ.sub dlen fill;
  let nfull = SZ.div restlen r;
  let tl = SZ.rem restlen r;
  Math.euclidean_division_definition (SZ.v restlen) (SZ.v r);
  Math.distributivity_add_left (SZ.v nb0 + 1) (SZ.v nfull) (SZ.v r);
  Math.multiple_division_lemma (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v r);
  Math.multiple_modulo_lemma (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v r);
  Math.lemma_div_plus (SZ.v tl) (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v r);
  Math.lemma_mod_plus (SZ.v tl) (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v r);
  tail_agrees (SZ.v r) (reveal seen) (reveal vdata)
              (SZ.v nb0 + 1) (SZ.v fill) (SZ.v nfull * SZ.v r);
  Math.lemma_mult_le_left (SZ.v nb0 + 1) 1 (SZ.v r);
  absorb_blocks st b c rotc_tbl rc_tbl data fill nfull (SZ.add nb0 1sz) r seen1;

  tail_agrees (SZ.v r) (reveal seen) (reveal vdata)
              (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v dlen - SZ.v tl) (SZ.v tl);
  assert (pure (Seq.length seen1 ==
                (SZ.v nb0 + 1 + SZ.v nfull) * SZ.v r + SZ.v tl));
  assert (pure (Seq.length seen1 / SZ.v r == SZ.v nb0 + 1 + SZ.v nfull));
  assert (pure (Seq.length seen1 % SZ.v r == SZ.v tl));
  copy_range buf 0sz data (SZ.sub dlen tl) tl;
  with vbuf2. assert (S.pts_to buf vbuf2);
  assert (pure (forall (k: nat). k < SZ.v tl ==>
                  Seq.index vbuf2 k ==
                  Seq.index seen1 ((SZ.v nb0 + 1 + SZ.v nfull) * SZ.v r + k)));
}

#pop-options


#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

(** Absorb [data]. *)
fn update_impl (st: S.slice S64.t) (b: S.slice S64.t) (c: S.slice S64.t)
               (rotc_tbl: S.slice U32.t) (rc_tbl: S.slice S64.t)
               (buf: S.slice S8.t) (tot: S.slice SZ.t) (data: S.slice S8.t) (r: SZ.t)
               (seen: erased (Seq.seq S8.t))
               (#vst0: erased (Seq.seq S64.t))
               (#vb0: erased (Seq.seq S64.t)) (#vc0: erased (Seq.seq S64.t))
               (#pr: perm) (#vr: erased (Seq.seq U32.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
               (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to st vst0 ** S.pts_to b vb0 ** S.pts_to c vc0 **
         S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
         S.pts_to buf vbuf ** S.pts_to tot vtot ** S.pts_to data #pd vdata **
         pure (Seq.length vb0 == 25 /\ Seq.length vc0 == 5 /\ Seq.length vr == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j) /\
               stream_ok r vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t)
                (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to st vst ** S.pts_to b vb ** S.pts_to c vc **
  S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
  S.pts_to buf vbuf' ** S.pts_to tot vtot' ** S.pts_to data #pd vdata **
  pure (Seq.length vb == 25 /\ Seq.length vc == 5 /\
        stream_ok r vst vbuf' vtot' (Seq.append seen vdata))
{
  S.pts_to_len st;
  S.pts_to_len buf;
  S.pts_to_len tot;
  S.pts_to_len data;
  let tlen = S.(tot.(0sz));
  let blen = SZ.rem tlen r;
  let nb0 = SZ.div tlen r;
  let dlen = S.len data;
  let fill = szmin (SZ.sub r blen) dlen;
  let seen1 = G.hide (Seq.append (reveal seen) (reveal vdata));
  Seq.lemma_len_append (reveal seen) (reveal vdata);
  Math.euclidean_division_definition (SZ.v tlen) (SZ.v r);

  sabsorb_congr (SZ.v r) (reveal seen) (reveal seen1) (SZ.v nb0);

  copy_range buf blen data 0sz fill;
  with vbuf1. assert (S.pts_to buf vbuf1);
  buf_agrees (SZ.v r) (reveal seen) (reveal vdata) (reveal vbuf) (reveal vbuf1)
             (SZ.v nb0) (SZ.v blen) (SZ.v fill);

  if (SZ.eq (SZ.add blen fill) r)
  ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t)
                  (vbuf': Seq.seq S8.t).
    S.pts_to st vst ** S.pts_to b vb ** S.pts_to c vc **
    S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
    S.pts_to buf vbuf' ** S.pts_to tot vtot ** S.pts_to data #pd vdata **
    pure (Seq.length vb == 25 /\ Seq.length vc == 5 /\
          state_ok (SZ.v r) (reveal seen1) vst vbuf')
  {
    update_full st b c rotc_tbl rc_tbl buf data blen nb0 fill r seen seen1;
  }
  else
  {
    (* All of [data] fitted in the buffer. *)
    Math.small_division_lemma_1 (SZ.v blen + SZ.v dlen) (SZ.v r);
    Math.lemma_div_plus (SZ.v blen + SZ.v dlen) (SZ.v nb0) (SZ.v r);
    Math.lemma_mod_plus (SZ.v blen + SZ.v dlen) (SZ.v nb0) (SZ.v r);
    ()
  };

  S.((tot.(0sz) <- SZ.add tlen dlen));
}

#pop-options


#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

(** The digest of everything seen so far, at whatever output length is asked
    for.  The state is left usable. *)
fn digest_impl (st: S.slice S64.t) (b: S.slice S64.t) (c: S.slice S64.t)
               (rotc_tbl: S.slice U32.t) (rc_tbl: S.slice S64.t)
               (buf: S.slice S8.t) (tot: S.slice SZ.t) (out: S.slice S8.t)
               (r: SZ.t) (suffix: U8.t)
               (seen: erased (Seq.seq S8.t))
               (#pst: perm) (#vst0: erased (Seq.seq S64.t))
               (#vb0: erased (Seq.seq S64.t)) (#vc0: erased (Seq.seq S64.t))
               (#pr: perm) (#vr: erased (Seq.seq U32.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
               (#vbuf: erased (Seq.seq S8.t))
               (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
               (#vout0: erased (Seq.seq S8.t))
requires S.pts_to st #pst vst0 ** S.pts_to b vb0 ** S.pts_to c vc0 **
         S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
         S.pts_to buf vbuf ** S.pts_to tot #ptot vtot ** S.pts_to out vout0 **
         pure (Seq.length vb0 == 25 /\ Seq.length vc0 == 5 /\ Seq.length vr == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j) /\
               stream_ok r vst0 vbuf vtot seen)
ensures exists* (vb: Seq.seq S64.t) (vc: Seq.seq S64.t)
                (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  S.pts_to st #pst vst0 ** S.pts_to b vb ** S.pts_to c vc **
  S.pts_to rotc_tbl #pr vr ** S.pts_to rc_tbl #prc vrc **
  S.pts_to buf vbuf' ** S.pts_to tot #ptot vtot ** S.pts_to out vout **
  pure (rate_ok r /\ Seq.length vb == 25 /\ Seq.length vc == 5 /\
        Seq.length vout == Seq.length vout0 /\
        vout == keccak (SZ.v r) suffix seen (Seq.length vout0))
{
  S.pts_to_len st;
  S.pts_to_len b;
  S.pts_to_len c;
  S.pts_to_len buf;
  S.pts_to_len tot;
  S.pts_to_len out;
  let tlen = S.(tot.(0sz));
  let blen = SZ.rem tlen r;
  let nb0 = SZ.div tlen r;
  Math.euclidean_division_definition (SZ.v tlen) (SZ.v r);

  let z64 = S64.classify 0uL;
  let mut starr = [| z64; 25sz |];
  A.pts_to_len starr;
  let st2 = S.from_array starr 25sz;
  S.pts_to_len st2;
  copy25 st2 st;

  (* The buffered tail, on its own, is a message whose last (and only) block is
     the last block of the padded [seen]. *)
  split3 (reveal vbuf) 0 (SZ.v blen);
  let tail = S.subslice buf 0sz blen;
  with vtail. assert (S.pts_to tail vtail);
  assert (pure (Seq.length vtail == SZ.v blen /\
                (forall (k: nat). k < SZ.v blen ==>
                   Seq.index vtail k ==
                     Seq.index seen (Seq.length seen / SZ.v r * SZ.v r + k))));

  let z8 = S8.classify 0uy;
  let mut blkarr = [| z8; 200sz |];
  A.pts_to_len blkarr;
  let blkfull = S.from_array blkarr 200sz;
  let blk = S.subslice blkfull 0sz r;
  last_block blk tail r suffix;
  with vk. assert (S.pts_to blk vk);
  Math.small_div (SZ.v blen) (SZ.v r);
  assert (pure (vk == block_at (SZ.v r) (padded (SZ.v r) suffix vtail) 0));
  last_block_eq (SZ.v r) suffix (reveal seen) (reveal vtail);
  assert (pure (reveal vk ==
                block_at (SZ.v r) (padded (SZ.v r) suffix seen) (Seq.length seen / SZ.v r)));

  (* Two subslices are live here -- the buffered tail and the last block -- so
     the resource to unfold has to be named. *)
  unfold (S.subslice_rest tail buf 1.0R 0sz blen vbuf);
  S.join tail _ _;
  S.join _ _ buf;

  xor_block_at st2 blk 0sz r;
  permute_impl st2 b c rotc_tbl rc_tbl;
  absorb_from_state (SZ.v r) suffix (reveal seen);
  with vst2. assert (S.pts_to st2 vst2);
  assert (pure (reveal vst2 == absorb (SZ.v r) suffix seen));

  squeeze_impl out st2 b c rotc_tbl rc_tbl r;

  unfold S.subslice_rest;
  S.join blk _ _;
  S.join _ _ blkfull;
  S.to_array blkfull;
  S.to_array st2;
  S.pts_to_len b;
  S.pts_to_len c;
}

#pop-options
