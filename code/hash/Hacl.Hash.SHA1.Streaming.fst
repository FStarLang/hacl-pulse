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

(** The incremental SHA-1.

    Structurally identical to [Hacl.Hash.SHA2.Streaming]: an accumulator of
    five words, a one-block buffer holding the bytes that have arrived since
    the last whole block, and a byte count.  [update] tops the buffer up,
    absorbs it if it filled, absorbs whatever whole blocks of the caller's
    data follow, and keeps the remainder; [digest] runs the padding over a
    copy so the state stays usable.

    The chunking lemmas ([Hacl.Spec.Chunks]) take the block length as an
    argument rather than a word type, so they are reused unchanged. *)
module Hacl.Hash.SHA1.Streaming

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Loops
open Spec.SHA1
open Spec.SHA1.Streaming
open Hacl.Hash.SHA1.Core
open Hacl.Impl.Copy
open Hacl.Spec.Chunks

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module G = FStar.Ghost

(** {2 The state invariant} *)

unfold let acc_ok (vacc: Seq.seq S32.t) (vbuf: Seq.seq S8.t) (seen: Seq.seq S8.t) =
  Seq.length vacc == state_words /\ Seq.length vbuf == block_len /\
  vacc == absorb seen (Seq.length seen / block_len) /\
  (forall (k: nat). k < Seq.length seen % block_len ==>
     Seq.index vbuf k ==
       Seq.index seen (Seq.length seen / block_len * block_len + k))

unfold let stream_ok (vacc: Seq.seq S32.t) (vbuf: Seq.seq S8.t) (vtot: Seq.seq SZ.t)
                     (seen: Seq.seq S8.t) =
  Seq.length seen < max_input /\
  Seq.length vtot == 1 /\ SZ.v (Seq.index vtot 0) == Seq.length seen /\
  acc_ok vacc vbuf seen

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Five words, the size of an accumulator. *)
fn copy5 (dst: A.array S32.t) (src: A.array S32.t)
         (#vd: erased (Seq.seq S32.t)) (#ps: perm) (#vs: erased (Seq.seq S32.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (Seq.length vd == state_words /\ Seq.length vs == state_words)
ensures exists* vd'. A.pts_to dst vd' ** A.pts_to src #ps vs **
        pure (Seq.length vd' == state_words /\ vd' == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S32.t).
    pts_to i vi ** A.pts_to dst vd' ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 5 /\ Seq.length vd' == state_words /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k))
  decreases (5 - SZ.v (!i))
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

    This is the only place the streaming state meets [Spec.SHA1.padded].
    [hash_blocks] states its contract against the padding of the whole
    message; [absorb_congr] says that is the same thing as the [n]-block fold
    of [seen], since the two agree on the bytes that have been absorbed. *)

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

fn absorb_blocks (wsb: A.array S32.t) (acc: A.array S32.t)
                 (input: A.array S8.t) (base_in: SZ.t) (nfull: SZ.t) (nb: SZ.t)
                 (seen: erased (Seq.seq S8.t))
                 (#vw0: erased (Seq.seq S32.t)) (#vacc: erased (Seq.seq S32.t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to acc vacc ** A.pts_to input #pin vin **
         pure (Seq.length vw0 == rounds /\ Seq.length vacc == state_words /\
               SZ.v base_in + SZ.v nfull * block_len <= Seq.length vin /\
               (SZ.v nb + SZ.v nfull) * block_len <= Seq.length seen /\
               Seq.length seen < max_input /\
               reveal vacc == absorb seen (SZ.v nb) /\
               (forall (k: nat). k < SZ.v nfull * block_len ==>
                  Seq.index vin (SZ.v base_in + k) ==
                    Seq.index seen (SZ.v nb * block_len + k)))
ensures exists* (vw: Seq.seq S32.t) (vacc': Seq.seq S32.t).
  A.pts_to wsb vw ** A.pts_to acc vacc' ** A.pts_to input #pin vin **
  pure (Seq.length vw == rounds /\ Seq.length vacc' == state_words /\
        vacc' == absorb seen (SZ.v nb + SZ.v nfull))
{
  A.pts_to_len input;
  A.pts_to_len acc;

  Math.lemma_mult_le_right block_len (SZ.v nb) (SZ.v nb + SZ.v nfull);
  Math.distributivity_add_left (SZ.v nb) (SZ.v nfull) block_len;
  SZ.fits_lte (SZ.v nfull * block_len) (Seq.length vin);
  let hi = SZ.add base_in (SZ.mul nfull 64sz);
  assert (pure (SZ.v base_in <= SZ.v hi /\ SZ.v hi <= Seq.length vin));
  split3 (reveal vin) (SZ.v base_in) (SZ.v hi);
  let sub = Sub.sub input base_in hi;
  with vsub. assert (A.pts_to sub #pin vsub);
  assert (pure (Seq.length vsub == SZ.v nfull * block_len));
  Math.multiple_division_lemma (SZ.v nfull) block_len;
  assert (pure (SZ.v nfull == Seq.length vsub / block_len));

  let pre = G.hide (Seq.slice (reveal seen) 0 (SZ.v nb * block_len));
  let whole = G.hide (Seq.append (reveal pre) (reveal vsub));
  Seq.lemma_len_append (reveal pre) (reveal vsub);
  assert (pure (Seq.length whole == (SZ.v nb + SZ.v nfull) * block_len));
  assert (pure (Seq.length whole <= Seq.length seen));

  (* [whole] and [seen] agree on every byte [whole] has. *)
  Seq.lemma_eq_intro (reveal whole) (Seq.slice (reveal seen) 0 (Seq.length whole));

  absorb_padded (reveal whole) (SZ.v nb);
  absorb_congr (reveal whole) (reveal seen) (SZ.v nb);
  assert (pure (reveal vacc ==
                repeati_g (SZ.v nb) (update_step (padded (Seq.append pre vsub))) iv));

  hash_blocks wsb acc sub nb nfull pre;

  absorb_padded (reveal whole) (SZ.v nb + SZ.v nfull);
  absorb_congr (reveal whole) (reveal seen) (SZ.v nb + SZ.v nfull);

  Sub.unsub input (SZ.v base_in) (SZ.v hi) sub;
  with vin1. assert (A.pts_to input #pin vin1);
  assert (pure (Seq.equal vin1 vin));
  ()
}

#pop-options

(** {2 The three operations} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Reset to the empty message. *)
fn init_impl (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
             (#vacc: erased (Seq.seq S32.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
             (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to acc vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vacc == state_words /\ Seq.length vbuf == block_len /\
               Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S32.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok vacc' vbuf vtot' (Seq.empty #S8.t))
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.((acc.(0sz) <- S32.classify 0x67452301ul));
  A.((acc.(1sz) <- S32.classify 0xefcdab89ul));
  A.((acc.(2sz) <- S32.classify 0x98badcfeul));
  A.((acc.(3sz) <- S32.classify 0x10325476ul));
  A.((acc.(4sz) <- S32.classify 0xc3d2e1f0ul));
  with vacc'. assert (A.pts_to acc vacc');
  Seq.lemma_eq_intro vacc' (iv <: Seq.seq S32.t);
  Seq.lemma_eq_elim vacc' (iv <: Seq.seq S32.t);
  A.((tot.(0sz) <- 0sz));
  absorb_zero (Seq.empty #S8.t);
  assert (pure (Seq.length (Seq.empty #S8.t) / block_len == 0));
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** The case of [update] in which the buffer has just been filled: absorb it,
    then absorb whatever whole blocks of [data] follow, then keep the trailing
    bytes.  Split out of [update_impl] because the two cases together make a
    verification condition large enough that even linear arithmetic times out. *)
fn update_full (wsb: A.array S32.t) (acc: A.array S32.t)
               (buf: A.array S8.t) (data: A.array S8.t) (dlen: SZ.t)
               (blen: SZ.t) (nb0: SZ.t) (fill: SZ.t)
               (seen: erased (Seq.seq S8.t)) (seen1: erased (Seq.seq S8.t))
               (#vw0: erased (Seq.seq S32.t)) (#vacc: erased (Seq.seq S32.t))
               (#vbuf: erased (Seq.seq S8.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to acc vacc **
         A.pts_to buf vbuf ** A.pts_to data #pd vdata **
         pure (Seq.length vw0 == rounds /\ Seq.length vacc == state_words /\
               Seq.length vbuf == block_len /\
               reveal seen1 == Seq.append (reveal seen) (reveal vdata) /\
               Seq.length seen == SZ.v nb0 * block_len + SZ.v blen /\
               SZ.v blen + SZ.v fill == block_len /\
               SZ.v fill <= Seq.length vdata /\
               Seq.length seen1 < max_input /\
               SZ.fits (Seq.length seen1) /\
               reveal vacc == absorb seen1 (SZ.v nb0) /\
               (forall (k: nat). k < block_len ==>
                  Seq.index vbuf k == Seq.index seen1 (SZ.v nb0 * block_len + k)))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vw: Seq.seq S32.t) (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t).
  A.pts_to wsb vw ** A.pts_to acc vacc' **
  A.pts_to buf vbuf' ** A.pts_to data #pd vdata **
  pure (Seq.length vw == rounds /\ acc_ok vacc' vbuf' (reveal seen1))
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len data;
  Seq.lemma_len_append (reveal seen) (reveal vdata);

  Math.distributivity_add_left (SZ.v nb0) 1 block_len;
  assert (pure ((SZ.v nb0 + 1) * block_len == Seq.length seen + SZ.v fill));
  assert (pure ((SZ.v nb0 + 1) * block_len <= Seq.length seen1));
  absorb_blocks wsb acc buf 0sz 1sz nb0 seen1;

  let restlen = SZ.sub dlen fill;
  let nfull = SZ.div restlen 64sz;
  let tl = SZ.rem restlen 64sz;
  Math.euclidean_division_definition (SZ.v restlen) block_len;
  Math.distributivity_add_left (SZ.v nb0 + 1) (SZ.v nfull) block_len;
  Math.multiple_division_lemma (SZ.v nb0 + 1 + SZ.v nfull) block_len;
  Math.multiple_modulo_lemma (SZ.v nb0 + 1 + SZ.v nfull) block_len;
  Math.lemma_div_plus (SZ.v tl) (SZ.v nb0 + 1 + SZ.v nfull) block_len;
  Math.lemma_mod_plus (SZ.v tl) (SZ.v nb0 + 1 + SZ.v nfull) block_len;
  tail_agrees block_len (reveal seen) (reveal vdata)
              (SZ.v nb0 + 1) (SZ.v fill) (SZ.v nfull * block_len);
  Math.lemma_mult_le_left (SZ.v nb0 + 1) 1 block_len;
  SZ.fits_lte (SZ.v nb0 + 1) (Seq.length seen1);
  absorb_blocks wsb acc data fill nfull (SZ.add nb0 1sz) seen1;

  tail_agrees block_len (reveal seen) (reveal vdata)
              (SZ.v nb0 + 1 + SZ.v nfull) (SZ.v dlen - SZ.v tl) (SZ.v tl);
  assert (pure (Seq.length seen1 == (SZ.v nb0 + 1 + SZ.v nfull) * block_len + SZ.v tl));
  assert (pure (Seq.length seen1 / block_len == SZ.v nb0 + 1 + SZ.v nfull));
  assert (pure (Seq.length seen1 % block_len == SZ.v tl));
  copy_range buf 0sz data (SZ.sub dlen tl) tl;
  with vbuf2. assert (A.pts_to buf vbuf2);
  assert (pure (forall (k: nat). k < SZ.v tl ==>
                  Seq.index vbuf2 k ==
                  Seq.index seen1 ((SZ.v nb0 + 1 + SZ.v nfull) * block_len + k)));
}

#pop-options

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

(** Absorb [data]. *)
fn update_impl (wsb: A.array S32.t) (acc: A.array S32.t)
               (buf: A.array S8.t) (tot: A.array SZ.t) (data: A.array S8.t) (dlen: SZ.t)
               (seen: erased (Seq.seq S8.t))
               (#vw0: erased (Seq.seq S32.t)) (#vacc: erased (Seq.seq S32.t))
               (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to acc vacc **
         A.pts_to buf vbuf ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
         pure (Seq.length vw0 == rounds /\
               stream_ok vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < max_input /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vw: Seq.seq S32.t) (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t).
  A.pts_to wsb vw ** A.pts_to acc vacc' **
  A.pts_to buf vbuf' ** A.pts_to tot vtot' ** A.pts_to data #pd vdata **
  pure (Seq.length vw == rounds /\
        stream_ok vacc' vbuf' vtot' (Seq.append seen vdata))
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len data;
  let tlen = A.(tot.(0sz));
  let blen = SZ.rem tlen 64sz;
  let nb0 = SZ.div tlen 64sz;
  let fill = szmin (SZ.sub 64sz blen) dlen;
  let seen1 = G.hide (Seq.append (reveal seen) (reveal vdata));
  Seq.lemma_len_append (reveal seen) (reveal vdata);
  Math.euclidean_division_definition (SZ.v tlen) block_len;

  absorb_congr (reveal seen) (reveal seen1) (SZ.v nb0);

  copy_range buf blen data 0sz fill;
  with vbuf1. assert (A.pts_to buf vbuf1);
  buf_agrees block_len (reveal seen) (reveal vdata) (reveal vbuf) (reveal vbuf1)
             (SZ.v nb0) (SZ.v blen) (SZ.v fill);

  if (SZ.eq (SZ.add blen fill) 64sz)
  ensures exists* (vw: Seq.seq S32.t) (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t).
    A.pts_to wsb vw ** A.pts_to acc vacc' **
    A.pts_to buf vbuf' ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
    pure (Seq.length vw == rounds /\ acc_ok vacc' vbuf' (reveal seen1))
  {
    update_full wsb acc buf data dlen blen nb0 fill seen seen1;
  }
  else
  {
    (* All of [data] fitted in the buffer. *)
    Math.small_division_lemma_1 (SZ.v blen + SZ.v dlen) block_len;
    Math.lemma_div_plus (SZ.v blen + SZ.v dlen) (SZ.v nb0) block_len;
    Math.lemma_mod_plus (SZ.v blen + SZ.v dlen) (SZ.v nb0) block_len;
    ()
  };

  A.((tot.(0sz) <- SZ.add tlen dlen));
}

#pop-options

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

(** The digest of everything seen so far.  The state is left usable. *)
fn digest_impl (wsb: A.array S32.t) (acc: A.array S32.t)
               (buf: A.array S8.t) (tot: A.array SZ.t) (out: A.array S8.t)
               (seen: erased (Seq.seq S8.t))
               (#vw0: erased (Seq.seq S32.t))
               (#pa: perm) (#vacc: erased (Seq.seq S32.t))
               (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
               (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
               (#vout: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to acc #pa vacc **
         A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot ** A.pts_to out vout **
         pure (Seq.length vw0 == rounds /\ Seq.length vout == hash_bytes /\
               stream_ok vacc vbuf vtot seen)
ensures exists* (vw: Seq.seq S32.t) (vout': Seq.seq S8.t).
  A.pts_to wsb vw ** A.pts_to acc #pa vacc **
  A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot ** A.pts_to out vout' **
  pure (Seq.length vw == rounds /\ Seq.length seen < max_input /\ vout' == hash seen)
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len out;
  let tlen = A.(tot.(0sz));
  let blen = SZ.rem tlen 64sz;
  let nb0 = SZ.div tlen 64sz;
  Math.euclidean_division_definition (SZ.v tlen) block_len;

  let z0 = S32.classify 0ul;
  let mut starr = [| z0; 5sz |];
  A.pts_to_len starr;
  A.pts_to_len starr;
  copy5 starr acc;

  split3 (reveal vbuf) 0 (SZ.v blen);
  let sub = Sub.sub buf 0sz blen;
  with vsub. assert (A.pts_to sub #pbuf vsub);
  let pre = G.hide (Seq.slice (reveal seen) 0 (SZ.v nb0 * block_len));
  Seq.lemma_len_append (reveal pre) (reveal vsub);
  buf_is_tail block_len (reveal seen) (reveal vbuf) (SZ.v nb0) (SZ.v blen);
  absorb_padded (reveal seen) (SZ.v nb0);

  tail_and_finish wsb starr out sub tlen nb0 0sz blen pre;

  Sub.unsub_id buf 0 (SZ.v blen) sub;
}

#pop-options
