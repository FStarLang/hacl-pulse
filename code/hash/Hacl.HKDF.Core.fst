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

(** HKDF, RFC 5869, over HMAC-SHA-2.

    [extract] is literally HMAC, so there is nothing to implement here.
    Round [i] of [expand] is

      T(i) = HMAC(prk, T(i-1) || info || i)

    and is computed by [Hacl.HMAC.Cat.hmac_cat], which takes its message in
    four pieces and streams them through the inner hash.  Nothing is ever
    concatenated, so the only scratch is two digests and a counter byte,
    whatever the length of [info].  An earlier version laid the message out
    in one buffer of [hash_bytes + |info| + 1] bytes on the stack, which let
    a caller choose the size of the stack frame.

    [info] itself is taken in two pieces, [pre] and [info], because HPKE's
    LabeledExpand prepends a few dozen bytes of labels to the caller's
    string; see {!Hacl.HPKE.Labeled}.  Plain HKDF passes an empty [pre].

    The block function is an argument (see {!Hacl.Hash.SHA2.Core.blocks_t}),
    so one copy of this code runs on the SHA instructions when
    {!Hacl.HKDF.expand_sha256} finds them and on the portable rounds
    otherwise. *)
module Hacl.HKDF.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC
open Spec.HKDF
open Hacl.Hash.SHA2.Core
open Hacl.HMAC.Cat
open Hacl.Impl.Copy

module Sub = Hacl.Impl.Sub

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module Mem = Hacl.Mem

(** {2 Small helpers} *)

let round_sizes (#t: Type0) {| word t |} (p: params t)
  : Lemma (255 * (hash_bytes p) < pow2 16 /\ hash_bytes p <= 8 * bytes #t)
  = assert_norm (255 * 128 < pow2 16)

(** [hmac_cat] hashes its pieces right-nested; [expand_t] is stated
    left-nested. *)
let round_msg (prev pre info c: Seq.seq S8.t)
  : Lemma (Seq.append prev (Seq.append pre (Seq.append info c)) ==
           Seq.append (Seq.append prev (Seq.append pre info)) c)
  = Seq.lemma_eq_intro (Seq.append prev (Seq.append pre (Seq.append info c)))
                       (Seq.append (Seq.append prev (Seq.append pre info)) c)

(** {2 One round} *)

let round_eq (#t: Type0) {| word t |} (p: params t)
             (prk: Seq.seq S8.t { prk_ok p prk })
             (pre info: Seq.seq S8.t { info_ok p (Seq.append pre info) })
             (ci: nat { 0 < ci /\ ci < 256 })
             (prev c h: Seq.seq S8.t)
  : Lemma (requires prev == expand_t p prk (Seq.append pre info) (ci - 1) /\
                    c == counter ci /\
                    Seq.length (Seq.append prev (Seq.append pre (Seq.append info c))) ==
                      Seq.length prev + Seq.length pre + Seq.length info + 1 /\
                    h == hmac p prk (Seq.append prev (Seq.append pre (Seq.append info c))))
          (ensures h == expand_t p prk (Seq.append pre info) ci)
  = round_msg prev pre info c;
    expand_t_unfold p prk (Seq.append pre info) ci


#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

(** [dg <- T(ci)], given [T(ci - 1)] in the first [lprev] bytes of [dg] --
    that is, all of it, or none of it in round one. *)
fn round (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
         ([@@@FStar.Attributes.monomorphize] blocks: blocks_t p)
         (kt: A.array t) (ivt: A.array t)
         (dg: A.array S8.t) (tmp: A.array S8.t) (ctr: A.array S8.t) (lprev: SZ.t)
         (prk: A.array S8.t) (plen: SZ.t)
         (pre: A.array S8.t) (lpre: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
         (ci: U8.t)
         (#pk: perm) (#vk: erased (Seq.seq t))
         (#pi: perm) (#vi: erased (Seq.seq t))
         (#vdg: erased (Seq.seq S8.t)) (#vtmp: erased (Seq.seq S8.t))
         (#vctr: erased (Seq.seq S8.t))
         (#pp: perm) (#vprk: erased (Seq.seq S8.t))
         (#pr: perm) (#vpre: erased (Seq.seq S8.t))
         (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to dg vdg ** A.pts_to tmp vtmp ** A.pts_to ctr vctr **
         A.pts_to prk #pp vprk ** A.pts_to pre #pr vpre ** A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vdg == hash_bytes p /\ Seq.length vtmp == hash_bytes p /\
               Seq.length vctr == 1 /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\
               info_ok p (Seq.append vpre vinfo) /\
               block_len #t + hash_bytes p + Seq.length vpre + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #t + hash_bytes p + Seq.length vpre + Seq.length vinfo + 1) /\
               0 < U8.v ci /\
               SZ.v lprev == Seq.length (expand_t p vprk (Seq.append vpre vinfo) (U8.v ci - 1)) /\
               Seq.slice vdg 0 (SZ.v lprev) ==
                 expand_t p vprk (Seq.append vpre vinfo) (U8.v ci - 1))
         ** pure (SZ.v plen == Seq.length vprk /\ SZ.v lpre == Seq.length vpre /\
                  SZ.v ilen == Seq.length vinfo)
ensures exists* (vdg': Seq.seq S8.t) (vtmp': Seq.seq S8.t) (vctr': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to dg vdg' ** A.pts_to tmp vtmp' ** A.pts_to ctr vctr' **
  A.pts_to prk #pp vprk ** A.pts_to pre #pr vpre ** A.pts_to info #pf vinfo **
  pure (prk_ok p vprk /\ info_ok p (Seq.append vpre vinfo) /\
        Seq.length vdg' == hash_bytes p /\ Seq.length vtmp' == hash_bytes p /\
        Seq.length vctr' == 1 /\
        vdg' == expand_t p vprk (Seq.append vpre vinfo) (U8.v ci))
{
  A.pts_to_len dg;
  A.pts_to_len tmp;
  A.pts_to_len ctr;
  A.pts_to_len prk;
  A.pts_to_len pre;
  A.pts_to_len info;
  Seq.lemma_len_append (reveal vpre) (reveal vinfo);

  A.((ctr.(0sz) <- S8.classify ci));
  with vc. assert (A.pts_to ctr vc);
  Seq.lemma_eq_intro (reveal vc) (counter (U8.v ci));

  let prev = Sub.sub dg 0sz lprev;
  with vprev. assert (A.pts_to prev vprev);
  hmac_cat p blocks kt ivt tmp prk prev pre info ctr plen lprev lpre ilen 1sz;
  with vh. assert (A.pts_to tmp vh);
  Sub.unsub_id dg 0 (SZ.v lprev) prev;
  round_eq p (reveal vprk) (reveal vpre) (reveal vinfo) (U8.v ci)
    (reveal vprev) (reveal vc) (reveal vh);
  assert (pure (reveal vh == expand_t p vprk (Seq.append vpre vinfo) (U8.v ci)));

  let hb = p.nhash_bytes;
  copy_at dg 0sz tmp hb;
  with vdg'. assert (A.pts_to dg vdg');
  with vtmp'. assert (A.pts_to tmp vtmp');
  Seq.lemma_eq_intro (reveal vdg') (reveal vtmp');
  assert (pure (vtmp' == vh));
  assert (pure (vdg' == vh));
}

#pop-options

(** {2 Expand} *)

#push-options "--z3rlimit 600 --fuel 1 --ifuel 0"

fn expand2_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                ([@@@FStar.Attributes.monomorphize] blocks: blocks_t p)
                (kt: A.array t) (ivt: A.array t) (out: A.array S8.t) (len: SZ.t)
                (prk: A.array S8.t) (plen: SZ.t)
                (pre: A.array S8.t) (lpre: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vout: erased (Seq.seq S8.t))
                (#pp: perm) (#vprk: erased (Seq.seq S8.t))
                (#pr: perm) (#vpre: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to prk #pp vprk ** A.pts_to pre #pr vpre ** A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\
               info_ok p (Seq.append vpre vinfo) /\
               block_len #t + hash_bytes p + Seq.length vpre + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #t + hash_bytes p + Seq.length vpre + Seq.length vinfo + 1) /\
               Seq.length vout <= 255 * (hash_bytes p) /\
               SZ.v len == Seq.length vout /\ SZ.v lpre == Seq.length vpre /\
               SZ.v ilen == Seq.length vinfo)
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to prk #pp vprk ** A.pts_to pre #pr vpre ** A.pts_to info #pf vinfo **
  pure (prk_ok p vprk /\ info_ok p (Seq.append vpre vinfo) /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes p) /\
        vout' == expand p vprk (Seq.append vpre vinfo) (Seq.length vout'))
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len pre;
  A.pts_to_len info;
  round_sizes #t p;
  let hb = p.nhash_bytes;
  let z8 = S8.classify 0uy;
  let vinfo2 = G.hide (Seq.append (reveal vpre) (reveal vinfo));

  let mut darr = [| z8; hb |];
  Mem.track darr;
  A.pts_to_len darr;
  let mut tarr = [| z8; hb |];
  Mem.track tarr;
  A.pts_to_len tarr;
  let mut carr = [| z8; 1sz |];
  Mem.track carr;
  A.pts_to_len carr;

  if (SZ.gt len 0sz)
  ensures exists* (vout': Seq.seq S8.t) (vdg': Seq.seq S8.t) (vt': Seq.seq S8.t)
                  (vc': Seq.seq S8.t).
    A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
    A.pts_to prk #pp vprk ** A.pts_to pre #pr vpre ** A.pts_to info #pf vinfo **
    A.pts_to darr vdg' ** A.pts_to tarr vt' ** A.pts_to carr vc' **
    Mem.must_wipe darr ** Mem.must_wipe tarr ** Mem.must_wipe carr **
    pure (prk_ok p vprk /\ info_ok p vinfo2 /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vdg' == hash_bytes p /\ Seq.length vt' == hash_bytes p /\
          Seq.length vc' == 1 /\
          Seq.length vout <= 255 * (hash_bytes p) /\
          (forall (k: nat). k < Seq.length vout' ==>
             k < (nrounds p (Seq.length vout)) * (hash_bytes p) /\
             Seq.index vout' k ==
               Seq.index (expand_all p vprk vinfo2 (nrounds p (Seq.length vout))) k))
  {
    with vd0. assert (A.pts_to darr vd0);
    Seq.lemma_eq_intro (Seq.slice (reveal vd0) 0 0) (Seq.empty #S8.t);
    round p blocks kt ivt darr tarr carr 0sz prk plen pre lpre info ilen 1uy;
    write_chunk out len 0sz darr hb;
    expand_all_index_last p (reveal vprk) (reveal vinfo2) 1;
    expand_all_index_le p (reveal vprk) (reveal vinfo2) 1 (nrounds p (SZ.v len));

    let mut base = hb;
    let mut ci = 1uy;
    while (let vb = !base; SZ.lt vb len)
    invariant exists* (vb: SZ.t) (vc: U8.t) (vout': Seq.seq S8.t)
                      (vdg': Seq.seq S8.t) (vt': Seq.seq S8.t) (vc': Seq.seq S8.t).
      pts_to base vb ** pts_to ci vc **
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to prk #pp vprk ** A.pts_to pre #pr vpre ** A.pts_to info #pf vinfo **
      A.pts_to darr vdg' ** A.pts_to tarr vt' ** A.pts_to carr vc' **
      Mem.must_wipe darr ** Mem.must_wipe tarr ** Mem.must_wipe carr **
      pure (prk_ok p vprk /\ info_ok p vinfo2 /\
            Seq.length vout' == Seq.length vout /\
            Seq.length vout' == SZ.v len /\
            Seq.length vdg' == hash_bytes p /\ Seq.length vt' == hash_bytes p /\
            Seq.length vc' == 1 /\
            0 < U8.v vc /\ U8.v vc <= nrounds p (SZ.v len) /\
            SZ.v vb == U8.v vc * (hash_bytes p) /\
            vdg' == expand_t p vprk vinfo2 (U8.v vc) /\
            (forall (k: nat). k < Seq.length vout' /\ k < SZ.v vb ==>
               k < (nrounds p (SZ.v len)) * (hash_bytes p) /\
               Seq.index vout' k ==
                 Seq.index (expand_all p vprk vinfo2 (nrounds p (SZ.v len))) k))
    decreases (255 - U8.v (!ci))
    {
      let vb = !base;
      let vc = !ci;
      let n = nrounds p (SZ.v len);
      (* [vb = vc * hb < len <= n * hb], so there is at least one more round. *)
      Spec.HKDF.mult_lt_cancel (U8.v vc) n (hash_bytes p);
      let nc = U8.add vc 1uy;
      with vd. assert (A.pts_to darr vd);
      Seq.lemma_eq_intro (Seq.slice (reveal vd) 0 (SZ.v hb)) (reveal vd);
      round p blocks kt ivt darr tarr carr hb prk plen pre lpre info ilen nc;
      write_chunk out len vb darr hb;
      expand_all_index_last p (reveal vprk) (reveal vinfo2) (U8.v nc);
      expand_all_index_le p (reveal vprk) (reveal vinfo2) (U8.v nc) n;
      Math.distributivity_add_left (U8.v vc) 1 (hash_bytes p);
      Math.lemma_mult_le_right (hash_bytes p) (U8.v nc) 255;
      SZ.fits_lte (SZ.v vb + SZ.v hb) (255 * (hash_bytes p));
      base := SZ.add vb hb;
      ci := nc;
    };
  }
  else
  {
    ()
  };

  with vout'. assert (A.pts_to out vout');
  Seq.lemma_eq_intro (reveal vout')
    (Seq.slice (expand_all p vprk vinfo2 (nrounds p (Seq.length vout))) 0 (Seq.length vout));
  Mem.wipe carr 1sz;
  Mem.wipe tarr hb;
  Mem.wipe darr hb;
  ()
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

fn expand_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               ([@@@FStar.Attributes.monomorphize] blocks: blocks_t p)
               (kt: A.array t) (ivt: A.array t) (out: A.array S8.t) (len: SZ.t)
               (prk: A.array S8.t) (plen: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#vout: erased (Seq.seq S8.t))
               (#pp: perm) (#vprk: erased (Seq.seq S8.t))
               (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p vinfo /\
               block_len #t + (hash_bytes p) + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #t + (hash_bytes p) + Seq.length vinfo + 1) /\
               Seq.length vout <= 255 * (hash_bytes p) /\
               SZ.v len == Seq.length vout /\ SZ.v ilen == Seq.length vinfo)
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok p vprk /\ info_ok p vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes p) /\
        vout' == expand p vprk vinfo (Seq.length vout'))
{
  (* An empty [pre]: a zero-length window of a one-byte array. *)
  let z8 = S8.classify 0uy;
  let mut earr = [| z8; 1sz |];
  Mem.track earr;
  A.pts_to_len earr;
  let pre = Sub.sub earr 0sz 0sz;
  with vpre. assert (A.pts_to pre vpre);
  Seq.lemma_eq_intro (reveal vpre) (Seq.empty #S8.t);
  Seq.append_empty_l (reveal vinfo);
  expand2_impl p blocks kt ivt out len prk plen pre 0sz info ilen;
  Sub.unsub_id earr 0 0 pre;
  Mem.wipe earr 1sz;
}

#pop-options
