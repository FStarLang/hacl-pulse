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
    [expand] needs one scratch buffer laid out as

      [ T(i-1) | info | i ]
        hb       ilen   1

    which is hashed once per round.  Only the first [hb] bytes and the last
    byte change from round to round, so [info] is written exactly once, and
    round [i] hashes the buffer in place.  Round 1 is the exception: [T(0)] is
    empty, so it hashes the [info | 1] suffix, obtained as a subslice. *)
module Hacl.HKDF.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.SHANI
open Spec.HMAC
open Spec.HKDF
open Hacl.Hash.SHA2.Core
open Hacl.HMAC.Core
open Hacl.HMAC.NI
open Hacl.Impl.Copy

module Sub = Hacl.Impl.Sub

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

(** {2 Small helpers} *)

(** The scratch buffer never exceeds a couple of hundred bytes plus [info]. *)
let round_sizes (#t: Type0) {| word t |} (p: params t)
  : Lemma (255 * (hash_bytes p) < pow2 16 /\ hash_bytes p <= 8 * bytes #t)
  = assert_norm (255 * 128 < pow2 16)

(** {2 One round} *)

(** The scratch buffer holds [info] in the middle, from [hash_bytes p]. *)
unfold let msg_ok (#t: Type0) {| word t |} (p: params t)
                  (m: Seq.seq S8.t) (info: Seq.seq S8.t) =
  Seq.length m == (hash_bytes p) + Seq.length info + 1 /\
  (forall (k: nat). k < Seq.length info ==>
     Seq.index m ((hash_bytes p) + k) == Seq.index info k)

(** What [copy_at] of [info] at offset [hash_bytes p] establishes, restated
    as [msg_ok] in a small context. *)
let msg_ok_of_copy (#t: Type0) {| word t |} (p: params t)
                   (m: Seq.seq S8.t) (info: Seq.seq S8.t) (base n: SZ.t)
  : Lemma (requires SZ.v base == hash_bytes p /\ SZ.v n == Seq.length info /\
                    Seq.length m == SZ.v base + SZ.v n + 1 /\
                    (forall (k: nat). k < SZ.v n ==>
                       Seq.index m (SZ.v base + k) == Seq.index info k))
          (ensures msg_ok p m info)
  = ()

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

(** Round 1: [T(0)] is empty, so hash the [info | 1] suffix of the buffer. *)
fn round_one (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: A.array t) (ivt: A.array t)
             (dg: A.array S8.t) (prk: A.array S8.t) (plen: SZ.t) (msg: A.array S8.t) (ml: SZ.t)
             (#info: erased (Seq.seq S8.t))
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vdg: erased (Seq.seq S8.t))
             (#pp: perm) (#vprk: erased (Seq.seq S8.t))
             (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg **
         A.pts_to prk #pp vprk ** A.pts_to msg vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vdg == (hash_bytes p) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p (reveal info) /\
               block_len #t + (hash_bytes p) + Seq.length info + 1 < pow2 61 /\
               SZ.fits (block_len #t + (hash_bytes p) + Seq.length info + 1) /\
               msg_ok p vmsg (reveal info) /\ SZ.v ml == Seq.length vmsg)
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg' **
  A.pts_to prk #pp vprk ** A.pts_to msg vmsg' **
  pure (prk_ok p vprk /\ info_ok p (reveal info) /\
        Seq.length vdg' == (hash_bytes p) /\
        msg_ok p vmsg' (reveal info) /\
        vdg' == expand_t p vprk info 1)
{
  A.pts_to_len dg;
  A.pts_to_len prk;
  A.pts_to_len msg;
  let hb = p.nhash_bytes;
  A.((msg.(SZ.sub ml 1sz) <- S8.classify 1uy));
  with vm1. assert (A.pts_to msg vm1);
  assert (pure (Seq.index vm1 (Seq.length vm1 - 1) == S8.classify 1uy));

  let sub = Sub.sub msg hb ml;
  with vsub. assert (A.pts_to sub vsub);
  assert (pure (reveal vsub == Seq.slice vm1 (SZ.v hb) (SZ.v ml)));
  assert (pure (Seq.length vsub == Seq.length info + 1));
  round_msg_pointwise #t (reveal vsub) Seq.empty (reveal info) 1;
  assert (pure (reveal vsub ==
                Seq.append (Seq.append (Seq.empty #S8.t) (reveal info)) (counter 1)));

  hmac_impl p kt ivt dg prk plen sub (SZ.sub ml hb);
  expand_t_unfold p (reveal vprk) (reveal info) 1;

  Sub.unsub_id msg (SZ.v hb) (SZ.v ml) sub;
}

(** Round [i > 1]: prepend the previous digest, bump the counter, hash. *)
fn round_step (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
              (kt: A.array t) (ivt: A.array t)
              (dg: A.array S8.t) (prk: A.array S8.t) (plen: SZ.t) (msg: A.array S8.t) (ml: SZ.t)
              (ci: U8.t)
              (#info: erased (Seq.seq S8.t))
              (#pk: perm) (#vk: erased (Seq.seq t))
              (#pi: perm) (#vi: erased (Seq.seq t))
              (#vdg: erased (Seq.seq S8.t))
              (#pp: perm) (#vprk: erased (Seq.seq S8.t))
              (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg **
         A.pts_to prk #pp vprk ** A.pts_to msg vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p (reveal info) /\
               block_len #t + (hash_bytes p) + Seq.length info + 1 < pow2 61 /\
               SZ.fits (block_len #t + (hash_bytes p) + Seq.length info + 1) /\
               msg_ok p vmsg (reveal info) /\ SZ.v ml == Seq.length vmsg /\
               1 < U8.v ci /\
               Seq.length vdg == (hash_bytes p) /\
               vdg == expand_t p vprk info (U8.v ci - 1))
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg' **
  A.pts_to prk #pp vprk ** A.pts_to msg vmsg' **
  pure (prk_ok p vprk /\ info_ok p (reveal info) /\ U8.v ci < 256 /\
        Seq.length vdg' == (hash_bytes p) /\
        msg_ok p vmsg' (reveal info) /\
        vdg' == expand_t p vprk info (U8.v ci))
{
  A.pts_to_len dg;
  A.pts_to_len prk;
  A.pts_to_len msg;
  let hb = p.nhash_bytes;
  copy_at msg 0sz dg hb;
  A.((msg.(SZ.sub ml 1sz) <- S8.classify ci));
  with vm1. assert (A.pts_to msg vm1);
  assert (pure (Seq.index vm1 (Seq.length vm1 - 1) == S8.classify (U8.uint_to_t (U8.v ci))));
  round_msg_pointwise #t (reveal vm1) (reveal vdg) (reveal info) (U8.v ci);
  expand_t_unfold p (reveal vprk) (reveal info) (U8.v ci);
  hmac_impl p kt ivt dg prk plen msg ml;
}

#pop-options

(** {2 Expand} *)

(** The loop's main invariant: the first [b] bytes of the output (or all of
    it, if shorter) agree with [expand_all] at the final round count.  Kept
    opaque so that the Pulse queries never see its quantifier; the three
    lemmas below are the only things that open it. *)
[@@"opaque_to_smt"]
let prefix_ok (#t: Type0) {| word t |} (p: params t)
              (prk: Seq.seq S8.t { prk_ok p prk })
              (info: Seq.seq S8.t { info_ok p info })
              (len: nat { len <= 255 * (hash_bytes p) })
              (vout: Seq.seq S8.t) (b: nat) : prop =
  Seq.length vout == len /\
  (forall (k: nat). k < len /\ k < b ==>
     Seq.index vout k == Seq.index (expand_all p prk info (nrounds p len)) k)

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let prefix_ok_zero (#t: Type0) {| word t |} (p: params t)
                   (prk: Seq.seq S8.t { prk_ok p prk })
                   (info: Seq.seq S8.t { info_ok p info })
                   (len: nat { len <= 255 * (hash_bytes p) })
                   (vout: Seq.seq S8.t) (b: nat)
  : Lemma (requires Seq.length vout == len /\ (b == 0 \/ len == 0))
          (ensures prefix_ok p prk info len vout b)
  = reveal_opaque (`%prefix_ok) (prefix_ok p prk info len vout b)

let prefix_ok_weaken (#t: Type0) {| word t |} (p: params t)
                     (prk: Seq.seq S8.t { prk_ok p prk })
                     (info: Seq.seq S8.t { info_ok p info })
                     (len: nat { len <= 255 * (hash_bytes p) })
                     (vout: Seq.seq S8.t) (b b': nat)
  : Lemma (requires prefix_ok p prk info len vout b /\ b' <= b)
          (ensures prefix_ok p prk info len vout b')
  = reveal_opaque (`%prefix_ok) (prefix_ok p prk info len vout b);
    reveal_opaque (`%prefix_ok) (prefix_ok p prk info len vout b')

let prefix_ok_final (#t: Type0) {| word t |} (p: params t)
                    (prk: Seq.seq S8.t { prk_ok p prk })
                    (info: Seq.seq S8.t { info_ok p info })
                    (len: nat { len <= 255 * (hash_bytes p) })
                    (vout: Seq.seq S8.t)
  : Lemma (requires prefix_ok p prk info len vout len)
          (ensures Seq.length vout == len /\ vout == expand p prk info len)
  = reveal_opaque (`%prefix_ok) (prefix_ok p prk info len vout len);
    Seq.lemma_eq_intro vout (expand p prk info len)

(** One round: [vnew] is [vold] with [T(vc+1)] written at [vc * hb]. *)
let prefix_ok_step (#t: Type0) {| word t |} (p: params t)
                   (prk: Seq.seq S8.t { prk_ok p prk })
                   (info: Seq.seq S8.t { info_ok p info })
                   (len: nat { len <= 255 * (hash_bytes p) })
                   (vc: nat { vc < 255 })
                   (vold vnew vdg: Seq.seq S8.t)
  : Lemma (requires
             Seq.length vold == len /\
             Seq.length vnew == Seq.length vold /\
             vc * (hash_bytes p) < len /\
             prefix_ok p prk info len vold (vc * (hash_bytes p)) /\
             (forall (k: nat). k < vc * (hash_bytes p) ==> Seq.index vnew k == Seq.index vold k) /\
             (forall (k: nat). k < Seq.length vdg /\ vc * (hash_bytes p) + k < Seq.length vold ==>
                Seq.index vnew (vc * (hash_bytes p) + k) == Seq.index vdg k) /\
             vdg == expand_t p prk info (vc + 1))
          (ensures
             vc + 1 <= nrounds p len /\
             (vc + 1) * (hash_bytes p) == vc * (hash_bytes p) + hash_bytes p /\
             prefix_ok p prk info len vnew (vc * (hash_bytes p) + hash_bytes p))
  = let hb = hash_bytes p in
    let n = nrounds p len in
    reveal_opaque (`%prefix_ok) (prefix_ok p prk info len vold (vc * hb));
    reveal_opaque (`%prefix_ok) (prefix_ok p prk info len vnew (vc * hb + hb));
    Spec.HKDF.mult_lt_cancel vc n hb;
    Math.distributivity_add_left vc 1 hb;
    expand_all_index_last p prk info (vc + 1);
    expand_all_index_le p prk info (vc + 1) n;
    let aux (k: nat)
      : Lemma (requires k < len /\ k < vc * hb + hb)
              (ensures k < len /\
                       Seq.index vnew k == Seq.index (expand_all p prk info n) k)
      = if k < vc * hb then ()
        else begin
          let j = k - vc * hb in
          assert (Seq.index vnew (vc * hb + j) == Seq.index vdg j);
          assert (Seq.index (expand_all p prk info (vc + 1)) (vc * hb + j) ==
                  Seq.index (expand_t p prk info (vc + 1)) j)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

fn expand_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
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
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len info;
  round_sizes #t p;
  let hb = p.nhash_bytes;
  let z8 = S8.classify 0uy;

  SZ.fits_lte (SZ.v hb + SZ.v ilen) (block_len #t + (hash_bytes p) + Seq.length vinfo + 1);
  let ml = SZ.add (SZ.add hb ilen) 1sz;
  assert (pure (SZ.v ml == SZ.v hb + SZ.v ilen + 1));

  let mut marr = [| z8; ml |];
  A.pts_to_len marr;
  A.pts_to_len marr;

  let mut darr = [| z8; hb |];
  A.pts_to_len darr;
  A.pts_to_len darr;

  copy_at marr hb info ilen;
  with vm0. assert (A.pts_to marr vm0);
  assert (pure (Seq.length vm0 == SZ.v ml));
  msg_ok_of_copy p vm0 (reveal vinfo) hb ilen;

  if (SZ.gt len 0sz)
  ensures exists* (vout': Seq.seq S8.t) (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
    A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
    A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    A.pts_to darr vdg' ** A.pts_to marr vmsg' **
    pure (prk_ok p vprk /\ info_ok p vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vdg' == (hash_bytes p) /\ Seq.length vmsg' == SZ.v ml /\
          Seq.length vout <= 255 * (hash_bytes p) /\
          prefix_ok p vprk vinfo (SZ.v len) vout' (SZ.v len))
  {
    with vout0. assert (A.pts_to out vout0);
    prefix_ok_zero p (reveal vprk) (reveal vinfo) (SZ.v len) vout0 0;
    round_one p kt ivt darr prk plen marr ml #vinfo;
    with vdg1. assert (A.pts_to darr vdg1);
    write_chunk out len 0sz darr hb;
    with vout1. assert (A.pts_to out vout1);
    prefix_ok_step p (reveal vprk) (reveal vinfo) (SZ.v len) 0 vout0 vout1 vdg1;

    let mut base = hb;
    let mut ci = 1uy;
    while (let vb = !base; SZ.lt vb len)
    invariant exists* (vb: SZ.t) (vc: U8.t) (vout': Seq.seq S8.t)
                      (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
      pts_to base vb ** pts_to ci vc **
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
      A.pts_to darr vdg' ** A.pts_to marr vmsg' **
      pure (prk_ok p vprk /\ info_ok p vinfo /\
            Seq.length vout' == Seq.length vout /\
            Seq.length vout' == SZ.v len /\
            Seq.length vdg' == (hash_bytes p) /\
            msg_ok p vmsg' (reveal vinfo) /\ Seq.length vmsg' == SZ.v ml /\
            0 < U8.v vc /\ U8.v vc <= nrounds p (SZ.v len) /\
            SZ.v vb == U8.v vc * (hash_bytes p) /\
            vdg' == expand_t p vprk vinfo (U8.v vc) /\
            prefix_ok p vprk vinfo (SZ.v len) vout' (SZ.v vb))
    decreases (255 - U8.v (!ci))
    {
      let vb = !base;
      let vc = !ci;
      let n = nrounds p (SZ.v len);
      (* [vb = vc * hb < len <= n * hb], so there is at least one more round. *)
      Spec.HKDF.mult_lt_cancel (U8.v vc) n (hash_bytes p);
      let nc = U8.add vc 1uy;
      with vold. assert (A.pts_to out vold);
      round_step p kt ivt darr prk plen marr ml nc #vinfo;
      with vdg1. assert (A.pts_to darr vdg1);
      write_chunk out len vb darr hb;
      with vnew. assert (A.pts_to out vnew);
      prefix_ok_step p (reveal vprk) (reveal vinfo) (SZ.v len) (U8.v vc) vold vnew vdg1;
      Math.lemma_mult_le_right (hash_bytes p) (U8.v nc) 255;
      SZ.fits_lte (SZ.v vb + SZ.v hb) (255 * (hash_bytes p));
      base := SZ.add vb hb;
      ci := nc;
    };
    with vbf. assert (pts_to base vbf);
    with voutf. assert (A.pts_to out voutf);
    assert (pure (SZ.v len <= SZ.v vbf));
    prefix_ok_weaken p (reveal vprk) (reveal vinfo) (SZ.v len) voutf (SZ.v vbf) (SZ.v len);
    assert (pure (prefix_ok p vprk vinfo (SZ.v len) voutf (SZ.v len)));
    with vdgf. assert (A.pts_to darr vdgf);
    with vmf. assert (A.pts_to marr vmf);
    assert (pure (Seq.length vdgf == hash_bytes p));
    assert (pure (Seq.length vmf == SZ.v ml));
    assert (pure (Seq.length voutf == Seq.length vout));
    assert (pure (prk_ok p vprk /\ info_ok p vinfo));
  }
  else
  {
    prefix_ok_zero p (reveal vprk) (reveal vinfo) (SZ.v len) vout (SZ.v len);
    assert (pure (prefix_ok p vprk vinfo (SZ.v len) vout (SZ.v len)));
  };

  with vout'. assert (A.pts_to out vout');
  prefix_ok_final p (reveal vprk) (reveal vinfo) (SZ.v len) vout';
  ()
}

#pop-options

(** {2 The same three functions over the SHA extensions}

    HKDF-expand over the SHA-EXT implementation.

    [Hacl.HKDF.Core.expand_impl] is generic in the word type, so -- for the
    same reason [Hacl.HMAC.Core.hmac_impl] is -- it cannot branch into code
    that exists only at thirty-two-bit words.  Giving HMAC-SHA-256 the
    extensions therefore did nothing for HKDF-expand, which reaches HMAC
    through [round_one] and [round_step] rather than through
    [Hacl.HMAC.hmac_sha256].  A sixty-four-byte expand is two HMACs of a few
    dozen bytes, which is eight compression blocks; at 270 ns a scalar block
    against 55, that is the whole of the measured 3,086 ns against a
    reference's 1,348.

    So the three functions are transcribed here at [S32.t], with
    [hmac_impl_ni] in place of [hmac_impl].  Nothing else differs: the buffer
    layout, the loop, the invariant and the lemma calls are the originals,
    and the specifications are the same, which is what lets
    [Hacl.HKDF.expand_sha256] pick between the two with nothing to prove.

    This is the third copy of this shape, after [hash_blocks_ni] and
    [hmac_impl_ni], and it is the one that makes the cost of the pattern
    plain: a static specialisation hierarchy pays for an implementation
    choice in duplicated proof, where EverCrypt's runtime agility pays for it
    in indirect calls.  A general fix -- threading the block function through
    the hash core so that one generic copy serves both -- would subsume all
    three, and is the right thing to do before a fourth consumer needs it. *)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"

(** Round 1: [T(0)] is empty, so hash the [info | 1] suffix of the buffer. *)
fn round_one_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
             (kt: A.array S32.t) (ivt: A.array S32.t)
             (dg: A.array S8.t) (prk: A.array S8.t) (plen: SZ.t) (msg: A.array S8.t) (ml: SZ.t)
             (#info: erased (Seq.seq S8.t))
             (#pk: perm) (#vk: erased (Seq.seq S32.t))
             (#pi: perm) (#vi: erased (Seq.seq S32.t))
             (#vdg: erased (Seq.seq S8.t))
             (#pp: perm) (#vprk: erased (Seq.seq S8.t))
             (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg **
         A.pts_to prk #pp vprk ** A.pts_to msg vmsg **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\ reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vdg == (hash_bytes p) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p (reveal info) /\
               block_len #S32.t + (hash_bytes p) + Seq.length info + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + (hash_bytes p) + Seq.length info + 1) /\
               msg_ok p vmsg (reveal info) /\ SZ.v ml == Seq.length vmsg)
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg' **
  A.pts_to prk #pp vprk ** A.pts_to msg vmsg' **
  pure (prk_ok p vprk /\ info_ok p (reveal info) /\
        Seq.length vdg' == (hash_bytes p) /\
        msg_ok p vmsg' (reveal info) /\
        vdg' == expand_t p vprk info 1)
{
  A.pts_to_len dg;
  A.pts_to_len prk;
  A.pts_to_len msg;
  let hb = p.nhash_bytes;
  A.((msg.(SZ.sub ml 1sz) <- S8.classify 1uy));
  with vm1. assert (A.pts_to msg vm1);
  assert (pure (Seq.index vm1 (Seq.length vm1 - 1) == S8.classify 1uy));

  let sub = Sub.sub msg hb ml;
  with vsub. assert (A.pts_to sub vsub);
  assert (pure (reveal vsub == Seq.slice vm1 (SZ.v hb) (SZ.v ml)));
  assert (pure (Seq.length vsub == Seq.length info + 1));
  round_msg_pointwise #S32.t (reveal vsub) Seq.empty (reveal info) 1;
  assert (pure (reveal vsub ==
                Seq.append (Seq.append (Seq.empty #S8.t) (reveal info)) (counter 1)));

  hmac_impl_ni p kt ivt dg prk plen sub (SZ.sub ml hb);
  expand_t_unfold p (reveal vprk) (reveal info) 1;

  Sub.unsub_id msg (SZ.v hb) (SZ.v ml) sub;
}

(** Round [i > 1]: prepend the previous digest, bump the counter, hash. *)
fn round_step_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
              (kt: A.array S32.t) (ivt: A.array S32.t)
              (dg: A.array S8.t) (prk: A.array S8.t) (plen: SZ.t) (msg: A.array S8.t) (ml: SZ.t)
              (ci: U8.t)
              (#info: erased (Seq.seq S8.t))
              (#pk: perm) (#vk: erased (Seq.seq S32.t))
              (#pi: perm) (#vi: erased (Seq.seq S32.t))
              (#vdg: erased (Seq.seq S8.t))
              (#pp: perm) (#vprk: erased (Seq.seq S8.t))
              (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg **
         A.pts_to prk #pp vprk ** A.pts_to msg vmsg **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\ reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p (reveal info) /\
               block_len #S32.t + (hash_bytes p) + Seq.length info + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + (hash_bytes p) + Seq.length info + 1) /\
               msg_ok p vmsg (reveal info) /\ SZ.v ml == Seq.length vmsg /\
               1 < U8.v ci /\
               Seq.length vdg == (hash_bytes p) /\
               vdg == expand_t p vprk info (U8.v ci - 1))
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg' **
  A.pts_to prk #pp vprk ** A.pts_to msg vmsg' **
  pure (prk_ok p vprk /\ info_ok p (reveal info) /\ U8.v ci < 256 /\
        Seq.length vdg' == (hash_bytes p) /\
        msg_ok p vmsg' (reveal info) /\
        vdg' == expand_t p vprk info (U8.v ci))
{
  A.pts_to_len dg;
  A.pts_to_len prk;
  A.pts_to_len msg;
  let hb = p.nhash_bytes;
  copy_at msg 0sz dg hb;
  A.((msg.(SZ.sub ml 1sz) <- S8.classify ci));
  with vm1. assert (A.pts_to msg vm1);
  assert (pure (Seq.index vm1 (Seq.length vm1 - 1) == S8.classify (U8.uint_to_t (U8.v ci))));
  round_msg_pointwise #S32.t (reveal vm1) (reveal vdg) (reveal info) (U8.v ci);
  expand_t_unfold p (reveal vprk) (reveal info) (U8.v ci);
  hmac_impl_ni p kt ivt dg prk plen msg ml;
}

#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

fn expand_impl_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
               (kt: A.array S32.t) (ivt: A.array S32.t) (out: A.array S8.t) (len: SZ.t)
               (prk: A.array S8.t) (plen: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
               (#pk: perm) (#vk: erased (Seq.seq S32.t))
               (#pi: perm) (#vi: erased (Seq.seq S32.t))
               (#vout: erased (Seq.seq S8.t))
               (#pp: perm) (#vprk: erased (Seq.seq S8.t))
               (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\ reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p vinfo /\
               block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1) /\
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
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len info;
  round_sizes #S32.t p;
  let hb = p.nhash_bytes;
  let z8 = S8.classify 0uy;

  SZ.fits_lte (SZ.v hb + SZ.v ilen) (block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1);
  let ml = SZ.add (SZ.add hb ilen) 1sz;
  assert (pure (SZ.v ml == SZ.v hb + SZ.v ilen + 1));

  let mut marr = [| z8; ml |];
  A.pts_to_len marr;
  A.pts_to_len marr;

  let mut darr = [| z8; hb |];
  A.pts_to_len darr;
  A.pts_to_len darr;

  copy_at marr hb info ilen;
  with vm0. assert (A.pts_to marr vm0);
  assert (pure (Seq.length vm0 == SZ.v ml));
  msg_ok_of_copy p vm0 (reveal vinfo) hb ilen;

  if (SZ.gt len 0sz)
  ensures exists* (vout': Seq.seq S8.t) (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
    A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
    A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    A.pts_to darr vdg' ** A.pts_to marr vmsg' **
    pure (prk_ok p vprk /\ info_ok p vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vdg' == (hash_bytes p) /\ Seq.length vmsg' == SZ.v ml /\
          Seq.length vout <= 255 * (hash_bytes p) /\
          prefix_ok p vprk vinfo (SZ.v len) vout' (SZ.v len))
  {
    with vout0. assert (A.pts_to out vout0);
    prefix_ok_zero p (reveal vprk) (reveal vinfo) (SZ.v len) vout0 0;
    round_one_ni p kt ivt darr prk plen marr ml #vinfo;
    with vdg1. assert (A.pts_to darr vdg1);
    write_chunk out len 0sz darr hb;
    with vout1. assert (A.pts_to out vout1);
    prefix_ok_step p (reveal vprk) (reveal vinfo) (SZ.v len) 0 vout0 vout1 vdg1;

    let mut base = hb;
    let mut ci = 1uy;
    while (let vb = !base; SZ.lt vb len)
    invariant exists* (vb: SZ.t) (vc: U8.t) (vout': Seq.seq S8.t)
                      (vdg': Seq.seq S8.t) (vmsg': Seq.seq S8.t).
      pts_to base vb ** pts_to ci vc **
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
      A.pts_to darr vdg' ** A.pts_to marr vmsg' **
      pure (prk_ok p vprk /\ info_ok p vinfo /\
            Seq.length vout' == Seq.length vout /\
            Seq.length vout' == SZ.v len /\
            Seq.length vdg' == (hash_bytes p) /\
            msg_ok p vmsg' (reveal vinfo) /\ Seq.length vmsg' == SZ.v ml /\
            0 < U8.v vc /\ U8.v vc <= nrounds p (SZ.v len) /\
            SZ.v vb == U8.v vc * (hash_bytes p) /\
            vdg' == expand_t p vprk vinfo (U8.v vc) /\
            prefix_ok p vprk vinfo (SZ.v len) vout' (SZ.v vb))
    decreases (255 - U8.v (!ci))
    {
      let vb = !base;
      let vc = !ci;
      let n = nrounds p (SZ.v len);
      (* [vb = vc * hb < len <= n * hb], so there is at least one more round. *)
      Spec.HKDF.mult_lt_cancel (U8.v vc) n (hash_bytes p);
      let nc = U8.add vc 1uy;
      with vold. assert (A.pts_to out vold);
      round_step_ni p kt ivt darr prk plen marr ml nc #vinfo;
      with vdg1. assert (A.pts_to darr vdg1);
      write_chunk out len vb darr hb;
      with vnew. assert (A.pts_to out vnew);
      prefix_ok_step p (reveal vprk) (reveal vinfo) (SZ.v len) (U8.v vc) vold vnew vdg1;
      Math.lemma_mult_le_right (hash_bytes p) (U8.v nc) 255;
      SZ.fits_lte (SZ.v vb + SZ.v hb) (255 * (hash_bytes p));
      base := SZ.add vb hb;
      ci := nc;
    };
    with vbf. assert (pts_to base vbf);
    with voutf. assert (A.pts_to out voutf);
    assert (pure (SZ.v len <= SZ.v vbf));
    prefix_ok_weaken p (reveal vprk) (reveal vinfo) (SZ.v len) voutf (SZ.v vbf) (SZ.v len);
    assert (pure (prefix_ok p vprk vinfo (SZ.v len) voutf (SZ.v len)));
    with vdgf. assert (A.pts_to darr vdgf);
    with vmf. assert (A.pts_to marr vmf);
    assert (pure (Seq.length vdgf == hash_bytes p));
    assert (pure (Seq.length vmf == SZ.v ml));
    assert (pure (Seq.length voutf == Seq.length vout));
    assert (pure (prk_ok p vprk /\ info_ok p vinfo));
  }
  else
  {
    prefix_ok_zero p (reveal vprk) (reveal vinfo) (SZ.v len) vout (SZ.v len);
    assert (pure (prefix_ok p vprk vinfo (SZ.v len) vout (SZ.v len)));
  };

  with vout'. assert (A.pts_to out vout');
  prefix_ok_final p (reveal vprk) (reveal vinfo) (SZ.v len) vout';
  ()
}

#pop-options
