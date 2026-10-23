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

(** AES-GCM.

    The result goes to an output buffer [out] that is either the input
    buffer itself (in place) or disjoint from it ([Hacl.Impl.InOut]).
    Encryption writes the ciphertext there, and the tag to a separate
    sixteen bytes.  Decryption writes the plaintext there, but only on
    success -- a wrong tag leaves [out] exactly as it was, so a caller that
    ignores the returned boolean still never sees forged plaintext, and the
    type of [Spec.GCM.gcm_decrypt] says so.

    The tag comparison accumulates a mask over all sixteen bytes and
    declassifies once, at the end: no early exit, nothing that depends on
    where the first difference is. *)
module Hacl.AES.GCM

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Spec.GCM
open Hacl.AES.GF128
open Hacl.AES.GHash
open Hacl.AES.Key
open Hacl.AES.Cipher
open Hacl.AES.Block
open Hacl.AES.Counter
open Hacl.AES.CTR
open Hacl.AES.GMul

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module G = Spec.GF128
module Poly = Spec.GF128.Poly
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module Alg = Spec.GF128.Algebra
module Bytes = Hacl.Impl.Bytes
module Declassify = Hacl.Secret.Declassify
module Vec = Hacl.Vec128
module Stitch = Hacl.AES.GCM.Stitch
module Mem = Hacl.Mem
module IO = Hacl.Impl.InOut

open Hacl.Secret.Word.Instances

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Small pure facts} *)

let zeroed (v: Seq.seq S8.t)
  : Lemma (requires v == Seq.create blocklen S8.zero)
          (ensures vals v == Seq.create blocklen 0)
  = Seq.lemma_eq_intro (vals v) (Seq.create blocklen 0)

let whole_slice (v: Seq.seq elem)
  : Lemma (requires Seq.length v == blocklen)
          (ensures Seq.slice v 0 blocklen == v)
  = Seq.lemma_eq_intro (Seq.slice v 0 blocklen) v

(** The two halves written by [put_lenblock] are the two halves of the
    length block of the spec. *)
let lenblock_eq (v: Seq.seq S8.t) (la lc: nat)
  : Lemma (requires Seq.length v == blocklen /\ la < pow2 64 /\ lc < pow2 64 /\
                    (forall (k: nat). k < 8 ==>
                       Seq.index (vals v) k == (la / pow2 (8 * (7 - k))) % 256) /\
                    (forall (k: nat). 8 <= k /\ k < blocklen ==>
                       Seq.index (vals v) k == (lc / pow2 (8 * (15 - k))) % 256))
          (ensures vals v == Seq.append (u64be la) (u64be lc))
  = let r = Seq.append (u64be la) (u64be lc) in
    Seq.lemma_len_append (u64be la) (u64be lc);
    let aux (k: nat { k < blocklen }) : Lemma (Seq.index (vals v) k == Seq.index r k) =
      if k < 8 then Seq.lemma_index_app1 (u64be la) (u64be lc) k
      else Seq.lemma_index_app2 (u64be la) (u64be lc) k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (vals v) r

(** The counter-mode output is the ciphertext the tag is taken over. *)
let bits_fit (n: nat)
  : Lemma (requires n <= max_aad) (ensures 8 * n < pow2 64 /\ n < pow2 64)
  = assert_norm (8 * (pow2 61 - 1) < pow2 64)

let msg_bits_fit (n: nat)
  : Lemma (requires n <= max_msg) (ensures 8 * n < pow2 64 /\ n < pow2 64)
  = assert_norm (8 * (pow2 36 - 32) < pow2 64)

(** {2 The pieces} *)

(** One window of the key context holds what it is meant to hold. *)

let win_eq (v w: Seq.seq S8.t) (i: nat)
  : Lemma (requires 16 * i + blocklen <= Seq.length v /\ Seq.length w == blocklen /\
                    (forall (k: nat). k < blocklen ==>
                       Seq.index v (16 * i + k) == Seq.index w k))
          (ensures Alg.hblk (vals v) i == vals w)
  = Seq.lemma_eq_intro (Seq.slice (vals v) (16 * i) (16 * i + blocklen)) (vals w)

(** The whole context, from the chain of products that built it.

    Proving {!Spec.GF128.Algebra.pows_ok} where the array was written would
    ask the solver to do this in a context holding eight intermediate array
    states and the frames that relate them; here there is nothing but the
    eight blocks. *)

let pows_build (v: Seq.seq elem) (b0 b1 b2 b3 b4 b5 b6 b7: G.block)
  : Lemma (requires Seq.length v == Alg.powlen /\
                    Alg.hblk v 0 == b0 /\ Alg.hblk v 1 == b1 /\
                    Alg.hblk v 2 == b2 /\ Alg.hblk v 3 == b3 /\
                    Alg.hblk v 4 == b4 /\ Alg.hblk v 5 == b5 /\
                    Alg.hblk v 6 == b6 /\ Alg.hblk v 7 == b7 /\
                    b1 == G.gmul b0 (Poly.xtimes b0) /\
                    b2 == G.gmul b1 (Poly.xtimes b0) /\
                    b3 == G.gmul b2 (Poly.xtimes b0) /\
                    b4 == G.gmul b3 (Poly.xtimes b0) /\
                    b5 == G.gmul b4 (Poly.xtimes b0) /\
                    b6 == G.gmul b5 (Poly.xtimes b0) /\
                    b7 == G.gmul b6 (Poly.xtimes b0))
          (ensures Alg.pows_ok v)
  = Alg.pow_adv b0 b0; Alg.pow_adv b1 b0; Alg.pow_adv b2 b0;
    Alg.pow_adv b3 b0; Alg.pow_adv b4 b0; Alg.pow_adv b5 b0;
    Alg.pow_adv b6 b0

(** [hb := h/x, h^2/x, ..., h^8/x], the first eight powers of the hash key,
    each divided by [x].

    GHASH's multiplier omits the one-bit shift that would line the carry-less
    product up with GHASH's bit order, and so computes [x] times the field
    product; the hash key is therefore stored pre-divided, once, here, and
    every multiplication the cipher goes on to do comes out exact at no cost.
    See [Hacl.AES.GF128.NI.raw_product].

    The powers are here rather than in the hash loop because they are a
    function of the key alone.  Aggregated GHASH needs [h^4] and [h^8] to
    fold four or eight blocks at a time, and recomputing them per message
    cost three serial multiplications -- enough that a short message could
    not earn them back, which is why the loop used to fall back to one block
    at a time below a hundred and twenty-eight bytes.  Computed once with the
    round keys, they are free, and the aggregated path can run from the first
    sixty-four bytes.

    [Spec.GF128.Algebra.pows_ok] says only that each window is the previous
    one advanced by the first, which is exactly the recurrence the loop below
    runs; nothing needs a closed form.  Nothing outside this file sees the
    division either: the key array is private to the context and the two
    routines that read it, [j0_impl] and [gtag_impl], ask only that advancing
    window zero once gives the real key. *)

fn hkey_impl ([@@@FStar.Attributes.monomorphize] p: params)
             (hb: A.array S8.t) (w: A.array S8.t)
             (#vh0 #vw: erased (Seq.seq S8.t))
requires A.pts_to hb vh0 ** A.pts_to w vw ** pure (
  Seq.length vh0 == 128 /\ Seq.length vw == xkeylen p.pv)
ensures exists* (vh1: Seq.seq S8.t). A.pts_to hb vh1 ** A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh1 == 128 /\
  Alg.pows_ok (vals vh1) /\ Poly.xtimes (Alg.hblk (vals vh1) 0) == hkey p.pv (vals vw))
{
  A.pts_to_len hb;
  let z = S8.zero;
  let mut kb = [| z; 16sz |];
  Mem.track kb;
  A.pts_to_len kb;
  A.pts_to_len kb;
  let mut ab = [| z; 16sz |];
  Mem.track ab;
  A.pts_to_len ab;
  A.pts_to_len ab;

  Copy.fill kb S8.zero 16sz;
  with vz. assert A.pts_to kb vz;
  zeroed vz;
  cipher_impl p kb w;
  with vk. assert A.pts_to kb vk;
  Poly.xtimes_xdiv (vals vk);
  Hacl.AES.GF128.xdiv_impl kb;
  with v0. assert A.pts_to kb v0;

  Copy.copy_exact ab kb 16sz;
  Copy.copy_range hb 0sz kb 0sz 16sz;

  gmul_impl ab kb; with v1. assert A.pts_to ab v1;
  Copy.copy_range hb 16sz ab 0sz 16sz;
  gmul_impl ab kb; with v2. assert A.pts_to ab v2;
  Copy.copy_range hb 32sz ab 0sz 16sz;
  gmul_impl ab kb; with v3. assert A.pts_to ab v3;
  Copy.copy_range hb 48sz ab 0sz 16sz;
  gmul_impl ab kb; with v4. assert A.pts_to ab v4;
  Copy.copy_range hb 64sz ab 0sz 16sz;
  gmul_impl ab kb; with v5. assert A.pts_to ab v5;
  Copy.copy_range hb 80sz ab 0sz 16sz;
  gmul_impl ab kb; with v6. assert A.pts_to ab v6;
  Copy.copy_range hb 96sz ab 0sz 16sz;
  gmul_impl ab kb; with v7. assert A.pts_to ab v7;
  Copy.copy_range hb 112sz ab 0sz 16sz;

  with vf. assert A.pts_to hb vf;
  win_eq vf v0 0; win_eq vf v1 1; win_eq vf v2 2; win_eq vf v3 3;
  win_eq vf v4 4; win_eq vf v5 5; win_eq vf v6 6; win_eq vf v7 7;
  pows_build (vals vf) (vals v0) (vals v1) (vals v2) (vals v3)
                       (vals v4) (vals v5) (vals v6) (vals v7);
  Mem.wipe ab 16sz;
  Mem.wipe kb 16sz;
  ()
}

(** The length block: the two lengths in bits, big end first. *)

fn put_lenblock (lb: A.array S8.t) (la lc: SZ.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to lb v0 ** pure (
  Seq.length v0 == blocklen /\ 8 * SZ.v la < pow2 64 /\ 8 * SZ.v lc < pow2 64)
ensures exists* (v1: Seq.seq S8.t). A.pts_to lb v1 ** pure (
  Seq.length v1 == blocklen /\
  8 * SZ.v la < pow2 64 /\ 8 * SZ.v lc < pow2 64 /\
  vals v1 == Seq.append (u64be (8 * SZ.v la)) (u64be (8 * SZ.v lc)))
{
  A.pts_to_len lb;
  Math.modulo_lemma (SZ.v la) (pow2 64);
  Math.modulo_lemma (SZ.v lc) (pow2 64);
  (* The two multiplications are named, and their values said, before they
     are classified: left inline inside [classify] the refinement on
     [U64.mul]'s result does not reach the solver. *)
  let la64 = SZ.sizet_to_uint64 la;
  let lc64 = SZ.sizet_to_uint64 lc;
  let xb = U64.mul la64 8uL;
  let yb = U64.mul lc64 8uL;
  assert (pure (U64.v xb == 8 * SZ.v la /\ U64.v yb == 8 * SZ.v lc));
  let x = S64.classify xb;
  let y = S64.classify yb;
  assert (pure (S64.v x == 8 * SZ.v la /\ S64.v y == 8 * SZ.v lc));
  Bytes.store_be #S64.t lb 0sz x;
  Bytes.store_be #S64.t lb 8sz y;
  with v1. assert A.pts_to lb v1;
  lenblock_eq v1 (8 * SZ.v la) (8 * SZ.v lc);
  A.pts_to_len lb;
}

(** The pre-counter block.  Twelve bytes of nonce and a counter of one, or a
    GHASH of the padded nonce and its length. *)

fn j0_impl ([@@@FStar.Attributes.monomorphize] p: params)
           (jb: A.array S8.t) (w: A.array S8.t) (hb: A.array S8.t)
           (iv: A.array S8.t) (n: SZ.t)
           (#vj0 #vw #vh: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
requires A.pts_to jb vj0 ** A.pts_to w vw ** A.pts_to hb vh **
         A.pts_to iv #pi viv ** pure (
  Seq.length vj0 == blocklen /\ Seq.length vw == xkeylen p.pv /\
  Seq.length vh == 128 /\ Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey p.pv (vals vw) /\
  iv_ok (vals viv) /\ SZ.fits (Seq.length viv + blocklen))
         ** pure (SZ.v n == Seq.length viv)
ensures exists* (vj1: Seq.seq S8.t).
  A.pts_to jb vj1 ** A.pts_to w vw ** A.pts_to hb vh **
  A.pts_to iv #pi viv ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
  Seq.length vj1 == blocklen /\ iv_ok (vals viv) /\
  vals vj1 == j0 p.pv (vals vw) (vals viv))
{
  A.pts_to_len jb;
  A.pts_to_len hb;
  A.pts_to_len iv;
  let z = S8.zero;
  let mut lbarr = [| z; 16sz |];
  Mem.track lbarr;
  A.pts_to_len lbarr;
  A.pts_to_len lbarr;

  if (n = 12sz) {
    Copy.copy_range jb 0sz iv 0sz 12sz;
    let one = S8.classify 1uy;
    A.((jb.(12sz) <- z));
    A.((jb.(13sz) <- z));
    A.((jb.(14sz) <- z));
    A.((jb.(15sz) <- one));
    with vj1. assert A.pts_to jb vj1;
    Seq.lemma_eq_intro (vals vj1)
      (Seq.append (vals viv) (Seq.init 4 (fun i -> (if i = 3 then 1 else 0) <: elem)));
    Mem.wipe lbarr 16sz;
    ()
  } else {
    Copy.fill jb S8.zero 16sz;
    with vz. assert A.pts_to jb vz;
    zeroed vz;
    ghash_upd_impl jb hb iv n;
    bits_fit (Seq.length viv);
    put_lenblock lbarr 0sz n;
    pad_exact (Seq.append (u64be 0) (u64be (8 * Seq.length viv)));
    ghash_upd_impl jb hb lbarr 16sz;
    j0_fold p.pv (vals vw) (vals viv);
    Mem.wipe lbarr 16sz;
    ()
  }
}

(** The tag: the GHASH of the three pieces, masked with the encryption of
    [j0]. *)

fn gtag_impl ([@@@FStar.Attributes.monomorphize] p: params)
             (tag: A.array S8.t) (w: A.array S8.t) (hb: A.array S8.t)
             (jb: A.array S8.t) (aad: A.array S8.t) (alen: SZ.t) (cip: A.array S8.t) (clen: SZ.t)
             (#vt0 #vw #vh #vj: erased (Seq.seq S8.t))
             (#pa: perm) (#va: erased (Seq.seq S8.t))
             (#pc: perm) (#vc: erased (Seq.seq S8.t))
requires A.pts_to tag vt0 ** A.pts_to w vw ** A.pts_to hb vh **
         A.pts_to jb vj ** A.pts_to aad #pa va ** A.pts_to cip #pc vc ** pure (
  Seq.length vt0 == taglen /\ Seq.length vw == xkeylen p.pv /\
  Seq.length vh == 128 /\ Seq.length vj == blocklen /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey p.pv (vals vw) /\
  aad_ok (vals va) /\ msg_ok (vals vc) /\
  SZ.fits (Seq.length va + blocklen) /\ SZ.fits (Seq.length vc + blocklen))
         ** pure (SZ.v alen == Seq.length va)
         ** pure (SZ.v clen == Seq.length vc)
ensures exists* (vt1: Seq.seq S8.t).
  A.pts_to tag vt1 ** A.pts_to w vw ** A.pts_to hb vh **
  A.pts_to jb vj ** A.pts_to aad #pa va ** A.pts_to cip #pc vc ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
  Seq.length vj == blocklen /\ Seq.length vt1 == taglen /\
  aad_ok (vals va) /\ msg_ok (vals vc) /\
  vals vt1 == gtag p.pv (vals vw) (vals vj) (vals va) (vals vc))
{
  A.pts_to_len tag;
  A.pts_to_len hb;
  A.pts_to_len jb;
  A.pts_to_len aad;
  A.pts_to_len cip;

  let z = S8.zero;
  let mut accarr = [| z; 16sz |];
  Mem.track accarr;
  A.pts_to_len accarr;
  A.pts_to_len accarr;
  let mut lbarr = [| z; 16sz |];
  Mem.track lbarr;
  A.pts_to_len lbarr;
  A.pts_to_len lbarr;

  with vz. assert A.pts_to accarr vz;
  zeroed vz;
  ghash_upd_impl accarr hb aad alen;
  ghash_upd_impl accarr hb cip clen;
  bits_fit (Seq.length va);
  msg_bits_fit (Seq.length vc);
  put_lenblock lbarr alen clen;
  pad_exact (len_block (vals va) (vals vc));
  ghash_upd_impl accarr hb lbarr 16sz;

  Copy.copy_exact tag jb 16sz;
  cipher_impl p tag w;
  with vacc. assert A.pts_to accarr vacc;
  whole_slice (vals vacc);
  gadd_at_impl tag accarr 0sz;
  gtag_fold p.pv (vals vw) (vals vj) (vals va) (vals vc);
  Mem.wipe lbarr 16sz;
  Mem.wipe accarr 16sz;
  ()
}

(** The tag's last two steps, once the associated data and the ciphertext
    are already in the accumulator: the length block, and the mask.  The
    stitched encryption path hashes the ciphertext as it writes it, so it
    comes in here. *)

[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn gtag_fin ([@@@FStar.Attributes.monomorphize] p: params)
            (tag: A.array S8.t) (w: A.array S8.t) (hb: A.array S8.t)
            (jb: A.array S8.t) (accarr: A.array S8.t) (alen clen: SZ.t)
            (a c: erased (Seq.seq elem))
            (#vt0 #vw #vh #vj #vacc: erased (Seq.seq S8.t))
requires A.pts_to tag vt0 ** A.pts_to w vw ** A.pts_to hb vh **
         A.pts_to jb vj ** A.pts_to accarr vacc ** pure (
  Seq.length vt0 == taglen /\ Seq.length vw == xkeylen p.pv /\
  Seq.length vh == 128 /\ Seq.length vj == blocklen /\ Seq.length vacc == blocklen /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey p.pv (vals vw) /\
  aad_ok a /\ Seq.length c <= max_msg /\
  SZ.v alen == Seq.length a /\ SZ.v clen == Seq.length c /\
  vals vacc == G.ghash_upd (hkey p.pv (vals vw))
                 (G.ghash_upd (hkey p.pv (vals vw)) G.zero (pad a)) (pad c))
ensures exists* (vt1 vacc1: Seq.seq S8.t).
  A.pts_to tag vt1 ** A.pts_to w vw ** A.pts_to hb vh **
  A.pts_to jb vj ** A.pts_to accarr vacc1 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
  Seq.length vj == blocklen /\ Seq.length vt1 == taglen /\
  aad_ok a /\ Seq.length c <= max_msg /\
  vals vt1 == gtag p.pv (vals vw) (vals vj) a c)
{
  A.pts_to_len tag;
  A.pts_to_len accarr;
  let z = S8.zero;
  let mut lbarr = [| z; 16sz |];
  Mem.track lbarr;
  A.pts_to_len lbarr;
  A.pts_to_len lbarr;

  bits_fit (Seq.length a);
  msg_bits_fit (Seq.length c);
  put_lenblock lbarr alen clen;
  pad_exact (len_block a c);
  ghash_upd_impl accarr hb lbarr 16sz;

  Copy.copy_exact tag jb 16sz;
  cipher_impl p tag w;
  with vacc1. assert A.pts_to accarr vacc1;
  whole_slice (vals vacc1);
  gadd_at_impl tag accarr 0sz;
  gtag_fold p.pv (vals vw) (vals vj) a c;
  Mem.wipe lbarr 16sz;
  ()
}

(** {2 The tag comparison}

    Sixteen [eq_mask]s folded with [logand]: every byte is read, the result
    is one mask, and exactly one bit of it becomes public. *)

let mask_and (a b: nat)
  : Lemma (requires (a == 0 \/ a == 255) /\ (b == 0 \/ b == 255))
          (ensures UInt.logand #8 a b == (if a = 255 && b = 255 then 255 else 0))
  = (* The four cases, from the library's own lemmas: normalising [logand]
       goes through [to_vec], which the solver no longer gets through. *)
    assert_norm (UInt.ones 8 == 255);
    assert_norm (UInt.zero 8 == 0);
    UInt.logand_self #8 255;
    UInt.logand_lemma_1 #8 255;
    UInt.logand_lemma_1 #8 0;
    UInt.logand_commutative #8 0 255

fn tag_match (a: A.array S8.t) (b: A.array S8.t)
             (#pa: perm) (#va: erased (Seq.seq S8.t))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb ** pure (
  Seq.length va == taglen /\ Seq.length vb == taglen)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb ** pure (
  Seq.length va == taglen /\ Seq.length vb == taglen /\
  r == Seq.equal (vals va) (vals vb))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut m = S8.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vm: S8.t).
    pts_to i vi ** pts_to m vm ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= taglen /\ Seq.length va == taglen /\ Seq.length vb == taglen /\
          S8.v vm == (if (forall (j: nat). j < SZ.v vi ==>
                            Seq.index (vals va) j == Seq.index (vals vb) j)
                      then 255 else 0))
  decreases (taglen - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let vm = !m;
    let e = S8.eq_mask x y;
    mask_and (S8.v vm) (S8.v e);
    m := S8.logand vm e;
    i := SZ.add vi 1sz;
  };
  let vm = !m;
  let r = Declassify.bool_of_mask vm;
  assert (pure (r == (S8.v vm = 255)));
  A.pts_to_len a;
  r
}

(** {2 The key schedule as a separate step}

    Expanding the key is a fixed cost of about 26 ns for AES-128, and
    dividing the hash key by [x] another 5, and neither depends on the
    nonce, the associated data or the message.  A caller that talks to the
    same peer more than once should pay for them once, so the two directions
    below are split: {!expand_impl} does everything that is a function of
    the key alone, and {!encrypt_w} and {!decrypt_w} do the rest.

    The context is two arrays rather than one, because every function that
    reads it wants a whole array and nothing here needs the two to be
    adjacent.  [ek] is the round keys, [xkeylen] bytes of them; [hk] is 128
    bytes, the first eight powers of the GHASH subkey, each held divided by
    [x] as {!hkey_impl} explains.

    The specification of {!encrypt_w} is [Spec.GCM.gcm_encrypt_w], which is
    [gcm_encrypt] with the expansion already done, so composing the two
    steps is by definition and the caller is never asked to reason about
    what a round key is. *)

fn expand_impl ([@@@FStar.Attributes.monomorphize] p: params)
               (ek: A.array S8.t) (hk: A.array S8.t) (key: A.array S8.t)
               (#ve0 #vh0: erased (Seq.seq S8.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to ek ve0 ** A.pts_to hk vh0 ** A.pts_to key #pk vkey ** pure (
  Seq.length ve0 == xkeylen p.pv /\ Seq.length vh0 == 128 /\
  Seq.length vkey == keylen p.pv)
ensures exists* (ve1 vh1: Seq.seq S8.t).
  A.pts_to ek ve1 ** A.pts_to hk vh1 ** A.pts_to key #pk vkey ** pure (
  Seq.length ve1 == xkeylen p.pv /\ Seq.length vh1 == 128 /\
  Seq.length vkey == keylen p.pv /\
  vals ve1 == key_expansion p.pv (vals vkey) /\
  Alg.pows_ok (vals vh1) /\ Poly.xtimes (Alg.hblk (vals vh1) 0) == hkey p.pv (vals ve1))
{
  key_expansion_impl p ek key;
  hkey_impl p hk ek;
}

(** [out] comes back holding the ciphertext of [msg] and [tag] the tag.
    [out] is [msg] itself (in place) or an array disjoint from it; see
    [Hacl.Impl.InOut]. *)

fn encrypt_w ([@@@FStar.Attributes.monomorphize] p: params)
             (ek: A.array S8.t) (hk: A.array S8.t)
             (iv: A.array S8.t) (iv_len: SZ.t) (aad: A.array S8.t) (aad_len: SZ.t)
             (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
             (#ve #vh: erased (Seq.seq S8.t))
             (#pi: perm) (#viv: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pm: perm) (#vo0 #vm0 #vt0: erased (Seq.seq S8.t))
requires A.pts_to ek ve ** A.pts_to hk vh **
         A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
         IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag vt0 ** pure (
  Seq.length ve == xkeylen p.pv /\ Seq.length vh == 128 /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey p.pv (vals ve) /\
  Seq.length vt0 == taglen /\ Seq.length vo0 == Seq.length vm0 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v iv_len == Seq.length viv)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v msg_len == Seq.length vm0)
ensures exists* (vo1 vt1: Seq.seq S8.t).
  A.pts_to ek ve ** A.pts_to hk vh **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag vt1 ** pure (
  Seq.length vo1 == Seq.length vm0 /\ Seq.length vt1 == taglen /\
  Seq.length ve == xkeylen p.pv /\ Seq.length vh == 128 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vo1, vals vt1) ==
    gcm_encrypt_w p.pv (vals ve) (vals viv) (vals vaad) (vals vm0))
{
  IO.inout_len out msg;
  A.pts_to_len tag;

  let z = S8.zero;
  let mut jarr = [| z; 16sz |];
  Mem.track jarr;
  A.pts_to_len jarr;
  A.pts_to_len jarr;
  let mut carr = [| z; 16sz |];
  Mem.track carr;
  A.pts_to_len carr;
  A.pts_to_len carr;

  j0_impl p jarr ek hk iv iv_len;
  Copy.copy_exact carr jarr 16sz;
  inc32_impl carr;
  if (Hacl.X64.x86_64)
  {
    if (SZ.lte 128sz msg_len && Vec.supported ())
    {
      (* Stitched: each 128 bytes of ciphertext is hashed while the next 128
         are being encrypted. *)
      let mut accarr = [| z; 16sz |];
      Mem.track accarr;
      A.pts_to_len accarr;
      with vz. assert A.pts_to accarr vz;
      zeroed vz;
      ghash_upd_impl accarr hk aad aad_len;
      Stitch.ctr_ghash p out msg msg_len ek hk carr accarr;
      with vo1. assert IO.inout out msg pm (SZ.v msg_len) vo1 vm0;
      gtag_fin p tag ek hk jarr accarr aad_len msg_len (vals vaad) (vals vo1);
      Mem.wipe accarr 16sz;
      Mem.wipe carr 16sz;
      Mem.wipe jarr 16sz;
      ()
    }
    else
    {
      ctr_encrypt_impl p out msg msg_len ek carr;
      with vo1. assert IO.inout out msg pm (SZ.v msg_len) vo1 vm0;
      unfold (IO.inout out msg pm (SZ.v msg_len) vo1 vm0);
      gtag_impl p tag ek hk jarr aad aad_len out msg_len;
      fold (IO.inout out msg pm (SZ.v msg_len) vo1 vm0);
      Mem.wipe carr 16sz;
      Mem.wipe jarr 16sz;
      ()
    }
  }
  else
  {
    ctr_encrypt_impl p out msg msg_len ek carr;
    with vo1. assert IO.inout out msg pm (SZ.v msg_len) vo1 vm0;
    unfold (IO.inout out msg pm (SZ.v msg_len) vo1 vm0);
    gtag_impl p tag ek hk jarr aad aad_len out msg_len;
    fold (IO.inout out msg pm (SZ.v msg_len) vo1 vm0);
    Mem.wipe carr 16sz;
    Mem.wipe jarr 16sz;
    ()
  }
}

(** The ciphertext [msg] is authenticated first, and only then decrypted
    into [out], which is [msg] itself (in place) or an array disjoint from
    it.  A wrong tag leaves [out] untouched. *)

fn decrypt_w ([@@@FStar.Attributes.monomorphize] p: params)
             (ek: A.array S8.t) (hk: A.array S8.t)
             (iv: A.array S8.t) (iv_len: SZ.t) (aad: A.array S8.t) (aad_len: SZ.t)
             (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
             (#ve #vh: erased (Seq.seq S8.t))
             (#pi: perm) (#viv: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pt: perm) (#vtag: erased (Seq.seq S8.t))
             (#pm: perm) (#vo0 #vm0: erased (Seq.seq S8.t))
requires A.pts_to ek ve ** A.pts_to hk vh **
         A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
         IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag #pt vtag ** pure (
  Seq.length ve == xkeylen p.pv /\ Seq.length vh == 128 /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey p.pv (vals ve) /\
  Seq.length vtag == taglen /\ Seq.length vo0 == Seq.length vm0 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v iv_len == Seq.length viv)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v msg_len == Seq.length vm0)
returns r: bool
ensures exists* (vo1: Seq.seq S8.t).
  A.pts_to ek ve ** A.pts_to hk vh **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag #pt vtag ** pure (
  Seq.length vo1 == Seq.length vm0 /\
  Seq.length ve == xkeylen p.pv /\ Seq.length vh == 128 /\
  Seq.length vtag == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt_w p.pv (vals ve) (vals viv) (vals vaad)
                         (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vo1 == Some?.v d) /\
   ((~r) ==> None? d /\ vo1 == reveal vo0)))
{
  IO.inout_len out msg;
  A.pts_to_len tag;

  let z = S8.zero;
  let mut jarr = [| z; 16sz |];
  Mem.track jarr;
  A.pts_to_len jarr;
  A.pts_to_len jarr;
  let mut carr = [| z; 16sz |];
  Mem.track carr;
  A.pts_to_len carr;
  A.pts_to_len carr;
  let mut tarr = [| z; 16sz |];
  Mem.track tarr;
  A.pts_to_len tarr;
  A.pts_to_len tarr;

  j0_impl p jarr ek hk iv iv_len;
  (* Nothing has been written yet, so all of [msg] is the ciphertext. *)
  IO.borrow_in out msg;
  with (q: perm) (v: Seq.seq S8.t). assert A.pts_to msg #q v;
  assert (pure (Seq.equal v vm0));
  gtag_impl p tarr ek hk jarr aad aad_len msg msg_len;
  IO.return_in out msg;
  let ok = tag_match tarr tag;

  if ok {
    Copy.copy_exact carr jarr 16sz;
    inc32_impl carr;
    ctr_encrypt_impl p out msg msg_len ek carr;
    Mem.wipe tarr 16sz;
    Mem.wipe carr 16sz;
    Mem.wipe jarr 16sz;
    true
  } else {
    unfold (IO.inout out msg pm 0 vo0 vm0);
    IO.inout_advance out msg (SZ.v msg_len);
    Mem.wipe tarr 16sz;
    Mem.wipe carr 16sz;
    Mem.wipe jarr 16sz;
    false
  }
}

(** {2 The two directions} *)

(** [out] comes back holding the ciphertext of [msg] and [tag] the tag.
    [out] is [msg] itself (in place) or an array disjoint from it. *)

fn encrypt ([@@@FStar.Attributes.monomorphize] p: params)
           (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t) (aad: A.array S8.t) (aad_len: SZ.t)
           (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pm: perm) (#vo0 #vm0 #vt0: erased (Seq.seq S8.t))
requires A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
         IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag vt0 ** pure (
  Seq.length vkey == keylen p.pv /\ Seq.length vt0 == taglen /\
  Seq.length vo0 == Seq.length vm0 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v iv_len == Seq.length viv)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v msg_len == Seq.length vm0)
ensures exists* (vo1 vt1: Seq.seq S8.t).
  A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag vt1 ** pure (
  Seq.length vo1 == Seq.length vm0 /\ Seq.length vt1 == taglen /\
  Seq.length vkey == keylen p.pv /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vo1, vals vt1) ==
    gcm_encrypt p.pv (vals vkey) (vals viv) (vals vaad) (vals vm0))
{
  A.pts_to_len key;
  IO.inout_len out msg;
  A.pts_to_len tag;

  let z = S8.zero;
  let mut warr = [| z; p.pxkeylen |];
  Mem.track warr;
  A.pts_to_len warr;
  A.pts_to_len warr;
  let mut harr = [| z; 128sz |];
  Mem.track harr;
  A.pts_to_len harr;
  A.pts_to_len harr;

  expand_impl p warr harr key;
  encrypt_w p warr harr iv iv_len aad aad_len out msg msg_len tag;

  Mem.wipe harr 128sz;
  Mem.wipe warr p.pxkeylen;
  ()
}

(** The ciphertext [msg] is decrypted into [out], which is [msg] itself
    (in place) or an array disjoint from it, if the tag is right.  A wrong
    tag leaves [out] untouched. *)

fn decrypt ([@@@FStar.Attributes.monomorphize] p: params)
           (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t) (aad: A.array S8.t) (aad_len: SZ.t)
           (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pt: perm) (#vtag: erased (Seq.seq S8.t))
           (#pm: perm) (#vo0 #vm0: erased (Seq.seq S8.t))
requires A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
         IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag #pt vtag ** pure (
  Seq.length vkey == keylen p.pv /\ Seq.length vtag == taglen /\
  Seq.length vo0 == Seq.length vm0 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v iv_len == Seq.length viv)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v msg_len == Seq.length vm0)
returns r: bool
ensures exists* (vo1: Seq.seq S8.t).
  A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag #pt vtag ** pure (
  Seq.length vo1 == Seq.length vm0 /\
  Seq.length vkey == keylen p.pv /\ Seq.length vtag == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt p.pv (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vo1 == Some?.v d) /\
   ((~r) ==> None? d /\ vo1 == reveal vo0)))
{
  A.pts_to_len key;
  IO.inout_len out msg;
  A.pts_to_len tag;

  let z = S8.zero;
  let mut warr = [| z; p.pxkeylen |];
  Mem.track warr;
  A.pts_to_len warr;
  A.pts_to_len warr;
  let mut harr = [| z; 128sz |];
  Mem.track harr;
  A.pts_to_len harr;
  A.pts_to_len harr;

  expand_impl p warr harr key;
  let wr = decrypt_w p warr harr iv iv_len aad aad_len out msg msg_len tag;
  Mem.wipe harr 128sz;
  Mem.wipe warr p.pxkeylen;
  wr
}

#pop-options

(** {2 The two key sizes}

    [encrypt] and [decrypt] are generic in the key schedule; these fix it, and
    are what the C header exports:

      void Hacl_AES_GCM_aes128_encrypt(uint8_t *out, uint8_t *tag,
                                       uint8_t *msg, size_t msg_len,
                                       uint8_t *key, uint8_t *iv, size_t iv_len,
                                       uint8_t *aad, size_t aad_len);
      bool Hacl_AES_GCM_aes128_decrypt(uint8_t *out, uint8_t *msg, size_t msg_len,
                                       uint8_t *tag, uint8_t *key,
                                       uint8_t *iv, size_t iv_len,
                                       uint8_t *aad, size_t aad_len);

    and the same for [aes256_*] with a 32-byte key.  [msg] is the input, the
    plaintext for [encrypt] and the ciphertext for [decrypt], and [out]
    receives the result; both are [msg_len] bytes long.  [out] may be the
    same pointer as [msg], for in-place operation, but otherwise the two
    must not overlap.  [decrypt] checks the tag before writing anything,
    and on a wrong tag returns [false] and leaves [out] untouched. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

fn aes128_encrypt (out: A.array S8.t) (tag: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vt0 #vm0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag vt0 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag vt1 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vo1 == SZ.v msg_len /\
  Seq.length vkey == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vo1, vals vt1) == gcm_encrypt AES128 (vals vkey) (vals viv)
                                      (vals vaad) (vals vm0))
{
  encrypt params128 key iv iv_len aad aad_len out msg msg_len tag;
}

fn aes128_decrypt (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vm0: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vo1 == SZ.v msg_len /\ Seq.length vkey == 16 /\
  Seq.length vtag == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt AES128 (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vo1 == Some?.v d) /\
   ((~r) ==> None? d /\ vo1 == reveal vo0)))
{
  decrypt params128 key iv iv_len aad aad_len out msg msg_len tag
}

fn aes256_encrypt (out: A.array S8.t) (tag: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vt0 #vm0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag vt0 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag vt1 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vo1 == SZ.v msg_len /\
  Seq.length vkey == 32 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vo1, vals vt1) == gcm_encrypt AES256 (vals vkey) (vals viv)
                                      (vals vaad) (vals vm0))
{
  encrypt params256 key iv iv_len aad aad_len out msg msg_len tag;
}

fn aes256_decrypt (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vm0: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vo1 == SZ.v msg_len /\ Seq.length vkey == 32 /\
  Seq.length vtag == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt AES256 (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vo1 == Some?.v d) /\
   ((~r) ==> None? d /\ vo1 == reveal vo0)))
{
  decrypt params256 key iv iv_len aad aad_len out msg msg_len tag
}

(** {2 The expanded-key entry points}

    The same four, with the key schedule hoisted out.  [ek] is 176 bytes for
    AES-128 and 240 for AES-256; [hk] is always 128, eight blocks holding
    the first eight powers of the GHASH subkey.  Both are written by
    [expand] and then only read, but they are passed with full ownership,
    because everything underneath wants a whole array it can be handed:

      void Hacl_AES_GCM_aes128_expand(uint8_t *ek, uint8_t *hk, uint8_t *key);
      void Hacl_AES_GCM_aes128_encrypt_expanded(uint8_t *out, uint8_t *tag,
                                                uint8_t *msg, size_t msg_len,
                                                uint8_t *ek, uint8_t *hk,
                                                uint8_t *iv, size_t iv_len,
                                                uint8_t *aad, size_t aad_len);
      bool Hacl_AES_GCM_aes128_decrypt_expanded(uint8_t *out, uint8_t *msg,
                                                size_t msg_len, uint8_t *tag,
                                                uint8_t *ek, uint8_t *hk,
                                                uint8_t *iv, size_t iv_len,
                                                uint8_t *aad, size_t aad_len);

    [out] and [msg] are as for [aes128_encrypt]: [msg_len] bytes each, and
    either the same pointer or not overlapping.

    There is nothing secret about the split: [aes128_encrypt] is
    [aes128_expand] followed by [aes128_encrypt_expanded] on a stack
    context, and [gcm_encrypt] is [gcm_encrypt_w] of [key_expansion], so the
    two specifications compose by unfolding one definition. *)

fn aes128_expand (ek: A.array S8.t) (hk: A.array S8.t) (key: A.array S8.t)
       (#ve0 #vh0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to ek ve0 ** A.pts_to hk vh0 ** A.pts_to key #pk vkey ** pure (
  Seq.length ve0 == 176 /\ Seq.length vh0 == 128 /\ Seq.length vkey == 16)
ensures exists* (ve1 vh1: Seq.seq S8.t).
  A.pts_to ek ve1 ** A.pts_to hk vh1 ** A.pts_to key #pk vkey ** pure (
  Seq.length ve1 == 176 /\ Seq.length vh1 == 128 /\ Seq.length vkey == 16 /\
  vals ve1 == key_expansion AES128 (vals vkey) /\
  Alg.pows_ok (vals vh1) /\ Poly.xtimes (Alg.hblk (vals vh1) 0) == hkey AES128 (vals ve1))
{
  expand_impl params128 ek hk key;
}

fn aes128_encrypt_expanded (out: A.array S8.t) (tag: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (ek: A.array S8.t) (hk: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vt0 #vm0 #ve #vh: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag vt0 ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length ve == 176 /\ Seq.length vh == 128 /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey AES128 (vals ve) /\
  Seq.length viv == SZ.v iv_len /\ Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag vt1 ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vo1 == SZ.v msg_len /\
  Seq.length ve == 176 /\ Seq.length vh == 128 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vo1, vals vt1) == gcm_encrypt_w AES128 (vals ve) (vals viv)
                                        (vals vaad) (vals vm0))
{
  encrypt_w params128 ek hk iv iv_len aad aad_len out msg msg_len tag;
}

fn aes128_decrypt_expanded (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
       (ek: A.array S8.t) (hk: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vm0 #ve #vh: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag #pt vtag ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length ve == 176 /\ Seq.length vh == 128 /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey AES128 (vals ve) /\
  Seq.length viv == SZ.v iv_len /\ Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag #pt vtag ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vo1 == SZ.v msg_len /\ Seq.length vtag == 16 /\
  Seq.length ve == 176 /\ Seq.length vh == 128 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt_w AES128 (vals ve) (vals viv) (vals vaad)
                         (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vo1 == Some?.v d) /\
   ((~r) ==> None? d /\ vo1 == reveal vo0)))
{
  decrypt_w params128 ek hk iv iv_len aad aad_len out msg msg_len tag
}

fn aes256_expand (ek: A.array S8.t) (hk: A.array S8.t) (key: A.array S8.t)
       (#ve0 #vh0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to ek ve0 ** A.pts_to hk vh0 ** A.pts_to key #pk vkey ** pure (
  Seq.length ve0 == 240 /\ Seq.length vh0 == 128 /\ Seq.length vkey == 32)
ensures exists* (ve1 vh1: Seq.seq S8.t).
  A.pts_to ek ve1 ** A.pts_to hk vh1 ** A.pts_to key #pk vkey ** pure (
  Seq.length ve1 == 240 /\ Seq.length vh1 == 128 /\ Seq.length vkey == 32 /\
  vals ve1 == key_expansion AES256 (vals vkey) /\
  Alg.pows_ok (vals vh1) /\ Poly.xtimes (Alg.hblk (vals vh1) 0) == hkey AES256 (vals ve1))
{
  expand_impl params256 ek hk key;
}

fn aes256_encrypt_expanded (out: A.array S8.t) (tag: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (ek: A.array S8.t) (hk: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vt0 #vm0 #ve #vh: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag vt0 ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length ve == 240 /\ Seq.length vh == 128 /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey AES256 (vals ve) /\
  Seq.length viv == SZ.v iv_len /\ Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag vt1 ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vo1 == SZ.v msg_len /\
  Seq.length ve == 240 /\ Seq.length vh == 128 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vo1, vals vt1) == gcm_encrypt_w AES256 (vals ve) (vals viv)
                                        (vals vaad) (vals vm0))
{
  encrypt_w params256 ek hk iv iv_len aad aad_len out msg msg_len tag;
}

fn aes256_decrypt_expanded (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
       (ek: A.array S8.t) (hk: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#pm: perm) (#vo0 #vm0 #ve #vh: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires IO.inout out msg pm 0 vo0 vm0 ** A.pts_to tag #pt vtag ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vo0 == SZ.v msg_len /\
  Seq.length ve == 240 /\ Seq.length vh == 128 /\
  Alg.pows_ok (vals vh) /\ Poly.xtimes (Alg.hblk (vals vh) 0) == hkey AES256 (vals ve) /\
  Seq.length viv == SZ.v iv_len /\ Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vo1: Seq.seq S8.t).
  IO.inout out msg pm (SZ.v msg_len) vo1 vm0 ** A.pts_to tag #pt vtag ** A.pts_to ek ve **
  A.pts_to hk vh ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vo1 == SZ.v msg_len /\ Seq.length vtag == 16 /\
  Seq.length ve == 240 /\ Seq.length vh == 128 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt_w AES256 (vals ve) (vals viv) (vals vaad)
                         (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vo1 == Some?.v d) /\
   ((~r) ==> None? d /\ vo1 == reveal vo0)))
{
  decrypt_w params256 ek hk iv iv_len aad aad_len out msg msg_len tag
}

#pop-options
