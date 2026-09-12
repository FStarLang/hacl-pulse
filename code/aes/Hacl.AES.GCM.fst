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

    Encryption is in place: the plaintext buffer comes back holding the
    ciphertext, and the tag is written to a separate sixteen bytes.
    Decryption is in place too, but only on success -- a wrong tag leaves the
    buffer exactly as it was, so a caller that ignores the returned boolean
    still never sees forged plaintext, and the type of [Spec.GCM.gcm_decrypt]
    says so.

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
open Hacl.AES.CTR

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module G = Spec.GF128
module Copy = Hacl.Impl.Copy
module Bytes = Hacl.Impl.Bytes
module Declassify = Hacl.Secret.Declassify

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

(** [hb := hkey], the encryption of the zero block. *)

fn hkey_impl ([@@@FStar.Attributes.monomorphize] p: params)
             (hb: S.slice S8.t) (w: S.slice S8.t)
             (#vh0 #vw: erased (Seq.seq S8.t))
requires S.pts_to hb vh0 ** S.pts_to w vw ** pure (
  Seq.length vh0 == blocklen /\ Seq.length vw == xkeylen p.pv)
ensures exists* (vh1: Seq.seq S8.t). S.pts_to hb vh1 ** S.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh1 == blocklen /\
  vals vh1 == hkey p.pv (vals vw))
{
  S.pts_to_len hb;
  Copy.fill hb S8.zero 16sz;
  with vz. assert S.pts_to hb vz;
  zeroed vz;
  cipher_impl p hb w;
}

(** The length block: the two lengths in bits, big end first. *)

fn put_lenblock (lb: S.slice S8.t) (la lc: SZ.t) (#v0: erased (Seq.seq S8.t))
requires S.pts_to lb v0 ** pure (
  Seq.length v0 == blocklen /\ 8 * SZ.v la < pow2 64 /\ 8 * SZ.v lc < pow2 64)
ensures exists* (v1: Seq.seq S8.t). S.pts_to lb v1 ** pure (
  Seq.length v1 == blocklen /\
  8 * SZ.v la < pow2 64 /\ 8 * SZ.v lc < pow2 64 /\
  vals v1 == Seq.append (u64be (8 * SZ.v la)) (u64be (8 * SZ.v lc)))
{
  S.pts_to_len lb;
  Math.modulo_lemma (SZ.v la) (pow2 64);
  Math.modulo_lemma (SZ.v lc) (pow2 64);
  let x = S64.classify (U64.mul (SZ.sizet_to_uint64 la) 8uL);
  let y = S64.classify (U64.mul (SZ.sizet_to_uint64 lc) 8uL);
  Bytes.store_be #S64.t lb 0sz x;
  Bytes.store_be #S64.t lb 8sz y;
  with v1. assert S.pts_to lb v1;
  lenblock_eq v1 (8 * SZ.v la) (8 * SZ.v lc);
  S.pts_to_len lb;
}

(** The pre-counter block.  Twelve bytes of nonce and a counter of one, or a
    GHASH of the padded nonce and its length. *)

fn j0_impl ([@@@FStar.Attributes.monomorphize] p: params)
           (jb: S.slice S8.t) (w: S.slice S8.t) (hb: S.slice S8.t)
           (iv: S.slice S8.t)
           (#vj0 #vw #vh: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
requires S.pts_to jb vj0 ** S.pts_to w vw ** S.pts_to hb vh **
         S.pts_to iv #pi viv ** pure (
  Seq.length vj0 == blocklen /\ Seq.length vw == xkeylen p.pv /\
  Seq.length vh == blocklen /\ vals vh == hkey p.pv (vals vw) /\
  iv_ok (vals viv) /\ SZ.fits (Seq.length viv + blocklen))
ensures exists* (vj1: Seq.seq S8.t).
  S.pts_to jb vj1 ** S.pts_to w vw ** S.pts_to hb vh **
  S.pts_to iv #pi viv ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == blocklen /\
  Seq.length vj1 == blocklen /\ iv_ok (vals viv) /\
  vals vj1 == j0 p.pv (vals vw) (vals viv))
{
  S.pts_to_len jb;
  S.pts_to_len hb;
  S.pts_to_len iv;
  let n = S.len iv;
  let z = S8.zero;
  let mut lbarr = [| z; 16sz |];
  A.pts_to_len lbarr;
  let lb = S.from_array lbarr 16sz;
  S.pts_to_len lb;

  if (n = 12sz) {
    Copy.copy_range jb 0sz iv 0sz 12sz;
    let one = S8.classify 1uy;
    S.((jb.(12sz) <- z));
    S.((jb.(13sz) <- z));
    S.((jb.(14sz) <- z));
    S.((jb.(15sz) <- one));
    with vj1. assert S.pts_to jb vj1;
    Seq.lemma_eq_intro (vals vj1)
      (Seq.append (vals viv) (Seq.init 4 (fun i -> (if i = 3 then 1 else 0) <: elem)));
    S.to_array lb;
  } else {
    Copy.fill jb S8.zero 16sz;
    with vz. assert S.pts_to jb vz;
    zeroed vz;
    ghash_upd_impl jb hb iv;
    bits_fit (Seq.length viv);
    put_lenblock lb 0sz n;
    pad_exact (Seq.append (u64be 0) (u64be (8 * Seq.length viv)));
    ghash_upd_impl jb hb lb;
    j0_fold p.pv (vals vw) (vals viv);
    S.to_array lb;
  }
}

(** The tag: the GHASH of the three pieces, masked with the encryption of
    [j0]. *)

fn gtag_impl ([@@@FStar.Attributes.monomorphize] p: params)
             (tag: S.slice S8.t) (w: S.slice S8.t) (hb: S.slice S8.t)
             (jb: S.slice S8.t) (aad: S.slice S8.t) (cip: S.slice S8.t)
             (#vt0 #vw #vh #vj: erased (Seq.seq S8.t))
             (#pa: perm) (#va: erased (Seq.seq S8.t))
             (#pc: perm) (#vc: erased (Seq.seq S8.t))
requires S.pts_to tag vt0 ** S.pts_to w vw ** S.pts_to hb vh **
         S.pts_to jb vj ** S.pts_to aad #pa va ** S.pts_to cip #pc vc ** pure (
  Seq.length vt0 == taglen /\ Seq.length vw == xkeylen p.pv /\
  Seq.length vh == blocklen /\ Seq.length vj == blocklen /\
  vals vh == hkey p.pv (vals vw) /\
  aad_ok (vals va) /\ msg_ok (vals vc) /\
  SZ.fits (Seq.length va + blocklen) /\ SZ.fits (Seq.length vc + blocklen))
ensures exists* (vt1: Seq.seq S8.t).
  S.pts_to tag vt1 ** S.pts_to w vw ** S.pts_to hb vh **
  S.pts_to jb vj ** S.pts_to aad #pa va ** S.pts_to cip #pc vc ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == blocklen /\
  Seq.length vj == blocklen /\ Seq.length vt1 == taglen /\
  aad_ok (vals va) /\ msg_ok (vals vc) /\
  vals vt1 == gtag p.pv (vals vw) (vals vj) (vals va) (vals vc))
{
  S.pts_to_len tag;
  S.pts_to_len hb;
  S.pts_to_len jb;
  S.pts_to_len aad;
  S.pts_to_len cip;

  let z = S8.zero;
  let mut accarr = [| z; 16sz |];
  A.pts_to_len accarr;
  let acc = S.from_array accarr 16sz;
  S.pts_to_len acc;
  let mut lbarr = [| z; 16sz |];
  A.pts_to_len lbarr;
  let lb = S.from_array lbarr 16sz;
  S.pts_to_len lb;

  with vz. assert S.pts_to acc vz;
  zeroed vz;
  ghash_upd_impl acc hb aad;
  ghash_upd_impl acc hb cip;
  bits_fit (Seq.length va);
  msg_bits_fit (Seq.length vc);
  put_lenblock lb (S.len aad) (S.len cip);
  pad_exact (len_block (vals va) (vals vc));
  ghash_upd_impl acc hb lb;

  Copy.copy_exact tag jb 16sz;
  cipher_impl p tag w;
  with vacc. assert S.pts_to acc vacc;
  whole_slice (vals vacc);
  gadd_at_impl tag acc 0sz;
  gtag_fold p.pv (vals vw) (vals vj) (vals va) (vals vc);
  S.to_array acc;
  S.to_array lb;
}

(** {2 The tag comparison}

    Sixteen [eq_mask]s folded with [logand]: every byte is read, the result
    is one mask, and exactly one bit of it becomes public. *)

let mask_and (a b: nat)
  : Lemma (requires (a == 0 \/ a == 255) /\ (b == 0 \/ b == 255))
          (ensures UInt.logand #8 a b == (if a = 255 && b = 255 then 255 else 0))
  = assert_norm (UInt.logand #8 255 255 == 255);
    assert_norm (UInt.logand #8 255 0 == 0);
    assert_norm (UInt.logand #8 0 255 == 0);
    assert_norm (UInt.logand #8 0 0 == 0)

fn tag_match (a: S.slice S8.t) (b: S.slice S8.t)
             (#pa: perm) (#va: erased (Seq.seq S8.t))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires S.pts_to a #pa va ** S.pts_to b #pb vb ** pure (
  Seq.length va == taglen /\ Seq.length vb == taglen)
returns r: bool
ensures S.pts_to a #pa va ** S.pts_to b #pb vb ** pure (
  Seq.length va == taglen /\ Seq.length vb == taglen /\
  r == Seq.equal (vals va) (vals vb))
{
  S.pts_to_len a;
  S.pts_to_len b;
  let mut m = S8.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vm: S8.t).
    pts_to i vi ** pts_to m vm ** S.pts_to a #pa va ** S.pts_to b #pb vb **
    pure (SZ.v vi <= taglen /\ Seq.length va == taglen /\ Seq.length vb == taglen /\
          S8.v vm == (if (forall (j: nat). j < SZ.v vi ==>
                            Seq.index (vals va) j == Seq.index (vals vb) j)
                      then 255 else 0))
  decreases (taglen - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(a.(vi));
    let y = S.(b.(vi));
    let vm = !m;
    let e = S8.eq_mask x y;
    mask_and (S8.v vm) (S8.v e);
    m := S8.logand vm e;
    i := SZ.add vi 1sz;
  };
  let vm = !m;
  let r = Declassify.bool_of_mask vm;
  assert (pure (r == (S8.v vm = 255)));
  S.pts_to_len a;
  r
}

(** {2 The two directions} *)

(** In place: [msg] comes back holding the ciphertext and [tag] the tag. *)

fn encrypt ([@@@FStar.Attributes.monomorphize] p: params)
           (key: S.slice S8.t) (iv: S.slice S8.t) (aad: S.slice S8.t)
           (msg: S.slice S8.t) (tag: S.slice S8.t)
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#vm0 #vt0: erased (Seq.seq S8.t))
requires S.pts_to key #pk vkey ** S.pts_to iv #pi viv ** S.pts_to aad #pa vaad **
         S.pts_to msg vm0 ** S.pts_to tag vt0 ** pure (
  Seq.length vkey == keylen p.pv /\ Seq.length vt0 == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
ensures exists* (vm1 vt1: Seq.seq S8.t).
  S.pts_to key #pk vkey ** S.pts_to iv #pi viv ** S.pts_to aad #pa vaad **
  S.pts_to msg vm1 ** S.pts_to tag vt1 ** pure (
  Seq.length vm1 == Seq.length vm0 /\ Seq.length vt1 == taglen /\
  Seq.length vkey == keylen p.pv /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vm1, vals vt1) ==
    gcm_encrypt p.pv (vals vkey) (vals viv) (vals vaad) (vals vm0))
{
  S.pts_to_len key;
  S.pts_to_len msg;
  S.pts_to_len tag;

  let z = S8.zero;
  let mut warr = [| z; p.pxkeylen |];
  A.pts_to_len warr;
  let w = S.from_array warr p.pxkeylen;
  S.pts_to_len w;
  let mut harr = [| z; 16sz |];
  A.pts_to_len harr;
  let hb = S.from_array harr 16sz;
  S.pts_to_len hb;
  let mut jarr = [| z; 16sz |];
  A.pts_to_len jarr;
  let jb = S.from_array jarr 16sz;
  S.pts_to_len jb;
  let mut carr = [| z; 16sz |];
  A.pts_to_len carr;
  let ctr = S.from_array carr 16sz;
  S.pts_to_len ctr;

  key_expansion_impl p w key;
  hkey_impl p hb w;
  j0_impl p jb w hb iv;
  Copy.copy_exact ctr jb 16sz;
  inc32_impl ctr;
  ctr_encrypt_impl p msg w ctr;
  gtag_impl p tag w hb jb aad msg;

  S.to_array w;
  S.to_array hb;
  S.to_array jb;
  S.to_array ctr;
}

(** In place on success only: a wrong tag leaves [msg] untouched. *)

fn decrypt ([@@@FStar.Attributes.monomorphize] p: params)
           (key: S.slice S8.t) (iv: S.slice S8.t) (aad: S.slice S8.t)
           (msg: S.slice S8.t) (tag: S.slice S8.t)
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pt: perm) (#vtag: erased (Seq.seq S8.t))
           (#vm0: erased (Seq.seq S8.t))
requires S.pts_to key #pk vkey ** S.pts_to iv #pi viv ** S.pts_to aad #pa vaad **
         S.pts_to msg vm0 ** S.pts_to tag #pt vtag ** pure (
  Seq.length vkey == keylen p.pv /\ Seq.length vtag == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
returns r: bool
ensures exists* (vm1: Seq.seq S8.t).
  S.pts_to key #pk vkey ** S.pts_to iv #pi viv ** S.pts_to aad #pa vaad **
  S.pts_to msg vm1 ** S.pts_to tag #pt vtag ** pure (
  Seq.length vm1 == Seq.length vm0 /\
  Seq.length vkey == keylen p.pv /\ Seq.length vtag == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt p.pv (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vm1 == Some?.v d) /\
   ((~r) ==> None? d /\ vm1 == reveal vm0)))
{
  S.pts_to_len key;
  S.pts_to_len msg;
  S.pts_to_len tag;

  let z = S8.zero;
  let mut warr = [| z; p.pxkeylen |];
  A.pts_to_len warr;
  let w = S.from_array warr p.pxkeylen;
  S.pts_to_len w;
  let mut harr = [| z; 16sz |];
  A.pts_to_len harr;
  let hb = S.from_array harr 16sz;
  S.pts_to_len hb;
  let mut jarr = [| z; 16sz |];
  A.pts_to_len jarr;
  let jb = S.from_array jarr 16sz;
  S.pts_to_len jb;
  let mut carr = [| z; 16sz |];
  A.pts_to_len carr;
  let ctr = S.from_array carr 16sz;
  S.pts_to_len ctr;
  let mut tarr = [| z; 16sz |];
  A.pts_to_len tarr;
  let ct = S.from_array tarr 16sz;
  S.pts_to_len ct;

  key_expansion_impl p w key;
  hkey_impl p hb w;
  j0_impl p jb w hb iv;
  gtag_impl p ct w hb jb aad msg;
  let ok = tag_match ct tag;

  if ok {
    Copy.copy_exact ctr jb 16sz;
    inc32_impl ctr;
    ctr_encrypt_impl p msg w ctr;
    S.to_array w; S.to_array hb; S.to_array jb; S.to_array ctr; S.to_array ct;
    true
  } else {
    S.to_array w; S.to_array hb; S.to_array jb; S.to_array ctr; S.to_array ct;
    false
  }
}

#pop-options
