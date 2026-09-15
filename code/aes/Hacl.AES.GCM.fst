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
open Hacl.AES.Block
open Hacl.AES.CTR

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
             (hb: A.array S8.t) (w: A.array S8.t)
             (#vh0 #vw: erased (Seq.seq S8.t))
requires A.pts_to hb vh0 ** A.pts_to w vw ** pure (
  Seq.length vh0 == blocklen /\ Seq.length vw == xkeylen p.pv)
ensures exists* (vh1: Seq.seq S8.t). A.pts_to hb vh1 ** A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh1 == blocklen /\
  vals vh1 == hkey p.pv (vals vw))
{
  A.pts_to_len hb;
  Copy.fill hb S8.zero 16sz;
  with vz. assert A.pts_to hb vz;
  zeroed vz;
  cipher_impl p hb w;
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
  let x = S64.classify (U64.mul (SZ.sizet_to_uint64 la) 8uL);
  let y = S64.classify (U64.mul (SZ.sizet_to_uint64 lc) 8uL);
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
  Seq.length vh == blocklen /\ vals vh == hkey p.pv (vals vw) /\
  iv_ok (vals viv) /\ SZ.fits (Seq.length viv + blocklen))
         ** pure (SZ.v n == Seq.length viv)
ensures exists* (vj1: Seq.seq S8.t).
  A.pts_to jb vj1 ** A.pts_to w vw ** A.pts_to hb vh **
  A.pts_to iv #pi viv ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == blocklen /\
  Seq.length vj1 == blocklen /\ iv_ok (vals viv) /\
  vals vj1 == j0 p.pv (vals vw) (vals viv))
{
  A.pts_to_len jb;
  A.pts_to_len hb;
  A.pts_to_len iv;
  let z = S8.zero;
  let mut lbarr = [| z; 16sz |];
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
  Seq.length vh == blocklen /\ Seq.length vj == blocklen /\
  vals vh == hkey p.pv (vals vw) /\
  aad_ok (vals va) /\ msg_ok (vals vc) /\
  SZ.fits (Seq.length va + blocklen) /\ SZ.fits (Seq.length vc + blocklen))
         ** pure (SZ.v alen == Seq.length va)
         ** pure (SZ.v clen == Seq.length vc)
ensures exists* (vt1: Seq.seq S8.t).
  A.pts_to tag vt1 ** A.pts_to w vw ** A.pts_to hb vh **
  A.pts_to jb vj ** A.pts_to aad #pa va ** A.pts_to cip #pc vc ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == blocklen /\
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
  A.pts_to_len accarr;
  A.pts_to_len accarr;
  let mut lbarr = [| z; 16sz |];
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
  ()
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

(** {2 The two directions} *)

(** In place: [msg] comes back holding the ciphertext and [tag] the tag. *)

fn encrypt ([@@@FStar.Attributes.monomorphize] p: params)
           (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t) (aad: A.array S8.t) (aad_len: SZ.t)
           (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#vm0 #vt0: erased (Seq.seq S8.t))
requires A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
         A.pts_to msg vm0 ** A.pts_to tag vt0 ** pure (
  Seq.length vkey == keylen p.pv /\ Seq.length vt0 == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v iv_len == Seq.length viv)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v msg_len == Seq.length vm0)
ensures exists* (vm1 vt1: Seq.seq S8.t).
  A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
  A.pts_to msg vm1 ** A.pts_to tag vt1 ** pure (
  Seq.length vm1 == Seq.length vm0 /\ Seq.length vt1 == taglen /\
  Seq.length vkey == keylen p.pv /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vm1, vals vt1) ==
    gcm_encrypt p.pv (vals vkey) (vals viv) (vals vaad) (vals vm0))
{
  A.pts_to_len key;
  A.pts_to_len msg;
  A.pts_to_len tag;

  let z = S8.zero;
  let mut warr = [| z; p.pxkeylen |];
  A.pts_to_len warr;
  A.pts_to_len warr;
  let mut harr = [| z; 16sz |];
  A.pts_to_len harr;
  A.pts_to_len harr;
  let mut jarr = [| z; 16sz |];
  A.pts_to_len jarr;
  A.pts_to_len jarr;
  let mut carr = [| z; 16sz |];
  A.pts_to_len carr;
  A.pts_to_len carr;

  key_expansion_impl p warr key;
  hkey_impl p harr warr;
  j0_impl p jarr warr harr iv iv_len;
  Copy.copy_exact carr jarr 16sz;
  inc32_impl carr;
  ctr_encrypt_impl p msg msg_len warr carr;
  gtag_impl p tag warr harr jarr aad aad_len msg msg_len;

  ()
}

(** In place on success only: a wrong tag leaves [msg] untouched. *)

fn decrypt ([@@@FStar.Attributes.monomorphize] p: params)
           (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t) (aad: A.array S8.t) (aad_len: SZ.t)
           (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pi: perm) (#viv: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pt: perm) (#vtag: erased (Seq.seq S8.t))
           (#vm0: erased (Seq.seq S8.t))
requires A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
         A.pts_to msg vm0 ** A.pts_to tag #pt vtag ** pure (
  Seq.length vkey == keylen p.pv /\ Seq.length vtag == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (Seq.length viv + blocklen) /\ SZ.fits (Seq.length vaad + blocklen) /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v iv_len == Seq.length viv)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v msg_len == Seq.length vm0)
returns r: bool
ensures exists* (vm1: Seq.seq S8.t).
  A.pts_to key #pk vkey ** A.pts_to iv #pi viv ** A.pts_to aad #pa vaad **
  A.pts_to msg vm1 ** A.pts_to tag #pt vtag ** pure (
  Seq.length vm1 == Seq.length vm0 /\
  Seq.length vkey == keylen p.pv /\ Seq.length vtag == taglen /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt p.pv (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vm1 == Some?.v d) /\
   ((~r) ==> None? d /\ vm1 == reveal vm0)))
{
  A.pts_to_len key;
  A.pts_to_len msg;
  A.pts_to_len tag;

  let z = S8.zero;
  let mut warr = [| z; p.pxkeylen |];
  A.pts_to_len warr;
  A.pts_to_len warr;
  let mut harr = [| z; 16sz |];
  A.pts_to_len harr;
  A.pts_to_len harr;
  let mut jarr = [| z; 16sz |];
  A.pts_to_len jarr;
  A.pts_to_len jarr;
  let mut carr = [| z; 16sz |];
  A.pts_to_len carr;
  A.pts_to_len carr;
  let mut tarr = [| z; 16sz |];
  A.pts_to_len tarr;
  A.pts_to_len tarr;

  key_expansion_impl p warr key;
  hkey_impl p harr warr;
  j0_impl p jarr warr harr iv iv_len;
  gtag_impl p tarr warr harr jarr aad aad_len msg msg_len;
  let ok = tag_match tarr tag;

  if ok {
    Copy.copy_exact carr jarr 16sz;
    inc32_impl carr;
    ctr_encrypt_impl p msg msg_len warr carr;
    true
  } else {
    false
  }
}

#pop-options

(** {2 The two key sizes}

    [encrypt] and [decrypt] are generic in the key schedule; these fix it, and
    are what the C header exports:

      void Hacl_AES_GCM_aes128_encrypt(uint8_t *tag, uint8_t *msg, size_t msg_len,
                                       uint8_t *key, uint8_t *iv, size_t iv_len,
                                       uint8_t *aad, size_t aad_len); *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

fn aes128_encrypt (tag: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#vt0 #vm0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires A.pts_to tag vt0 ** A.pts_to msg vm0 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vm1: Seq.seq S8.t).
  A.pts_to tag vt1 ** A.pts_to msg vm1 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vm1 == SZ.v msg_len /\
  Seq.length vkey == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vm1, vals vt1) == gcm_encrypt AES128 (vals vkey) (vals viv)
                                      (vals vaad) (vals vm0))
{
  encrypt params128 key iv iv_len aad aad_len msg msg_len tag;
}

fn aes128_decrypt (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#vm0: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires A.pts_to msg vm0 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vm1: Seq.seq S8.t).
  A.pts_to msg vm1 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vm1 == SZ.v msg_len /\ Seq.length vkey == 16 /\
  Seq.length vtag == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt AES128 (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vm1 == Some?.v d) /\
   ((~r) ==> None? d /\ vm1 == reveal vm0)))
{
  decrypt params128 key iv iv_len aad aad_len msg msg_len tag
}

fn aes256_encrypt (tag: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#vt0 #vm0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires A.pts_to tag vt0 ** A.pts_to msg vm0 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vm1: Seq.seq S8.t).
  A.pts_to tag vt1 ** A.pts_to msg vm1 ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vm1 == SZ.v msg_len /\
  Seq.length vkey == 32 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vm1, vals vt1) == gcm_encrypt AES256 (vals vkey) (vals viv)
                                      (vals vaad) (vals vm0))
{
  encrypt params256 key iv iv_len aad aad_len msg msg_len tag;
}

fn aes256_decrypt (msg: A.array S8.t) (msg_len: SZ.t) (tag: A.array S8.t)
       (key: A.array S8.t) (iv: A.array S8.t) (iv_len: SZ.t)
       (aad: A.array S8.t) (aad_len: SZ.t)
       (#vm0: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires A.pts_to msg vm0 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vm1: Seq.seq S8.t).
  A.pts_to msg vm1 ** A.pts_to tag #pt vtag ** A.pts_to key #pk vkey **
  A.pts_to iv #pi viv ** A.pts_to aad #pa vaad ** pure (
  Seq.length vm1 == SZ.v msg_len /\ Seq.length vkey == 32 /\
  Seq.length vtag == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt AES256 (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vm1 == Some?.v d) /\
   ((~r) ==> None? d /\ vm1 == reveal vm0)))
{
  decrypt params256 key iv iv_len aad aad_len msg msg_len tag
}

#pop-options
