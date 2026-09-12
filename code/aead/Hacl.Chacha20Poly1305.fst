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

(** ChaCha20-Poly1305, RFC 8439 section 2.8.

    The one-time Poly1305 key is the first half of the ChaCha20 block at
    counter zero, and it is obtained here by encrypting thirty-two zero bytes
    -- the same bytes, and no keystream function to export separately.  The
    message is encrypted at counter one.

    The tag is computed with the three-segment loop rather than with the
    plain MAC, because the authenticated input is a concatenation whose
    segments are padded to block boundaries with zeros: a segment's final
    block is a full block with a zero tail, not Poly1305's one-bit-padded
    short block, so the pieces cannot be handed to [poly1305_mac] one at a
    time.  [Hacl.Poly1305.absorb_seg] is exactly one such segment, and
    [Spec.Chacha20Poly1305.mac_input_acc] is the proof that three of them
    authenticate the concatenation.

    Decryption verifies before it decrypts.  The comparison is
    [S8.eq_mask] over the sixteen bytes, folded with [logand], and the
    single bit that comes out is the only thing declassified. *)
module Hacl.Chacha20Poly1305

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Bytes
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Impl.Bytes
open Spec.Poly1305.Field
open Hacl.Poly1305.Field
open Hacl.Poly1305.Load
open Hacl.Poly1305.Reduce
open Hacl.Poly1305

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module D = Hacl.Secret.Declassify
module C = Spec.Chacha20
module P = Spec.Poly1305
module Spec = Spec.Chacha20Poly1305

(** {2 The length block}

    Two little-endian sixty-four bit lengths.  [of_sizet_lo] truncates to
    sixty-four bits, which is what the specification says too: a length that
    did not fit would be authenticated modulo [2^64], and no platform this
    compiles on has a [size_t] that wide. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let len_block_bytes (la lc: nat) (b: Seq.seq S8.t)
  : Lemma
      (requires
        Seq.length b == 16 /\
        (forall (k: nat). k < 8 ==>
           S8.v (Seq.index b k) == ((la % pow2 64) / pow2 (8 * k)) % 256) /\
        (forall (k: nat). k < 8 ==>
           S8.v (Seq.index b (8 + k)) == ((lc % pow2 64) / pow2 (8 * k)) % 256))
      (ensures b == Spec.len_block la lc)
  = let l = Spec.len_block la lc in
    let aux (i: nat { i < 16 }) : Lemma (Seq.index b i == Seq.index l i)
      = if i < 8 then nat_to_le_index 8 (la % pow2 64) i
                 else nat_to_le_index 8 (lc % pow2 64) (i - 8)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro b l;
    Seq.lemma_eq_elim b l

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

fn write_len_block (lb: A.array S8.t) (la: SZ.t) (lc: SZ.t)
                   (#vlb: erased (Seq.seq S8.t))
requires A.pts_to lb vlb ** pure (Seq.length vlb == 16)
ensures exists* (vlb': Seq.seq S8.t).
  A.pts_to lb vlb' ** pure (vlb' == Spec.len_block (SZ.v la) (SZ.v lc))
{
  A.pts_to_len lb;
  let wa: S64.t = of_sizet_lo #S64.t la;
  let wc: S64.t = of_sizet_lo #S64.t lc;
  store_le #S64.t lb 0sz wa;
  with v1. assert (A.pts_to lb v1);
  store_le #S64.t lb 8sz wc;
  with v'. assert (A.pts_to lb v');
  Math.lemma_mod_twice (SZ.v la) (pow2 64);
  Math.lemma_mod_twice (SZ.v lc) (pow2 64);
  assert_norm (bytes #S64.t == 8);
  assert (pure (forall (k: nat). k < 8 ==>
            S8.v (Seq.index v' k) == ((SZ.v la % pow2 64) / pow2 (8 * k)) % 256));
  assert (pure (forall (k: nat). k < 8 ==>
            S8.v (Seq.index v' (8 + k)) == ((SZ.v lc % pow2 64) / pow2 (8 * k)) % 256));
  len_block_bytes (SZ.v la) (SZ.v lc) v';
  assert (pure (v' == Spec.len_block (SZ.v la) (SZ.v lc)));
}

#pop-options

(** {2 The tag}

    Three segments: the additional data, the ciphertext, and the sixteen-byte
    length block, which is already a whole block and so passes through
    [absorb_seg] unpadded. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn aead_tag (tag: A.array S8.t) (aad: A.array S8.t) (alen: SZ.t) (ct: A.array S8.t) (clen: SZ.t)
            (key: A.array S8.t)
            (#vtag: erased (Seq.seq S8.t))
            (#pa: perm) (#vaad: erased (Seq.seq S8.t))
            (#pc: perm) (#vct: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to tag vtag ** A.pts_to aad #pa vaad ** A.pts_to ct #pc vct **
         A.pts_to key #pk vkey **
         pure (Seq.length vtag == 16 /\ Seq.length vkey == 32)
         ** pure (SZ.v alen == Seq.length vaad)
         ** pure (SZ.v clen == Seq.length vct)
ensures exists* (vtag': Seq.seq S8.t).
  A.pts_to tag vtag' ** A.pts_to aad #pa vaad ** A.pts_to ct #pc vct **
  A.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vtag' == 16 /\
        vtag' == P.poly1305 (Spec.mac_input vaad vct) vkey)
{
  A.pts_to_len tag;
  A.pts_to_len aad;
  A.pts_to_len ct;
  A.pts_to_len key;

  let z = S64.zero;
  let z8 = S8.classify 0uy;
  let mut rarr = [| z; 5sz |];
  A.pts_to_len rarr;
  A.pts_to_len rarr;
  let mut harr = [| z; 5sz |];
  A.pts_to_len harr;
  A.pts_to_len harr;
  let mut earr = [| z; 5sz |];
  A.pts_to_len earr;
  A.pts_to_len earr;
  let mut darr = [| z; 5sz |];
  A.pts_to_len darr;
  A.pts_to_len darr;
  let mut lbarr = [| z8; 16sz |];
  A.pts_to_len lbarr;
  A.pts_to_len lbarr;

  write_len_block lbarr alen clen;

  load_r rarr key;
  set_zero harr;
  with vr. assert (A.pts_to rarr vr);
  Math.pow2_lt_compat 27 26;

  absorb_seg harr rarr darr earr aad alen #_ #_ #_ #_ #_ #_ #(hide 0);
  absorb_seg harr rarr darr earr ct clen
    #_ #_ #_ #_ #_ #_ #(hide (P.seg_acc vaad (feval vr) 0));
  absorb_seg harr rarr darr earr lbarr 16sz
    #_ #_ #_ #_ #_ #_
    #(hide (P.seg_acc vct (feval vr) (P.seg_acc vaad (feval vr) 0)));

  reduce harr;
  Spec.mac_input_acc vaad vct (feval vr);
  store_tag tag harr key;

  ()
}

#pop-options

(** {2 Encryption} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn derive_otk (otk: A.array S8.t) (key: A.array S8.t) (nonce: A.array S8.t)
              (#vo: erased (Seq.seq S8.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to otk vo ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vo == 32 /\ Seq.length vkey == 32 /\
               Seq.length vnon == 12)
ensures exists* (vo': Seq.seq S8.t).
  A.pts_to otk vo' ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vo' == 32 /\ vo' == Spec.otk vkey vnon)
{
  A.pts_to_len otk;
  let z8 = S8.classify 0uy;
  let mut zarr = [| z8; 32sz |];
  A.pts_to_len zarr;
  A.pts_to_len zarr;
  assert (pure (Seq.equal (Seq.create 32 (S8.classify 0uy)) (P.zeros 32)));
  Hacl.Chacha20.encrypt otk zarr 32sz key nonce 0ul;
  Spec.otk_is_encrypt vkey vnon;
  ()
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn encrypt (ct: A.array S8.t) (tag: A.array S8.t)
           (msg: A.array S8.t) (mlen: SZ.t) (aad: A.array S8.t) (alen: SZ.t)
           (key: A.array S8.t) (nonce: A.array S8.t)
           (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
           (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to ct vct ** A.pts_to tag vtag ** A.pts_to msg #pm vmsg **
         A.pts_to aad #pa vaad ** A.pts_to key #pk vkey **
         A.pts_to nonce #pn vnon **
         pure (Seq.length vct == Seq.length vmsg /\ Seq.length vtag == 16 /\
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               Seq.length vmsg <= C.max_len 1ul)
         ** pure (SZ.v mlen == Seq.length vmsg)
         ** pure (SZ.v alen == Seq.length vaad)
ensures exists* (vct': Seq.seq S8.t) (vtag': Seq.seq S8.t).
  A.pts_to ct vct' ** A.pts_to tag vtag' ** A.pts_to msg #pm vmsg **
  A.pts_to aad #pa vaad ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vmsg <= C.max_len 1ul /\
        Seq.length vct' == Seq.length vmsg /\ Seq.length vtag' == 16 /\
        (vct', vtag') == Spec.encrypt vkey vnon vaad vmsg)
{
  A.pts_to_len ct;
  A.pts_to_len tag;
  A.pts_to_len msg;
  A.pts_to_len key;
  A.pts_to_len nonce;

  let z8 = S8.classify 0uy;
  let mut karr = [| z8; 32sz |];
  A.pts_to_len karr;
  A.pts_to_len karr;

  derive_otk karr key nonce;
  Hacl.Chacha20.encrypt ct msg mlen key nonce 1ul;
  aead_tag tag aad alen ct mlen karr;

  ()
}

#pop-options

(** {2 The tag comparison}

    Sixteen [eq_mask]s folded with [logand]: all-ones exactly when every byte
    agrees, and the loop's shape does not depend on where a mismatch is.  The
    resulting bit is the answer the caller asked for, so it is declassified
    here and nowhere else. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn tag_eq (a: A.array S8.t) (b: A.array S8.t)
          (#pa: perm) (#va: erased (Seq.seq S8.t))
          (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length va == 16 /\ Seq.length vb == 16)
returns res: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length va == 16 /\ Seq.length vb == 16 /\
              (res <==> Seq.equal va vb))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut acc = S8.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (m: S8.t).
    pts_to i vi ** pts_to acc m ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length va == 16 /\ Seq.length vb == 16 /\
          (S8.v m == 0 \/ S8.v m == pow2 8 - 1) /\
          (S8.v m == pow2 8 - 1 <==>
           (forall (k: nat). k < SZ.v vi ==>
              S8.v (Seq.index va k) == S8.v (Seq.index vb k))))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let m = !acc;
    let eq = S8.eq_mask x y;
    let m' = S8.logand m eq;
    UInt.logand_lemma_1 #8 (S8.v m);
    UInt.logand_lemma_2 #8 (S8.v m);
    UInt.logand_commutative #8 (S8.v m) (S8.v eq);
    UInt.logand_lemma_1 #8 (S8.v eq);
    UInt.logand_lemma_2 #8 (S8.v eq);
    acc := m';
    i := SZ.add vi 1sz;
  };
  let m = !acc;
  D.bool_of_mask m
}

#pop-options

(** {2 Decryption}

    Nothing is written to [msg] unless the tag is right. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn decrypt (msg: A.array S8.t) (ct: A.array S8.t) (clen: SZ.t) (tag: A.array S8.t)
           (aad: A.array S8.t) (alen: SZ.t) (key: A.array S8.t) (nonce: A.array S8.t)
           (#vmsg: erased (Seq.seq S8.t))
           (#pc: perm) (#vct: erased (Seq.seq S8.t))
           (#pt: perm) (#vtag: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to msg vmsg ** A.pts_to ct #pc vct ** A.pts_to tag #pt vtag **
         A.pts_to aad #pa vaad ** A.pts_to key #pk vkey **
         A.pts_to nonce #pn vnon **
         pure (Seq.length vmsg == Seq.length vct /\ Seq.length vtag == 16 /\
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               Seq.length vct <= C.max_len 1ul)
         ** pure (SZ.v clen == Seq.length vct)
         ** pure (SZ.v alen == Seq.length vaad)
returns res: bool
ensures exists* (vmsg': Seq.seq S8.t).
  A.pts_to msg vmsg' ** A.pts_to ct #pc vct ** A.pts_to tag #pt vtag **
  A.pts_to aad #pa vaad ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vtag == 16 /\
        Seq.length vct <= C.max_len 1ul /\
        Seq.length vmsg' == Seq.length vct /\
        (res <==> Spec.decrypt_ok vkey vnon vaad vct vtag) /\
        (if res then vmsg' == Spec.decrypted vkey vnon vct else vmsg' == vmsg))
{
  A.pts_to_len msg;
  A.pts_to_len ct;
  A.pts_to_len tag;
  A.pts_to_len key;
  A.pts_to_len nonce;

  let z8 = S8.classify 0uy;
  let mut karr = [| z8; 32sz |];
  A.pts_to_len karr;
  A.pts_to_len karr;
  let mut tarr = [| z8; 16sz |];
  A.pts_to_len tarr;
  A.pts_to_len tarr;

  derive_otk karr key nonce;
  aead_tag tarr aad alen ct clen karr;
  let ok = tag_eq tarr tag;

  if ok {
    Hacl.Chacha20.encrypt msg ct clen key nonce 1ul;
    true
  } else {
    false
  }
}

#pop-options
