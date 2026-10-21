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

(** HPKE's labelled KDF, RFC 9180 section 4.

    [LabeledExtract] and [LabeledExpand] are HKDF with three or four extra
    strings in front of the input: the version [HPKE-v1], a suite identifier,
    a per-use label, and -- for expand -- the output length.  Each is
    streamed: extract hands the four pieces straight to
    {!Hacl.HMAC.Cat.hmac_cat}, and expand builds the fixed-size prefix (at
    most 41 bytes) in a local buffer and passes it to
    {!Hacl.HKDF.Core.expand2_impl} alongside the caller's string.  Nothing
    of caller-chosen size is ever copied or allocated.

    The suite identifier and the label are arguments rather than constants
    because both KDF stages go through this code: the KEM passes [KEM] and
    its own algorithm identifier, the key schedule passes [HPKE] and all
    three.  The version string is the same for everybody and comes from
    {!Hacl.HPKE.Tables}. *)
module Hacl.HPKE.Labeled

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HPKE
open Hacl.Hash.SHA2.Core
open Hacl.HMAC.Cat
open Hacl.HKDF.Core
open Hacl.HPKE.Tables
open Hacl.Impl.Copy
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module B = Hacl.Spec.Bytes
module Cast = FStar.Int.Cast
module Sub = Hacl.Impl.Sub
module Mem = Hacl.Mem

(** The message is the version, the suite identifier, the label and the
    caller's string, and the first three are bounded by construction.
    Restating the bound as a machine fact once keeps [SZ.fits] obligations out
    of the two functions below. *)
let prefix_bound (#t: Type0) {| word t |} (p: params t) (n: nat)
  : Lemma (requires n < pow2 32)
          (ensures fits p n /\ block_len #t <= 256 /\ hash_bytes p <= 128 /\
                   9 + 16 + 16 + n < pow2 61 /\
                   block_len #t + hash_bytes p + 9 + 16 + 16 + n + 1 < pow2 61 /\
                   block_len #t + hash_bytes p + 9 + 16 + 16 + n + 1 < max_input #t)
  = FStar.Math.Lemmas.pow2_le_compat (8 * len_len #t - 3) 61;
    assert_norm (256 + 128 + 41 + pow2 32 + 1 < pow2 61);
    assert_norm (256 + 128 + pow2 32 + 64 < pow2 61)

(** The HMAC key (the salt) is at most 64 bytes, well under the hash's
    input-length bound. *)
let salt_bound (#t: Type0) {| word t |} (n: nat)
  : Lemma (requires n <= 64)
          (ensures n < pow2 61 /\ n < pow2 (8 * len_len #t - 3))
  = FStar.Math.Lemmas.pow2_le_compat (8 * len_len #t - 3) 61;
    assert_norm (64 < pow2 61)

(** Two pointwise byte equalities give the length-prefix clause of
    [cat5_pointwise]. *)
let two_pointwise (m a: Seq.seq S8.t)
  : Lemma (requires Seq.length a == 2 /\ Seq.length m >= 2 /\
                    Seq.index m 0 == Seq.index a 0 /\ Seq.index m 1 == Seq.index a 1)
          (ensures forall (k: nat). k < Seq.length a ==> Seq.index m k == Seq.index a k)
  = ()

(** The two bytes the code writes for [I2OSP(L, 2)] are [two_bytes L]. *)
let two_bytes_hi_lo (n: nat { n < 65536 }) (l32: U32.t)
  : Lemma (requires U32.v l32 == n % pow2 32)
          (ensures Seq.index (two_bytes n) 0 ==
                     S8.classify (Cast.uint32_to_uint8 (U32.div l32 256ul)) /\
                   Seq.index (two_bytes n) 1 == S8.classify (Cast.uint32_to_uint8 l32))
  = assert_norm (65536 < pow2 32);
    FStar.Math.Lemmas.small_mod n (pow2 32);
    B.nat_to_be_index 2 n 0;
    B.nat_to_be_index 2 n 1;
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 0 == 1);
    S8.v_extensional (Seq.index (two_bytes n) 0)
                     (S8.classify (Cast.uint32_to_uint8 (U32.div l32 256ul)));
    S8.v_extensional (Seq.index (two_bytes n) 1) (S8.classify (Cast.uint32_to_uint8 l32))

(** [hmac_cat] hashes its pieces right-nested; [extract_input] is stated
    left-nested. *)
let extract_assoc (s l m: Seq.seq S8.t)
  : Lemma (Seq.append version (Seq.append s (Seq.append l m)) == extract_input s l m)
  = Seq.lemma_eq_intro (Seq.append version (Seq.append s (Seq.append l m)))
                       (Seq.append (Seq.append (Seq.append version s) l) m)

(** {2 LabeledExtract} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

fn labeled_extract_impl (#t: Type0) {| w: word t |}
                        ([@@@FStar.Attributes.monomorphize] p: params t)
                        (kt: A.array t) (ivt: A.array t)
                        (out: A.array S8.t)
                        (sid: A.array S8.t) (sid_len: SZ.t)
                        (salt: A.array S8.t) (salt_len: SZ.t)
                        (lbl: A.array S8.t) (lbl_len: SZ.t)
                        (ikm: A.array S8.t) (ikm_len: SZ.t)
                        (#pk: perm) (#vk: erased (Seq.seq t))
                        (#pi: perm) (#vi: erased (Seq.seq t))
                        (#vout: erased (Seq.seq S8.t))
                        (#pd: perm) (#vsid: erased (Seq.seq S8.t))
                        (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
                        (#pl: perm) (#vlabel: erased (Seq.seq S8.t))
                        (#pm: perm) (#vikm: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to sid #pd vsid ** A.pts_to salt #ps vsalt **
         A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == hash_bytes p /\
               Seq.length vsid <= 16 /\ Seq.length vsalt <= 64 /\
               Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\
               SZ.fits (block_len #t + 7 + Seq.length vsid + Seq.length vlabel + Seq.length vikm))
         ** pure (SZ.v sid_len == Seq.length vsid)
         ** pure (SZ.v salt_len == Seq.length vsalt)
         ** pure (SZ.v lbl_len == Seq.length vlabel)
         ** pure (SZ.v ikm_len == Seq.length vikm)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to sid #pd vsid ** A.pts_to salt #ps vsalt **
  A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
  pure (Seq.length vsid <= 16 /\ Seq.length vsalt <= 64 /\
        Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\ fits p (Seq.length vikm) /\
        vout' == labeled_extract p vsid vsalt vlabel vikm)
{
  A.pts_to_len out;
  A.pts_to_len sid;
  A.pts_to_len salt;
  A.pts_to_len lbl;
  A.pts_to_len ikm;
  prefix_bound p (Seq.length vikm);

  let vtab = table version_arr 7sz;
  A.pts_to_len vtab;

  hmac_cat p (blocks_scalar p) kt ivt out salt vtab sid lbl ikm salt_len 7sz sid_len lbl_len ikm_len;
  extract_assoc vsid vlabel vikm;
  drop_table vtab;
}

(** {2 LabeledExpand} *)

fn labeled_expand_impl (#t: Type0) {| w: word t |}
                       ([@@@FStar.Attributes.monomorphize] p: params t)
                       (kt: A.array t) (ivt: A.array t)
                       (out: A.array S8.t) (out_len: SZ.t)
                       (prk: A.array S8.t) (prk_len: SZ.t)
                       (sid: A.array S8.t) (sid_len: SZ.t)
                       (lbl: A.array S8.t) (lbl_len: SZ.t)
                       (info: A.array S8.t) (info_len: SZ.t)
                       (#pk: perm) (#vk: erased (Seq.seq t))
                       (#pi: perm) (#vi: erased (Seq.seq t))
                       (#vout: erased (Seq.seq S8.t))
                       (#pp: perm) (#vprk: erased (Seq.seq S8.t))
                       (#pd: perm) (#vsid: erased (Seq.seq S8.t))
                       (#pl: perm) (#vlabel: erased (Seq.seq S8.t))
                       (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to prk #pp vprk ** A.pts_to sid #pd vsid **
         A.pts_to lbl #pl vlabel ** A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vprk <= 64 /\
               Seq.length vsid <= 16 /\ Seq.length vlabel <= 16 /\
               Seq.length vinfo < pow2 32 /\
               Seq.length vout < 65536 /\ Seq.length vout <= 255 * hash_bytes p /\
               SZ.fits (block_len #t + hash_bytes p + 9 + Seq.length vsid + Seq.length vlabel +
                        Seq.length vinfo + 1))
         ** pure (SZ.v out_len == Seq.length vout)
         ** pure (SZ.v prk_len == Seq.length vprk)
         ** pure (SZ.v sid_len == Seq.length vsid)
         ** pure (SZ.v lbl_len == Seq.length vlabel)
         ** pure (SZ.v info_len == Seq.length vinfo)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to prk #pp vprk ** A.pts_to sid #pd vsid **
  A.pts_to lbl #pl vlabel ** A.pts_to info #pf vinfo **
  pure (Seq.length vsid <= 16 /\ Seq.length vlabel <= 16 /\ Seq.length vprk <= 64 /\
        Seq.length vinfo < pow2 32 /\ fits p (Seq.length vinfo) /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' < 65536 /\ Seq.length vout' <= 255 * hash_bytes p /\
        vout' == labeled_expand p vsid vprk vlabel vinfo (Seq.length vout'))
{
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len sid;
  A.pts_to_len lbl;
  A.pts_to_len info;
  prefix_bound p (Seq.length vinfo);
  Hacl.SizeT.fits32 ();

  let vtab = table version_arr 7sz;
  A.pts_to_len vtab;

  let n2 = SZ.add 9sz sid_len;
  let n3 = SZ.add n2 lbl_len;

  (* The prefix [I2OSP(L, 2) || "HPKE-v1" || sid || label] is at most
     2 + 7 + 16 + 16 bytes; only its first [n3] bytes are used. *)
  let z8 = S8.zero;
  let mut buf = [| z8; 41sz |];
  Mem.track buf;
  A.pts_to_len buf;

  (* [I2OSP(L, 2)]: the high byte then the low byte. *)
  let l32 = SZ.sizet_to_uint32 out_len;
  let hi = Cast.uint32_to_uint8 (U32.div l32 256ul);
  let lo = Cast.uint32_to_uint8 l32;
  A.((buf.(0sz) <- S8.classify hi));
  A.((buf.(1sz) <- S8.classify lo));
  with v0. assert (A.pts_to buf v0);
  A.pts_to_len buf;
  assert (pure (Seq.index v0 0 == S8.classify hi /\ Seq.index v0 1 == S8.classify lo));

  copy_at buf 2sz vtab 7sz;
  with v1. assert (A.pts_to buf v1);
  A.pts_to_len buf;
  assert (pure (Seq.index v1 0 == Seq.index v0 0 /\ Seq.index v1 1 == Seq.index v0 1));
  copy_at buf 9sz sid sid_len;
  with v2. assert (A.pts_to buf v2);
  A.pts_to_len buf;
  assert (pure (Seq.index v2 0 == Seq.index v1 0 /\ Seq.index v2 1 == Seq.index v1 1));
  copy_at buf n2 lbl lbl_len;

  with vbuf. assert (A.pts_to buf vbuf);
  B.nat_to_be_index 2 (SZ.v out_len) 0;
  B.nat_to_be_index 2 (SZ.v out_len) 1;
  let pre = Sub.sub buf 0sz n3;
  with vpre. assert (A.pts_to pre vpre);
  assert (pure (Seq.index vpre 0 == Seq.index (two_bytes (SZ.v out_len)) 0));
  assert (pure (Seq.index vpre 1 == Seq.index (two_bytes (SZ.v out_len)) 1));
  cat4_pointwise vpre (two_bytes (SZ.v out_len)) version vsid vlabel;
  Seq.lemma_eq_intro (Seq.append (reveal vpre) (reveal vinfo))
                     (expand_input (SZ.v out_len) vsid vlabel vinfo);

  expand2_impl p (blocks_scalar p) kt ivt out out_len prk prk_len pre n3 info info_len;
  Sub.unsub_id buf 0 (SZ.v n3) pre;
  Mem.wipe buf 41sz;
  drop_table vtab;
}

#pop-options

(** {2 LabeledExtract with no salt}

    Three of the four uses of [LabeledExtract] pass an empty salt, and an
    empty array is not something a caller can conveniently produce: a
    zero-length stack allocation is not a thing C wants to see.  One byte is
    allocated and a zero-length window taken of it, which costs a stack slot
    and no instructions. *)

module Sub = Hacl.Impl.Sub

fn labeled_extract_nosalt (#t: Type0) {| w: word t |}
                          ([@@@FStar.Attributes.monomorphize] p: params t)
                          (kt: A.array t) (ivt: A.array t)
                          (out: A.array S8.t)
                          (sid: A.array S8.t) (sid_len: SZ.t)
                          (lbl: A.array S8.t) (lbl_len: SZ.t)
                          (ikm: A.array S8.t) (ikm_len: SZ.t)
                          (#pk: perm) (#vk: erased (Seq.seq t))
                          (#pi: perm) (#vi: erased (Seq.seq t))
                          (#vout: erased (Seq.seq S8.t))
                          (#pd: perm) (#vsid: erased (Seq.seq S8.t))
                          (#pl: perm) (#vlabel: erased (Seq.seq S8.t))
                          (#pm: perm) (#vikm: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to sid #pd vsid ** A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == hash_bytes p /\
               Seq.length vsid <= 16 /\
               Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\
               SZ.fits (block_len #t + 7 + Seq.length vsid + Seq.length vlabel + Seq.length vikm))
         ** pure (SZ.v sid_len == Seq.length vsid)
         ** pure (SZ.v lbl_len == Seq.length vlabel)
         ** pure (SZ.v ikm_len == Seq.length vikm)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to sid #pd vsid ** A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
  pure (Seq.length vsid <= 16 /\
        Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\ fits p (Seq.length vikm) /\
        vout' == labeled_extract p vsid Seq.empty vlabel vikm)
{
  prefix_bound p (Seq.length vikm);
  let z8 = S8.zero;
  let mut one = [| z8; 1sz |];
  Mem.track one;
  A.pts_to_len one;
  with vone. assert (A.pts_to one vone);
  let nil = Sub.sub one 0sz 0sz;
  with vnil. assert (A.pts_to nil vnil);
  A.pts_to_len nil;
  Seq.lemma_eq_elim (reveal vnil) (Seq.empty #S8.t);
  labeled_extract_impl p kt ivt out sid sid_len nil 0sz lbl lbl_len ikm ikm_len;
  Sub.unsub_id one 0 0 nil;
  Mem.wipe one 1sz;
}
