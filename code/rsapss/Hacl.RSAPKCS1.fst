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

(** RSASSA-PKCS1-v1_5, RFC 8017 section 8.2.

    Signing is the encoding {!Spec.RSAPKCS1.pkcs1_encode} followed by
    {!Hacl.RSAPSS.rsa_exp} under the private exponent, with the
    constant-time ladder.  Its postcondition says exactly when it fails, so
    {!Spec.RSAPKCS1.Correctness} can show that a valid key always signs, and
    that what it signs verifies.

    Verification is the RSA function under the public exponent, then a
    comparison against the encoding {!Spec.RSAPKCS1.pkcs1_encode} built
    afresh from the message.  Nothing in the recovered encoded message is
    parsed: the verifier never looks for the end of the padding or reads a
    length out of the DigestInfo, so there is nothing for a forged signature
    to steer.

    The calling convention is {!Hacl.RSAPSS}'s, without the salt: the
    modulus and the public exponent are big-endian byte strings, the modulus
    [ceil(modBits/8)] bytes long, and nothing about the key is trusted. *)
module Hacl.RSAPKCS1

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.RSAPKCS1
open Hacl.Spec.Bytes
open Hacl.Hash.SHA2.Core
open Spec.SHA2.Constants
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.Impl.Copy
open Hacl.RSAPSS.PSS
open Hacl.RSAPSS

module Sub = Hacl.Impl.Sub
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Mem = Hacl.Mem

(** {2 The DigestInfo prefixes}

    In the program image, with their contents in their types, as for the
    SHA-2 tables. *)

let digest_info_sha256_arr : (a: G.static_array S8.t
                                { G.static_array_elems a == (digest_info_sha256 <: Seq.seq S8.t) })
  = G.mk_static_array digest_info_sha256_list

let digest_info_sha384_arr : (a: G.static_array S8.t
                                { G.static_array_elems a == (digest_info_sha384 <: Seq.seq S8.t) })
  = G.mk_static_array digest_info_sha384_list

let digest_info_sha512_arr : (a: G.static_array S8.t
                                { G.static_array_elems a == (digest_info_sha512 <: Seq.seq S8.t) })
  = G.mk_static_array digest_info_sha512_list

(** {2 The encoding} *)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

(** [em] receives [EMSA-PKCS1-v1_5-ENCODE(msg, emLen)] with the DigestInfo
    prefix [di].  Every byte is written, so [em] may start out as anything. *)
fn pkcs1_encode_impl (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                     ([@@@FStar.Attributes.monomorphize] p: params t)
                     (kt: A.array t) (ivt: A.array t)
                     (em: A.array S8.t) (emLen: SZ.t)
                     (di: A.array S8.t) (diLen: SZ.t)
                     (msg: A.array S8.t) (mLen: SZ.t)
                     (#pk: perm) (#vk: erased (Seq.seq t))
                     (#pi: perm) (#vi: erased (Seq.seq t))
                     (#vem: erased (Seq.seq S8.t))
                     (#pd: perm) (#vdi: erased (Seq.seq S8.t))
                     (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to em vem **
         A.pts_to di #pd vdi ** A.pts_to msg #pm vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vem == SZ.v emLen /\ Seq.length vdi == SZ.v diLen /\
               pkcs1_ok p (SZ.v diLen) (SZ.v emLen) /\
               SZ.v mLen == Seq.length vmsg /\
               Seq.length vmsg < pow2 61 /\ Seq.length vmsg < max_input #t)
ensures exists* vem'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to em vem' **
  A.pts_to di #pd vdi ** A.pts_to msg #pm vmsg **
  pure (Seq.length vmsg < max_input #t /\ pkcs1_ok p (Seq.length vdi) (SZ.v emLen) /\
        vem' == pkcs1_encode p vdi (SZ.v emLen) vmsg)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len em;
  A.pts_to_len di;
  A.pts_to_len msg;
  let hLen = p.nhash_bytes;
  let hOff = SZ.sub emLen hLen;
  let diOff = SZ.sub hOff diLen;
  let psLen = SZ.sub diOff 3sz;
  let z8 = S8.zero;

  (* [0x00 | 0x01 | PS | 0x00]. *)
  A.((em.(0sz) <- z8));
  A.((em.(1sz) <- S8.classify 1uy));
  fill_range em 2sz psLen (S8.classify 0xffuy);
  A.((em.(SZ.add psLen 2sz) <- z8));
  with vemA. assert (A.pts_to em vemA);

  (* The DigestInfo prefix, then the digest itself, hashed into place. *)
  copy_at em diOff di diLen;
  with vemB. assert (A.pts_to em vemB);
  let hw = Sub.sub em hOff emLen;
  hash_impl p kt ivt hw msg mLen;
  Sub.unsub em (SZ.v hOff) (SZ.v emLen) hw;
  with vemC. assert (A.pts_to em vemC);

  assert (pure (Seq.length vemC == SZ.v emLen));
  assert (pure (forall (k: nat). k < SZ.v hOff ==> Seq.index vemC k == Seq.index vemB k));
  assert (pure (forall (k: nat). k < SZ.v diOff ==> Seq.index vemB k == Seq.index vemA k));
  assert (pure (Seq.index vemC 0 == S8.zero));
  assert (pure (Seq.index vemC 1 == S8.classify 1uy));
  assert (pure (forall (k: nat). k < SZ.v psLen ==>
                  Seq.index vemC (2 + k) == S8.classify 0xffuy));
  assert (pure (Seq.index vemC (SZ.v psLen + 2) == S8.zero));
  assert (pure (forall (k: nat). k < SZ.v diLen ==>
                  Seq.index vemC (SZ.v psLen + 3 + k) == Seq.index vdi k));
  assert (pure (forall (k: nat). k < SZ.v hLen ==>
                  Seq.index vemC (SZ.v emLen - SZ.v hLen + k) == Seq.index (hash p vmsg) k));
  emsa_pkcs1_intro vdi (hash p vmsg) (SZ.v emLen) vemC;
  pkcs1_encode_eq p vdi (SZ.v emLen) vmsg;
}

#pop-options

(** {2 Verification} *)

#push-options "--z3rlimit 600 --fuel 0 --ifuel 0"

(** Two byte strings of the same length are equal exactly when their
    numbers are. *)
let be_nat_eq (a b: Seq.seq S8.t)
  : Lemma (requires Seq.length a == Seq.length b)
          (ensures (forall (k: nat). k < Seq.length a ==>
                      S8.v (Seq.index a k) == S8.v (Seq.index b k)) <==>
                   be_nat a == be_nat b)
  = introduce (forall (k: nat). k < Seq.length a ==>
                 S8.v (Seq.index a k) == S8.v (Seq.index b k)) ==> be_nat a == be_nat b
    with Seq.lemma_eq_intro a b;
    introduce be_nat a == be_nat b ==>
              (forall (k: nat). k < Seq.length a ==> S8.v (Seq.index a k) == S8.v (Seq.index b k))
    with Spec.RSAPSS.be_nat_inj a b

(** The result of the RSA function is below the modulus, so it always fits
    in the modulus's width: when the output is that wide, the arithmetic
    step refuses only a key that is not a key, or a signature that is not
    below the modulus. *)
let rsa_pow_fits (s e: nat) (nb: Seq.seq S8.t)
  : Lemma (0 < be_nat nb ==> rsa_pow s e (be_nat nb) < pow2 (8 * Seq.length nb))
  = be_nat_bound nb

(** RSASSA-PKCS1-v1_5-VERIFY, RFC 8017 section 8.2.2, for the hash [p]
    named by the DigestInfo prefix [di]. *)
fn rsapkcs1_verify (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                   ([@@@FStar.Attributes.monomorphize] p: params t)
                   (kt: A.array t) (ivt: A.array t)
                   (di: A.array S8.t) (diLen: SZ.t)
                   (modBits: (m: U32.t { 1 < U32.v m }))
                   (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                   (sgnt: A.array S8.t)
                   (mLen: SZ.t) (msg: A.array S8.t)
                   (#pk: perm) (#vk: erased (Seq.seq t))
                   (#pi: perm) (#vi: erased (Seq.seq t))
                   (#pd: perm) (#vdi: erased (Seq.seq S8.t))
                   (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                   (#peb: perm) (#veb: erased (Seq.seq S8.t))
                   (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                   (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to di #pd vdi **
         A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb ** A.pts_to sgnt #psg vsg **
         A.pts_to msg #pm vmsg **
  pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
        Seq.length vdi == SZ.v diLen /\ SZ.v diLen < 256 /\
        U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\
        Seq.length vmsg < pow2 61 /\ Seq.length vmsg < max_input #t)
returns ok: bool
ensures A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to di #pd vdi **
        A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb ** A.pts_to sgnt #psg vsg **
        A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       pkcs1_valid p vdi ((U32.v modBits + 7) / 8) vmsg
                                   (rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb))))
{
  A.pts_to_len di;
  A.pts_to_len nb;
  A.pts_to_len eb;
  A.pts_to_len sgnt;
  A.pts_to_len msg;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (U32.v modBits + 7);
  let mb = sz_of_u32 modBits;
  let kLen = SZ.div (SZ.add mb 7sz) 8sz;
  SZ.fits_u32_implies_fits (SZ.v kLen + 7);
  SZ.fits_u32_implies_fits (128 * SZ.v kLen);
  SZ.fits_u32_implies_fits (SZ.v eLen + 7);
  SZ.fits_u32_implies_fits (64 * SZ.v eLen);
  let hLen = p.nhash_bytes;
  assert (pure (SZ.v hLen <= 128));
  SZ.fits_u32_implies_fits (SZ.v diLen + SZ.v hLen + 11);
  (* A modulus too short to hold the encoding: RFC 8017 section 9.2, step
     3, and section 8.2.2, step 3, which turns it into "invalid signature". *)
  if (SZ.lt kLen (SZ.add (SZ.add diLen hLen) 11sz)) {
    false
  } else {
    let em = Mem.alloc (zero8 <: S8.t) kLen;
    A.pts_to_len em;
    let good = rsa_exp em kLen sgnt kLen nb kLen eb eLen false;
    if good {
      with vem. assert (A.pts_to em vem);
      let enc = Mem.alloc (zero8 <: S8.t) kLen;
      A.pts_to_len enc;
      pkcs1_encode_impl p kt ivt enc kLen di diLen msg mLen;
      with venc. assert (A.pts_to enc venc);
      let r = eq_range enc em 0sz kLen;
      be_nat_eq venc vem;
      Mem.free enc kLen;
      Mem.free em kLen;
      r
    } else {
      rsa_pow_fits (be_nat vsg) (be_nat veb) vnb;
      Mem.free em kLen;
      false
    }
  }
}

(** RSASSA-PKCS1-v1_5-SIGN, RFC 8017 section 8.2.1, for the hash [p] named
    by the DigestInfo prefix [di].  [nb] and [db] are the modulus and the
    private exponent, big-endian; [sgnt] receives [ceil(modBits/8)] bytes.
    The result is [false] exactly when the modulus is too short for the
    encoding or is not a modulus the encoding is below, which never happens
    for a valid key of [modBits] bits. *)
fn rsapkcs1_sign (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (kt: A.array t) (ivt: A.array t)
                 (di: A.array S8.t) (diLen: SZ.t)
                 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (sgnt: A.array S8.t)
                 (#pk: perm) (#vk: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#pd: perm) (#vdi: erased (Seq.seq S8.t))
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
                 (#vsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to di #pd vdi **
         A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb ** A.pts_to msg #pm vmsg **
         A.pts_to sgnt vsg **
  pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
        Seq.length vdi == SZ.v diLen /\ SZ.v diLen < 256 /\
        U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\
        Seq.length vmsg < pow2 61 /\ Seq.length vmsg < max_input #t)
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to di #pd vdi **
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb ** A.pts_to msg #pm vmsg **
  A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok <==> pkcs1_signable p vdi ((U32.v modBits + 7) / 8) vmsg (be_nat vnb)) /\
        (ok ==> pkcs1_signed p vdi ((U32.v modBits + 7) / 8) vmsg
                             (be_nat vnb) (be_nat vdb) (be_nat vsg')))
{
  A.pts_to_len di;
  A.pts_to_len nb;
  A.pts_to_len db;
  A.pts_to_len sgnt;
  A.pts_to_len msg;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (U32.v modBits + 7);
  let mb = sz_of_u32 modBits;
  let kLen = SZ.div (SZ.add mb 7sz) 8sz;
  SZ.fits_u32_implies_fits (SZ.v kLen + 7);
  SZ.fits_u32_implies_fits (128 * SZ.v kLen);
  SZ.fits_u32_implies_fits (SZ.v dLen + 7);
  SZ.fits_u32_implies_fits (64 * SZ.v dLen);
  let hLen = p.nhash_bytes;
  assert (pure (SZ.v hLen <= 128));
  SZ.fits_u32_implies_fits (SZ.v diLen + SZ.v hLen + 11);
  (* RFC 8017 section 9.2, step 3: "intended encoded message length too
     short". *)
  if (SZ.lt kLen (SZ.add (SZ.add diLen hLen) 11sz)) {
    false
  } else {
    let em = Mem.alloc (zero8 <: S8.t) kLen;
    A.pts_to_len em;
    pkcs1_encode_impl p kt ivt em kLen di diLen msg mLen;
    with vem. assert (A.pts_to em vem);
    let r = rsa_exp sgnt kLen em kLen nb kLen db dLen true;
    rsa_pow_fits (be_nat vem) (be_nat vdb) vnb;
    Mem.free em kLen;
    r
  }
}

#pop-options

(* As in {!Hacl.RSAPSS}: the entry points get a fresh solver, so that how
   long their queries take does not depend on what came before. *)
#restart-solver

(** {2 The entry points}

    One per hash.  [modBits] is the bit length of the modulus, so [nb] and
    [sgnt] are [ceil(modBits/8)] bytes; the public exponent [eb] is a
    big-endian string of whatever length the caller has it in.  The result
    is [true] exactly when the modulus is odd and greater than one, the
    signature is below it, and the signature raised to the exponent is the
    encoding of the message. *)

(** RSASSA-PKCS1-v1_5-VERIFY with sha256. *)
fn verify_sha256 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
         A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61)
returns ok: bool
ensures A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
        A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       pkcs1_valid sha2_256 digest_info_sha256 ((U32.v modBits + 7) / 8) vmsg
                                   (rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb))))
{
  max_input_bound ();
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let dit = table digest_info_sha256_arr 19sz;
  sha2_256_facts ();
  let r = rsapkcs1_verify sha2_256 kt ivt dit 19sz modBits nb eLen eb sgnt mLen msg;
  drop_table dit;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PKCS1-v1_5-VERIFY with sha384. *)
fn verify_sha384 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
         A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61)
returns ok: bool
ensures A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
        A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       pkcs1_valid sha2_384 digest_info_sha384 ((U32.v modBits + 7) / 8) vmsg
                                   (rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb))))
{
  max_input_bound ();
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  let dit = table digest_info_sha384_arr 19sz;
  sha2_384_facts ();
  sha2_384_tables ();
  let r = rsapkcs1_verify sha2_384 kt ivt dit 19sz modBits nb eLen eb sgnt mLen msg;
  drop_table dit;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PKCS1-v1_5-VERIFY with sha512. *)
fn verify_sha512 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
         A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61)
returns ok: bool
ensures A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
        A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       pkcs1_valid sha2_512 digest_info_sha512 ((U32.v modBits + 7) / 8) vmsg
                                   (rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb))))
{
  max_input_bound ();
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  let dit = table digest_info_sha512_arr 19sz;
  sha2_512_facts ();
  sha2_512_tables ();
  let r = rsapkcs1_verify sha2_512 kt ivt dit 19sz modBits nb eLen eb sgnt mLen msg;
  drop_table dit;
  drop_table ivt;
  drop_table kt;
  r
}

(** {2 Signing entry points}

    As above, with the private exponent [db] in place of the public one;
    [sgnt] receives the signature.  The result is [true] exactly when the
    modulus is long enough for the encoding, odd, greater than one, and
    above the encoding, which a valid key of [modBits] bits always is (see
    {!Spec.RSAPKCS1.Correctness}). *)

(** RSASSA-PKCS1-v1_5-SIGN with sha256. *)
fn sign_sha256 (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
         A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61)
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
  A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok <==> pkcs1_signable sha2_256 digest_info_sha256 ((U32.v modBits + 7) / 8) vmsg
                                (be_nat vnb)) /\
        (ok ==> pkcs1_signed sha2_256 digest_info_sha256 ((U32.v modBits + 7) / 8) vmsg
                             (be_nat vnb) (be_nat vdb) (be_nat vsg')))
{
  max_input_bound ();
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let dit = table digest_info_sha256_arr 19sz;
  sha2_256_facts ();
  let r = rsapkcs1_sign sha2_256 kt ivt dit 19sz modBits nb dLen db mLen msg sgnt;
  drop_table dit;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PKCS1-v1_5-SIGN with sha384. *)
fn sign_sha384 (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
         A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61)
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
  A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok <==> pkcs1_signable sha2_384 digest_info_sha384 ((U32.v modBits + 7) / 8) vmsg
                                (be_nat vnb)) /\
        (ok ==> pkcs1_signed sha2_384 digest_info_sha384 ((U32.v modBits + 7) / 8) vmsg
                             (be_nat vnb) (be_nat vdb) (be_nat vsg')))
{
  max_input_bound ();
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  let dit = table digest_info_sha384_arr 19sz;
  sha2_384_facts ();
  sha2_384_tables ();
  let r = rsapkcs1_sign sha2_384 kt ivt dit 19sz modBits nb dLen db mLen msg sgnt;
  drop_table dit;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PKCS1-v1_5-SIGN with sha512. *)
fn sign_sha512 (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
         A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61)
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
  A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok <==> pkcs1_signable sha2_512 digest_info_sha512 ((U32.v modBits + 7) / 8) vmsg
                                (be_nat vnb)) /\
        (ok ==> pkcs1_signed sha2_512 digest_info_sha512 ((U32.v modBits + 7) / 8) vmsg
                             (be_nat vnb) (be_nat vdb) (be_nat vsg')))
{
  max_input_bound ();
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  let dit = table digest_info_sha512_arr 19sz;
  sha2_512_facts ();
  sha2_512_tables ();
  let r = rsapkcs1_sign sha2_512 kt ivt dit 19sz modBits nb dLen db mLen msg sgnt;
  drop_table dit;
  drop_table ivt;
  drop_table kt;
  r
}
