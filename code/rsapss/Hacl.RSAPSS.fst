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

(** RSASSA-PSS, RFC 8017 sections 8.1.1 and 8.1.2.

    Signing is EMSA-PSS encoding followed by a modular exponentiation with
    the private exponent; verifying is an exponentiation with the public
    exponent followed by EMSA-PSS verification.  {!Hacl.RSAPSS.PSS} has the
    encoding; this module has the arithmetic and the plumbing.

    {b Keys are byte strings.}  There is no key type, no loading step and no
    allocation.  A caller passes the modulus and the exponent as big-endian
    byte strings of the lengths it already has them in, which is how they
    arrive in every format a key is stored in.  HACL* instead asks the
    caller to call a loader that mallocs a flat limb array and to free it
    afterwards; that buys a little speed when one key signs many messages
    and costs an allocator, a lifetime and a failure mode.

    {b Nothing is trusted.}  The modulus is checked to be odd and greater
    than one, and the signature is checked to be below it, at run time.  A
    caller that passes rubbish gets [false], not a proof obligation. *)
module Hacl.RSAPSS

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.Bignum
open Spec.RSAPSS
open Hacl.Spec.Bytes
open Hacl.Bignum.Base
open Hacl.Impl.Copy
open Hacl.Hash.SHA2.Core
open Spec.SHA2.Constants
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.RSAPSS.PSS

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
(* [S32] is only the SHA-224/256 working word; bignum limbs are [S64]. *)
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Declassify = Hacl.Secret.Declassify
module Conv = Hacl.Bignum.Convert
module Mont = Hacl.Bignum.Montgomery
module Exp = Hacl.Bignum.Exponentiation
module Mem = Hacl.Mem

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

(** {2 Key parts are byte strings of an arbitrary length}

    {!Hacl.Bignum.Convert} converts whole limbs.  A modulus of [modBits]
    bits occupies [ceil(modBits/8)] bytes, which is not a multiple of four
    in general, so both directions stage through a zeroed buffer of [4n]
    bytes and put the bytes at the right end.  That is exactly what the
    left-padding in the standards means. *)

(** A zero byte, with its value in its type: a Pulse [let] keeps the type of
    the binding, not the refinement of the definition. *)
let zero8 : (z: S8.t { S8.v z == 0 }) = S8.zero

(** The limb count that holds a [len]-byte number. *)
let limbs_of (len: nat) : nat = (len + 7) / 8

let limbs_of_ok (len: nat) : Lemma (len <= 8 * limbs_of len /\ limbs_of len <= (len + 7) / 8) = ()

(** [res <- be_nat b], left-padding [b] to the width of [res]. *)
fn bn_from_be (res: A.array S64.t) (nn: SZ.t) (b: A.array S8.t) (len: SZ.t)
              (#p: perm) (#vres: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to res vres ** A.pts_to b #p vb **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vb == SZ.v len /\
        SZ.v len <= 8 * SZ.v nn /\ SZ.fits (8 * SZ.v nn))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v nn /\ num v == be_nat vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  let width = SZ.mul 8sz nn;
  let off = SZ.sub width len;
  let tmp = Mem.alloc (zero8 <: S8.t) width;
  A.pts_to_len tmp;
  (* The padding is at most three bytes, and the stack allocation already
     starts out zero, so [copy_at] leaving the prefix alone is enough.
     Writing it again would be dead code, and C compilers cannot see that
     [off] is small and warn about the store. *)
  with v0. assert (A.pts_to tmp v0);
  assert (pure (forall (i: nat). i < SZ.v width ==> S8.v (Seq.index v0 i) == 0));
  copy_at tmp off b len;
  with vt. assert (A.pts_to tmp vt);
  assert (pure (forall (i: nat). i < SZ.v off ==> S8.v (Seq.index vt i) == 0));
  be_nat_pad vt (SZ.v len);
  Seq.lemma_eq_intro (Seq.slice vt (SZ.v off) (SZ.v width)) (reveal vb);
  Conv.from_bytes_be res nn tmp;
  Mem.free tmp width;
}

(** [b <- the low [len] bytes of [a]], which are all of it. *)
fn bn_to_be (b: A.array S8.t) (len: SZ.t) (a: A.array S64.t) (nn: SZ.t)
            (#p: perm) (#vb: erased (Seq.seq S8.t)) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #p va **
  pure (Seq.length vb == SZ.v len /\ Seq.length va == SZ.v nn /\
        SZ.v len <= 8 * SZ.v nn /\ SZ.fits (8 * SZ.v nn) /\
        num va < pow2 (8 * SZ.v len))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to b v ** A.pts_to a #p va **
  pure (Seq.length v == SZ.v len /\ be_nat v == num va)
{
  A.pts_to_len b;
  A.pts_to_len a;
  let width = SZ.mul 8sz nn;
  let off = SZ.sub width len;
  let tmp = Mem.alloc (zero8 <: S8.t) width;
  A.pts_to_len tmp;
  Conv.to_bytes_be tmp a nn;
  with vt. assert (A.pts_to tmp vt);
  be_nat_trunc vt (SZ.v len);
  copy_range b 0sz tmp off len;
  with vb'. assert (A.pts_to b vb');
  assert (pure (Seq.length vb' == SZ.v len));
  assert (pure (forall (k: nat). k < SZ.v len ==>
                  Seq.index vb' k == Seq.index vt (SZ.v off + k)));
  Seq.lemma_eq_intro (Seq.slice vt (SZ.v off) (SZ.v width)) vb';
  assert (pure (be_nat vb' == num va));
  Mem.free tmp width;
}

(** [res <- 1]. *)
fn bn_one (res: A.array S64.t) (nn: SZ.t) (#vres: erased (Seq.seq S64.t))
requires A.pts_to res vres ** pure (Seq.length vres == SZ.v nn /\ 0 < SZ.v nn)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** pure (Seq.length v == SZ.v nn /\ num v == 1)
{
  A.pts_to_len res;
  zero res nn;
  with v0. assert (A.pts_to res v0);
  pre_zeros v0 (SZ.v nn);
  pre_full v0;
  let one = S64.classify 1uL;
  A.((res.(0sz) <- one));
  num_upd v0 0 one;
  wt_zero ();
}

(** A number is below the weight of its own width. *)
let num_bound (v: Seq.seq S64.t) : Lemma (num v < wt (Seq.length v))
  = pre_bnd v (Seq.length v); pre_full v

#pop-options

(** {2 Modular exponentiation over byte-string exponents} *)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

(** A [size_t] holding a [uint32].  Extracts to a cast. *)
inline_for_extraction
let sz_of_u32 (x: U32.t) : (r: SZ.t { SZ.v r == U32.v x }) =
  Hacl.SizeT.fits32 ();
  SZ.uint32_to_sizet x

(** Refinement subtyping does not fire through [erased]; a modulus argument
    goes through one of these. *)
let as_modulus (s: Seq.seq S64.t)
  : Pure (r: Seq.seq S64.t { 1 < num r }) (requires 1 < num s) (ensures fun r -> r == s)
  = s

(** [res <- a ^ be_nat eb mod n].

    The exponent is a byte string, as it comes out of a key, and is used to
    its full width: the loop counts bits of the buffer, not bits of the
    number, so that nothing about a private exponent leaks through a loop
    bound.  [ct] chooses the constant-time ladder; a public exponent may
    take the other one. *)
fn mod_exp_be (res: A.array S64.t) (a: A.array S64.t)
              (eb: A.array S8.t) (eLen: SZ.t) (en: SZ.t)
              (nmod: A.array S64.t) (nn: SZ.t) (ct: bool)
              (#vres: erased (Seq.seq S64.t)) (#pa #pe #pn: perm)
              (#va: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S8.t))
              (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to eb #pe ve **
         A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vn == SZ.v nn /\ Seq.length ve == SZ.v eLen /\
        0 < SZ.v nn /\ 0 < SZ.v en /\ 1 < num vn /\ SZ.v eLen <= 8 * SZ.v en /\
        SZ.fits (2 * rad * SZ.v nn) /\ SZ.fits (8 * SZ.v en) /\ SZ.fits (64 * SZ.v en) /\
        num va < num vn /\ S64.v (Seq.index vn 0) % 2 == 1)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to eb #pe ve **
  A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ num v == pw (num va) (be_nat ve) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len eb;
  A.pts_to_len nmod;
  SZ.fits_lte (SZ.v nn + SZ.v nn) (2 * rad * SZ.v nn);
  let z64 = S64.zero;
  let ebn = Mem.alloc z64 en;
  let r2 = Mem.alloc z64 nn;
  let aM = Mem.alloc z64 nn;
  let accu = Mem.alloc z64 nn;
  let tn = Mem.alloc z64 nn;
  let wide = Mem.alloc z64 (SZ.add nn nn);
  A.pts_to_len ebn;
  A.pts_to_len r2;
  A.pts_to_len aM;
  A.pts_to_len accu;
  A.pts_to_len tn;
  A.pts_to_len wide;
  bn_from_be ebn en eb eLen;
  with vebn. assert (A.pts_to ebn vebn);
  num_bound vebn;
  let n0 = A.(nmod.(0sz));
  let mu = Mont.mont_mu n0;
  Mont.precomp r2 accu tn wide nmod nn mu
               #_ #_ #_ #_ #_ #(hide (as_modulus (reveal vn)));
  let bbits = SZ.mul 64sz en;
  assert (pure (wt (SZ.v en) == pow2 (SZ.v bbits)));
  if ct {
    SZ.fits_lte (16 * SZ.v nn) (2 * rad * SZ.v nn);
    Exp.mul64_mod4 (SZ.v en);
    Exp.mod_exp_consttime res a ebn bbits r2 nmod nn mu aM accu tn wide;
    Mem.free wide (SZ.add nn nn);
    Mem.free tn nn;
    Mem.free accu nn;
    Mem.free aM nn;
    Mem.free r2 nn;
    Mem.free ebn en;
  } else {
    Exp.mod_exp_vartime res a ebn bbits r2 nmod nn mu aM accu tn wide;
    Mem.free wide (SZ.add nn nn);
    Mem.free tn nn;
    Mem.free accu nn;
    Mem.free aM nn;
    Mem.free r2 nn;
    Mem.free ebn en;
  }
}

#pop-options

(** {2 The RSA primitive}

    Both directions of RSASSA-PSS are the same three steps: read a
    big-endian number, raise it to an exponent modulo the modulus, write a
    big-endian number of a possibly different length.  The differences are
    which exponent, which lengths, and whether the ladder has to be
    constant-time.  So it is written once.

    Every hypothesis the arithmetic needs is checked here rather than
    assumed of the caller: that the modulus is odd and exceeds one, that the
    base is below it, and that the result fits the output.  The answer is a
    [bool] and the specification says exactly when it is [true]. *)

#push-options "--z3rlimit 600 --fuel 0 --ifuel 0"

(** [s ^ e mod n], total in [n].  A postcondition names this value in the
    same breath as it says that [n] is not zero, and a quantifier does not
    carry the one fact into the other. *)
let rsa_pow (s e n: nat) : nat = if n = 0 then 0 else pw s e % n

(** The parity of a number is the parity of its bottom limb. *)
let num_parity (v: Seq.seq S64.t { 0 < Seq.length v })
  : Lemma (num v % 2 == S64.v (Seq.index v 0) % 2)
  = pre_mod v 1;
    pre_snoc v 0;
    pre_zero v;
    wt_zero ();
    assert (pre v 1 == S64.v (Seq.index v 0));
    assert (wt 1 == pow2 64);
    Math.pow2_modulo_modulo_lemma_1 (num v) 1 64

(** [(len + 7) / 8] limbs hold [len] bytes and no more than [len] limbs do. *)
let limbs_le (len: pos) : Lemma (0 < (len + 7) / 8 /\ (len + 7) / 8 <= len /\
                                 len <= 8 * ((len + 7) / 8)) = ()

let as_modulus0 (s: Seq.seq S64.t)
  : Pure (r: Seq.seq S64.t { 0 < num r /\ 0 < Seq.length r })
         (requires 0 < num s /\ 0 < Seq.length s) (ensures fun r -> r == s)
  = s

(** [out <- (be_nat inp) ^ (be_nat eb) mod (be_nat nb)], or [false]. *)
fn rsa_exp (out: A.array S8.t) (outLen: SZ.t)
           (inp: A.array S8.t) (inLen: SZ.t)
           (nb: A.array S8.t) (kLen: SZ.t)
           (eb: A.array S8.t) (eLen: SZ.t) (ct: bool)
           (#vout: erased (Seq.seq S8.t)) (#pin #pnb #peb: perm)
           (#vin #vnb #veb: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to inp #pin vin **
         A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
  pure (Seq.length vout == SZ.v outLen /\ Seq.length vin == SZ.v inLen /\
        Seq.length vnb == SZ.v kLen /\ Seq.length veb == SZ.v eLen /\
        0 < SZ.v kLen /\ 0 < SZ.v eLen /\
        SZ.v outLen <= SZ.v kLen /\ SZ.v inLen <= SZ.v kLen /\
        SZ.fits (SZ.v kLen + 7) /\ SZ.fits (128 * SZ.v kLen) /\
        SZ.fits (SZ.v eLen + 7) /\ SZ.fits (64 * SZ.v eLen))
returns ok: bool
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to inp #pin vin **
  A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
  pure (Seq.length vout' == SZ.v outLen /\
        (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vin < be_nat vnb /\
                  rsa_pow (be_nat vin) (be_nat veb) (be_nat vnb) < pow2 (8 * SZ.v outLen))) /\
        (ok ==> be_nat vout' == rsa_pow (be_nat vin) (be_nat veb) (be_nat vnb)))
{
  A.pts_to_len out;
  A.pts_to_len inp;
  A.pts_to_len nb;
  A.pts_to_len eb;
  limbs_le (SZ.v kLen);
  limbs_le (SZ.v eLen);
  let nn = SZ.div (SZ.add kLen 7sz) 8sz;
  let en = SZ.div (SZ.add eLen 7sz) 8sz;
  SZ.fits_lte (8 * SZ.v nn) (128 * SZ.v kLen);
  SZ.fits_lte (2 * rad * SZ.v nn) (128 * SZ.v kLen);
  SZ.fits_lte (8 * SZ.v en) (64 * SZ.v eLen);
  SZ.fits_lte (64 * SZ.v en) (64 * SZ.v eLen);
  let z64 = S64.zero;
  let nbn = Mem.alloc z64 nn;
  let mbn = Mem.alloc z64 nn;
  let sbn = Mem.alloc z64 nn;
  let onebn = Mem.alloc z64 nn;
  A.pts_to_len nbn;
  A.pts_to_len mbn;
  A.pts_to_len sbn;
  A.pts_to_len onebn;

  bn_from_be nbn nn nb kLen;
  bn_from_be mbn nn inp inLen;
  bn_one onebn nn;
  with vnbn. assert (A.pts_to nbn vnbn);
  num_parity vnbn;
  assert_norm (pow2 64 - 1 == 18446744073709551615);

  let n0 = A.(nbn.(0sz));
  let odd = U64.eq (U64.rem (Declassify.u64 n0) 2uL) 1uL;
  let gt1 = U64.eq (Declassify.u64 (lt_mask onebn nbn nn)) 18446744073709551615uL;
  let below = U64.eq (Declassify.u64 (lt_mask mbn nbn nn)) 18446744073709551615uL;

  if (odd && gt1 && below) {
    mod_exp_be sbn mbn eb eLen en nbn nn ct
               #_ #_ #_ #_ #_ #_ #(hide (as_modulus0 (reveal vnbn)));
    (* The result is written at full limb width, and the bytes above the
       output must be zero.  When the output is as wide as the modulus they
       are, because the result is below the modulus: that is the signing
       path, where the result is secret and is not looked at.  Otherwise
       -- verification, where it is public -- they are checked. *)
    let width = SZ.mul 8sz nn;
    let off = SZ.sub width outLen;
    let tmp = Mem.alloc (zero8 <: S8.t) width;
    A.pts_to_len tmp;
    Conv.to_bytes_be tmp sbn nn;
    with vt. assert (A.pts_to tmp vt);
    be_nat_prefix_zero vt (SZ.v outLen);
    be_nat_bound vnb;
    let fits = if (SZ.eq outLen kLen) { true } else { all_zero tmp off };
    if fits {
      be_nat_trunc vt (SZ.v outLen);
      copy_range out 0sz tmp off outLen;
      with vo. assert (A.pts_to out vo);
      assert (pure (Seq.length vo == SZ.v outLen));
      assert (pure (forall (k: nat). k < SZ.v outLen ==>
                      Seq.index vo k == Seq.index vt (SZ.v off + k)));
      Seq.lemma_eq_intro (Seq.slice vt (SZ.v off) (SZ.v width)) vo;
      Mem.free tmp width;
      Mem.free onebn nn;
      Mem.free sbn nn;
      Mem.free mbn nn;
      Mem.free nbn nn;
      true
    } else {
      Mem.free tmp width;
      Mem.free onebn nn;
      Mem.free sbn nn;
      Mem.free mbn nn;
      Mem.free nbn nn;
      false
    }
  } else {
    Mem.free onebn nn;
    Mem.free sbn nn;
    Mem.free mbn nn;
    Mem.free nbn nn;
    false
  }
}

#pop-options

(** {2 Signing and verifying} *)

#push-options "--z3rlimit 600 --fuel 0 --ifuel 1"

(** Naming the encoding is the same as saying one exists.  A verifier
    computes [s^e mod n] and then asks whether {i that} number, written in
    [emLen] bytes, is a valid encoding; since big-endian writing is
    injective at a fixed width, the two readings agree. *)
let verify_intro (#t: Type0) {| word t |} (p: params t) (sLen: nat)
                 (emBits: (b: pos { pss_ok p sLen b }))
                 (msg: (s: Seq.seq S8.t { Seq.length s < max_input #t }))
                 (em: Seq.lseq S8.t (em_len emBits))
                 (m: nat) (ok: bool)
  : Lemma (requires be_nat em == m /\ (ok <==> pss_valid p sLen emBits msg em))
          (ensures ok <==> (exists (e: Seq.lseq S8.t (em_len emBits)).
                              be_nat e == m /\ pss_valid p sLen emBits msg e))
  = introduce (exists (e: Seq.lseq S8.t (em_len emBits)).
                 be_nat e == m /\ pss_valid p sLen emBits msg e) ==> ok
    with begin
      eliminate exists (e: Seq.lseq S8.t (em_len emBits)).
                  be_nat e == m /\ pss_valid p sLen emBits msg e
      with be_nat_inj e em
    end

(** When the arithmetic step refuses, there is nothing to verify: either
    the key is not a key, or the result of the exponentiation is too wide to
    be an encoding at all, and a number has no [emLen]-byte encoding when it
    does not fit in [emLen] bytes. *)
let verify_reject (#t: Type0) {| word t |} (p: params t) (sLen: nat)
                  (emBits: (b: pos { pss_ok p sLen b }))
                  (msg: (s: Seq.seq S8.t { Seq.length s < max_input #t }))
                  (n s e: nat)
  : Lemma (requires ~(1 < n /\ n % 2 == 1 /\ s < n /\
                      rsa_pow s e n < pow2 (8 * em_len emBits)))
          (ensures ~(1 < n /\ n % 2 == 1 /\ s < n /\
                     (exists (x: Seq.lseq S8.t (em_len emBits)).
                        be_nat x == rsa_pow s e n /\ pss_valid p sLen emBits msg x)))
  = introduce (1 < n /\ n % 2 == 1 /\ s < n /\
               (exists (x: Seq.lseq S8.t (em_len emBits)).
                  be_nat x == rsa_pow s e n /\ pss_valid p sLen emBits msg x)) ==> False
    with begin
      eliminate exists (x: Seq.lseq S8.t (em_len emBits)).
                  be_nat x == rsa_pow s e n /\ pss_valid p sLen emBits msg x
      with be_nat_bound x
    end

(** RSASSA-PSS-SIGN, RFC 8017 section 8.1.1.

    [nb] and [db] are the modulus and the private exponent, big-endian;
    [sgnt] receives [ceil(modBits/8)] bytes.  The result is [false] exactly
    when the key does not make sense, which a caller that got its key from
    somewhere trustworthy will never see. *)
fn rsapss_sign (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (ivt: A.array t)
               (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (sLen: SZ.t) (salt: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#psa: perm)
               (#vsalt: erased (s: Seq.seq S8.t { pss_ok p (Seq.length s) (U32.v modBits - 1) }))
               (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #t }))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to nb #pnb vnb **
         A.pts_to db #pdb vdb ** A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg **
         A.pts_to sgnt vsg **
  pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
        U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v sLen == Seq.length vsalt /\ SZ.v mLen == Seq.length vmsg /\
        Seq.length vmsg < pow2 61 /\
        SZ.fits (8 + (hash_bytes p) + Seq.length vsalt) /\
        8 + (hash_bytes p) + Seq.length vsalt < pow2 61)
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to nb #pnb vnb **
  A.pts_to db #pdb vdb ** A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg **
  A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok ==> be_nat vsg' ==
                  rsa_pow (be_nat (pss_encode p (Seq.length vsalt) (U32.v modBits - 1) vsalt vmsg))
                          (be_nat vdb) (be_nat vnb)))
{
  A.pts_to_len nb;
  A.pts_to_len db;
  A.pts_to_len sgnt;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (U32.v modBits + 7);
  let mb = sz_of_u32 modBits;
  let kLen = SZ.div (SZ.add mb 7sz) 8sz;
  SZ.fits_lte (SZ.v mb + 6) (SZ.v mb + 7);
  let emLen = SZ.div (SZ.add mb 6sz) 8sz;
  SZ.fits_u32_implies_fits (SZ.v kLen + 7);
  SZ.fits_u32_implies_fits (128 * SZ.v kLen);
  SZ.fits_u32_implies_fits (SZ.v dLen + 7);
  SZ.fits_u32_implies_fits (64 * SZ.v dLen);
  let emBits = U32.sub modBits 1ul;
  let em = Mem.alloc (zero8 <: S8.t) emLen;
  A.pts_to_len em;
  pss_encode_impl p kt ivt em emBits emLen salt sLen msg mLen;
  let wr = rsa_exp sgnt kLen em emLen nb kLen db dLen true;
  Mem.free em emLen;
  wr
}

(** RSASSA-PSS-VERIFY, RFC 8017 section 8.1.2. *)
fn rsapss_verify (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (kt: A.array t) (ivt: A.array t)
                 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sLen: (n: SZ.t { pss_ok p (SZ.v n) (U32.v modBits - 1) }))
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pk: perm) (#vk: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #t }))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to nb #pnb vnb **
         A.pts_to eb #peb veb ** A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
        U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61 /\
        SZ.fits (8 + (hash_bytes p) + SZ.v sLen) /\
        8 + (hash_bytes p) + SZ.v sLen < pow2 61)
returns ok: bool
ensures A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to nb #pnb vnb **
        A.pts_to eb #peb veb ** A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       (exists (e: Seq.lseq S8.t (em_len (U32.v modBits - 1))).
                          be_nat e == rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb) /\
                          pss_valid p (SZ.v sLen) (U32.v modBits - 1) vmsg e)))
{
  A.pts_to_len nb;
  A.pts_to_len eb;
  A.pts_to_len sgnt;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (U32.v modBits + 7);
  let mb = sz_of_u32 modBits;
  let kLen = SZ.div (SZ.add mb 7sz) 8sz;
  SZ.fits_lte (SZ.v mb + 6) (SZ.v mb + 7);
  let emLen = SZ.div (SZ.add mb 6sz) 8sz;
  SZ.fits_u32_implies_fits (SZ.v kLen + 7);
  SZ.fits_u32_implies_fits (128 * SZ.v kLen);
  SZ.fits_u32_implies_fits (SZ.v eLen + 7);
  SZ.fits_u32_implies_fits (64 * SZ.v eLen);
  let emBits = U32.sub modBits 1ul;
  let em = Mem.alloc (zero8 <: S8.t) emLen;
  A.pts_to_len em;
  let good = rsa_exp em emLen sgnt kLen nb kLen eb eLen false;
  if good {
    with vem. assert (A.pts_to em vem);
    let r = pss_verify_impl p kt ivt em emBits emLen sLen msg mLen
                            #_ #_ #_ #_ #_ #(hide (as_lseq (em_len (U32.v emBits)) (reveal vem)));
    verify_intro p (SZ.v sLen) (U32.v emBits) (reveal vmsg)
                 (as_lseq (em_len (U32.v emBits)) (reveal vem))
                 (rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb)) r;
    Mem.free em emLen;
    r
  } else {
    verify_reject p (SZ.v sLen) (U32.v emBits) (reveal vmsg)
                  (be_nat vnb) (be_nat vsg) (be_nat veb);
    Mem.free em emLen;
    false
  }
}

#pop-options

(* The entry points below run at the default options, and how long their
   queries take depends on what the solver has seen before them: a change
   to the body of [rsa_exp] alone was enough to time one out.  A fresh
   solver makes them independent of everything above. *)
#restart-solver

(** {2 The entry points}

    One pair per hash, as everywhere else in this library.  A caller that
    wants SHA-256 calls the SHA-256 function; there is no algorithm
    argument, no table of function pointers and no way to ask for a
    combination that does not exist.

    [modBits] is the bit length of the modulus, so [nb] and [sgnt] are
    [ceil(modBits/8)] bytes.  The exponents are big-endian strings of
    whatever length the caller has them in.  The salt length must leave room
    in the encoding: [emLen >= hLen + sLen + 2], where [emLen] is
    [ceil((modBits-1)/8)]. *)

(** RSASSA-PSS-SIGN with sha256. *)
fn sign_sha256 (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (sLen: SZ.t) (salt: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#psa: perm)
               (#vsalt: erased (s: Seq.seq S8.t { pss_ok sha2_256 (Seq.length s) (U32.v modBits - 1) }))
               (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #S32.t }))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
         A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v sLen == Seq.length vsalt /\ SZ.v mLen == Seq.length vmsg /\
        Seq.length vmsg < pow2 61 /\ Seq.length vsalt < pow2 32 /\
        SZ.fits (8 + (hash_bytes sha2_256) + Seq.length vsalt))
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
  A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok ==> be_nat vsg' ==
                  rsa_pow (be_nat (pss_encode sha2_256 (Seq.length vsalt) (U32.v modBits - 1) vsalt vmsg))
                          (be_nat vdb) (be_nat vnb)))
{
  A.pts_to_len salt;
  A.pts_to_len msg;
  max_input_bound ();
  assert_norm (8 + 64 + pow2 32 < pow2 61);
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let r = rsapss_sign sha2_256 kt ivt modBits nb dLen db sLen salt mLen msg sgnt;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PSS-VERIFY with sha256. *)
fn verify_sha256 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sLen: (n: SZ.t { pss_ok sha2_256 (SZ.v n) (U32.v modBits - 1) }))
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #S32.t }))
requires A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
         A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61 /\
        SZ.v sLen < pow2 32 /\ SZ.fits (8 + (hash_bytes sha2_256) + SZ.v sLen))
returns ok: bool
ensures A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
        A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       (exists (e: Seq.lseq S8.t (em_len (U32.v modBits - 1))).
                          be_nat e == rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb) /\
                          pss_valid sha2_256 (SZ.v sLen) (U32.v modBits - 1) vmsg e)))
{
  A.pts_to_len msg;
  max_input_bound ();
  assert_norm (8 + 64 + pow2 32 < pow2 61);
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let r = rsapss_verify sha2_256 kt ivt modBits nb eLen eb sLen sgnt mLen msg;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PSS-SIGN with sha384. *)
fn sign_sha384 (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (sLen: SZ.t) (salt: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#psa: perm)
               (#vsalt: erased (s: Seq.seq S8.t { pss_ok sha2_384 (Seq.length s) (U32.v modBits - 1) }))
               (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #S64.t }))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
         A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v sLen == Seq.length vsalt /\ SZ.v mLen == Seq.length vmsg /\
        Seq.length vmsg < pow2 61 /\ Seq.length vsalt < pow2 32 /\
        SZ.fits (8 + (hash_bytes sha2_384) + Seq.length vsalt))
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
  A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok ==> be_nat vsg' ==
                  rsa_pow (be_nat (pss_encode sha2_384 (Seq.length vsalt) (U32.v modBits - 1) vsalt vmsg))
                          (be_nat vdb) (be_nat vnb)))
{
  A.pts_to_len salt;
  A.pts_to_len msg;
  max_input_bound ();
  assert_norm (8 + 64 + pow2 32 < pow2 61);
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  let r = rsapss_sign sha2_384 kt ivt modBits nb dLen db sLen salt mLen msg sgnt;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PSS-VERIFY with sha384. *)
fn verify_sha384 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sLen: (n: SZ.t { pss_ok sha2_384 (SZ.v n) (U32.v modBits - 1) }))
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #S64.t }))
requires A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
         A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61 /\
        SZ.v sLen < pow2 32 /\ SZ.fits (8 + (hash_bytes sha2_384) + SZ.v sLen))
returns ok: bool
ensures A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
        A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       (exists (e: Seq.lseq S8.t (em_len (U32.v modBits - 1))).
                          be_nat e == rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb) /\
                          pss_valid sha2_384 (SZ.v sLen) (U32.v modBits - 1) vmsg e)))
{
  A.pts_to_len msg;
  max_input_bound ();
  assert_norm (8 + 64 + pow2 32 < pow2 61);
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  let r = rsapss_verify sha2_384 kt ivt modBits nb eLen eb sLen sgnt mLen msg;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PSS-SIGN with sha512. *)
fn sign_sha512 (modBits: (m: U32.t { 1 < U32.v m }))
               (nb: A.array S8.t) (dLen: SZ.t) (db: A.array S8.t)
               (sLen: SZ.t) (salt: A.array S8.t)
               (mLen: SZ.t) (msg: A.array S8.t)
               (sgnt: A.array S8.t)
               (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
               (#pdb: perm) (#vdb: erased (Seq.seq S8.t))
               (#psa: perm)
               (#vsalt: erased (s: Seq.seq S8.t { pss_ok sha2_512 (Seq.length s) (U32.v modBits - 1) }))
               (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #S64.t }))
               (#vsg: erased (Seq.seq S8.t))
requires A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
         A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length vdb == SZ.v dLen /\
        0 < SZ.v dLen /\ SZ.v dLen <= (U32.v modBits + 7) / 8 /\
        SZ.v sLen == Seq.length vsalt /\ SZ.v mLen == Seq.length vmsg /\
        Seq.length vmsg < pow2 61 /\ Seq.length vsalt < pow2 32 /\
        SZ.fits (8 + (hash_bytes sha2_512) + Seq.length vsalt))
returns ok: bool
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to nb #pnb vnb ** A.pts_to db #pdb vdb **
  A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg ** A.pts_to sgnt vsg' **
  pure (Seq.length vsg' == (U32.v modBits + 7) / 8 /\
        (ok ==> be_nat vsg' ==
                  rsa_pow (be_nat (pss_encode sha2_512 (Seq.length vsalt) (U32.v modBits - 1) vsalt vmsg))
                          (be_nat vdb) (be_nat vnb)))
{
  A.pts_to_len salt;
  A.pts_to_len msg;
  max_input_bound ();
  assert_norm (8 + 64 + pow2 32 < pow2 61);
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  let r = rsapss_sign sha2_512 kt ivt modBits nb dLen db sLen salt mLen msg sgnt;
  drop_table ivt;
  drop_table kt;
  r
}

(** RSASSA-PSS-VERIFY with sha512. *)
fn verify_sha512 (modBits: (m: U32.t { 1 < U32.v m }))
                 (nb: A.array S8.t) (eLen: SZ.t) (eb: A.array S8.t)
                 (sLen: (n: SZ.t { pss_ok sha2_512 (SZ.v n) (U32.v modBits - 1) }))
                 (sgnt: A.array S8.t)
                 (mLen: SZ.t) (msg: A.array S8.t)
                 (#pnb: perm) (#vnb: erased (Seq.seq S8.t))
                 (#peb: perm) (#veb: erased (Seq.seq S8.t))
                 (#psg: perm) (#vsg: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #S64.t }))
requires A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
         A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
  pure (U32.v modBits <= 65536 /\
        Seq.length vnb == (U32.v modBits + 7) / 8 /\
        Seq.length vsg == (U32.v modBits + 7) / 8 /\
        Seq.length veb == SZ.v eLen /\
        0 < SZ.v eLen /\ SZ.v eLen <= (U32.v modBits + 7) / 8 /\
        SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61 /\
        SZ.v sLen < pow2 32 /\ SZ.fits (8 + (hash_bytes sha2_512) + SZ.v sLen))
returns ok: bool
ensures A.pts_to nb #pnb vnb ** A.pts_to eb #peb veb **
        A.pts_to sgnt #psg vsg ** A.pts_to msg #pm vmsg **
        pure (ok <==> (1 < be_nat vnb /\ be_nat vnb % 2 == 1 /\ be_nat vsg < be_nat vnb /\
                       (exists (e: Seq.lseq S8.t (em_len (U32.v modBits - 1))).
                          be_nat e == rsa_pow (be_nat vsg) (be_nat veb) (be_nat vnb) /\
                          pss_valid sha2_512 (SZ.v sLen) (U32.v modBits - 1) vmsg e)))
{
  A.pts_to_len msg;
  max_input_bound ();
  assert_norm (8 + 64 + pow2 32 < pow2 61);
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  let r = rsapss_verify sha2_512 kt ivt modBits nb eLen eb sLen sgnt mLen msg;
  drop_table ivt;
  drop_table kt;
  r
}
