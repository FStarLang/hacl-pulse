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
open Hacl.RSAPSS.PSS

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Declassify = Hacl.Secret.Declassify
module Conv = Hacl.Bignum.Convert
module Mont = Hacl.Bignum.Montgomery
module Exp = Hacl.Bignum.Exponentiation

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
let limbs_of (len: nat) : nat = (len + 3) / 4

let limbs_of_ok (len: nat) : Lemma (len <= 4 * limbs_of len /\ limbs_of len <= (len + 3) / 4) = ()

(** [res <- be_nat b], left-padding [b] to the width of [res]. *)
fn bn_from_be (res: A.array S32.t) (nn: SZ.t) (b: A.array S8.t) (len: SZ.t)
              (#p: perm) (#vres: erased (Seq.seq S32.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to res vres ** A.pts_to b #p vb **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vb == SZ.v len /\
        SZ.v len <= 4 * SZ.v nn /\ SZ.fits (4 * SZ.v nn))
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v nn /\ num v == be_nat vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  let width = SZ.mul 4sz nn;
  let off = SZ.sub width len;
  let mut tmp = [| (zero8 <: S8.t); width |];
  A.pts_to_len tmp;
  (* The padding is at most three bytes, and writing it is cheaper than
     reasoning about what a stack allocation starts out holding. *)
  fill_range tmp 0sz off zero8;
  copy_at tmp off b len;
  with vt. assert (A.pts_to tmp vt);
  assert (pure (forall (i: nat). i < SZ.v off ==> S8.v (Seq.index vt i) == 0));
  be_nat_pad vt (SZ.v len);
  Seq.lemma_eq_intro (Seq.slice vt (SZ.v off) (SZ.v width)) (reveal vb);
  Conv.from_bytes_be res nn tmp;
}

(** [b <- the low [len] bytes of [a]], which are all of it. *)
fn bn_to_be (b: A.array S8.t) (len: SZ.t) (a: A.array S32.t) (nn: SZ.t)
            (#p: perm) (#vb: erased (Seq.seq S8.t)) (#va: erased (Seq.seq S32.t))
requires A.pts_to b vb ** A.pts_to a #p va **
  pure (Seq.length vb == SZ.v len /\ Seq.length va == SZ.v nn /\
        SZ.v len <= 4 * SZ.v nn /\ SZ.fits (4 * SZ.v nn) /\
        num va < pow2 (8 * SZ.v len))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to b v ** A.pts_to a #p va **
  pure (Seq.length v == SZ.v len /\ be_nat v == num va)
{
  A.pts_to_len b;
  A.pts_to_len a;
  let width = SZ.mul 4sz nn;
  let off = SZ.sub width len;
  let mut tmp = [| (zero8 <: S8.t); width |];
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
}

(** [res <- 1]. *)
fn bn_one (res: A.array S32.t) (nn: SZ.t) (#vres: erased (Seq.seq S32.t))
requires A.pts_to res vres ** pure (Seq.length vres == SZ.v nn /\ 0 < SZ.v nn)
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** pure (Seq.length v == SZ.v nn /\ num v == 1)
{
  A.pts_to_len res;
  zero res nn;
  with v0. assert (A.pts_to res v0);
  pre_zeros v0 (SZ.v nn);
  pre_full v0;
  let one = S32.classify 1ul;
  A.((res.(0sz) <- one));
  num_upd v0 0 one;
  wt_zero ();
}

(** A number is below the weight of its own width. *)
let num_bound (v: Seq.seq S32.t) : Lemma (num v < wt (Seq.length v))
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
let as_modulus (s: Seq.seq S32.t)
  : Pure (r: Seq.seq S32.t { 1 < num r }) (requires 1 < num s) (ensures fun r -> r == s)
  = s

(** [res <- a ^ be_nat eb mod n].

    The exponent is a byte string, as it comes out of a key, and is used to
    its full width: the loop counts bits of the buffer, not bits of the
    number, so that nothing about a private exponent leaks through a loop
    bound.  [ct] chooses the constant-time ladder; a public exponent may
    take the other one. *)
fn mod_exp_be (res: A.array S32.t) (a: A.array S32.t)
              (eb: A.array S8.t) (eLen: SZ.t) (en: SZ.t)
              (nmod: A.array S32.t) (nn: SZ.t) (ct: bool)
              (#vres: erased (Seq.seq S32.t)) (#pa #pe #pn: perm)
              (#va: erased (Seq.seq S32.t)) (#ve: erased (Seq.seq S8.t))
              (#vn: erased (s: Seq.seq S32.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to eb #pe ve **
         A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vn == SZ.v nn /\ Seq.length ve == SZ.v eLen /\
        0 < SZ.v nn /\ 0 < SZ.v en /\ 1 < num vn /\ SZ.v eLen <= 4 * SZ.v en /\
        SZ.fits (2 * rad * SZ.v nn) /\ SZ.fits (4 * SZ.v en) /\ SZ.fits (32 * SZ.v en) /\
        num va < num vn /\ S32.v (Seq.index vn 0) % 2 == 1)
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to eb #pe ve **
  A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ num v == pw (num va) (be_nat ve) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len eb;
  A.pts_to_len nmod;
  SZ.fits_lte (SZ.v nn + SZ.v nn) (2 * rad * SZ.v nn);
  let z32 = S32.zero;
  let mut ebn = [| z32; en |];
  let mut r2 = [| z32; nn |];
  let mut aM = [| z32; nn |];
  let mut accu = [| z32; nn |];
  let mut tn = [| z32; nn |];
  let mut wide = [| z32; SZ.add nn nn |];
  A.pts_to_len ebn;
  A.pts_to_len r2;
  A.pts_to_len aM;
  A.pts_to_len accu;
  A.pts_to_len tn;
  A.pts_to_len wide;
  bn_from_be ebn en eb eLen;
  with vebn. assert (A.pts_to ebn vebn);
  num_bound vebn;
  Mont.precomp r2 nmod nn #_ #_ #(hide (as_modulus (reveal vn)));
  let n0 = A.(nmod.(0sz));
  let mu = Mont.mont_mu n0;
  let bbits = SZ.mul 32sz en;
  assert (pure (wt (SZ.v en) == pow2 (SZ.v bbits)));
  if ct {
    Exp.mod_exp_consttime res a ebn bbits r2 nmod nn mu aM accu tn wide;
  } else {
    Exp.mod_exp_vartime res a ebn bbits r2 nmod nn mu aM accu tn wide;
  }
}

#pop-options
