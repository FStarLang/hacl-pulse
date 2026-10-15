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

(** Finite-field Diffie-Hellman over the RFC 7919 groups.

    The whole of FFDHE is one modular exponentiation with the generator two,
    so this module is thin: it converts the big-endian byte strings the
    protocol speaks into limbs, calls
    {!Hacl.Bignum.Exponentiation.mod_exp_consttime}, and converts back.  The
    interesting part is the peer-key validation, which is what stops a
    small-subgroup attack.

    {b Constant time.}  The exponentiation is the constant-time ladder: the
    secret is the exponent, and its bits must not be observable.  Peer-key
    validation is the one place a secret-looking value is declassified, and
    it is sound because the peer's key is public: it arrived over the wire.

    {b Nothing allocates and nothing is precomputed across calls.}  HACL*
    offers a [_precomp] variant so that a server can amortize [R^2 mod p]
    over many handshakes.  The two exist here as well -- the [_precomp] core
    is what every group's entry point calls -- but the per-group entry points
    do the precomputation themselves, because it is a doubling chain of
    [2*bits] steps against an exponentiation of [bits] rungs each costing a
    full multiply, which is to say a few tenths of a percent. *)
module Hacl.FFDHE

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Spec.FFDHE
open Hacl.Spec.Bytes
open Hacl.Bignum.Base
open Hacl.Bignum.Convert
open Hacl.Bignum.Montgomery
open Hacl.Bignum.Exponentiation
open Hacl.Impl.Table
open Hacl.FFDHE.Tables

module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Declassify = Hacl.Secret.Declassify

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 Facts about a modulus whose ends are all ones}

    Every FFDHE prime is congruent to [-1] modulo [2^64] and has its top bit
    set, so its lowest and highest limbs are both [2^32 - 1].  Those two
    literals are all the implementation needs to know about the group: the
    first says the modulus is odd, which is what Montgomery arithmetic
    requires, and the second says it is large, which is what makes the
    generator smaller than it. *)

(** A modulus with a full top limb is bigger than the generator, without
    anyone having to evaluate the other limbs. *)
let modulus_big (v: Seq.seq S64.t) (k: nat { k < Seq.length v })
  : Lemma (requires S64.v (Seq.index v k) == pow2 64 - 1)
          (ensures 2 < num v)
  = num_top v k;
    Math.lemma_mult_le_right (pow2 64 - 1) 1 (wt k)

(** [p - 1] comes out of a subtraction with no borrow, because [p] is at
    least two. *)
let no_borrow (pN e c w: int)
  : Lemma (requires pN + c * w == e + 1 /\ 0 <= c /\ c <= 1 /\ 2 < pN /\
                    0 <= e /\ e < w)
          (ensures e == pN - 1)
  = ()

(** The declassified comparison mask is a [bool] with the obvious meaning. *)
let mask_ones () : Lemma (pow2 64 - 1 == 18446744073709551615) = assert_norm (pow2 64 - 1 == 18446744073709551615)

(** What {!mont_mu} promises, recalled as a lemma so that each group's entry
    point need not dig it out of the refinement on [mu]'s type. *)
let mu_spec (m0: S64.t { S64.v m0 % 2 == 1 }) (mu: S64.t)
  : Lemma (requires mu == mont_mu m0)
          (ensures (S64.v mu * S64.v m0 + 1) % base == 0)
  = ()


(** {2 The two operations, over any group}

    [nn] is the modulus length in limbs and the byte strings are [8 * nn]
    bytes, which is the group size: FFDHE fixes both, so there is no
    length negotiation and no short encoding. *)

#push-options "--z3rlimit 200"

(** [secret_to_public_precomp pk sk p r2 nn mu ...] is [pk = 2^sk mod p],
    the public key for the secret [sk].  Both byte strings are big-endian
    and exactly the group size. *)
fn secret_to_public_precomp (pk: A.array S8.t) (sk: A.array S8.t)
                            (p: A.array S64.t) (r2: A.array S64.t)
                            (nn: SZ.t) (mu: S64.t)
                            (g: A.array S64.t) (e: A.array S64.t)
                            (res: A.array S64.t)
                            (aM: A.array S64.t) (acc: A.array S64.t)
                            (t: A.array S64.t) (wide: A.array S64.t)
                            (#vpk: erased (Seq.seq S8.t))
                            (#psk: perm) (#vsk: erased (Seq.seq S8.t))
                            (#pp #pr: perm) (#vr2: erased (Seq.seq S64.t))
                            (#vg #ve #vres #vaM #vacc #vt #vwide: erased (Seq.seq S64.t))
                            (#vp: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to pk vpk ** A.pts_to sk #psk vsk **
         A.pts_to p #pp vp ** A.pts_to r2 #pr vr2 **
         A.pts_to g vg ** A.pts_to e ve ** A.pts_to res vres **
         A.pts_to aM vaM ** A.pts_to acc vacc ** A.pts_to t vt **
         A.pts_to wide vwide **
  pure (Seq.length vpk == 8 * SZ.v nn /\ Seq.length vsk == 8 * SZ.v nn /\
        Seq.length vp == SZ.v nn /\ Seq.length vr2 == SZ.v nn /\
        Seq.length vg == SZ.v nn /\ Seq.length ve == SZ.v nn /\
        Seq.length vres == SZ.v nn /\ Seq.length vaM == SZ.v nn /\
        Seq.length vacc == SZ.v nn /\ Seq.length vt == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (8 * SZ.v nn) /\ SZ.fits (64 * SZ.v nn) /\
        SZ.fits (SZ.v nn + SZ.v nn) /\
        2 < num vp /\
        num vr2 == (wt (SZ.v nn) * wt (SZ.v nn)) % num vp /\
        (S64.v mu * S64.v (Seq.index vp 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S8.t)
                (v0 v1 v2 v3 v4 v5 v6: Seq.seq S64.t).
  A.pts_to pk v ** A.pts_to sk #psk vsk **
  A.pts_to p #pp vp ** A.pts_to r2 #pr vr2 **
  A.pts_to g v0 ** A.pts_to e v1 ** A.pts_to res v2 **
  A.pts_to aM v3 ** A.pts_to acc v4 ** A.pts_to t v5 ** A.pts_to wide v6 **
  pure (Seq.length v == 8 * SZ.v nn /\ Seq.length v0 == SZ.v nn /\
        Seq.length v1 == SZ.v nn /\ Seq.length v2 == SZ.v nn /\
        Seq.length v3 == SZ.v nn /\ Seq.length v4 == SZ.v nn /\
        Seq.length v5 == SZ.v nn /\ Seq.length v6 == SZ.v nn + SZ.v nn /\
        be_nat v == pw 2 (be_nat vsk) % num vp)
{
  A.pts_to_len pk;
  A.pts_to_len sk;
  A.pts_to_len p;
  A.pts_to_len r2;
  A.pts_to_len g;
  A.pts_to_len e;
  A.pts_to_len res;
  A.pts_to_len aM;
  A.pts_to_len acc;
  A.pts_to_len t;
  A.pts_to_len wide;

  (* The generator, as a bignum. *)
  zero g nn;
  with vg0. assert (A.pts_to g vg0);
  num_zeros_above vg0 0;
  pre_zero vg0;
  A.((g.(0sz) <- S64.classify 2uL));
  num_upd vg0 0 (S64.classify 2uL);
  with vg1. assert (A.pts_to g vg1);
  assert (pure (num vg1 == 2));

  (* The secret, as a bignum: [8 * nn] big-endian bytes are [nn] limbs. *)
  from_bytes_be e nn sk;
  with ve1. assert (A.pts_to e ve1);
  pre_bnd ve1 (SZ.v nn);
  pre_full ve1;

  SZ.fits_lte (16 * SZ.v nn) (64 * SZ.v nn);
  mul64_mod4 (SZ.v nn);
  mod_exp_consttime res g e (SZ.mul 64sz nn) r2 p nn mu aM acc t wide;
  with vres1. assert (A.pts_to res vres1);
  to_bytes_be pk res nn;
  ()
}

(** [shared_secret_precomp ss sk pk p r2 nn mu ...] validates the peer's
    public key and, if it is good, writes [ss = pk^sk mod p].  It returns
    whether the key was good; on a bad key [ss] is zeroed.

    Validation is [1 < pk < p - 1].  Rejecting [0], [1] and [p - 1] rules
    out the three elements of small order, which is what stops a peer from
    forcing a shared secret it already knows. *)
fn shared_secret_precomp (ss: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
                         (p: A.array S64.t) (r2: A.array S64.t)
                         (nn: SZ.t) (mu: S64.t)
                         (a: A.array S64.t) (e: A.array S64.t)
                         (res: A.array S64.t)
                         (aM: A.array S64.t) (acc: A.array S64.t)
                         (t: A.array S64.t) (wide: A.array S64.t)
                         (#vss: erased (Seq.seq S8.t))
                         (#psk #ppk: perm)
                         (#vsk #vpk: erased (Seq.seq S8.t))
                         (#pp #pr: perm) (#vr2: erased (Seq.seq S64.t))
                         (#va #ve #vres #vaM #vacc #vt #vwide: erased (Seq.seq S64.t))
                         (#vp: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to ss vss ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
         A.pts_to p #pp vp ** A.pts_to r2 #pr vr2 **
         A.pts_to a va ** A.pts_to e ve ** A.pts_to res vres **
         A.pts_to aM vaM ** A.pts_to acc vacc ** A.pts_to t vt **
         A.pts_to wide vwide **
  pure (Seq.length vss == 8 * SZ.v nn /\ Seq.length vsk == 8 * SZ.v nn /\
        Seq.length vpk == 8 * SZ.v nn /\
        Seq.length vp == SZ.v nn /\ Seq.length vr2 == SZ.v nn /\
        Seq.length va == SZ.v nn /\ Seq.length ve == SZ.v nn /\
        Seq.length vres == SZ.v nn /\ Seq.length vaM == SZ.v nn /\
        Seq.length vacc == SZ.v nn /\ Seq.length vt == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (8 * SZ.v nn) /\ SZ.fits (64 * SZ.v nn) /\
        SZ.fits (SZ.v nn + SZ.v nn) /\
        2 < num vp /\
        num vr2 == (wt (SZ.v nn) * wt (SZ.v nn)) % num vp /\
        (S64.v mu * S64.v (Seq.index vp 0) + 1) % base == 0)
returns ok: bool
ensures exists* (v: Seq.seq S8.t)
                (v0 v1 v2 v3 v4 v5 v6: Seq.seq S64.t).
  A.pts_to ss v ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  A.pts_to p #pp vp ** A.pts_to r2 #pr vr2 **
  A.pts_to a v0 ** A.pts_to e v1 ** A.pts_to res v2 **
  A.pts_to aM v3 ** A.pts_to acc v4 ** A.pts_to t v5 ** A.pts_to wide v6 **
  pure (Seq.length v == 8 * SZ.v nn /\ Seq.length v0 == SZ.v nn /\
        Seq.length v1 == SZ.v nn /\ Seq.length v2 == SZ.v nn /\
        Seq.length v3 == SZ.v nn /\ Seq.length v4 == SZ.v nn /\
        Seq.length v5 == SZ.v nn /\ Seq.length v6 == SZ.v nn + SZ.v nn /\
        (ok <==> (1 < be_nat vpk /\ be_nat vpk < num vp - 1)) /\
        (if ok then be_nat v == pw (be_nat vpk) (be_nat vsk) % num vp
         else be_nat v == 0))
{
  A.pts_to_len ss;
  A.pts_to_len sk;
  A.pts_to_len pk;
  A.pts_to_len p;
  A.pts_to_len r2;
  A.pts_to_len a;
  A.pts_to_len e;
  A.pts_to_len res;
  A.pts_to_len aM;
  A.pts_to_len acc;
  A.pts_to_len t;
  A.pts_to_len wide;
  mask_ones ();

  from_bytes_be a nn pk;
  with va1. assert (A.pts_to a va1);
  pre_bnd va1 (SZ.v nn);
  pre_full va1;

  (* One, and [p - 1], in two arrays that the ladder will reuse as scratch. *)
  zero aM nn;
  with vone0. assert (A.pts_to aM vone0);
  num_zeros_above vone0 0;
  pre_zero vone0;
  A.((aM.(0sz) <- S64.classify 1uL));
  num_upd vone0 0 (S64.classify 1uL);
  with vone. assert (A.pts_to aM vone);
  assert (pure (num vone == 1));

  let c = sub acc p aM nn;
  with vpm1. assert (A.pts_to acc vpm1);
  pre_bnd vpm1 (SZ.v nn);
  pre_full vpm1;
  no_borrow (num vp) (num vpm1) (S64.v c) (wt (SZ.v nn));
  assert (pure (num vpm1 == num vp - 1));

  let m1 = lt_mask aM a nn;
  let m2 = lt_mask a acc nn;
  let ok1 = U64.eq (Declassify.u64 m1) 18446744073709551615uL;
  let ok2 = U64.eq (Declassify.u64 m2) 18446744073709551615uL;
  let good = ok1 && ok2;

  if good
  {
    from_bytes_be e nn sk;
    with ve1. assert (A.pts_to e ve1);
    pre_bnd ve1 (SZ.v nn);
    pre_full ve1;
    SZ.fits_lte (16 * SZ.v nn) (64 * SZ.v nn);
    mul64_mod4 (SZ.v nn);
    mod_exp_consttime res a e (SZ.mul 64sz nn) r2 p nn mu aM acc t wide;
    to_bytes_be ss res nn;
    true
  }
  else
  {
    zero res nn;
    with vz. assert (A.pts_to res vz);
    num_zeros_above vz 0;
    pre_zero vz;
    to_bytes_be ss res nn;
    false
  }
}

#pop-options


(** {2 The five groups}

    One entry point per group per direction.  There is no algorithm
    identifier and no dispatch: the group is in the name, so a caller that
    uses one group links one modulus and one set of loop bounds, and a
    caller that passes a wrong-sized buffer has a bug the C compiler cannot
    see but the F* one can.

    Each group contributes one fact: its modulus has [2^32 - 1] at both
    ends, which is what says it is odd and what says it is large.  It
    arrives as a ghost accessor rather than as a lemma because the
    postconditions below reduce modulo the group, and a Pulse [ensures] is
    typechecked with no precondition in scope: the modulus has to be known
    non-zero from its *type*, which is what the [pos] here says.

    The scratch is eight arrays -- seven of [nn] limbs and one of [2*nn] --
    and it is on the stack, because at this point the size is a constant.
    That is the one place in the library where an array is not the caller's:
    an entry point named for a group knows how big the group is. *)

(** {3 FFDHE-2048} *)

let ffdhe2048_mod () : GTot (p: pos { p == num ffdhe2048 /\ 2 < p }) =
  ffdhe2048_ends ();
  modulus_big ffdhe2048 31;
  num ffdhe2048

#push-options "--z3rlimit 200"

(** [ffdhe2048_secret_to_public pk sk] is [pk = 2^sk mod p] over FFDHE-2048.
    Both arrays are 256 big-endian bytes. *)
fn ffdhe2048_secret_to_public (pk: A.array S8.t) (sk: A.array S8.t)
                              (#vpk: erased (Seq.seq S8.t))
                              (#psk: perm) (#vsk: erased (Seq.seq S8.t))
requires A.pts_to pk vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length vpk == 256 /\ Seq.length vsk == 256)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to pk v ** A.pts_to sk #psk vsk **
  pure (Seq.length v == 256 /\ be_nat v == pw 2 (be_nat vsk) % ffdhe2048_mod ())
{
  ffdhe2048_ends ();
  modulus_big ffdhe2048 31;
  let p = table ffdhe2048_arr 32sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe2048_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 32sz |];
  let mut g = [| z; 32sz |];
  let mut e = [| z; 32sz |];
  let mut res = [| z; 32sz |];
  let mut aM = [| z; 32sz |];
  let mut acc = [| z; 32sz |];
  let mut t = [| z; 32sz |];
  let mut wide = [| z; 64sz |];
  precomp r2 acc t wide p 32sz mu;
  secret_to_public_precomp pk sk p r2 32sz mu g e res aM acc t wide;
  drop_table p;
}

(** [ffdhe2048_shared_secret ss sk pk] validates the peer's key and, if it is
    good, writes [ss = pk^sk mod p] over FFDHE-2048.  All three arrays are
    256 big-endian bytes. *)
fn ffdhe2048_shared_secret (ss: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
                           (#vss: erased (Seq.seq S8.t))
                           (#psk #ppk: perm)
                           (#vsk #vpk: erased (Seq.seq S8.t))
requires A.pts_to ss vss ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length vss == 256 /\ Seq.length vsk == 256 /\ Seq.length vpk == 256)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to ss v ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length v == 256 /\
        (ok <==> (1 < be_nat vpk /\ be_nat vpk < ffdhe2048_mod () - 1)) /\
        (if ok then be_nat v == pw (be_nat vpk) (be_nat vsk) % ffdhe2048_mod ()
         else be_nat v == 0))
{
  ffdhe2048_ends ();
  modulus_big ffdhe2048 31;
  let p = table ffdhe2048_arr 32sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe2048_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 32sz |];
  let mut a = [| z; 32sz |];
  let mut e = [| z; 32sz |];
  let mut res = [| z; 32sz |];
  let mut aM = [| z; 32sz |];
  let mut acc = [| z; 32sz |];
  let mut t = [| z; 32sz |];
  let mut wide = [| z; 64sz |];
  precomp r2 acc t wide p 32sz mu;
  let ok = shared_secret_precomp ss sk pk p r2 32sz mu a e res aM acc t wide;
  drop_table p;
  ok
}

#pop-options

(** {3 FFDHE-3072} *)

let ffdhe3072_mod () : GTot (p: pos { p == num ffdhe3072 /\ 2 < p }) =
  ffdhe3072_ends ();
  modulus_big ffdhe3072 47;
  num ffdhe3072

#push-options "--z3rlimit 200"

(** [ffdhe3072_secret_to_public pk sk] is [pk = 2^sk mod p] over FFDHE-3072.
    Both arrays are 384 big-endian bytes. *)
fn ffdhe3072_secret_to_public (pk: A.array S8.t) (sk: A.array S8.t)
                              (#vpk: erased (Seq.seq S8.t))
                              (#psk: perm) (#vsk: erased (Seq.seq S8.t))
requires A.pts_to pk vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length vpk == 384 /\ Seq.length vsk == 384)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to pk v ** A.pts_to sk #psk vsk **
  pure (Seq.length v == 384 /\ be_nat v == pw 2 (be_nat vsk) % ffdhe3072_mod ())
{
  ffdhe3072_ends ();
  modulus_big ffdhe3072 47;
  let p = table ffdhe3072_arr 48sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe3072_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 48sz |];
  let mut g = [| z; 48sz |];
  let mut e = [| z; 48sz |];
  let mut res = [| z; 48sz |];
  let mut aM = [| z; 48sz |];
  let mut acc = [| z; 48sz |];
  let mut t = [| z; 48sz |];
  let mut wide = [| z; 96sz |];
  precomp r2 acc t wide p 48sz mu;
  secret_to_public_precomp pk sk p r2 48sz mu g e res aM acc t wide;
  drop_table p;
}

(** [ffdhe3072_shared_secret ss sk pk] validates the peer's key and, if it is
    good, writes [ss = pk^sk mod p] over FFDHE-3072.  All three arrays are
    384 big-endian bytes. *)
fn ffdhe3072_shared_secret (ss: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
                           (#vss: erased (Seq.seq S8.t))
                           (#psk #ppk: perm)
                           (#vsk #vpk: erased (Seq.seq S8.t))
requires A.pts_to ss vss ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length vss == 384 /\ Seq.length vsk == 384 /\ Seq.length vpk == 384)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to ss v ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length v == 384 /\
        (ok <==> (1 < be_nat vpk /\ be_nat vpk < ffdhe3072_mod () - 1)) /\
        (if ok then be_nat v == pw (be_nat vpk) (be_nat vsk) % ffdhe3072_mod ()
         else be_nat v == 0))
{
  ffdhe3072_ends ();
  modulus_big ffdhe3072 47;
  let p = table ffdhe3072_arr 48sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe3072_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 48sz |];
  let mut a = [| z; 48sz |];
  let mut e = [| z; 48sz |];
  let mut res = [| z; 48sz |];
  let mut aM = [| z; 48sz |];
  let mut acc = [| z; 48sz |];
  let mut t = [| z; 48sz |];
  let mut wide = [| z; 96sz |];
  precomp r2 acc t wide p 48sz mu;
  let ok = shared_secret_precomp ss sk pk p r2 48sz mu a e res aM acc t wide;
  drop_table p;
  ok
}

#pop-options

(** {3 FFDHE-4096} *)

let ffdhe4096_mod () : GTot (p: pos { p == num ffdhe4096 /\ 2 < p }) =
  ffdhe4096_ends ();
  modulus_big ffdhe4096 63;
  num ffdhe4096

#push-options "--z3rlimit 200"

(** [ffdhe4096_secret_to_public pk sk] is [pk = 2^sk mod p] over FFDHE-4096.
    Both arrays are 512 big-endian bytes. *)
fn ffdhe4096_secret_to_public (pk: A.array S8.t) (sk: A.array S8.t)
                              (#vpk: erased (Seq.seq S8.t))
                              (#psk: perm) (#vsk: erased (Seq.seq S8.t))
requires A.pts_to pk vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length vpk == 512 /\ Seq.length vsk == 512)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to pk v ** A.pts_to sk #psk vsk **
  pure (Seq.length v == 512 /\ be_nat v == pw 2 (be_nat vsk) % ffdhe4096_mod ())
{
  ffdhe4096_ends ();
  modulus_big ffdhe4096 63;
  let p = table ffdhe4096_arr 64sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe4096_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 64sz |];
  let mut g = [| z; 64sz |];
  let mut e = [| z; 64sz |];
  let mut res = [| z; 64sz |];
  let mut aM = [| z; 64sz |];
  let mut acc = [| z; 64sz |];
  let mut t = [| z; 64sz |];
  let mut wide = [| z; 128sz |];
  precomp r2 acc t wide p 64sz mu;
  secret_to_public_precomp pk sk p r2 64sz mu g e res aM acc t wide;
  drop_table p;
}

(** [ffdhe4096_shared_secret ss sk pk] validates the peer's key and, if it is
    good, writes [ss = pk^sk mod p] over FFDHE-4096.  All three arrays are
    512 big-endian bytes. *)
fn ffdhe4096_shared_secret (ss: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
                           (#vss: erased (Seq.seq S8.t))
                           (#psk #ppk: perm)
                           (#vsk #vpk: erased (Seq.seq S8.t))
requires A.pts_to ss vss ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length vss == 512 /\ Seq.length vsk == 512 /\ Seq.length vpk == 512)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to ss v ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length v == 512 /\
        (ok <==> (1 < be_nat vpk /\ be_nat vpk < ffdhe4096_mod () - 1)) /\
        (if ok then be_nat v == pw (be_nat vpk) (be_nat vsk) % ffdhe4096_mod ()
         else be_nat v == 0))
{
  ffdhe4096_ends ();
  modulus_big ffdhe4096 63;
  let p = table ffdhe4096_arr 64sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe4096_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 64sz |];
  let mut a = [| z; 64sz |];
  let mut e = [| z; 64sz |];
  let mut res = [| z; 64sz |];
  let mut aM = [| z; 64sz |];
  let mut acc = [| z; 64sz |];
  let mut t = [| z; 64sz |];
  let mut wide = [| z; 128sz |];
  precomp r2 acc t wide p 64sz mu;
  let ok = shared_secret_precomp ss sk pk p r2 64sz mu a e res aM acc t wide;
  drop_table p;
  ok
}

#pop-options

(** {3 FFDHE-6144} *)

let ffdhe6144_mod () : GTot (p: pos { p == num ffdhe6144 /\ 2 < p }) =
  ffdhe6144_ends ();
  modulus_big ffdhe6144 95;
  num ffdhe6144

#push-options "--z3rlimit 200"

(** [ffdhe6144_secret_to_public pk sk] is [pk = 2^sk mod p] over FFDHE-6144.
    Both arrays are 768 big-endian bytes. *)
fn ffdhe6144_secret_to_public (pk: A.array S8.t) (sk: A.array S8.t)
                              (#vpk: erased (Seq.seq S8.t))
                              (#psk: perm) (#vsk: erased (Seq.seq S8.t))
requires A.pts_to pk vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length vpk == 768 /\ Seq.length vsk == 768)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to pk v ** A.pts_to sk #psk vsk **
  pure (Seq.length v == 768 /\ be_nat v == pw 2 (be_nat vsk) % ffdhe6144_mod ())
{
  ffdhe6144_ends ();
  modulus_big ffdhe6144 95;
  let p = table ffdhe6144_arr 96sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe6144_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 96sz |];
  let mut g = [| z; 96sz |];
  let mut e = [| z; 96sz |];
  let mut res = [| z; 96sz |];
  let mut aM = [| z; 96sz |];
  let mut acc = [| z; 96sz |];
  let mut t = [| z; 96sz |];
  let mut wide = [| z; 192sz |];
  precomp r2 acc t wide p 96sz mu;
  secret_to_public_precomp pk sk p r2 96sz mu g e res aM acc t wide;
  drop_table p;
}

(** [ffdhe6144_shared_secret ss sk pk] validates the peer's key and, if it is
    good, writes [ss = pk^sk mod p] over FFDHE-6144.  All three arrays are
    768 big-endian bytes. *)
fn ffdhe6144_shared_secret (ss: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
                           (#vss: erased (Seq.seq S8.t))
                           (#psk #ppk: perm)
                           (#vsk #vpk: erased (Seq.seq S8.t))
requires A.pts_to ss vss ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length vss == 768 /\ Seq.length vsk == 768 /\ Seq.length vpk == 768)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to ss v ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length v == 768 /\
        (ok <==> (1 < be_nat vpk /\ be_nat vpk < ffdhe6144_mod () - 1)) /\
        (if ok then be_nat v == pw (be_nat vpk) (be_nat vsk) % ffdhe6144_mod ()
         else be_nat v == 0))
{
  ffdhe6144_ends ();
  modulus_big ffdhe6144 95;
  let p = table ffdhe6144_arr 96sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe6144_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 96sz |];
  let mut a = [| z; 96sz |];
  let mut e = [| z; 96sz |];
  let mut res = [| z; 96sz |];
  let mut aM = [| z; 96sz |];
  let mut acc = [| z; 96sz |];
  let mut t = [| z; 96sz |];
  let mut wide = [| z; 192sz |];
  precomp r2 acc t wide p 96sz mu;
  let ok = shared_secret_precomp ss sk pk p r2 96sz mu a e res aM acc t wide;
  drop_table p;
  ok
}

#pop-options

(** {3 FFDHE-8192} *)

let ffdhe8192_mod () : GTot (p: pos { p == num ffdhe8192 /\ 2 < p }) =
  ffdhe8192_ends ();
  modulus_big ffdhe8192 127;
  num ffdhe8192

#push-options "--z3rlimit 200"

(** [ffdhe8192_secret_to_public pk sk] is [pk = 2^sk mod p] over FFDHE-8192.
    Both arrays are 1024 big-endian bytes. *)
fn ffdhe8192_secret_to_public (pk: A.array S8.t) (sk: A.array S8.t)
                              (#vpk: erased (Seq.seq S8.t))
                              (#psk: perm) (#vsk: erased (Seq.seq S8.t))
requires A.pts_to pk vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length vpk == 1024 /\ Seq.length vsk == 1024)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to pk v ** A.pts_to sk #psk vsk **
  pure (Seq.length v == 1024 /\ be_nat v == pw 2 (be_nat vsk) % ffdhe8192_mod ())
{
  ffdhe8192_ends ();
  modulus_big ffdhe8192 127;
  let p = table ffdhe8192_arr 128sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe8192_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 128sz |];
  let mut g = [| z; 128sz |];
  let mut e = [| z; 128sz |];
  let mut res = [| z; 128sz |];
  let mut aM = [| z; 128sz |];
  let mut acc = [| z; 128sz |];
  let mut t = [| z; 128sz |];
  let mut wide = [| z; 256sz |];
  precomp r2 acc t wide p 128sz mu;
  secret_to_public_precomp pk sk p r2 128sz mu g e res aM acc t wide;
  drop_table p;
}

(** [ffdhe8192_shared_secret ss sk pk] validates the peer's key and, if it is
    good, writes [ss = pk^sk mod p] over FFDHE-8192.  All three arrays are
    1024 big-endian bytes. *)
fn ffdhe8192_shared_secret (ss: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
                           (#vss: erased (Seq.seq S8.t))
                           (#psk #ppk: perm)
                           (#vsk #vpk: erased (Seq.seq S8.t))
requires A.pts_to ss vss ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length vss == 1024 /\ Seq.length vsk == 1024 /\ Seq.length vpk == 1024)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to ss v ** A.pts_to sk #psk vsk ** A.pts_to pk #ppk vpk **
  pure (Seq.length v == 1024 /\
        (ok <==> (1 < be_nat vpk /\ be_nat vpk < ffdhe8192_mod () - 1)) /\
        (if ok then be_nat v == pw (be_nat vpk) (be_nat vsk) % ffdhe8192_mod ()
         else be_nat v == 0))
{
  ffdhe8192_ends ();
  modulus_big ffdhe8192 127;
  let p = table ffdhe8192_arr 128sz;
  A.pts_to_len p;
  let m0 = A.(p.(0sz));
  let mu = mont_mu m0;
  mu_spec m0 mu;
  assert (pure ((S64.v mu * S64.v (Seq.index (G.static_array_elems ffdhe8192_arr) 0) + 1) % base == 0));
  let z = S64.zero;
  let mut r2 = [| z; 128sz |];
  let mut a = [| z; 128sz |];
  let mut e = [| z; 128sz |];
  let mut res = [| z; 128sz |];
  let mut aM = [| z; 128sz |];
  let mut acc = [| z; 128sz |];
  let mut t = [| z; 128sz |];
  let mut wide = [| z; 256sz |];
  precomp r2 acc t wide p 128sz mu;
  let ok = shared_secret_precomp ss sk pk p r2 128sz mu a e res aM acc t wide;
  drop_table p;
  ok
}

#pop-options

#pop-options
