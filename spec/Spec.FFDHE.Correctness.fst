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

(** Key agreement for finite-field Diffie-Hellman: two honest parties end up
    with the same shared secret.

    {!Hacl.FFDHE} has no functional specification beyond its postconditions,
    which say, over a group with modulus [p] and the generator two,

    {[ be_nat pk == pw 2 (be_nat sk) % p ]}

    for [secret_to_public], and for [shared_secret] that it returns [ok]
    exactly when [1 < be_nat pk < p - 1] and then writes
    [be_nat ss == pw (be_nat pk) (be_nat sk) % p].  The statements below are
    phrased in exactly those terms, so that a caller holding the two
    postconditions can chain them.

    The headline is [dh_agree]:

    {[ pw (pw g b % p) a % p == pw (pw g a % p) b % p ]}

    for any generator and any positive modulus -- no primality is needed.
    The proof is two facts about [pw]: reducing the base modulo [p] does not
    change the power modulo [p] ([pw_mod]), and a power of a power is the
    power of the product ([pw_pw]); then [a * b == b * a].

    Then [agree_bytes] lifts it to the byte strings the implementation
    writes: both secrets are the same number, and big-endian writing at a
    fixed width is injective ({!Spec.RSAPSS.be_nat_inj}), so they are the
    same bytes.  Finally there is one corollary per RFC 7919 group, stated
    over that group's own byte width.

    {b What is not proved.}  The responder's acceptance check
    [1 < pk < p - 1] holds for an honest public key [2^a mod p] exactly when
    [2^a mod p] is none of [0], [1] and [p - 1].  Showing that for a given
    range of [a] needs [p] prime and [2] of large order, which
    {!Spec.FFDHE} establishes only by testing, not by proof.  So agreement
    is stated conditionally on both checks passing. *)
module Spec.FFDHE.Correctness

open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Bignum.Base
open Spec.FFDHE

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(** {2 Powers modulo [p]} *)

#push-options "--fuel 1"

let rec pw_mod (a: nat) (k: nat) (p: pos)
  : Lemma (ensures pw (a % p) k % p == pw a k % p) (decreases k)
  = if k = 0 then ()
    else begin
      pw_mod a (k - 1) p;
      Math.lemma_mod_mul_distr_r (a % p) (pw (a % p) (k - 1)) p;
      Math.lemma_mod_mul_distr_r (a % p) (pw a (k - 1)) p;
      Math.lemma_mod_mul_distr_l a (pw a (k - 1)) p
    end

let rec pw_pw (a: nat) (b c: nat)
  : Lemma (ensures pw (pw a b) c == pw a (b * c)) (decreases c)
  = if c = 0 then ()
    else begin
      pw_pw a b (c - 1);
      pw_add a b (b * (c - 1));
      Math.distributivity_sub_right b c 1
    end

#pop-options

(** {2 Agreement over any group} *)

(** Each party raises the other's public value to its own secret. *)
let dh_agree (g: nat) (p: pos) (a b: nat)
  : Lemma (pw (pw g b % p) a % p == pw (pw g a % p) b % p)
  = pw_mod (pw g b) a p;
    pw_mod (pw g a) b p;
    pw_pw g b a;
    pw_pw g a b;
    Math.swap_mul a b

(** The same at the level of the implementation's byte strings.  [pkA] and
    [pkB] are what [secret_to_public] wrote for the secrets [skA] and [skB];
    [ssA] is what [shared_secret] wrote for [A] from [B]'s public key, and
    [ssB] the other way round. *)
let agree_bytes (p: pos) (len: nat) (skA skB pkA pkB ssA ssB: Seq.seq S8.t)
  : Lemma (requires Seq.length ssA == len /\ Seq.length ssB == len /\
                    be_nat pkA == pw 2 (be_nat skA) % p /\
                    be_nat pkB == pw 2 (be_nat skB) % p /\
                    be_nat ssA == pw (be_nat pkB) (be_nat skA) % p /\
                    be_nat ssB == pw (be_nat pkA) (be_nat skB) % p)
          (ensures ssA == ssB)
  = dh_agree 2 p (be_nat skA) (be_nat skB);
    Spec.RSAPSS.be_nat_inj ssA ssB;
    Seq.lemma_eq_elim ssA ssB

(** The postconditions of the two [shared_secret] calls, verbatim, with
    both checks passing. *)
let agree_checked (p: pos) (len: nat) (skA skB pkA pkB ssA ssB: Seq.seq S8.t)
                  (okA okB: bool)
  : Lemma (requires Seq.length ssA == len /\ Seq.length ssB == len /\
                    be_nat pkA == pw 2 (be_nat skA) % p /\
                    be_nat pkB == pw 2 (be_nat skB) % p /\
                    (okA <==> (1 < be_nat pkB /\ be_nat pkB < p - 1)) /\
                    (if okA then be_nat ssA == pw (be_nat pkB) (be_nat skA) % p
                     else be_nat ssA == 0) /\
                    (okB <==> (1 < be_nat pkA /\ be_nat pkA < p - 1)) /\
                    (if okB then be_nat ssB == pw (be_nat pkA) (be_nat skB) % p
                     else be_nat ssB == 0) /\
                    okA /\ okB)
          (ensures ssA == ssB)
  = agree_bytes p len skA skB pkA pkB ssA ssB


(** {2 The five groups}

    Each accessor is the group's modulus as a [pos], which is what lets a
    statement reduce modulo it.  The implementation's [ffdheN_mod ()] has the
    refinement [p == num ffdheN], so it is this same number. *)

let modulus_pos (v: Seq.seq S64.t) (k: nat { k < Seq.length v })
  : Lemma (requires S64.v (Seq.index v k) == pow2 64 - 1) (ensures 0 < num v)
  = num_top v k;
    Math.lemma_mult_le_right (pow2 64 - 1) 1 (wt k)

(** Agreement over a group given by its limbs, for byte strings of the
    group's size. *)
unfold let group_agreement (p: pos) (len: nat)
                           (skA skB pkA pkB ssA ssB: Seq.seq S8.t) (okA okB: bool) : prop =
  Seq.length ssA == len /\ Seq.length ssB == len /\
  be_nat pkA == pw 2 (be_nat skA) % p /\
  be_nat pkB == pw 2 (be_nat skB) % p /\
  (okA <==> (1 < be_nat pkB /\ be_nat pkB < p - 1)) /\
  (if okA then be_nat ssA == pw (be_nat pkB) (be_nat skA) % p else be_nat ssA == 0) /\
  (okB <==> (1 < be_nat pkA /\ be_nat pkA < p - 1)) /\
  (if okB then be_nat ssB == pw (be_nat pkA) (be_nat skB) % p else be_nat ssB == 0)

(** {3 FFDHE-2048} *)

let ffdhe2048_p () : GTot (p: pos { p == num ffdhe2048 }) =
  ffdhe2048_ends (); modulus_pos ffdhe2048 31; num ffdhe2048

let ffdhe2048_agree (skA skB pkA pkB ssA ssB: Seq.seq S8.t) (okA okB: bool)
  : Lemma (requires group_agreement (ffdhe2048_p ()) 256 skA skB pkA pkB ssA ssB okA okB /\
                    okA /\ okB)
          (ensures ssA == ssB)
  = agree_checked (ffdhe2048_p ()) 256 skA skB pkA pkB ssA ssB okA okB

(** {3 FFDHE-3072} *)

let ffdhe3072_p () : GTot (p: pos { p == num ffdhe3072 }) =
  ffdhe3072_ends (); modulus_pos ffdhe3072 47; num ffdhe3072

let ffdhe3072_agree (skA skB pkA pkB ssA ssB: Seq.seq S8.t) (okA okB: bool)
  : Lemma (requires group_agreement (ffdhe3072_p ()) 384 skA skB pkA pkB ssA ssB okA okB /\
                    okA /\ okB)
          (ensures ssA == ssB)
  = agree_checked (ffdhe3072_p ()) 384 skA skB pkA pkB ssA ssB okA okB

(** {3 FFDHE-4096} *)

let ffdhe4096_p () : GTot (p: pos { p == num ffdhe4096 }) =
  ffdhe4096_ends (); modulus_pos ffdhe4096 63; num ffdhe4096

let ffdhe4096_agree (skA skB pkA pkB ssA ssB: Seq.seq S8.t) (okA okB: bool)
  : Lemma (requires group_agreement (ffdhe4096_p ()) 512 skA skB pkA pkB ssA ssB okA okB /\
                    okA /\ okB)
          (ensures ssA == ssB)
  = agree_checked (ffdhe4096_p ()) 512 skA skB pkA pkB ssA ssB okA okB

(** {3 FFDHE-6144} *)

let ffdhe6144_p () : GTot (p: pos { p == num ffdhe6144 }) =
  ffdhe6144_ends (); modulus_pos ffdhe6144 95; num ffdhe6144

let ffdhe6144_agree (skA skB pkA pkB ssA ssB: Seq.seq S8.t) (okA okB: bool)
  : Lemma (requires group_agreement (ffdhe6144_p ()) 768 skA skB pkA pkB ssA ssB okA okB /\
                    okA /\ okB)
          (ensures ssA == ssB)
  = agree_checked (ffdhe6144_p ()) 768 skA skB pkA pkB ssA ssB okA okB

(** {3 FFDHE-8192} *)

let ffdhe8192_p () : GTot (p: pos { p == num ffdhe8192 }) =
  ffdhe8192_ends (); modulus_pos ffdhe8192 127; num ffdhe8192

let ffdhe8192_agree (skA skB pkA pkB ssA ssB: Seq.seq S8.t) (okA okB: bool)
  : Lemma (requires group_agreement (ffdhe8192_p ()) 1024 skA skB pkA pkB ssA ssB okA okB /\
                    okA /\ okB)
          (ensures ssA == ssB)
  = agree_checked (ffdhe8192_p ()) 1024 skA skB pkA pkB ssA ssB okA okB

#pop-options
