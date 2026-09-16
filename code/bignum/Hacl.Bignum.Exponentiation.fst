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

(** Modular exponentiation: square and multiply, in Montgomery form.

    The exponent is scanned from its top bit down; at every step the
    accumulator is squared and the base is multiplied in when the bit is
    set.  Keeping the whole ladder in Montgomery form means the only
    conversions are one at the start and one at the end, and every rung
    costs exactly two {!Hacl.Bignum.Montgomery.mont_mul}s.

    The accumulator holds [pw a e * R mod n], where [e] is the exponent
    truncated to the bits seen so far.  A Montgomery product drops a factor
    of [R], which is exactly what turns the product of two such
    representatives back into one.

    {b Constant time.}  The ladder does the same work for every bit and
    chooses between the two candidates with a mask, so its timing depends
    only on the announced bit length.  A variable-time variant that skips
    the multiply is a compatible fast path for public exponents. *)
module Hacl.Bignum.Exponentiation

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Bignum.Base
open Hacl.Bignum.Montgomery

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module Declassify = Hacl.Secret.Declassify

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

#push-options "--fuel 1 --ifuel 1"
let pw_zero (a: nat) : Lemma (pw a 0 == 1) = ()
#pop-options

(** One step down the exponent, at the level of the number itself: the bits
    above [i] are twice the bits above [i+1] plus the bit at [i]. *)
let bit_split (n i: nat)
  : Lemma (n / pow2 i ==
           n / pow2 (i + 1) + n / pow2 (i + 1) + n / pow2 i % 2)
  = assert_norm (pow2 1 == 2);
    Math.pow2_plus i 1;
    Math.division_multiplication_lemma n (pow2 i) (pow2 1);
    Math.euclidean_division_definition (n / pow2 i) 2

(** Regrouping a product of two Montgomery representatives. *)
let mul_expand (p q rr: nat)
  : Lemma ((p * rr) * (q * rr) == (p * q * rr) * rr)
  = Math.paren_mul_right p rr (q * rr);
    Math.paren_mul_right rr q rr;
    Math.swap_mul rr q;
    Math.paren_mul_right p (q * rr) rr;
    Math.paren_mul_right p q rr

(** A Montgomery product of representatives is a representative of the
    product: this is the one arithmetic fact the ladder runs on. *)
let exp_mul (r x y p q rr nN: nat)
  : Lemma (requires 0 < nN /\ x == (p * rr) % nN /\ y == (q * rr) % nN /\
                    (r * rr) % nN == (x * y) % nN)
          (ensures (r * rr) % nN == (((p * q * rr) % nN) * rr) % nN)
  = Math.lemma_mod_mul_distr_l (p * rr) y nN;
    Math.lemma_mod_mul_distr_r (p * rr) (q * rr) nN;
    mul_expand p q rr;
    Math.lemma_mod_mul_distr_l (p * q * rr) rr nN

(** Entering Montgomery form: multiplying by [R^2] and dropping one [R]. *)
let exp_embed (aM a rr nN: nat)
  : Lemma (requires 0 < nN /\ (aM * rr) % nN == (a * ((rr * rr) % nN)) % nN)
          (ensures (aM * rr) % nN == (((a * rr) % nN) * rr) % nN)
  = Math.lemma_mod_mul_distr_r a (rr * rr) nN;
    Math.paren_mul_right a rr rr;
    Math.lemma_mod_mul_distr_l (a * rr) rr nN

(** The representative of one is [R] itself, and {!from_mont} of [R^2]
    produces it. *)
let exp_init (acc rr nN: nat)
  : Lemma (requires 0 < nN /\ (acc * rr) % nN == ((rr * rr) % nN) % nN)
          (ensures (acc * rr) % nN == ((rr % nN) * rr) % nN)
  = Math.lemma_mod_twice (rr * rr) nN;
    Math.lemma_mod_mul_distr_l rr rr nN

(** Leaving Montgomery form. *)
let exp_fin (r acc pf rr nN: nat)
  : Lemma (requires 0 < nN /\ acc < nN /\ acc == (pf * rr) % nN /\
                    (r * rr) % nN == acc % nN)
          (ensures (r * rr) % nN == ((pf % nN) * rr) % nN)
  = Math.small_mod acc nN;
    Math.lemma_mod_mul_distr_l pf rr nN

(** The modulus modulo the radix is its lowest limb. *)
let modulus_low (v: Seq.seq S64.t { 0 < Seq.length v })
  : Lemma (num v % base == S64.v (Seq.index v 0))
  = wt_zero (); wt_succ 0; pre_zero v; pre_snoc v 0; pre_mod v 1

(** Entering the ladder: the base and the accumulator in Montgomery form. *)
let exp_start (aMv acc1 anum rr nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ aMv < nN /\ acc1 < nN /\
                    (aMv * rr) % nN == (anum * ((rr * rr) % nN)) % nN /\
                    (acc1 * rr) % nN == ((rr * rr) % nN) % nN)
          (ensures aMv == (anum * rr) % nN /\ acc1 == (pw anum 0 * rr) % nN)
  = exp_embed aMv anum rr nN;
    mont_cancel aMv ((anum * rr) % nN) nN mu m0 k;
    exp_init acc1 rr nN;
    mont_cancel acc1 (rr % nN) nN mu m0 k;
    pw_zero anum

#push-options "--z3rlimit 200"

(** The squaring half of a rung. *)
let exp_sq_step (acc0 sq anum e rr nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ acc0 == (pw anum e * rr) % nN /\
                    sq < nN /\ (sq * rr) % nN == (acc0 * acc0) % nN)
          (ensures sq == (pw anum (e + e) * rr) % nN)
  = let pe = pw anum e in
    exp_mul sq acc0 acc0 pe pe rr nN;
    mont_cancel sq ((pe * pe * rr) % nN) nN mu m0 k;
    assert (sq == (pe * pe * rr) % nN);
    pw_step anum e 0;
    assert (pw anum (e + e) == pe * pe)

(** The multiplying half of a rung. *)
let exp_mul_step (sq pr aMv anum e rr nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ sq == (pw anum (e + e) * rr) % nN /\
                    aMv == (anum * rr) % nN /\
                    pr < nN /\ (pr * rr) % nN == (sq * aMv) % nN)
          (ensures pr == (pw anum (e + e + 1) * rr) % nN)
  = let pe = pw anum e in
    pw_step anum e 0;
    assert (pw anum (e + e) == pe * pe);
    assert (sq == (pe * pe * rr) % nN);
    exp_mul pr sq aMv (pe * pe) anum rr nN;
    mont_cancel pr ((pe * pe * anum * rr) % nN) nN mu m0 k;
    assert (pr == (pe * pe * anum * rr) % nN);
    pw_step anum e 1;
    assert (pw anum (e + e + 1) == pe * pe * anum)

#pop-options

(** Everything one rung of the ladder needs, in a single step.  Squaring
    and multiplying each contribute a {!mont_mul} postcondition; this turns
    the pair of them into the two candidates the next rung chooses between.
    It is one lemma rather than six calls because the loop body already
    carries nine arrays, and the solver does not cope with both at once. *)
let exp_column (acc0 sq pr aMv anum e bn rr nN mu m0: nat) (j k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ e == bn / pow2 (j + 1) /\
                    acc0 == (pw anum e * rr) % nN /\
                    aMv == (anum * rr) % nN /\
                    sq < nN /\ (sq * rr) % nN == (acc0 * acc0) % nN /\
                    pr < nN /\ (pr * rr) % nN == (sq * aMv) % nN)
          (ensures sq == (pw anum (e + e) * rr) % nN /\
                   pr == (pw anum (e + e + 1) * rr) % nN /\
                   bn / pow2 j == e + e + (bn / pow2 j % 2))
  = exp_sq_step acc0 sq anum e rr nN mu m0 k;
    exp_mul_step sq pr aMv anum e rr nN mu m0 k;
    bit_split bn j

(** Decoding the ladder's exit test.  Stated as a lemma because at the foot
    of the loop the solver has the whole function's context to sift through,
    and it does not find this by itself. *)
let sz_zero (x: SZ.t) : Lemma (requires SZ.gt x 0sz == false) (ensures SZ.v x == 0) = ()

(** At the bottom of the ladder the truncated exponent is the whole one. *)
let exp_top (bn: nat) : Lemma (bn / pow2 0 == bn) = assert_norm (pow2 0 == 1)

(** Leaving the ladder. *)
let exp_end (r accf pf rr nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ accf < nN /\ accf == (pf * rr) % nN /\
                    r < nN /\ (r * rr) % nN == accf % nN)
          (ensures r == pf % nN)
  = exp_fin r accf pf rr nN;
    mont_cancel r (pf % nN) nN mu m0 k


#push-options "--z3rlimit 200"

(** [mod_exp_consttime res a bb bbits r2 nmod nn mu aM acc t wide] is
    [res = a ^ bb mod nmod], in time depending only on [bbits].  [a] must
    already be reduced; [aM], [acc] and [t] are [n] limbs of scratch and
    [wide] is [2n].  [res] doubles as a fourth scratch during the ladder. *)
fn mod_exp_consttime (res: A.array S64.t) (a: A.array S64.t)
                     (bb: A.array S64.t) (bbits: SZ.t)
                     (r2: A.array S64.t) (nmod: A.array S64.t)
                     (nn: SZ.t) (mu: S64.t)
                     (aM: A.array S64.t) (acc: A.array S64.t)
                     (t: A.array S64.t) (wide: A.array S64.t)
                     (#vres #vaM #vacc #vt #vwide: erased (Seq.seq S64.t))
                     (#pa #pb #pr #pn: perm)
                     (#va #vbb #vr2: erased (Seq.seq S64.t))
                     (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to bb #pb vbb **
         A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
         A.pts_to aM vaM ** A.pts_to acc vacc ** A.pts_to t vt **
         A.pts_to wide vwide **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vr2 == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vaM == SZ.v nn /\ Seq.length vacc == SZ.v nn /\
        Seq.length vt == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        SZ.v bbits <= 64 * Seq.length vbb /\
        num vbb < pow2 (SZ.v bbits) /\ num va < num vn /\
        num vr2 == (wt (SZ.v nn) * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3 v4: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bb #pb vbb **
  A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
  A.pts_to aM v1 ** A.pts_to acc v2 ** A.pts_to t v3 ** A.pts_to wide v4 **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn /\
        Seq.length v4 == SZ.v nn + SZ.v nn /\
        num v == pw (num va) (num vbb) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len bb;
  A.pts_to_len r2;
  A.pts_to_len nmod;
  A.pts_to_len aM;
  A.pts_to_len acc;
  A.pts_to_len t;
  A.pts_to_len wide;
  modulus_low vn;
  (* the base in Montgomery form, and one in Montgomery form *)
  mont_mul aM a r2 wide nmod nn mu;
  from_mont acc r2 wide nmod nn mu;
  with vaM1. assert (A.pts_to aM vaM1);
  with vacc1. assert (A.pts_to acc vacc1);
  exp_start (num vaM1) (num vacc1) (num va) (wt (SZ.v nn)) (num vn)
            (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
  Math.small_div (num vbb) (pow2 (SZ.v bbits));
  let mut i = bbits;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t) (v v1 v2 v3 v4: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bb #pb vbb **
    A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
    A.pts_to aM v1 ** A.pts_to acc v2 ** A.pts_to t v3 ** A.pts_to wide v4 **
    pure (SZ.v vi <= SZ.v bbits /\
          Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
          Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn /\
          Seq.length v4 == SZ.v nn + SZ.v nn /\
          num v1 == (num va * wt (SZ.v nn)) % num vn /\
          num v2 < num vn /\
          num v2 == (pw (num va) (num vbb / pow2 (SZ.v vi)) * wt (SZ.v nn))
                    % num vn)
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let j = SZ.sub vi 1sz;
    with vacc0. assert (A.pts_to acc vacc0);
    with vaMc. assert (A.pts_to aM vaMc);
    (* square *)
    copy t acc nn;
    mont_mul res acc t wide nmod nn mu;
    with vsq. assert (A.pts_to res vsq);
    copy acc res nn;
    (* multiply *)
    mont_mul t acc aM wide nmod nn mu;
    with vpr. assert (A.pts_to t vpr);
    exp_column (num vacc0) (num vsq) (num vpr) (num vaMc) (num va)
               (num vbb / pow2 (SZ.v vi)) (num vbb) (wt (SZ.v nn)) (num vn)
               (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v j) (SZ.v nn);
    let msk = get_bit bb j;
    cselect acc t nn msk (num vbb / pow2 (SZ.v j) % 2);
    i := j;
  };
  let vend = !i;
  sz_zero vend;
  exp_top (num vbb);
  with vaccf. assert (A.pts_to acc vaccf);
  assert (pure (num vaccf ==
    (pw (num va) (num vbb / pow2 (SZ.v vend)) * wt (SZ.v nn)) % num vn));
  assert (pure (num vaccf ==
    (pw (num va) (num vbb) * wt (SZ.v nn)) % num vn));
  from_mont res acc wide nmod nn mu;
  with vf. assert (A.pts_to res vf);
  exp_end (num vf) (num vaccf) (pw (num va) (num vbb)) (wt (SZ.v nn)) (num vn)
          (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
  ()
}

#pop-options


(** {2 A variable-time ladder}

    When the exponent is public -- an RSA verification exponent, or the
    [n-2] of an inversion -- there is no reason to compute a product and
    throw it away.  This is the same ladder with the multiply under a
    branch, which is why the module that provides the branch is named for
    what it gives up. *)

#push-options "--z3rlimit 200"

(** [mod_exp_vartime] is {!mod_exp_consttime} with the multiply skipped on
    zero bits.  Its timing reveals the exponent, so the exponent must be
    public. *)
fn mod_exp_vartime (res: A.array S64.t) (a: A.array S64.t)
                   (bb: A.array S64.t) (bbits: SZ.t)
                   (r2: A.array S64.t) (nmod: A.array S64.t)
                   (nn: SZ.t) (mu: S64.t)
                   (aM: A.array S64.t) (acc: A.array S64.t)
                   (t: A.array S64.t) (wide: A.array S64.t)
                   (#vres #vaM #vacc #vt #vwide: erased (Seq.seq S64.t))
                   (#pa #pb #pr #pn: perm)
                   (#va #vbb #vr2: erased (Seq.seq S64.t))
                   (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to bb #pb vbb **
         A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
         A.pts_to aM vaM ** A.pts_to acc vacc ** A.pts_to t vt **
         A.pts_to wide vwide **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vr2 == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vaM == SZ.v nn /\ Seq.length vacc == SZ.v nn /\
        Seq.length vt == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        SZ.v bbits <= 64 * Seq.length vbb /\
        num vbb < pow2 (SZ.v bbits) /\ num va < num vn /\
        num vr2 == (wt (SZ.v nn) * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3 v4: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bb #pb vbb **
  A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
  A.pts_to aM v1 ** A.pts_to acc v2 ** A.pts_to t v3 ** A.pts_to wide v4 **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn /\
        Seq.length v4 == SZ.v nn + SZ.v nn /\
        num v == pw (num va) (num vbb) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len bb;
  A.pts_to_len r2;
  A.pts_to_len nmod;
  A.pts_to_len aM;
  A.pts_to_len acc;
  A.pts_to_len t;
  A.pts_to_len wide;
  modulus_low vn;
  mont_mul aM a r2 wide nmod nn mu;
  from_mont acc r2 wide nmod nn mu;
  with vaM1. assert (A.pts_to aM vaM1);
  with vacc1. assert (A.pts_to acc vacc1);
  exp_start (num vaM1) (num vacc1) (num va) (wt (SZ.v nn)) (num vn)
            (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
  Math.small_div (num vbb) (pow2 (SZ.v bbits));
  let mut i = bbits;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t) (v v1 v2 v3 v4: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bb #pb vbb **
    A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
    A.pts_to aM v1 ** A.pts_to acc v2 ** A.pts_to t v3 ** A.pts_to wide v4 **
    pure (SZ.v vi <= SZ.v bbits /\
          Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
          Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn /\
          Seq.length v4 == SZ.v nn + SZ.v nn /\
          num v1 == (num va * wt (SZ.v nn)) % num vn /\
          num v2 < num vn /\
          num v2 == (pw (num va) (num vbb / pow2 (SZ.v vi)) * wt (SZ.v nn))
                    % num vn)
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let j = SZ.sub vi 1sz;
    assert (pure (SZ.v j + 1 == SZ.v vi));
    with vacc0. assert (A.pts_to acc vacc0);
    with vaMc. assert (A.pts_to aM vaMc);
    copy t acc nn;
    mont_mul res acc t wide nmod nn mu;
    with vsq. assert (A.pts_to res vsq);
    exp_sq_step (num vacc0) (num vsq) (num va) (num vbb / pow2 (SZ.v vi))
                (wt (SZ.v nn)) (num vn) (S64.v mu) (S64.v (Seq.index vn 0))
                (SZ.v nn);
    bit_split (num vbb) (SZ.v j);
    copy acc res nn;
    let msk = get_bit bb j;
    let bit = Declassify.u64 msk;
    if (U64.eq bit 0uL) {
      assert (pure (num vbb / pow2 (SZ.v j) % 2 == 0));
      assert (pure (num vbb / pow2 (SZ.v j + 1) == num vbb / pow2 (SZ.v vi)));
      assert (pure (num vbb / pow2 (SZ.v j) ==
        num vbb / pow2 (SZ.v j + 1) + num vbb / pow2 (SZ.v j + 1)));
      assert (pure (num vbb / pow2 (SZ.v j) ==
        num vbb / pow2 (SZ.v vi) + num vbb / pow2 (SZ.v vi)));
      with vaccz. assert (A.pts_to acc vaccz);
      assert (pure (num vaccz ==
        (pw (num va) (num vbb / pow2 (SZ.v j)) * wt (SZ.v nn)) % num vn));
      i := j;
    } else {
      assert (pure (num vbb / pow2 (SZ.v j) % 2 == 1));
      mont_mul t acc aM wide nmod nn mu;
      with vpr. assert (A.pts_to t vpr);
      exp_mul_step (num vsq) (num vpr) (num vaMc) (num va)
                   (num vbb / pow2 (SZ.v vi)) (wt (SZ.v nn)) (num vn)
                   (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
      copy acc t nn;
      assert (pure (num vbb / pow2 (SZ.v j + 1) == num vbb / pow2 (SZ.v vi)));
      assert (pure (num vbb / pow2 (SZ.v j) ==
        num vbb / pow2 (SZ.v j + 1) + num vbb / pow2 (SZ.v j + 1) + 1));
      assert (pure (num vbb / pow2 (SZ.v j) ==
        num vbb / pow2 (SZ.v vi) + num vbb / pow2 (SZ.v vi) + 1));
      with vaccn. assert (A.pts_to acc vaccn);
      assert (pure (num vaccn ==
        (pw (num va) (num vbb / pow2 (SZ.v j)) * wt (SZ.v nn)) % num vn));
      i := j;
    }
  };
  let vend = !i;
  sz_zero vend;
  exp_top (num vbb);
  with vaccf. assert (A.pts_to acc vaccf);
  assert (pure (num vaccf ==
    (pw (num va) (num vbb / pow2 (SZ.v vend)) * wt (SZ.v nn)) % num vn));
  assert (pure (num vaccf ==
    (pw (num va) (num vbb) * wt (SZ.v nn)) % num vn));
  from_mont res acc wide nmod nn mu;
  with vf. assert (A.pts_to res vf);
  exp_end (num vf) (num vaccf) (pw (num va) (num vbb)) (wt (SZ.v nn)) (num vn)
          (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
  ()
}

#pop-options

#pop-options


(** {2 Inversion modulo a prime}

    Fermat's little theorem: if [n] is prime and [a] is not a multiple of
    it, then [a^(n-2)] is the inverse of [a] modulo [n].  We do not ask the
    caller to prove that [n] is prime -- HACL* does not either -- so the
    specification below is the honest one: this computes a power.  It is an
    inverse exactly when the hypothesis the name announces holds. *)

(** The exponent [n-2] fits, and is what [sub] leaves behind when no borrow
    comes out. *)
let inv_exp (nN e c w: int)
  : Lemma (requires nN + c * w == e + 2 /\ 0 <= c /\ c <= 1 /\ 2 <= nN /\
                    0 <= e /\ e < w)
          (ensures e == nN - 2)
  = ()

#push-options "--z3rlimit 100"

(** [mod_inv_prime_vartime res a r2 nmod nn mu e aM acc t wide] is
    [a^(n-2) mod n].  The array [res] doubles as the scratch that holds the
    constant two while the exponent is being formed, and [e] holds that
    exponent for the duration of the ladder. *)
fn mod_inv_prime_vartime (res: A.array S64.t) (a: A.array S64.t)
                         (r2: A.array S64.t) (nmod: A.array S64.t)
                         (nn: SZ.t) (mu: S64.t)
                         (e: A.array S64.t)
                         (aM: A.array S64.t) (acc: A.array S64.t)
                         (t: A.array S64.t) (wide: A.array S64.t)
                         (#vres #ve #vaM #vacc #vt #vwide: erased (Seq.seq S64.t))
                         (#pa #pr #pn: perm)
                         (#va #vr2: erased (Seq.seq S64.t))
                         (#vn: erased (s: Seq.seq S64.t { 1 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va **
         A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn ** A.pts_to e ve **
         A.pts_to aM vaM ** A.pts_to acc vacc ** A.pts_to t vt **
         A.pts_to wide vwide **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vr2 == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length ve == SZ.v nn /\
        Seq.length vaM == SZ.v nn /\ Seq.length vacc == SZ.v nn /\
        Seq.length vt == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\ SZ.fits (64 * SZ.v nn) /\
        num va < num vn /\
        num vr2 == (wt (SZ.v nn) * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v0 v1 v2 v3 v4: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va **
  A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn ** A.pts_to e v0 **
  A.pts_to aM v1 ** A.pts_to acc v2 ** A.pts_to t v3 ** A.pts_to wide v4 **
  pure (Seq.length v == SZ.v nn /\ Seq.length v0 == SZ.v nn /\
        Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn /\
        Seq.length v4 == SZ.v nn + SZ.v nn /\
        num v == pw (num va) (num vn - 2) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len r2;
  A.pts_to_len nmod;
  A.pts_to_len e;
  A.pts_to_len aM;
  A.pts_to_len acc;
  A.pts_to_len t;
  A.pts_to_len wide;
  zero res nn;
  with v0. assert (A.pts_to res v0);
  num_zeros_above v0 0;
  pre_zero v0;
  A.((res.(0sz) <- S64.classify 2uL));
  num_upd v0 0 (S64.classify 2uL);
  with v1. assert (A.pts_to res v1);
  assert (pure (num v1 == 2));
  let c = sub e nmod res nn;
  with v2. assert (A.pts_to e v2);
  pre_bnd v2 (SZ.v nn);
  pre_full v2;
  inv_exp (num vn) (num v2) (S64.v c) (wt (SZ.v nn)) ;
  assert (pure (num v2 == num vn - 2));
  mod_exp_vartime res a e (SZ.mul 64sz nn) r2 nmod nn mu aM acc t wide;
  ()
}

#pop-options
