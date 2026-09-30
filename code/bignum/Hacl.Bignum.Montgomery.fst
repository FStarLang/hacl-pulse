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

(** Montgomery arithmetic: division by the radix instead of by the modulus.

    Reducing a number modulo [m] costs a trial division per limb.  Montgomery
    observed that if you are willing to work with [a * R mod m] instead of
    [a], where [R] is [base^n] -- a power of the radix, so that dividing by
    it is dropping limbs -- then the reduction becomes a multiply and a
    shift.  Everything below is that observation.

    {b What [mu] is.}  The one precomputed quantity is a single limb [mu]
    with [mu * m0 + 1 = 0 mod base], where [m0] is the lowest limb of the
    modulus.  It exists exactly when the modulus is odd, and {!mont_mu}
    computes it with six steps of Hensel lifting -- [x := x * (2 - m0 * x)]
    doubles the number of correct bits each time, so one, two, four, eight,
    sixteen, thirty-two, sixty-four.

    {b Why [res] and [c] are separate.}  The reduction consumes a [2n]-limb
    number and produces an [n]-limb one.  HACL* reduces in place and then
    copies; here the input array is explicitly clobbered and the output is
    its own array, which is what separation logic wants and costs nothing. *)
module Hacl.Bignum.Montgomery

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Bignum.Base

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Declassify = Hacl.Secret.Declassify

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The inverse of a limb}

    Hensel's lemma in two lines: if [m0 * x = 1] to [k] bits then
    [m0 * (x * (2 - m0 * x)) = 1 - (1 - m0 * x)^2] is [1] to [2k] bits.
    Starting from [x = 1], which is correct to one bit because the modulus
    is odd, six steps reach sixty-four. *)

inline_for_extraction
let inv_step (m0 x: S64.t)
  : r: S64.t { S64.v r ==
                 (S64.v x * ((2 - (S64.v m0 * S64.v x) % pow2 64) % pow2 64)) % pow2 64 }
  = S64.mul_mod x (S64.sub_mod (S64.classify 2uL) (S64.mul_mod m0 x))

(** [(1 + a)(1 - a) = 1 - a^2], which is the whole content of the step. *)
let sq_id (a: int) : Lemma ((1 + a) * (2 - (1 + a)) == 1 - a * a) = ()

let sq_scale (e q: int) : Lemma ((e * q) * (e * q) == (e * e) * (q * q)) = ()

(** One Hensel step, as pure arithmetic: [p = 1 mod 2^m] gives
    [p * (2 - p) = 1 mod 2^(2m)]. *)
let hensel (p: nat) (m: pos)
  : Lemma (requires p % pow2 m == 1)
          (ensures (p * (2 - p)) % pow2 (2 * m) == 1)
  = let q = pow2 m in
    let e = p / q in
    Math.euclidean_division_definition p q;
    assert (p == 1 + e * q);
    sq_id (e * q);
    assert (p * (2 - p) == 1 - (e * q) * (e * q));
    sq_scale e q;
    Math.pow2_plus m m;
    assert (p * (2 - p) == 1 + (- (e * e)) * pow2 (2 * m));
    Math.lemma_mod_plus 1 (- (e * e)) (pow2 (2 * m));
    Math.small_mod 1 (pow2 (2 * m))

(** What holds modulo [2^64] holds modulo any power of two below it. *)
let narrow (a b: int) (k: nat { k <= 64 })
  : Lemma (requires a % pow2 64 == b % pow2 64)
          (ensures a % pow2 k == b % pow2 k)
  = Math.pow2_plus k (64 - k);
    Math.modulo_modulo_lemma a (pow2 k) (pow2 (64 - k));
    Math.modulo_modulo_lemma b (pow2 k) (pow2 (64 - k))

let inv_step_ok (mv xv: nat) (m: pos) (r: nat)
  : Lemma (requires 2 * m <= 64 /\ (mv * xv) % pow2 m == 1 /\
                    r == (xv * ((2 - (mv * xv) % pow2 64) % pow2 64)) % pow2 64)
          (ensures (mv * r) % pow2 (2 * m) == 1)
  = let p = mv * xv in
    let bq = pow2 64 in
    (* [(mv * r) % bq == (p * (2 - p)) % bq]: three distributions of [%]. *)
    Math.lemma_mod_sub_distr 2 p bq;
    Math.lemma_mod_mul_distr_r xv (2 - p) bq;
    Math.lemma_mod_mul_distr_r mv (xv * (2 - p)) bq;
    Math.paren_mul_right mv xv (2 - p);
    assert ((mv * r) % bq == (p * (2 - p)) % bq);
    narrow (mv * r) (p * (2 - p)) (2 * m);
    hensel p m

(** Negating the inverse: if [m0 * x = 1] then [m0 * (-x) + 1 = 0]. *)
let negate (mv xv r: nat)
  : Lemma (requires (mv * xv) % pow2 64 == 1 /\ r == (0 - xv) % pow2 64)
          (ensures (r * mv + 1) % base == 0)
  = assert (base == pow2 64);
    Math.lemma_mod_mul_distr_l (0 - xv) mv (pow2 64);
    Math.paren_mul_right 0 xv mv;
    Math.swap_mul xv mv;
    assert ((r * mv) % pow2 64 == (- (mv * xv)) % pow2 64);
    Math.lemma_mod_add_distr 1 (r * mv) (pow2 64);
    Math.lemma_mod_add_distr 1 (- (mv * xv)) (pow2 64);
    Math.lemma_mod_plus 0 1 (pow2 64)

(** [mont_mu m0] is the [mu] with [mu * m0 + 1 = 0 mod base].  The modulus
    must be odd; every modulus Montgomery arithmetic applies to is. *)
let mont_mu (m0: S64.t)
  : Pure S64.t (requires S64.v m0 % 2 == 1)
               (ensures fun r -> (S64.v r * S64.v m0 + 1) % base == 0)
  = let x0 = S64.classify 1uL in
    assert_norm (pow2 1 == 2);
    assert (S64.v m0 * S64.v x0 == S64.v m0);
    let x1 = inv_step m0 x0 in inv_step_ok (S64.v m0) (S64.v x0) 1 (S64.v x1);
    let x2 = inv_step m0 x1 in inv_step_ok (S64.v m0) (S64.v x1) 2 (S64.v x2);
    let x3 = inv_step m0 x2 in inv_step_ok (S64.v m0) (S64.v x2) 4 (S64.v x3);
    let x4 = inv_step m0 x3 in inv_step_ok (S64.v m0) (S64.v x3) 8 (S64.v x4);
    let x5 = inv_step m0 x4 in inv_step_ok (S64.v m0) (S64.v x4) 16 (S64.v x5);
    let x6 = inv_step m0 x5 in inv_step_ok (S64.v m0) (S64.v x5) 32 (S64.v x6);
    (* [x6] inverts [m0]; negating it gives the [mu] a reduction wants. *)
    let r = S64.sub_mod S64.zero x6 in
    negate (S64.v m0) (S64.v x6) (S64.v r);
    r

(** {2 The arithmetic of one reduction column}

    Each of these is stated in exactly the shape the loop body needs, and
    proved in isolation, because the body already carries three arrays. *)

let cancel (k: pos) (a b: nat) : Lemma (requires k * a == k * b) (ensures a == b)
  = Math.swap_mul k a; Math.swap_mul k b;
    Math.cancel_mul_div a k; Math.cancel_mul_div b k

(** Scaling commutes with taking a remainder. *)
let mod_scale (k: pos) (x: nat) (m: pos)
  : Lemma ((k * x) % (k * m) == k * (x % m))
  = Math.euclidean_division_definition x m;
    Math.distributivity_add_right k ((x / m) * m) (x % m);
    Math.paren_mul_right k (x / m) m;
    Math.paren_mul_right (x / m) k m;
    Math.swap_mul (x / m) k;
    Math.lemma_mult_lt_left k (x % m) m;
    Math.lemma_mod_plus (k * (x % m)) (x / m) (k * m);
    Math.small_mod (k * (x % m)) (k * m)

(** A multiple of [wt (i + j)] is a multiple of [wt i], so a remainder
    modulo [wt i] does not see it. *)
let drop_high (a t: nat) (i j: nat)
  : Lemma (a % wt i == ((a + t * wt (i + j)) % wt i))
  = wt_add i j;
    Math.swap_mul (wt i) (wt j);
    Math.paren_mul_right t (wt j) (wt i);
    Math.lemma_mod_plus a (t * wt j) (wt i)

(** The digit at the cursor: if [v] is [wt i] times [v1] and its residue
    modulo the next weight is [wt i * ci], then [ci] is [v1] modulo the
    radix. *)
let red_digit (vv v1 ci: nat) (i: nat)
  : Lemma (requires vv == wt i * v1 /\ vv % wt (i + 1) == wt i * ci /\ ci < base)
          (ensures v1 % base == ci)
  = wt_succ i;
    Math.swap_mul base (wt i);
    mod_scale (wt i) v1 base;
    cancel (wt i) (v1 % base) ci

(** The choice of [qi] clears the cursor limb: [mu] was built so that
    [ci + qi * m] is zero modulo the radix. *)
let red_q (ci mu m0 nN qi: nat)
  : Lemma (requires (mu * m0 + 1) % base == 0 /\ qi == (ci * mu) % base /\
                    nN % base == m0)
          (ensures (ci + qi * nN) % base == 0)
  = Math.lemma_mod_add_distr ci (qi * nN) base;
    Math.lemma_mod_mul_distr_l (ci * mu) nN base;
    Math.lemma_mod_mul_distr_r (ci * mu) nN base;
    Math.paren_mul_right ci mu m0;
    Math.lemma_mod_mul_distr_r ci (mu * m0) base;
    Math.distributivity_add_right ci 1 (mu * m0);
    Math.lemma_mod_mul_distr_r ci (1 + mu * m0) base;
    Math.lemma_mod_add_distr ci (ci * (mu * m0)) base

(** One column, as an equation between the value before and the value
    after.  The three hypotheses are, in order, the limb that was written,
    the double word it came out of, and what {!mul_row} did. *)
let red_step (n2 n1 nc ov2 ov cr old lot qi nN: int) (i nn: nat)
  : Lemma (requires
      n2 + wt (i + nn) * old == n1 + wt (i + nn) * lot /\
      lot + base * ov2 == old + cr + ov /\
      n1 + cr * wt (i + nn) == nc + (nN * qi) * wt i)
    (ensures n2 + ov2 * wt (i + 1 + nn) == nc + ov * wt (i + nn) + (nN * qi) * wt i)
  = wt_succ (i + nn);
    Math.distributivity_add_right (wt (i + nn)) (old + cr) ov;
    Math.distributivity_add_right (wt (i + nn)) old cr;
    Math.distributivity_sub_right (wt (i + nn)) (old + cr + ov) (base * ov2);
    Math.paren_mul_right (wt (i + nn)) base ov2;
    Math.swap_mul (wt (i + nn)) base;
    Math.swap_mul (wt (i + nn)) cr;
    Math.swap_mul (wt (i + nn) * base) ov2

(** The value grows by less than one more weight of the modulus. *)
let red_bound (v v2 nc nN qi: nat) (i: nat)
  : Lemma (requires v < nc + wt i * nN /\ v2 == v + (nN * qi) * wt i /\ qi < base)
          (ensures v2 < nc + wt (i + 1) * nN)
  = wt_succ i;
    Math.lemma_mult_le_left nN qi (base - 1);
    Math.lemma_mult_le_right (wt i) (nN * qi) (nN * (base - 1));
    Math.distributivity_sub_right nN base 1;
    Math.distributivity_add_left (nN * base) (- nN) (wt i);
    Math.paren_mul_right nN base (wt i);
    Math.swap_mul base (wt i);
    Math.paren_mul_right nN (wt i) base;
    Math.swap_mul nN (wt i);
    Math.swap_mul (nN * base) (wt i)

(** Everything above put together: after the column, the value is divisible
    by one more weight, which is what lets the loop drop a limb. *)
let red_clear (na ov n2 ov2 nN qi ci mu m0: nat) (i nn: nat)
  : Lemma (requires
      0 < nn /\ i < nn /\ ci < base /\ qi == (ci * mu) % base /\
      (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
      na % wt i == 0 /\ na % wt (i + 1) == wt i * ci /\
      n2 + ov2 * wt (i + 1 + nn) == na + ov * wt (i + nn) + (nN * qi) * wt i)
    (ensures n2 % wt (i + 1) == 0)
  = let vv = na + ov * wt (i + nn) in
    drop_high na ov i nn;
    drop_high na ov (i + 1) (nn - 1);
    assert (vv % wt i == 0);
    assert (vv % wt (i + 1) == wt i * ci);
    let v1 = vv / wt i in
    Math.euclidean_division_definition vv (wt i);
    Math.swap_mul (vv / wt i) (wt i);
    assert (vv == wt i * v1);
    red_digit vv v1 ci i;
    red_q ci mu m0 nN qi;
    Math.lemma_mod_add_distr (nN * qi) v1 base;
    Math.swap_mul nN qi;
    Math.lemma_mod_add_distr (qi * nN) ci base;
    assert ((v1 + nN * qi) % base == 0);
    Math.distributivity_add_right (wt i) v1 (nN * qi);
    Math.swap_mul (wt i) (nN * qi);
    assert (vv + (nN * qi) * wt i == wt i * (v1 + nN * qi));
    let z = (v1 + nN * qi) / base in
    Math.euclidean_division_definition (v1 + nN * qi) base;
    wt_succ i;
    Math.paren_mul_right (wt i) base z;
    Math.swap_mul (wt i) base;
    Math.multiple_modulo_lemma z (wt (i + 1));
    Math.swap_mul z (wt (i + 1));
    assert ((vv + (nN * qi) * wt i) % wt (i + 1) == 0);
    drop_high n2 ov2 (i + 1) nn

(** The value is unchanged modulo the modulus, because what was added is a
    multiple of it. *)
let red_cong (v v2 nc nN qi: nat) (i: nat)
  : Lemma (requires 0 < nN /\ v % nN == nc % nN /\ v2 == v + (nN * qi) * wt i)
          (ensures v2 % nN == nc % nN)
  = Math.swap_mul nN qi;
    Math.paren_mul_right qi nN (wt i);
    Math.swap_mul nN (wt i);
    Math.paren_mul_right qi (wt i) nN;
    Math.lemma_mod_plus v (qi * wt i) nN

(** One whole column, as the loop body sees it: three raw equations in,
    the three halves of the invariant out.  It is one lemma rather than
    four because the loop body already carries three arrays, and asking the
    solver to thread intermediate arithmetic facts through that context is
    what makes these proofs time out. *)
let red_column (n2 n1 nc ov2 ov cr old lot qi nN ci mu m0 nc0: nat) (i nn: nat)
  : Lemma (requires
      0 < nn /\ i < nn /\ 0 < nN /\ ci < base /\ qi == (ci * mu) % base /\
      (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
      nc % wt i == 0 /\ nc % wt (i + 1) == wt i * ci /\
      (nc + ov * wt (i + nn)) % nN == nc0 % nN /\
      nc + ov * wt (i + nn) < nc0 + wt i * nN /\
      n2 + wt (i + nn) * old == n1 + wt (i + nn) * lot /\
      lot + base * ov2 == old + cr + ov /\
      n1 + cr * wt (i + nn) == nc + (nN * qi) * wt i)
    (ensures
      n2 % wt (i + 1) == 0 /\
      (n2 + ov2 * wt (i + 1 + nn)) % nN == nc0 % nN /\
      n2 + ov2 * wt (i + 1 + nn) < nc0 + wt (i + 1) * nN)
  = red_step n2 n1 nc ov2 ov cr old lot qi nN i nn;
    red_clear nc ov n2 ov2 nN qi ci mu m0 i nn;
    red_cong (nc + ov * wt (i + nn)) (n2 + ov2 * wt (i + 1 + nn)) nc0 nN qi i;
    red_bound (nc + ov * wt (i + nn)) (n2 + ov2 * wt (i + 1 + nn)) nc0 nN qi i

(** {2 The reduction}

    Separated-operand Montgomery reduction.  The accumulator [c] holds [2n]
    limbs; the loop walks the bottom [n] of them, and at each step adds a
    multiple of the modulus chosen so that the limb under the cursor becomes
    zero.  After [n] steps the bottom half is zero, so the value is the
    original one divided by [base^n] -- which is exactly what Montgomery
    form asks for.

    The loop keeps a single carry bit rather than propagating one through
    the top half: the carry produced at step [i] weighs [base^(n+i+1)],
    which is precisely where step [i+1] adds its own column, so it is
    consumed one step later and never accumulates. *)

(** Copy the top half of [c] into [res].  Together with the loop's
    invariant -- the bottom half is zero -- this is the division by
    [base^n]. *)
let copy_step (pc pcn pv ci: int) (nn i: nat)
  : Lemma (requires pc == pcn + wt nn * pv)
          (ensures pc + wt (i + nn) * ci == pcn + wt nn * (pv + wt i * ci))
  = wt_add nn i;
    Math.distributivity_add_right (wt nn) pv (wt i * ci);
    Math.paren_mul_right (wt nn) (wt i) ci

fn copy_upper (res: A.array S64.t) (c: A.array S64.t) (nn: SZ.t)
              (#vres: erased (Seq.seq S64.t)) (#pc: perm)
              (#vc: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to c #pc vc **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vc == SZ.v nn + SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to c #pc vc **
  pure (Seq.length v == SZ.v nn /\
        num vc == pre vc (SZ.v nn) + wt (SZ.v nn) * num v)
{
  A.pts_to_len res;
  A.pts_to_len c;
  pre_zero vres;
  wt_zero ();
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi nn)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to c #pc vc **
    pure (SZ.v vi <= SZ.v nn /\ Seq.length v == SZ.v nn /\
          pre vc (SZ.v nn + SZ.v vi) ==
            pre vc (SZ.v nn) + wt (SZ.v nn) * pre v (SZ.v vi))
  decreases (SZ.v nn - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let ci = A.(c.(SZ.add nn vi));
    A.((res.(vi) <- ci));
    pre_upd v (SZ.v vi) ci (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) ci) (SZ.v vi);
    pre_snoc vc (SZ.v nn + SZ.v vi);
    copy_step (pre vc (SZ.v nn + SZ.v vi)) (pre vc (SZ.v nn)) (pre v (SZ.v vi))
              (S64.v ci) (SZ.v nn) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full vc;
  pre_full v;
  ()
}

(** The last conditional subtraction.  At this point the value is [a + ov *
    base^n] and is below twice the modulus, so subtracting the modulus once
    is enough -- but only if the value was at least the modulus, which the
    borrow tells us.  The two flags together decide it: the subtraction has
    to be undone exactly when it borrowed and there was no carry above. *)
let final_cases (a nN ov borrow n1 k n2 c2 rr: nat)
  : Lemma (requires
      0 < nN /\ nN < rr /\ a < rr /\ ov <= 1 /\ borrow <= 1 /\ c2 <= 1 /\
      a + ov * rr < 2 * nN /\
      a + borrow * rr == n1 + nN /\ n1 < rr /\
      (borrow == 1 /\ ov == 0 ==> k == 1) /\
      (~(borrow == 1 /\ ov == 0) ==> k == 0) /\
      n2 + c2 * rr == n1 + k * nN /\ n2 < rr)
    (ensures n2 == (a + ov * rr) % nN)
  = if ov = 0 then
      if borrow = 0 then begin
        Math.small_mod (a - nN) nN;
        Math.lemma_mod_plus (a - nN) 1 nN
      end else
        Math.small_mod a nN
    else begin
      Math.small_mod (a + rr - nN) nN;
      Math.lemma_mod_plus (a + rr - nN) 1 nN
    end

(** What the reduction computes, once the division by [base^n] is folded
    back in: a residue equal to the input scaled down. *)
let mont_result (r v1 nN wnn c0: nat)
  : Lemma (requires 0 < nN /\ r == v1 % nN /\ wnn * v1 == c0)
          (ensures (r * wnn) % nN == c0 % nN /\ r < nN)
  = Math.lemma_mod_mul_distr_l v1 wnn nN;
    Math.swap_mul v1 wnn

(** The bottom half is zero, so the whole value is the top half scaled by
    the radix power -- including the carry that sits just above it. *)
let mont_top (na nva ov nn: nat)
  : Lemma (requires na == wt nn * nva)
          (ensures na + ov * wt (nn + nn) == wt nn * (nva + ov * wt nn))
  = wt_add nn nn;
    Math.distributivity_add_right (wt nn) nva (ov * wt nn);
    Math.paren_mul_right (wt nn) ov (wt nn);
    Math.swap_mul (wt nn) ov;
    Math.paren_mul_right ov (wt nn) (wt nn)

(** The mask that decides whether the subtraction has to be undone.  It is
    all ones exactly when the subtraction borrowed and no carry came out of
    the loop, which is the one case where the value was already reduced. *)
let flag_mask (borrow ov m: S64.t)
  : Lemma (requires S64.v borrow <= 1 /\ S64.v ov <= 1 /\
                    m == S64.eq_mask (S64.sub_mod borrow ov) (S64.classify 1uL))
          (ensures is_mask m /\
                   (S64.v borrow == 1 /\ S64.v ov == 0 ==> mask_bit m == 1) /\
                   (~(S64.v borrow == 1 /\ S64.v ov == 0) ==> mask_bit m == 0))
  = assert_norm (pow2 32 == 4294967296);
    Math.small_mod (pow2 32 - 1) (pow2 32);
    Math.lemma_mod_plus (S64.v borrow - S64.v ov) 1 (pow2 32);
    if S64.v borrow >= S64.v ov then
      Math.small_mod (S64.v borrow - S64.v ov) (pow2 32)

(** The value at the end of the loop is below twice the modulus, so its
    top half is a valid input to one conditional subtraction. *)
let mont_split (vv v1 nc nN wnn: nat)
  : Lemma (requires 0 < nN /\ 0 < wnn /\ vv == wnn * v1 /\ nc < nN * wnn /\
                    vv < nc + wnn * nN)
          (ensures v1 < 2 * nN)
  = Math.swap_mul nN wnn;
    Math.distributivity_add_left nN nN wnn;
    Math.lemma_mult_lt_left wnn v1 (2 * nN)

#push-options "--z3rlimit 600"

(** [reduction res c nmod nn mu] divides the [2n]-limb [c] by [base^n]
    modulo the [n]-limb modulus, leaving the result in [res].  [c] is
    clobbered.  [mu] must be the inverse computed by {!mont_mu}, and [c]
    must be below the modulus times [base^n]. *)
(** [mul_row]'s contract is stated on a prefix of the multiplier, because
    the squaring in {!Hacl.Bignum.Base} needs it that way.  Here the prefix
    is the whole modulus, and saying so is a merge of [pre vn (SZ.v nn)]
    with [num vn] that the solver will not make on its own inside the
    reduction loop. *)
let pre_len (v: Seq.seq S64.t) (k: nat)
  : Lemma (requires k == Seq.length v) (ensures pre v k == num v)
  = pre_full v

fn reduction (res: A.array S64.t) (c: A.array S64.t) (nmod: A.array S64.t)
             (nn: SZ.t) (mu: S64.t)
             (#vres: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
             (#pn: perm)
             (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to c vc ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vc == SZ.v nn + SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn) /\
        num vc < num vn * wt (SZ.v nn) /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t) (v2: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to c v2 ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length v2 == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        (num v * wt (SZ.v nn)) % num vn == num vc % num vn)
{
  A.pts_to_len res;
  A.pts_to_len c;
  A.pts_to_len nmod;
  wt_zero ();
  wt_succ 0;
  pre_zero vn;
  pre_snoc vn 0;
  pre_mod vn 1;
  pre_len vn (SZ.v nn);
  eval_bnd (vals vn);
  let mut i = 0sz;
  let mut ov = S64.zero;
  while (let vi = !i; SZ.lt vi nn)
  invariant exists* (vi: SZ.t) (vov: S64.t) (varr: Seq.seq S64.t).
    pts_to i vi ** pts_to ov vov ** A.pts_to c varr ** A.pts_to nmod #pn vn **
    pure (SZ.v vi <= SZ.v nn /\ Seq.length varr == SZ.v nn + SZ.v nn /\
          S64.v vov <= 1 /\ num varr % wt (SZ.v vi) == 0 /\
          (num varr + S64.v vov * wt (SZ.v vi + SZ.v nn)) % num vn ==
            num vc % num vn /\
          num varr + S64.v vov * wt (SZ.v vi + SZ.v nn) <
            num vc + wt (SZ.v vi) * num vn)
  decreases (SZ.v nn - SZ.v (!i))
  {
    with varr. assert (A.pts_to c varr);
    let vi = !i;
    let vov = !ov;
    let ci = A.(c.(vi));
    let qi = S64.mul_mod ci mu;
    pre_mod varr (SZ.v vi);
    pre_mod varr (SZ.v vi + 1);
    pre_snoc varr (SZ.v vi);
    let cr = mul_row c nmod nn qi vi;
    with v1. assert (A.pts_to c v1);
    num_above varr v1 (SZ.v vi + SZ.v nn);
    let pos = SZ.add vi nn;
    let old = A.(c.(pos));
    let t = sum old cr vov;
    lo_hi t;
    carry_bit t;
    let lot = lo t;
    let ov2 = hi t;
    A.((c.(pos) <- lot));
    num_upd v1 (SZ.v pos) lot;
    with v2. assert (A.pts_to c v2);
    red_column (num v2) (num v1) (num varr) (S64.v ov2) (S64.v vov) (S64.v cr)
               (S64.v old) (S64.v lot) (S64.v qi) (num vn) (S64.v ci) (S64.v mu)
               (S64.v (Seq.index vn 0)) (num vc) (SZ.v vi) (SZ.v nn);
    ov := ov2;
    i := SZ.add vi 1sz;
  };
  with varr. assert (A.pts_to c varr);
  let vov = !ov;
  pre_mod varr (SZ.v nn);
  copy_upper res c nn;
  with va. assert (A.pts_to res va);
  eval_bnd (vals va);
  mont_top (num varr) (num va) (S64.v vov) (SZ.v nn);
  mont_split (num varr + S64.v vov * wt (SZ.v nn + SZ.v nn))
             (num va + S64.v vov * wt (SZ.v nn)) (num vc) (num vn) (wt (SZ.v nn));
  let borrow = sub_from res nmod nn;
  with v1. assert (A.pts_to res v1);
  eval_bnd (vals v1);
  let mask = S64.eq_mask (S64.sub_mod borrow vov) (S64.classify 1uL);
  flag_mask borrow vov mask;
  mask_bit_ok mask;
  let c2 = add_masked res nmod nn mask (hide (mask_bit mask));
  with v2. assert (A.pts_to res v2);
  eval_bnd (vals v2);
  final_cases (num va) (num vn) (S64.v vov) (S64.v borrow) (num v1)
              (mask_bit mask) (num v2) (S64.v c2) (wt (SZ.v nn));
  mont_result (num v2) (num va + S64.v vov * wt (SZ.v nn)) (num vn)
              (wt (SZ.v nn)) (num varr + S64.v vov * wt (SZ.v nn + SZ.v nn));
  ()
}

#pop-options

(** {2 Copying into the wide accumulator} *)

fn embed (tmp: A.array S64.t) (a: A.array S64.t) (nn: SZ.t)
         (#vtmp: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to tmp vtmp ** A.pts_to a #pa va **
  pure (Seq.length vtmp == SZ.v nn + SZ.v nn /\ Seq.length va == SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to tmp v ** A.pts_to a #pa va **
  pure (Seq.length v == SZ.v nn + SZ.v nn /\ num v == num va)
{
  A.pts_to_len tmp;
  A.pts_to_len a;
  zero tmp (SZ.add nn nn);
  pre_zero va;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi nn)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to tmp v ** A.pts_to a #pa va **
    pure (SZ.v vi <= SZ.v nn /\ Seq.length v == SZ.v nn + SZ.v nn /\
          (forall (k: nat). SZ.v vi <= k /\ k < Seq.length v ==>
             S64.v (Seq.index v k) == 0) /\
          pre v (SZ.v vi) == pre va (SZ.v vi))
  decreases (SZ.v nn - SZ.v (!i))
  {
    with v. assert (A.pts_to tmp v);
    let vi = !i;
    let ai = A.(a.(vi));
    A.((tmp.(vi) <- ai));
    pre_upd v (SZ.v vi) ai (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) ai) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to tmp v);
  num_zeros_above v (SZ.v nn);
  pre_full va;
  ()
}

(** {2 Montgomery multiplication}

    [mont_mul res a b] is [a * b / R] modulo the modulus: the product in
    Montgomery form of two numbers in Montgomery form.  The [2n]-limb
    scratch is the caller's, because this library never allocates. *)

let mul_bnd (a b nN rr: nat)
  : Lemma (requires a < nN /\ b < rr) (ensures a * b < nN * rr)
  = Math.lemma_mult_le_right b a (nN - 1);
    Math.lemma_mult_le_left (nN - 1) b (rr - 1);
    Math.distributivity_sub_right (nN - 1) rr 1;
    Math.distributivity_sub_left nN 1 rr

#push-options "--z3rlimit 300"

fn mont_mul (res: A.array S64.t) (a b: A.array S64.t) (tmp: A.array S64.t)
            (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
            (#vres #vtmp: erased (Seq.seq S64.t)) (#pa #pb #pn: perm)
            (#va #vb: erased (Seq.seq S64.t))
            (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         A.pts_to tmp vtmp ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vb == SZ.v nn /\ Seq.length vtmp == SZ.v nn + SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn) /\ num va < num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t) (vt: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to tmp vt ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length vt == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        (num v * wt (SZ.v nn)) % num vn == (num va * num vb) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  A.pts_to_len tmp;
  A.pts_to_len nmod;
  mul tmp a b nn;
  eval_bnd (vals vb);
  mul_bnd (num va) (num vb) (num vn) (wt (SZ.v nn));
  reduction res tmp nmod nn mu;
  ()
}

(** [mont_sqr res a] is [a * a / R] modulo the modulus: {!mont_mul} with
    both operands the same, but going through {!Base.sqr} rather than
    {!Base.mul}.  Three quarters of the multiplications in a windowed
    exponentiation are of this shape, and the triangle costs a little over
    half of the full [n^2], so this is where the exponentiation time goes. *)
fn mont_sqr (res: A.array S64.t) (a: A.array S64.t) (tmp: A.array S64.t)
            (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
            (#vres #vtmp: erased (Seq.seq S64.t)) (#pa #pn: perm)
            (#va: erased (Seq.seq S64.t))
            (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va **
         A.pts_to tmp vtmp ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vtmp == SZ.v nn + SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn) /\ num va < num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t) (vt: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va **
  A.pts_to tmp vt ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length vt == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        (num v * wt (SZ.v nn)) % num vn == (num va * num va) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len tmp;
  A.pts_to_len nmod;
  sqr tmp a nn;
  eval_bnd (vals va);
  mul_bnd (num va) (num va) (num vn) (wt (SZ.v nn));
  reduction res tmp nmod nn mu;
  ()
}

(** [from_mont res a] leaves Montgomery form: the result is [a / R] modulo
    the modulus.  Entering it is {!mont_mul} against the precomputed
    [precomp] square, so there is no separate function for that direction. *)
fn from_mont (res: A.array S64.t) (a: A.array S64.t) (tmp: A.array S64.t)
             (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
             (#vres #vtmp: erased (Seq.seq S64.t)) (#pa #pn: perm)
             (#va: erased (Seq.seq S64.t))
             (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to tmp vtmp **
         A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn /\
        Seq.length vtmp == SZ.v nn + SZ.v nn /\ Seq.length vn == SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t) (vt: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to tmp vt **
  A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length vt == SZ.v nn + SZ.v nn /\
        num v < num vn /\ (num v * wt (SZ.v nn)) % num vn == num va % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len tmp;
  A.pts_to_len nmod;
  embed tmp a nn;
  eval_bnd (vals va);
  Math.lemma_mult_le_right (wt (SZ.v nn)) 1 (num vn);
  reduction res tmp nmod nn mu;
  ()
}

#pop-options

(** {2 The inverse of the radix}

    Montgomery arithmetic computes with an extra factor of [R] throughout,
    and taking it off at the end is only legitimate because [R] is
    invertible modulo the modulus.  It is, and [mu] hands us the witness:
    [1 + mu * N] is a multiple of [base] by the very equation that defines
    [mu], so its quotient is an inverse of [base], and a power of that is an
    inverse of [R].  No appeal to Bezout, and nothing to compute at run
    time. *)

let base_inv (nN mu m0: nat)
  : Ghost nat (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0)
              (ensures fun b1 -> (base * b1) % nN == 1 % nN)
  = Math.lemma_mod_mul_distr_r mu nN base;
    Math.lemma_mod_mul_distr_r mu m0 base;
    Math.lemma_mod_add_distr 1 (mu * nN) base;
    Math.lemma_mod_add_distr 1 (mu * m0) base;
    let b1 = (1 + mu * nN) / base in
    Math.euclidean_division_definition (1 + mu * nN) base;
    Math.lemma_mod_plus 1 mu nN;
    b1

let rec wt_inv (nN: pos) (b1: nat { (base * b1) % nN == 1 % nN }) (k: nat)
  : GTot (u: nat { (wt k * u) % nN == 1 % nN }) (decreases k)
  = if k = 0 then begin wt_zero (); 1 end
    else begin
      let u = wt_inv nN b1 (k - 1) in
      wt_succ (k - 1);
      Math.paren_mul_right base (wt (k - 1)) (b1 * u);
      Math.paren_mul_right (wt (k - 1)) b1 u;
      Math.swap_mul (wt (k - 1)) b1;
      Math.paren_mul_right b1 (wt (k - 1)) u;
      Math.paren_mul_right base b1 (wt (k - 1) * u);
      Math.lemma_mod_mul_distr_l (base * b1) (wt (k - 1) * u) nN;
      Math.lemma_mod_mul_distr_l 1 (wt (k - 1) * u) nN;
      b1 * u
    end

let cancel_mod (x y rr u nN: nat)
  : Lemma (requires 0 < nN /\ x < nN /\ y < nN /\
                    (x * rr) % nN == (y * rr) % nN /\ (rr * u) % nN == 1 % nN)
          (ensures x == y)
  = Math.lemma_mod_mul_distr_l (x * rr) u nN;
    Math.lemma_mod_mul_distr_l (y * rr) u nN;
    Math.paren_mul_right x rr u;
    Math.paren_mul_right y rr u;
    Math.lemma_mod_mul_distr_r x (rr * u) nN;
    Math.lemma_mod_mul_distr_r y (rr * u) nN;
    Math.lemma_mod_mul_distr_r x 1 nN;
    Math.lemma_mod_mul_distr_r y 1 nN;
    Math.small_mod x nN;
    Math.small_mod y nN

(** Two reduced numbers that agree once scaled by [R] are equal. *)
let mont_cancel (x y nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ x < nN /\ y < nN /\
                    (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    (x * wt k) % nN == (y * wt k) % nN)
          (ensures x == y)
  = let b1 = base_inv nN mu m0 in
    let u = wt_inv nN b1 k in
    cancel_mod x y (wt k) u nN

(** {2 The Montgomery constant}

    [precomp] is [R^2] modulo the modulus, the number that every entry into
    Montgomery form goes through.

    Doubling from one all the way up to it takes [2 * rad * nn] steps -- four
    thousand and ninety-six of them for RSA-2048 -- and that is what this
    function used to do.  It is also unnecessary.  In Montgomery form the
    accumulator stands for [2 ^ m], and two moves are available: a Montgomery
    squaring, which sends [m] to [2 * m] because the spare factor of [R]
    cancels, and a modular doubling, which sends [m] to [m + 1].  Those are
    exactly the two moves of a binary ladder, so [m] can be walked up to [rad
    * nn] in a dozen multiplications -- and [m == rad * nn] says precisely
    that the accumulator is [R * R] modulo the modulus.

    Climbing onto the ladder is the one part that stays linear.  It means
    having [2 ^ (rad * nn + 1)] reduced, and doubling is the only operation
    that raises an exponent by a fixed amount, so we start as high as we can
    get for free: at [wt k], where [k] is the topmost nonzero limb of the
    modulus.  A power of the radix at or below an odd number greater than one
    is strictly below it, so [wt k] is already its own residue and no
    reduction is needed to write it down; [rad * (nn - k) + 1] doublings then
    remain, which is sixty-five for a modulus that fills its limbs.

    Finding [k] reads the modulus.  That is public in every caller -- an RSA
    modulus travels with the public key, and the FFDHE primes are in the
    source -- so the scan declassifies one comparison per limb and branches
    on it, and the number of doublings that follows depends on the modulus's
    length but on nothing secret. *)

(** A limb that is set is a lower bound on the whole number: everything
    else in {!eval}'s expansion around limb [k] is a natural number.  This
    is how the seed below finds a power of the radix under the modulus
    without computing anything. *)
let num_ge_at (v: Seq.seq S64.t) (k: nat { k < Seq.length v })
  : Lemma (requires 0 < S64.v (Seq.index v k)) (ensures wt k <= num v)
  = let n = Seq.length (vals v) in
    eval_at (vals v) k;
    Math.lemma_mult_le_left (wt k) 1
      (Seq.index (vals v) k + base * eval (Seq.slice (vals v) (k + 1) n))

(** The modulus's bottom limb is what it is modulo the radix, which is the
    shape {!mont_cancel} wants. *)
let modulus_low (v: Seq.seq S64.t { 0 < Seq.length v })
  : Lemma (num v % base == S64.v (Seq.index v 0))
  = wt_zero (); wt_succ 0; pre_zero v; pre_snoc v 0; pre_mod v 1

let dbl_mod (nN: pos) (i: nat)
  : Lemma (((pow2 i % nN) + (pow2 i % nN)) % nN == pow2 (i + 1) % nN)
  = Math.lemma_mod_add_distr (pow2 i % nN) (pow2 i) nN;
    Math.lemma_mod_add_distr (pow2 i) (pow2 i) nN;
    Math.pow2_double_sum i

(** [mu] exists only for an odd modulus, and oddness is what keeps the seed
    from landing exactly on the modulus.  Reading it back off [mu] costs one
    lemma and saves a precondition at eleven call sites. *)
let odd_mu (mu m0: nat)
  : Lemma (requires (mu * m0 + 1) % base == 0) (ensures m0 % 2 == 1)
  = assert_norm (pow2 1 == 2);
    Math.pow2_modulo_modulo_lemma_1 (mu * m0 + 1) 1 rad;
    Math.lemma_mod_mul_distr_r mu m0 2

(** Only the bottom limb decides the parity, the radix being even. *)
let num_odd (v: Seq.seq S64.t)
  : Lemma (requires 0 < Seq.length v /\ S64.v (Seq.index v 0) % 2 == 1)
          (ensures num v % 2 == 1)
  = let n = Seq.length (vals v) in
    let hi = eval (Seq.slice (vals v) 1 n) in
    eval_at (vals v) 0;
    eval_empty (Seq.slice (vals v) 0 0);
    wt_zero ();
    Math.pow2_plus 1 (rad - 1);
    Math.lemma_mod_mul_distr_l base hi 2;
    Math.lemma_mod_add_distr (S64.v (Seq.index v 0)) (base * hi) 2

(** An odd number above one is not a power of the radix. *)
let seed_lt (nN: nat) (k: nat)
  : Lemma (requires 1 < nN /\ nN % 2 == 1 /\ wt k <= nN) (ensures wt k < nN)
  = assert_norm (pow2 1 == 2);
    if k = 0 then wt_zero () else Math.pow2_plus 1 (rad * k - 1)

#push-options "--fuel 2 --ifuel 1"
let pw_one (a: nat) : Lemma (pw a 1 == a) = ()

(** [pw] at base two is [pow2].  The seed is counted in the latter, because
    that is what a modular doubling speaks, and the ladder in the former,
    because that is what the exponentiation lemmas speak. *)
let rec pw_pow2 (e: nat) : Lemma (ensures pw 2 e == pow2 e) (decreases e)
  = if e = 0 then ()
    else begin
      pw_pow2 (e - 1);
      assert_norm (pow2 1 == 2);
      Math.pow2_plus 1 (e - 1)
    end

(** A bit index is smaller than the power it names, which is all the
    ladder's counters need in order to fit in a [size_t]. *)
let rec pow2_ge (e: nat) : Lemma (ensures e < pow2 e) (decreases e)
  = if e = 0 then ()
    else begin
      pow2_ge (e - 1);
      assert_norm (pow2 1 == 2);
      Math.pow2_plus 1 (e - 1)
    end

(** Only the zeroth power of two is one, so a descending [p] that is still
    above one has a bit index left to spend. *)
let pow2_one (e: nat) : Lemma (requires 1 < pow2 e) (ensures 1 <= e)
  = assert_norm (pow2 0 == 1)
#pop-options

let pw_succ (a e: nat) : Lemma (pw a (e + 1) == a * pw a e)
  = pw_add a e 1; pw_one a

let pw_dbl (a e: nat) : Lemma (pw a (e + e) == pw a (2 * e)) = ()

(** Regrouping a product of two Montgomery representatives. *)
let mul_expand (p q rr: nat)
  : Lemma ((p * rr) * (q * rr) == (p * q * rr) * rr)
  = Math.paren_mul_right p rr (q * rr);
    Math.paren_mul_right rr q rr;
    Math.swap_mul rr q;
    Math.paren_mul_right p (q * rr) rr;
    Math.paren_mul_right p q rr

(** A Montgomery product of representatives is a representative of the
    product: this is the one arithmetic fact every ladder here runs on. *)
let exp_mul (r x y p q rr nN: nat)
  : Lemma (requires 0 < nN /\ x == (p * rr) % nN /\ y == (q * rr) % nN /\
                    (r * rr) % nN == (x * y) % nN)
          (ensures (r * rr) % nN == (((p * q * rr) % nN) * rr) % nN)
  = Math.lemma_mod_mul_distr_l (p * rr) y nN;
    Math.lemma_mod_mul_distr_r (p * rr) (q * rr) nN;
    mul_expand p q rr;
    Math.lemma_mod_mul_distr_l (p * q * rr) rr nN

(** Squaring a representative doubles the exponent. *)
let exp_sq_step (acc0 sq anum e rr nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ acc0 == (pw anum e * rr) % nN /\
                    sq < nN /\ (sq * rr) % nN == (acc0 * acc0) % nN)
          (ensures sq == (pw anum (e + e) * rr) % nN)
  = let pe = pw anum e in
    exp_mul sq acc0 acc0 pe pe rr nN;
    mont_cancel sq ((pe * pe * rr) % nN) nN mu m0 k;
    assert (sq == (pe * pe * rr) % nN);
    pw_add anum e e

(** Doubling a representative of [2 ^ e] gives one of [2 ^ (e + 1)]: the
    ladder's other move, and the only one the seed has. *)
let mont_dbl (a e rr nN: nat)
  : Lemma (requires 0 < nN /\ a == (pw 2 e * rr) % nN)
          (ensures (a + a) % nN == (pw 2 (e + 1) * rr) % nN)
  = pw_succ 2 e;
    Math.lemma_mod_mul_distr_r 2 (pw 2 e * rr) nN;
    Math.paren_mul_right 2 (pw 2 e) rr

(** The exponent a rung reaches, transported to an equal one.  The two
    branches of {!ladder_step} arrive at [2 e + SZ.v bit] with the bit
    known to be zero or one, and the contract asks for [2 e] or [2 e + 1].
    Those are the same number, but merging them underneath [pw] is a
    propagation from the arithmetic theory into congruence closure that the
    solver, in a body that carries five arrays, will not make: left to
    itself it searches for well over an hour. *)
let pw_ext (a x y: nat) : Lemma (requires x == y) (ensures pw a x == pw a y) = ()

(** One step down a descending power of two, at the level of the exponent:
    the bits of [n] above [q] are twice those above [q + q], plus one. *)
let half_split (n: nat) (q: pos)
  : Lemma (n / q == n / (q + q) + n / (q + q) + n / q % 2)
  = Math.division_multiplication_lemma n q 2;
    Math.euclidean_division_definition (n / q) 2

let div_one (n: nat) (q: pos)
  : Lemma (requires q <= n /\ n < q + q) (ensures n / q == 1)
  = Math.small_div (n - q) q;
    Math.lemma_div_plus (n - q) 1 q

#push-options "--z3rlimit 300"

(** [top_limb nmod nn] is the index of the topmost nonzero limb of the
    modulus -- or rather, all the caller needs of it: an index whose weight
    is at or below the modulus.  Limb zero always qualifies, the modulus
    being greater than one, so the scan never has to report failure. *)
fn top_limb (nmod: A.array S64.t) (nn: SZ.t) (#pn: perm)
            (#vn: erased (s: Seq.seq S64.t { 1 < num s }))
requires A.pts_to nmod #pn vn **
  pure (Seq.length vn == SZ.v nn /\ 0 < SZ.v nn)
returns k: SZ.t
ensures A.pts_to nmod #pn vn **
  pure (SZ.v k < SZ.v nn /\ wt (SZ.v k) <= num vn)
{
  A.pts_to_len nmod;
  wt_zero ();
  assert_norm (pow2 64 > 1);
  let z = S64.zero;
  let mut k = 0sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi nn)
  invariant exists* (vi: SZ.t) (vk: SZ.t).
    pts_to i vi ** pts_to k vk ** A.pts_to nmod #pn vn **
    pure (SZ.v vi <= SZ.v nn /\ SZ.v vk < SZ.v nn /\ wt (SZ.v vk) <= num vn)
  decreases (SZ.v nn - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(nmod.(vi));
    let m = S64.eq_mask x z;
    let nz = U64.eq (Declassify.u64 m) 0uL;
    if nz {
      num_ge_at vn (SZ.v vi);
      k := vi;
    };
    i := SZ.add vi 1sz;
  };
  !k
}

(** [seed res nmod nn] is [2 ^ (rad * nn + 1) mod nmod], written as the
    Montgomery representative of [2 ^ 1]: the rung the ladder starts from.

    It begins at [wt k], the highest power of the radix that is below the
    modulus, which needs no reduction to write down, and doubles the [rad *
    (nn - k) + 1] remaining times. *)
fn seed (res: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t)
        (#vres: erased (Seq.seq S64.t)) (#pn: perm)
        (#vn: erased (s: Seq.seq S64.t { 1 < num s }))
requires A.pts_to res vres ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (2 * rad * SZ.v nn) /\ num vn % 2 == 1)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ num v < num vn /\
        num v == (pw 2 1 * wt (SZ.v nn)) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len nmod;
  let k = top_limb nmod nn;
  seed_lt (num vn) (SZ.v k);
  zero res nn;
  with v0. assert (A.pts_to res v0);
  pre_zeros v0 (SZ.v nn);
  pre_full v0;
  let one = S64.classify 1uL;
  A.((res.(k) <- one));
  num_upd v0 (SZ.v k) one;
  Math.small_mod (wt (SZ.v k)) (num vn);
  SZ.fits_lte (rad * (SZ.v nn - SZ.v k)) (2 * rad * SZ.v nn);
  SZ.fits_lte (rad * (SZ.v nn - SZ.v k) + 1) (2 * rad * SZ.v nn);
  let steps = SZ.add (SZ.mul 64sz (SZ.sub nn k)) 1sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi steps)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to nmod #pn vn **
    pure (SZ.v vi <= SZ.v steps /\ Seq.length v == SZ.v nn /\
          num v == pow2 (rad * SZ.v k + SZ.v vi) % num vn)
  decreases (SZ.v steps - SZ.v (!i))
  {
    let vi = !i;
    double_mod res nmod nn;
    dbl_mod (num vn) (rad * SZ.v k + SZ.v vi);
    i := SZ.add vi 1sz;
  };
  pw_one 2;
  Math.pow2_plus 1 (rad * SZ.v nn);
  ()
}

(** One rung: the exponent doubles, and then gains [bit].  Squaring in
    Montgomery form is what doubles it, and a modular doubling is what adds
    the one; the contract mentions no division, so the index arithmetic of
    the ladder and the arithmetic of the modulus never share a query. *)
(** The second half of a rung: add the exponent's bit, by doubling the
    accumulator modulo the modulus or not.

    It is a function of its own, and one that mentions only the two arrays
    it touches, for the reason {!pw_ext} gives: proved in place, at the end
    of a body that still carries five arrays and the whole squaring half,
    the merge of [2 e + SZ.v bit] with [2 e] runs for over an hour.  With
    the context cut down to this it is seconds. *)
inline_for_extraction
fn ladder_bit (res: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t)
              (e2: erased nat) (bit: SZ.t)
              (#vres: erased (Seq.seq S64.t)) (#pn: perm)
              (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        0 < SZ.v nn /\ SZ.v bit < 2 /\ num vres < num vn /\
        num vres == (pw 2 (reveal e2) * wt (SZ.v nn)) % num vn)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ num v < num vn /\
        num v == (pw 2 (reveal e2 + SZ.v bit) * wt (SZ.v nn)) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len nmod;
  if (SZ.eq bit 1sz) {
    with vhalf. assert (A.pts_to res vhalf);
    double_mod res nmod nn;
    mont_dbl (num vhalf) (reveal e2) (wt (SZ.v nn)) (num vn);
    pw_ext 2 (reveal e2 + 1) (reveal e2 + SZ.v bit);
    ()
  } else {
    pw_ext 2 (reveal e2) (reveal e2 + SZ.v bit);
    ()
  }
}

fn ladder_step (res: A.array S64.t) (t1: A.array S64.t) (t2: A.array S64.t)
               (wide: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t)
               (mu: S64.t) (e: erased nat) (bit: SZ.t)
               (#vres #vt1 #vt2 #vwide: erased (Seq.seq S64.t)) (#pn: perm)
               (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to t1 vt1 ** A.pts_to t2 vt2 **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vt1 == SZ.v nn /\
        Seq.length vt2 == SZ.v nn /\ Seq.length vwide == SZ.v nn + SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn) /\ SZ.v bit < 2 /\
        num vres < num vn /\
        num vres == (pw 2 (reveal e) * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to t1 v1 ** A.pts_to t2 v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        num v == (pw 2 (2 * reveal e + SZ.v bit) * wt (SZ.v nn)) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len t1;
  A.pts_to_len t2;
  A.pts_to_len wide;
  A.pts_to_len nmod;
  modulus_low vn;
  copy t1 res nn;
  mont_mul t2 res t1 wide nmod nn mu;
  with vsq. assert (A.pts_to t2 vsq);
  exp_sq_step (num vres) (num vsq) 2 (reveal e) (wt (SZ.v nn)) (num vn)
              (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
  pw_dbl 2 (reveal e);
  copy res t2 nn;
  ladder_bit res nmod nn (hide (2 * reveal e)) bit;
  ()
}

(** [precomp res t1 t2 wide nmod nn mu] is [res = R^2 mod nmod].  [t1] and
    [t2] are [n] limbs of scratch and [wide] is [2n]; [mu] is what
    {!mont_mu} makes of the modulus's bottom limb.

    The exponent reached after a rung is always [mm / p], for [mm == rad *
    nn] and a [p] that starts at the highest power of two below [mm] and
    halves: one at the start, and [mm] at the end. *)
fn precomp (res: A.array S64.t) (t1: A.array S64.t) (t2: A.array S64.t)
           (wide: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
           (#vres #vt1 #vt2 #vwide: erased (Seq.seq S64.t)) (#pn: perm)
           (#vn: erased (s: Seq.seq S64.t { 1 < num s }))
requires A.pts_to res vres ** A.pts_to t1 vt1 ** A.pts_to t2 vt2 **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vt1 == SZ.v nn /\
        Seq.length vt2 == SZ.v nn /\ Seq.length vwide == SZ.v nn + SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\ SZ.fits (2 * rad * SZ.v nn) /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to t1 v1 ** A.pts_to t2 v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
        num v == (wt (SZ.v nn) * wt (SZ.v nn)) % num vn)
{
  A.pts_to_len res;
  A.pts_to_len t1;
  A.pts_to_len t2;
  A.pts_to_len wide;
  A.pts_to_len nmod;
  SZ.fits_lte (SZ.v nn + SZ.v nn) (2 * rad * SZ.v nn);
  odd_mu (S64.v mu) (S64.v (Seq.index vn 0));
  num_odd vn;
  seed res nmod nn;

  let mm = SZ.mul 64sz nn;
  SZ.fits_lte 2 (2 * rad * SZ.v nn);
  let mut p = 1sz;
  let mut b = 0sz;
  while (let vp = !p; SZ.lte (SZ.mul 2sz vp) mm)
  invariant exists* (vp: SZ.t) (vb: SZ.t).
    pts_to p vp ** pts_to b vb **
    pure (SZ.v vp == pow2 (SZ.v vb) /\ SZ.v vp <= SZ.v mm /\
          SZ.fits (2 * SZ.v vp) /\ SZ.fits (SZ.v vb + 1))
  decreases (SZ.v mm - SZ.v (!p))
  {
    let vp = !p;
    let vb = !b;
    assert_norm (pow2 1 == 2);
    Math.pow2_plus 1 (SZ.v vb);
    pow2_ge (SZ.v vb + 1);
    SZ.fits_lte (2 * (2 * SZ.v vp)) (2 * rad * SZ.v nn);
    SZ.fits_lte (SZ.v vb + 2) (2 * rad * SZ.v nn);
    p := SZ.mul 2sz vp;
    b := SZ.add vb 1sz;
  };
  with vp0. assert (pts_to p vp0);
  div_one (SZ.v mm) (SZ.v vp0);

  while (let vp = !p; SZ.gt vp 1sz)
  invariant exists* (vp: SZ.t) (vb: SZ.t) (v v1 v2 v3: Seq.seq S64.t).
    pts_to p vp ** pts_to b vb ** A.pts_to res v ** A.pts_to t1 v1 **
    A.pts_to t2 v2 ** A.pts_to wide v3 ** A.pts_to nmod #pn vn **
    pure (SZ.v vp == pow2 (SZ.v vb) /\ 0 < SZ.v vp /\
          Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
          Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
          num v < num vn /\
          num v == (pw 2 (SZ.v mm / SZ.v vp) * wt (SZ.v nn)) % num vn)
  decreases (SZ.v (!p))
  {
    let vp = !p;
    let vb = !b;
    assert_norm (pow2 1 == 2);
    pow2_one (SZ.v vb);
    Math.pow2_plus 1 (SZ.v vb - 1);
    let q = SZ.div vp 2sz;
    assert (pure (SZ.v q + SZ.v q == SZ.v vp));
    half_split (SZ.v mm) (SZ.v q);
    let d = SZ.rem (SZ.div mm q) 2sz;
    ladder_step res t1 t2 wide nmod nn mu (hide (SZ.v mm / SZ.v vp)) d;
    p := q;
    b := SZ.sub vb 1sz;
  };
  pw_pow2 (SZ.v mm);
  ()
}
#pop-options

(** {2 Plain remainder}

    With the constant in hand, reducing a [2n]-limb number modulo the
    modulus is two Montgomery steps: one takes a factor of [R] out, the
    other puts it back. *)

let mod_chain (r acc rr nN va: nat)
  : Lemma (requires 0 < nN /\ (r * rr) % nN == (acc * ((rr * rr) % nN)) % nN /\
                    (acc * rr) % nN == va % nN)
          (ensures (r * rr) % nN == ((va % nN) * rr) % nN)
  = Math.lemma_mod_mul_distr_r acc (rr * rr) nN;
    Math.paren_mul_right acc rr rr;
    Math.lemma_mod_mul_distr_l (acc * rr) rr nN;
    Math.lemma_mod_mul_distr_l (va % nN) rr nN;
    Math.lemma_mod_twice va nN

#push-options "--z3rlimit 300"

(** [modulo res a acc r2 nmod nn mu] is [res = a mod nmod], for a [2n]-limb
    [a] below the modulus times [R].  [a] is clobbered -- it doubles as the
    scratch of the second step -- and [acc] is [n] limbs of scratch. *)
fn modulo (res: A.array S64.t) (a: A.array S64.t) (acc: A.array S64.t)
          (r2: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
          (#vres #vacc: erased (Seq.seq S64.t)) (#va: erased (Seq.seq S64.t))
          (#pr #pn: perm) (#vr2: erased (Seq.seq S64.t))
          (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a va ** A.pts_to acc vacc **
         A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length va == SZ.v nn + SZ.v nn /\
        Seq.length vacc == SZ.v nn /\ Seq.length vr2 == SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn) /\
        num va < num vn * wt (SZ.v nn) /\
        num vr2 == (wt (SZ.v nn) * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t) (v2: Seq.seq S64.t) (v3: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a v2 ** A.pts_to acc v3 **
  A.pts_to r2 #pr vr2 ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length v2 == SZ.v nn + SZ.v nn /\
        Seq.length v3 == SZ.v nn /\ num v == num va % num vn)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len acc;
  A.pts_to_len r2;
  A.pts_to_len nmod;
  wt_zero ();
  wt_succ 0;
  pre_zero vn;
  pre_snoc vn 0;
  pre_mod vn 1;
  reduction acc a nmod nn mu;
  with vacc1. assert (A.pts_to acc vacc1);
  mont_mul res acc r2 a nmod nn mu;
  with v. assert (A.pts_to res v);
  mod_chain (num v) (num vacc1) (wt (SZ.v nn)) (num vn) (num va);
  mont_cancel (num v) (num va % num vn) (num vn) (S64.v mu)
              (S64.v (Seq.index vn 0)) (SZ.v nn);
  ()
}

#pop-options

#pop-options
