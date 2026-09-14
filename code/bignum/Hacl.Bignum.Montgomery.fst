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
    computes it with five steps of Hensel lifting -- [x := x * (2 - m0 * x)]
    doubles the number of correct bits each time, so one, two, four, eight,
    sixteen, thirty-two.

    {b Why [res] and [c] are separate.}  The reduction consumes a [2n]-limb
    number and produces an [n]-limb one.  HACL* reduces in place and then
    copies; here the input array is explicitly clobbered and the output is
    its own array, which is what separation logic wants and costs nothing. *)
module Hacl.Bignum.Montgomery

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb32
open Hacl.Bignum.Base

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The inverse of a limb}

    Hensel's lemma in two lines: if [m0 * x = 1] to [k] bits then
    [m0 * (x * (2 - m0 * x)) = 1 - (1 - m0 * x)^2] is [1] to [2k] bits.
    Starting from [x = 1], which is correct to one bit because the modulus
    is odd, five steps reach thirty-two. *)

inline_for_extraction
let inv_step (m0 x: S32.t)
  : r: S32.t { S32.v r ==
                 (S32.v x * ((2 - (S32.v m0 * S32.v x) % pow2 32) % pow2 32)) % pow2 32 }
  = S32.mul_mod x (S32.sub_mod (S32.classify 2ul) (S32.mul_mod m0 x))

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

(** What holds modulo [2^32] holds modulo any power of two below it. *)
let narrow (a b: int) (k: nat { k <= 32 })
  : Lemma (requires a % pow2 32 == b % pow2 32)
          (ensures a % pow2 k == b % pow2 k)
  = Math.pow2_plus k (32 - k);
    Math.modulo_modulo_lemma a (pow2 k) (pow2 (32 - k));
    Math.modulo_modulo_lemma b (pow2 k) (pow2 (32 - k))

let inv_step_ok (mv xv: nat) (m: pos) (r: nat)
  : Lemma (requires 2 * m <= 32 /\ (mv * xv) % pow2 m == 1 /\
                    r == (xv * ((2 - (mv * xv) % pow2 32) % pow2 32)) % pow2 32)
          (ensures (mv * r) % pow2 (2 * m) == 1)
  = let p = mv * xv in
    let bq = pow2 32 in
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
  : Lemma (requires (mv * xv) % pow2 32 == 1 /\ r == (0 - xv) % pow2 32)
          (ensures (r * mv + 1) % base == 0)
  = assert (base == pow2 32);
    Math.lemma_mod_mul_distr_l (0 - xv) mv (pow2 32);
    Math.paren_mul_right 0 xv mv;
    Math.swap_mul xv mv;
    assert ((r * mv) % pow2 32 == (- (mv * xv)) % pow2 32);
    Math.lemma_mod_add_distr 1 (r * mv) (pow2 32);
    Math.lemma_mod_add_distr 1 (- (mv * xv)) (pow2 32);
    Math.lemma_mod_plus 0 1 (pow2 32)

(** [mont_mu m0] is the [mu] with [mu * m0 + 1 = 0 mod base].  The modulus
    must be odd; every modulus Montgomery arithmetic applies to is. *)
inline_for_extraction
let mont_mu (m0: S32.t)
  : Pure S32.t (requires S32.v m0 % 2 == 1)
               (ensures fun r -> (S32.v r * S32.v m0 + 1) % base == 0)
  = let x0 = S32.classify 1ul in
    assert_norm (pow2 1 == 2);
    assert (S32.v m0 * S32.v x0 == S32.v m0);
    let x1 = inv_step m0 x0 in inv_step_ok (S32.v m0) (S32.v x0) 1 (S32.v x1);
    let x2 = inv_step m0 x1 in inv_step_ok (S32.v m0) (S32.v x1) 2 (S32.v x2);
    let x3 = inv_step m0 x2 in inv_step_ok (S32.v m0) (S32.v x2) 4 (S32.v x3);
    let x4 = inv_step m0 x3 in inv_step_ok (S32.v m0) (S32.v x3) 8 (S32.v x4);
    let x5 = inv_step m0 x4 in inv_step_ok (S32.v m0) (S32.v x4) 16 (S32.v x5);
    (* [x5] inverts [m0]; negating it gives the [mu] a reduction wants. *)
    let r = S32.sub_mod S32.zero x5 in
    negate (S32.v m0) (S32.v x5) (S32.v r);
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

fn copy_upper (res: A.array S32.t) (c: A.array S32.t) (nn: SZ.t)
              (#vres: erased (Seq.seq S32.t)) (#pc: perm)
              (#vc: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to c #pc vc **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vc == SZ.v nn + SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn))
ensures exists* (v: Seq.seq S32.t).
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
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
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
              (S32.v ci) (SZ.v nn) (SZ.v vi);
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
let flag_mask (borrow ov m: S32.t)
  : Lemma (requires S32.v borrow <= 1 /\ S32.v ov <= 1 /\
                    m == S32.eq_mask (S32.sub_mod borrow ov) (S32.classify 1ul))
          (ensures is_mask m /\
                   (S32.v borrow == 1 /\ S32.v ov == 0 ==> mask_bit m == 1) /\
                   (~(S32.v borrow == 1 /\ S32.v ov == 0) ==> mask_bit m == 0))
  = assert_norm (pow2 32 == 4294967296);
    Math.small_mod (pow2 32 - 1) (pow2 32);
    Math.lemma_mod_plus (S32.v borrow - S32.v ov) 1 (pow2 32);
    if S32.v borrow >= S32.v ov then
      Math.small_mod (S32.v borrow - S32.v ov) (pow2 32)

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
fn reduction (res: A.array S32.t) (c: A.array S32.t) (nmod: A.array S32.t)
             (nn: SZ.t) (mu: S32.t)
             (#vres: erased (Seq.seq S32.t)) (#vc: erased (Seq.seq S32.t))
             (#pn: perm)
             (#vn: erased (s: Seq.seq S32.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to c vc ** A.pts_to nmod #pn vn **
  pure (Seq.length vres == SZ.v nn /\ Seq.length vc == SZ.v nn + SZ.v nn /\
        Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
        SZ.fits (SZ.v nn + SZ.v nn) /\
        num vc < num vn * wt (SZ.v nn) /\
        (S32.v mu * S32.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S32.t) (v2: Seq.seq S32.t).
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
  eval_bnd (vals vn);
  let mut i = 0sz;
  let mut ov = S32.zero;
  while (let vi = !i; SZ.lt vi nn)
  invariant exists* (vi: SZ.t) (vov: S32.t) (varr: Seq.seq S32.t).
    pts_to i vi ** pts_to ov vov ** A.pts_to c varr ** A.pts_to nmod #pn vn **
    pure (SZ.v vi <= SZ.v nn /\ Seq.length varr == SZ.v nn + SZ.v nn /\
          S32.v vov <= 1 /\ num varr % wt (SZ.v vi) == 0 /\
          (num varr + S32.v vov * wt (SZ.v vi + SZ.v nn)) % num vn ==
            num vc % num vn /\
          num varr + S32.v vov * wt (SZ.v vi + SZ.v nn) <
            num vc + wt (SZ.v vi) * num vn)
  decreases (SZ.v nn - SZ.v (!i))
  {
    with varr. assert (A.pts_to c varr);
    let vi = !i;
    let vov = !ov;
    let ci = A.(c.(vi));
    let qi = S32.mul_mod ci mu;
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
    red_column (num v2) (num v1) (num varr) (S32.v ov2) (S32.v vov) (S32.v cr)
               (S32.v old) (S32.v lot) (S32.v qi) (num vn) (S32.v ci) (S32.v mu)
               (S32.v (Seq.index vn 0)) (num vc) (SZ.v vi) (SZ.v nn);
    ov := ov2;
    i := SZ.add vi 1sz;
  };
  with varr. assert (A.pts_to c varr);
  let vov = !ov;
  pre_mod varr (SZ.v nn);
  copy_upper res c nn;
  with va. assert (A.pts_to res va);
  eval_bnd (vals va);
  mont_top (num varr) (num va) (S32.v vov) (SZ.v nn);
  mont_split (num varr + S32.v vov * wt (SZ.v nn + SZ.v nn))
             (num va + S32.v vov * wt (SZ.v nn)) (num vc) (num vn) (wt (SZ.v nn));
  let borrow = sub_from res nmod nn;
  with v1. assert (A.pts_to res v1);
  eval_bnd (vals v1);
  let mask = S32.eq_mask (S32.sub_mod borrow vov) (S32.classify 1ul);
  flag_mask borrow vov mask;
  mask_bit_ok mask;
  let c2 = add_masked res nmod nn mask (hide (mask_bit mask));
  with v2. assert (A.pts_to res v2);
  eval_bnd (vals v2);
  final_cases (num va) (num vn) (S32.v vov) (S32.v borrow) (num v1)
              (mask_bit mask) (num v2) (S32.v c2) (wt (SZ.v nn));
  mont_result (num v2) (num va + S32.v vov * wt (SZ.v nn)) (num vn)
              (wt (SZ.v nn)) (num varr + S32.v vov * wt (SZ.v nn + SZ.v nn));
  ()
}

#pop-options

#pop-options
