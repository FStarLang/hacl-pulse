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


(** {2 Windows}

    Four bits at a time rather than one.  A rung of the wide ladder squares
    the accumulator four times and then multiplies in [a^d], where [d] is
    the next four bits of the exponent: five multiplications per four bits
    against the eight the single-bit ladder spends.  The price is sixteen
    precomputed powers, and a lookup that must not let [d] reach the address
    bus -- see {!Hacl.Bignum.Base.table_select}. *)

(** One step down the exponent, four bits at a time. *)
let digit_split (n i: nat)
  : Lemma (n / pow2 i == 16 * (n / pow2 (i + 4)) + n / pow2 i % 16)
  = assert_norm (pow2 4 == 16);
    Math.pow2_plus i 4;
    Math.division_multiplication_lemma n (pow2 i) (pow2 4);
    Math.euclidean_division_definition (n / pow2 i) 16

(** {!digit_split} lifted through {!pw}, with no precondition: the whole
    point is that the caller never has to prove the index equality in a
    context already full of nonlinear Montgomery facts. *)
let pw_digit (a n i: nat)
  : Lemma (pw a (16 * (n / pow2 (i + 4)) + n / pow2 i % 16) == pw a (n / pow2 i))
  = digit_split n i

#push-options "--fuel 2 --ifuel 1"
let pw_one (a: nat) : Lemma (pw a 1 == a) = ()
#pop-options

(** Congruence for {!pw}, stated so that the solver is handed the
    equality rather than left to find it: the ladder's exponents are
    arithmetic, and matching [pw a (e + e)] against [pw a (2 * e)] by
    congruence closure alone turns out to be ruinously expensive. *)
let pw_cong (a x y: nat) : Lemma (requires x == y) (ensures pw a x == pw a y) = ()

(** And the same for {!Prims.pow2}, for the same reason. *)
let pow2_cong (x y: nat) : Lemma (requires x == y) (ensures pow2 x == pow2 y) = ()


(** Multiplying two Montgomery representatives of powers adds the
    exponents.  {!exp_mul_step} is this with [d] fixed at one. *)
let exp_mul_gen (sq td pr anum m d rr nN mu m0: nat) (k: nat)
  : Lemma (requires 0 < nN /\ (mu * m0 + 1) % base == 0 /\ nN % base == m0 /\
                    rr == wt k /\ sq == (pw anum m * rr) % nN /\
                    td == (pw anum d * rr) % nN /\
                    pr < nN /\ (pr * rr) % nN == (sq * td) % nN)
          (ensures pr == (pw anum (m + d) * rr) % nN)
  = exp_mul pr sq td (pw anum m) (pw anum d) rr nN;
    mont_cancel pr ((pw anum m * pw anum d * rr) % nN) nN mu m0 k;
    pw_add anum m d

(** The window table lives in one flat array of sixteen [nn]-limb numbers.
    [entry] is total -- out of range it is the empty sequence -- so that the
    loop invariants below typecheck without dragging the bound on [d * nn]
    through every one of them. *)
let entry (vtbl: Seq.seq S64.t) (nn: nat) (d: nat) : Seq.seq S64.t =
  if d * nn + nn <= Seq.length vtbl
  then Seq.slice vtbl (d * nn) (d * nn + nn)
  else Seq.empty #S64.t

let entry_fits (d nn: nat) : Lemma (requires d < 16)
                                   (ensures d * nn + nn <= 16 * nn)
  = Math.lemma_mult_le_right nn (d + 1) 16

#push-options "--ifuel 1"
let entry_def (vtbl: Seq.seq S64.t) (nn d: nat)
  : Lemma (requires d * nn + nn <= Seq.length vtbl)
          (ensures entry vtbl nn d == Seq.slice vtbl (d * nn) (d * nn + nn))
  = ()
#pop-options

(** [tbl_ok vtbl nn anum rr nN upto] is "the first [upto] entries hold the
    first [upto] powers of [anum], in Montgomery form and reduced". *)
let tbl_ok (vtbl: Seq.seq S64.t) (nn anum rr: nat) (nN: pos) (upto: nat) : prop =
  forall (d: nat). d < upto ==>
    (num (entry vtbl nn d) == (pw anum d * rr) % nN /\
     num (entry vtbl nn d) < nN)

(** Reading one entry back out.  Spelled as a lemma so that the caller's
    query never has to instantiate the quantifier itself. *)
let tbl_get (vtbl: Seq.seq S64.t) (nn anum rr: nat) (nN: pos) (d: nat)
  : Lemma (requires tbl_ok vtbl nn anum rr nN 16 /\ d < 16)
          (ensures num (entry vtbl nn d) == (pw anum d * rr) % nN /\
                   num (entry vtbl nn d) < nN)
  = ()

#push-options "--ifuel 1 --z3rlimit 100"

(** Writing one entry leaves the others where they were. *)
let entry_untouched (v v': Seq.seq S64.t) (nn e d: nat)
  : Lemma (requires Seq.length v == 16 * nn /\ Seq.length v' == 16 * nn /\
                    e < 16 /\ d < 16 /\ ~(d == e) /\
                    (forall (j: nat). j < 16 * nn ==>
                       (j < e * nn \/ e * nn + nn <= j) ==>
                       Seq.index v' j == Seq.index v j))
          (ensures entry v' nn d == entry v nn d)
  = entry_fits d nn;
    entry_fits e nn;
    entry_def v nn d;
    entry_def v' nn d;
    if d < e then Math.lemma_mult_le_right nn (d + 1) e
             else Math.lemma_mult_le_right nn (e + 1) d;
    Seq.lemma_eq_intro (Seq.slice v' (d * nn) (d * nn + nn))
                       (Seq.slice v (d * nn) (d * nn + nn))

(** And it puts what was asked for into the one it does write. *)
let entry_written (v': Seq.seq S64.t) (src: Seq.seq S64.t) (nn e: nat)
  : Lemma (requires Seq.length v' == 16 * nn /\ Seq.length src == nn /\
                    e < 16 /\
                    (forall (j: nat). j < nn ==>
                       Seq.index v' (e * nn + j) == Seq.index src j))
          (ensures entry v' nn e == src)
  = entry_fits e nn;
    entry_def v' nn e;
    Seq.lemma_eq_intro (Seq.slice v' (e * nn) (e * nn + nn)) src

#pop-options

(** Extending the table by one entry: the store wrote what we asked for
    into slot [e] and left the ones below it alone. *)
#push-options "--ifuel 1 --z3rlimit 500"

(** What one [table_store] does to the table, entry by entry rather than
    limb by limb. *)
let tbl_shape (v v' src: Seq.seq S64.t) (nn e: nat)
  : Lemma (requires Seq.length v == 16 * nn /\ Seq.length v' == 16 * nn /\
                    Seq.length src == nn /\ e < 16 /\
                    e * nn + nn <= 16 * nn /\
                    (forall (j: nat). j < nn ==>
                       Seq.index v' (e * nn + j) == Seq.index src j) /\
                    (forall (j: nat). j < 16 * nn ==>
                       (j < e * nn \/ e * nn + nn <= j) ==>
                       Seq.index v' j == Seq.index v j))
          (ensures (forall (dd: nat). dd < e ==> entry v' nn dd == entry v nn dd) /\
                   entry v' nn e == src)
  = entry_written v' src nn e;
    let aux (dd: nat) : Lemma (dd < e ==> entry v' nn dd == entry v nn dd)
      = if dd < e then entry_untouched v v' nn e dd else () in
    FStar.Classical.forall_intro aux

(** The two cases of the invariant's extension, each stated on its own so
    that neither is proved in the presence of the other's hypotheses. *)
let tbl_below (v v': Seq.seq S64.t) (nn anum rr: nat) (nN: pos) (e dd: nat)
  : Lemma (requires tbl_ok v nn anum rr nN e /\ dd < e /\
                    entry v' nn dd == entry v nn dd)
          (ensures num (entry v' nn dd) == (pw anum dd * rr) % nN /\
                   num (entry v' nn dd) < nN)
  = ()

let tbl_at (v': Seq.seq S64.t) (src: Seq.seq S64.t) (nn anum rr: nat)
           (nN: pos) (e dd: nat)
  : Lemma (requires entry v' nn e == src /\ num src == (pw anum e * rr) % nN /\
                    num src < nN /\ dd == e)
          (ensures num (entry v' nn dd) == (pw anum dd * rr) % nN /\
                   num (entry v' nn dd) < nN)
  = pw_cong anum dd e

(** And what that does to the invariant. *)
let tbl_extend (v v' src: Seq.seq S64.t) (nn anum rr: nat) (nN: pos) (e: nat)
  : Lemma (requires Seq.length v == 16 * nn /\ Seq.length v' == 16 * nn /\
                    Seq.length src == nn /\ e < 16 /\
                    e * nn + nn <= 16 * nn /\
                    tbl_ok v nn anum rr nN e /\
                    num src == (pw anum e * rr) % nN /\ num src < nN /\
                    (forall (dd: nat). dd < e ==>
                       entry v' nn dd == entry v nn dd) /\
                    entry v' nn e == src)
          (ensures tbl_ok v' nn anum rr nN (e + 1))
  = introduce forall (dd: nat). dd < e + 1 ==>
      (num (entry v' nn dd) == (pw anum dd * rr) % nN /\
       num (entry v' nn dd) < nN)
    with introduce _ ==> _
    with (if dd < e then tbl_below v v' nn anum rr nN e dd
          else begin assert (dd == e); tbl_at v' src nn anum rr nN e dd end)
#pop-options

(** Where entry [vd] of the table starts, and that it is addressable. *)
let store_off (vd nn: nat)
  : Lemma (requires vd < 16 /\ SZ.fits (16 * nn))
          (ensures vd * nn + nn <= 16 * nn /\ SZ.fits (vd * nn) /\
                   SZ.fits (vd * nn + nn))
  = Math.lemma_mult_le_right nn (vd + 1) 16;
    SZ.fits_lte (vd * nn) (16 * nn);
    SZ.fits_lte (vd * nn + nn) (16 * nn)

(** A bit position below the end of the array names a limb inside it. *)
let digit_in_range (x l: nat) : Lemma (requires x < 64 * l) (ensures x / 64 < l)
  = Math.lemma_div_mod x 64;
    if x / 64 >= l then Math.lemma_mult_le_right 64 l (x / 64) else ()

let sz_sixteen (x: SZ.t) : Lemma (requires SZ.lt x 16sz == false /\ SZ.v x <= 16)
                                 (ensures SZ.v x == 16) = ()

(** Stepping the ladder counter down by a whole window. *)
let step4 (x: nat) : Lemma (requires x > 0 /\ x % 4 == 0)
                           (ensures 4 <= x /\ (x - 4) % 4 == 0) = ()

(** Two facts the solver knows but will not always find in a context this
    size: a power of two is positive, and dividing by one keeps a natural
    number natural. *)
let pow2_pos (i: nat) : Lemma (pow2 i > 0)
  = Math.pow2_le_compat i 0; assert_norm (pow2 0 == 1)

let div_nonneg (x: nat) (i: nat)
  : Lemma (requires pow2 i > 0) (ensures x / pow2 i >= 0) = ()

(** The four steps of a rung, as equalities with nothing left to discharge
    at the point of use.  A conditional congruence would do just as well in
    principle, but its hypothesis has to be proved in the caller's context,
    and in the caller's context even [e + e == 2 * e] is out of reach. *)
let pw_dbl (a e: nat) : Lemma (pw a (e + e) == pw a (2 * e)) = ()
let pw_q4 (a e: nat) : Lemma (pw a (2 * (2 * e)) == pw a (4 * e)) = ()
let pw_q8 (a e: nat) : Lemma (pw a (2 * (4 * e)) == pw a (8 * e)) = ()
let pw_q16 (a e: nat) : Lemma (pw a (2 * (8 * e)) == pw a (16 * e)) = ()

#push-options "--z3rlimit 300"

(** One squaring of the accumulator, in Montgomery form.  Four of these and
    a table multiply are a rung of the wide ladder; pulling it out of the
    loop body is what keeps the number of arrays the solver has to track at
    once down to something it will accept. *)
fn mont_sq (acc: A.array S64.t) (res: A.array S64.t) (t: A.array S64.t)
           (wide: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
           (anum: erased nat) (e: erased nat)
           (#vacc #vres #vt #vwide: erased (Seq.seq S64.t)) (#pn: perm)
           (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to acc vacc ** A.pts_to res vres ** A.pts_to t vt **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
  pure (Seq.length vacc == SZ.v nn /\ Seq.length vres == SZ.v nn /\
        Seq.length vt == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        num vacc < num vn /\
        num vacc == (pw anum e * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3: Seq.seq S64.t).
  A.pts_to acc v ** A.pts_to res v1 ** A.pts_to t v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        num v == (pw anum (2 * e) * wt (SZ.v nn)) % num vn)
{
  A.pts_to_len acc;
  A.pts_to_len res;
  A.pts_to_len t;
  A.pts_to_len wide;
  A.pts_to_len nmod;
  modulus_low vn;
  mont_sqr res acc wide nmod nn mu;
  with vsq. assert (A.pts_to res vsq);
  exp_sq_step (num vacc) (num vsq) anum e (wt (SZ.v nn)) (num vn)
              (S64.v mu) (S64.v (Seq.index vn 0)) (SZ.v nn);
  pw_dbl anum (reveal e);
  copy acc res nn;
  ()
}

(** Four of them, which is the whole squaring half of a rung. *)
fn mont_sq4 (acc: A.array S64.t) (res: A.array S64.t) (t: A.array S64.t)
            (wide: A.array S64.t) (nmod: A.array S64.t) (nn: SZ.t) (mu: S64.t)
            (anum: erased nat) (e: erased nat)
            (#vacc #vres #vt #vwide: erased (Seq.seq S64.t)) (#pn: perm)
            (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to acc vacc ** A.pts_to res vres ** A.pts_to t vt **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
  pure (Seq.length vacc == SZ.v nn /\ Seq.length vres == SZ.v nn /\
        Seq.length vt == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        num vacc < num vn /\
        num vacc == (pw anum e * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3: Seq.seq S64.t).
  A.pts_to acc v ** A.pts_to res v1 ** A.pts_to t v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        num v == (pw anum (16 * e) * wt (SZ.v nn)) % num vn)
{
  mont_sq acc res t wide nmod nn mu anum e;
  mont_sq acc res t wide nmod nn mu anum (hide (2 * reveal e));
  pw_q4 anum (reveal e);
  mont_sq acc res t wide nmod nn mu anum (hide (4 * reveal e));
  pw_q8 anum (reveal e);
  mont_sq acc res t wide nmod nn mu anum (hide (8 * reveal e));
  pw_q16 anum (reveal e);
  ()
}

#push-options "--z3rlimit 100"
(** The second half of a rung: look up [tbl[d]] in constant time and
    multiply it into the accumulator.  Its contract mentions no divisions
    and no powers of two -- the exponent [e2] and the digit [d] are opaque
    naturals -- which keeps this query small and, more importantly, keeps
    the caller's context free of everything that happens in here. *)
fn mont_win_mul (acc: A.array S64.t) (res: A.array S64.t) (t: A.array S64.t)
                (wide: A.array S64.t) (nmod: A.array S64.t)
                (tbl: A.array S64.t)
                (dig: S64.t) (nn: SZ.t) (mu: S64.t)
                (anum: erased nat) (e2: erased nat) (d: erased nat)
                (#vacc #vres #vt #vwide: erased (Seq.seq S64.t))
                (#pt #pn: perm)
                (#vtbl: erased (Seq.seq S64.t))
                (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to acc vacc ** A.pts_to res vres ** A.pts_to t vt **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
         A.pts_to tbl #pt vtbl **
  pure (Seq.length vacc == SZ.v nn /\ Seq.length vres == SZ.v nn /\
        Seq.length vt == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        Seq.length vtbl == 16 * SZ.v nn /\ SZ.fits (16 * SZ.v nn) /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        reveal d < 16 /\ S64.v dig == reveal d /\
        tbl_ok vtbl (SZ.v nn) anum (wt (SZ.v nn)) (num vn) 16 /\
        num vacc < num vn /\
        num vacc == (pw anum e2 * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v1 v2 v3: Seq.seq S64.t).
  A.pts_to acc vacc ** A.pts_to res v1 ** A.pts_to t v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn ** A.pts_to tbl #pt vtbl **
  pure (Seq.length v1 == SZ.v nn /\ Seq.length v2 == SZ.v nn /\
        Seq.length v3 == SZ.v nn + SZ.v nn /\ num v1 < num vn /\
        num v1 == (pw anum (reveal e2 + reveal d) * wt (SZ.v nn)) % num vn)
{
  A.pts_to_len acc;
  A.pts_to_len res;
  A.pts_to_len t;
  A.pts_to_len wide;
  A.pts_to_len nmod;
  A.pts_to_len tbl;
  modulus_low vn;
  entry_fits (reveal d) (SZ.v nn);
  table_select t tbl nn dig d;
  with vtd. assert (A.pts_to t vtd);
  entry_def vtbl (SZ.v nn) (reveal d);
  tbl_get vtbl (SZ.v nn) anum (wt (SZ.v nn)) (num vn) (reveal d);
  assert (pure (num vtd == (pw anum (reveal d) * wt (SZ.v nn)) % num vn));
  mont_mul res acc t wide nmod nn mu;
  with vpr. assert (A.pts_to res vpr);
  exp_mul_gen (num vacc) (num vtd) (num vpr) anum (reveal e2) (reveal d)
              (wt (SZ.v nn)) (num vn) (S64.v mu) (S64.v (Seq.index vn 0))
              (SZ.v nn);
  assert (pure (num vpr == (pw anum (reveal e2 + reveal d) *
                            wt (SZ.v nn)) % num vn));
}

#pop-options
#push-options "--z3rlimit 100"
(** A whole rung with the exponent left abstract: square four times, then
    multiply in [tbl[d]].  No divisions and no powers of two appear here,
    which is what keeps the query tractable -- {!mont_rung} adds the index
    arithmetic on top, in a context that contains nothing else. *)
fn mont_rung_core (acc: A.array S64.t) (res: A.array S64.t) (t: A.array S64.t)
                  (wide: A.array S64.t) (nmod: A.array S64.t)
                  (tbl: A.array S64.t)
                  (dig: S64.t) (nn: SZ.t) (mu: S64.t)
                  (anum: erased nat) (e: erased nat) (d: erased nat)
                  (#vacc #vres #vt #vwide: erased (Seq.seq S64.t))
                  (#pt #pn: perm)
                  (#vtbl: erased (Seq.seq S64.t))
                  (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to acc vacc ** A.pts_to res vres ** A.pts_to t vt **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
         A.pts_to tbl #pt vtbl **
  pure (Seq.length vacc == SZ.v nn /\ Seq.length vres == SZ.v nn /\
        Seq.length vt == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        Seq.length vtbl == 16 * SZ.v nn /\ SZ.fits (16 * SZ.v nn) /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        reveal d < 16 /\ S64.v dig == reveal d /\
        tbl_ok vtbl (SZ.v nn) anum (wt (SZ.v nn)) (num vn) 16 /\
        num vacc < num vn /\
        num vacc == (pw anum e * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v v1 v2 v3: Seq.seq S64.t).
  A.pts_to acc v ** A.pts_to res v1 ** A.pts_to t v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn ** A.pts_to tbl #pt vtbl **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
        num v < num vn /\
        num v == (pw anum (16 * reveal e + reveal d) *
                  wt (SZ.v nn)) % num vn)
{
  A.pts_to_len acc;
  A.pts_to_len res;
  A.pts_to_len t;
  A.pts_to_len wide;
  A.pts_to_len nmod;
  A.pts_to_len tbl;
  mont_sq4 acc res t wide nmod nn mu anum e;
  mont_win_mul acc res t wide nmod tbl dig nn mu anum
               (hide (16 * reveal e)) d;
  with vpr. assert (A.pts_to res vpr);
  copy acc res nn;
  with vfin. assert (A.pts_to acc vfin);
  assert (pure (num vfin == (pw anum (16 * reveal e + reveal d) *
                             wt (SZ.v nn)) % num vn));
}

#push-options "--z3rlimit 300"
(** One rung of the wide ladder: four squarings, then the table entry named
    by the four bits of the exponent at [j] multiplied in.  Like
    {!mont_sq}, this is a separate function because the solver's work grows
    with the number of arrays in scope, and the ladder itself has eight. *)
fn mont_rung (acc: A.array S64.t) (res: A.array S64.t) (t: A.array S64.t)
             (wide: A.array S64.t) (nmod: A.array S64.t)
             (tbl: A.array S64.t) (bb: A.array S64.t)
             (i: SZ.t) (nn: SZ.t) (mu: S64.t)
             (anum: erased nat) (e: erased nat)
             (#vacc #vres #vt #vwide: erased (Seq.seq S64.t))
             (#pt #pb #pn: perm)
             (#vtbl #vbb: erased (Seq.seq S64.t))
             (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to acc vacc ** A.pts_to res vres ** A.pts_to t vt **
         A.pts_to wide vwide ** A.pts_to nmod #pn vn **
         A.pts_to tbl #pt vtbl ** A.pts_to bb #pb vbb **
  pure (Seq.length vacc == SZ.v nn /\ Seq.length vres == SZ.v nn /\
        Seq.length vt == SZ.v nn /\ Seq.length vn == SZ.v nn /\
        Seq.length vwide == SZ.v nn + SZ.v nn /\
        Seq.length vtbl == 16 * SZ.v nn /\ SZ.fits (16 * SZ.v nn) /\
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\
        SZ.v i % 4 == 0 /\ 4 <= SZ.v i /\
        (SZ.v i - 4) / 64 < Seq.length vbb /\
        pow2 (SZ.v i) > 0 /\ num vbb / pow2 (SZ.v i) >= 0 /\
        reveal e == num vbb / pow2 (SZ.v i) /\
        tbl_ok vtbl (SZ.v nn) anum (wt (SZ.v nn)) (num vn) 16 /\
        num vacc < num vn /\
        num vacc == (pw anum e * wt (SZ.v nn)) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
returns j: SZ.t
ensures exists* (v v1 v2 v3: Seq.seq S64.t).
  A.pts_to acc v ** A.pts_to res v1 ** A.pts_to t v2 **
  A.pts_to wide v3 ** A.pts_to nmod #pn vn **
  A.pts_to tbl #pt vtbl ** A.pts_to bb #pb vbb **
  pure (Seq.length v == SZ.v nn /\ Seq.length v1 == SZ.v nn /\
        Seq.length v2 == SZ.v nn /\ Seq.length v3 == SZ.v nn + SZ.v nn /\
        num v < num vn /\ SZ.v j == SZ.v i - 4 /\ SZ.v j % 4 == 0 /\
        pow2 (SZ.v j) > 0 /\ num vbb / pow2 (SZ.v j) >= 0 /\
        num v == (pw anum (num vbb / pow2 (SZ.v j)) *
                  wt (SZ.v nn)) % num vn)
{
  A.pts_to_len acc;
  A.pts_to_len res;
  A.pts_to_len t;
  A.pts_to_len wide;
  A.pts_to_len nmod;
  A.pts_to_len tbl;
  A.pts_to_len bb;
  modulus_low vn;
  let j = SZ.sub i 4sz;
  pow2_pos (SZ.v j);
  div_nonneg (num vbb) (SZ.v j);
  let dig = get_digit bb j;
  assert (pure (num vbb / pow2 (SZ.v j) % 16 < 16));
  mont_rung_core acc res t wide nmod tbl dig nn mu anum e
                 (hide (num vbb / pow2 (SZ.v j) % 16));
  pow2_cong (SZ.v j + 4) (SZ.v i);
  pw_digit anum (num vbb) (SZ.v j);
  with vfin. assert (A.pts_to acc vfin);
  assert (pure (num vfin == (pw anum (num vbb / pow2 (SZ.v j)) *
                             wt (SZ.v nn)) % num vn));
  j
}
#pop-options
#pop-options

#pop-options

#push-options "--z3rlimit 300"

(** Every caller passes [bbits = 64 * nn], so the window's "divisible by
    four" requirement is free -- but only if the solver is handed it. *)
let mul64_mod4 (x: nat) : Lemma ((64 * x) % 4 == 0)
  = Math.multiple_modulo_lemma (16 * x) 4

(** [mod_exp_consttime res a bb bbits r2 nmod nn mu aM acc t wide] is
    [res = a ^ bb mod nmod], in time depending only on [bbits].  [a] must
    already be reduced; [aM], [acc] and [t] are [n] limbs of scratch and
    [wide] is [2n].  [res] doubles as a fourth [n]-limb scratch throughout.

    The sixteen-entry window table is [16n] limbs, and is the one thing
    this function allocates itself: threading it through every caller of
    every exponentiation would be a wide change for a private scratch
    buffer. *)
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
        0 < SZ.v nn /\ SZ.fits (SZ.v nn + SZ.v nn) /\ SZ.fits (16 * SZ.v nn) /\
        SZ.v bbits % 4 == 0 /\
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
  pw_one (num va);
  (* the table: T[d] = a^d in Montgomery form, for d < 16 *)
  let z64 = S64.zero;
  let mut tbl = [| z64; SZ.mul 16sz nn |];
  A.pts_to_len tbl;
  with vtbl. assert (A.pts_to tbl vtbl);
  table_store tbl acc nn 0sz;
  with vtb0. assert (A.pts_to tbl vtb0);
  tbl_shape vtbl vtb0 vacc1 (SZ.v nn) 0;
  tbl_extend vtbl vtb0 vacc1 (SZ.v nn) (num va) (wt (SZ.v nn)) (num vn) 0;
  table_store tbl aM nn nn;
  with vtb1. assert (A.pts_to tbl vtb1);
  tbl_shape vtb0 vtb1 vaM1 (SZ.v nn) 1;
  tbl_extend vtb0 vtb1 vaM1 (SZ.v nn) (num va) (wt (SZ.v nn)) (num vn) 1;
  copy t aM nn;
  let mut d = 2sz;
  while (let vd = !d; SZ.lt vd 16sz)
  invariant exists* (vd: SZ.t) (vtb vt1 vr vw: Seq.seq S64.t).
    pts_to d vd ** A.pts_to tbl vtb ** A.pts_to t vt1 ** A.pts_to res vr **
    A.pts_to aM vaM1 ** A.pts_to wide vw ** A.pts_to nmod #pn vn **
    pure (2 <= SZ.v vd /\ SZ.v vd <= 16 /\
          Seq.length vtb == 16 * SZ.v nn /\ Seq.length vt1 == SZ.v nn /\
          Seq.length vr == SZ.v nn /\ Seq.length vw == SZ.v nn + SZ.v nn /\
          Seq.length vn == SZ.v nn /\ 0 < SZ.v nn /\
          num vt1 < num vn /\
          num vt1 == (pw (num va) (SZ.v vd - 1) * wt (SZ.v nn)) % num vn /\
          tbl_ok vtb (SZ.v nn) (num va) (wt (SZ.v nn)) (num vn) (SZ.v vd))
  decreases (16 - SZ.v (!d))
  {
    let vd = !d;
    with vt1. assert (A.pts_to t vt1);
    with vtb. assert (A.pts_to tbl vtb);
    mont_mul res t aM wide nmod nn mu;
    with vpr. assert (A.pts_to res vpr);
    exp_mul_gen (num vt1) (num vaM1) (num vpr) (num va) (SZ.v vd - 1) 1
                (wt (SZ.v nn)) (num vn) (S64.v mu) (S64.v (Seq.index vn 0))
                (SZ.v nn);
    pw_cong (num va) (SZ.v vd - 1 + 1) (SZ.v vd);
    copy t res nn;
    store_off (SZ.v vd) (SZ.v nn);
    table_store tbl res nn (SZ.mul vd nn);
    with vtb'. assert (A.pts_to tbl vtb');
    tbl_shape vtb vtb' vpr (SZ.v nn) (SZ.v vd);
    tbl_extend vtb vtb' vpr (SZ.v nn) (num va) (wt (SZ.v nn)) (num vn) (SZ.v vd);
    pw_cong (num va) (SZ.v vd + 1 - 1) (SZ.v vd);
    d := SZ.add vd 1sz;
  };
  (* the ladder, four bits at a time *)
  let vdend = !d;
  sz_sixteen vdend;
  let w4 = bbits;
  pow2_pos (SZ.v w4);
  div_nonneg (num vbb) (SZ.v w4);
  Math.pow2_le_compat (SZ.v w4) (SZ.v bbits);
  Math.small_div (num vbb) (pow2 (SZ.v w4));
  pw_cong (num va) 0 (num vbb / pow2 (SZ.v w4));
  let mut i = w4;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t) (v v2 v3 v4 vtb: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to bb #pb vbb **
    A.pts_to nmod #pn vn ** A.pts_to acc v2 ** A.pts_to t v3 **
    A.pts_to wide v4 ** A.pts_to tbl vtb **
    pure (SZ.v vi <= SZ.v w4 /\ SZ.v vi % 4 == 0 /\
          SZ.v w4 <= 64 * Seq.length vbb /\
          pow2 (SZ.v vi) > 0 /\ num vbb / pow2 (SZ.v vi) >= 0 /\
          Seq.length v == SZ.v nn /\ Seq.length v2 == SZ.v nn /\
          Seq.length v3 == SZ.v nn /\ Seq.length v4 == SZ.v nn + SZ.v nn /\
          Seq.length vtb == 16 * SZ.v nn /\ Seq.length vn == SZ.v nn /\
          0 < SZ.v nn /\
          tbl_ok vtb (SZ.v nn) (num va) (wt (SZ.v nn)) (num vn) 16 /\
          num v2 < num vn /\
          num v2 == (pw (num va) (num vbb / pow2 (SZ.v vi)) * wt (SZ.v nn))
                    % num vn)
  decreases (SZ.v (!i))
  {
    let vi = !i;
    step4 (SZ.v vi);
    pow2_pos (SZ.v vi);
    div_nonneg (num vbb) (SZ.v vi);
    digit_in_range (SZ.v vi - 4) (Seq.length vbb);
    let j = mont_rung acc res t wide nmod tbl bb vi nn mu (num va)
                      (hide (num vbb / pow2 (SZ.v vi)));
    i := j;
  };
  let vend = !i;
  sz_zero vend;
  exp_top (num vbb);
  pw_cong (num va) (num vbb / pow2 (SZ.v vend)) (num vbb);
  with vaccf. assert (A.pts_to acc vaccf);
  assert (pure (pow2 (SZ.v vend) > 0 /\ num vbb / pow2 (SZ.v vend) >= 0 /\
    num vaccf ==
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

#push-options "--z3rlimit 200 --z3refresh"

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
  pw_cong (num va) (num vbb / pow2 (SZ.v vend)) (num vbb);
  with vaccf. assert (A.pts_to acc vaccf);
  assert (pure (pow2 (SZ.v vend) > 0 /\ num vbb / pow2 (SZ.v vend) >= 0 /\
    num vaccf ==
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
