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

(** The arithmetic behind a signed-digit comb for the base point.

    {!Hacl.Ed25519.PointMulComb} writes the scalar in sixty-four signed
    radix-sixteen digits [e_i] in [[-8, 7]] and adds [e_i 16^i G] for each
    of them out of thirty-two compiled-in tables: table [j] holds
    [m 256^j G] for [m] in [0..8], the odd digits are added first, the
    accumulator is multiplied by sixteen, and the even digits are added on
    top.  That is four doublings and sixty-four additions where an unsigned
    window over four base points needs sixty doublings, and every addition
    is a {i mixed} one, because each table entry is stored affine and
    pre-digested.

    This file says what that computes, in four parts:

    - the stored form of an affine point, [(y + x, y - x, 2 d t)], and
      the seven-multiplication addition that consumes it, which is
      [point_add] on the nose;
    - negation, which on the stored form is a swap and a sign;
    - [repq], "is the [n]-th multiple of [G]" for an {i integer} [n],
      which a signed digit needs, read modulo the group order;
    - the recoding itself and the two half-sums the algorithm walks. *)
module Spec.Ed25519.Comb

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

module SM = Spec.Ed25519.Smul
module O = Spec.Ed25519.Order
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The stored form} *)

type niels = elem & elem & elem

let to_niels (p: ext_point) : niels =
  let (x, y, _, t) = p in (fadd y x, fsub y x, fmul d2 t)

(** A point whose [z] is one.  Every table entry is one. *)
let affine (p: ext_point) : prop = let (_, _, z, _) = p in z == one

(** The addition the implementation performs.  It is [point_add] with
    the second operand's three sums and products read off the table
    rather than computed, and with [z2] gone because it is one. *)
let madd (p: ext_point) (n: niels) : ext_point =
  let (x1, y1, z1, t1) = p in
  let (ypx, ymx, xy) = n in
  let a = fmul (fsub y1 x1) ymx in
  let b = fmul (fadd y1 x1) ypx in
  let c = fmul t1 xy in
  let dd = fadd z1 z1 in
  let e = fsub b a in
  let f = fsub dd c in
  let gg = fadd dd c in
  let h = fadd b a in
  (fmul e f, fmul gg h, fmul f gg, fmul e h)

let madd_ok (p q: ext_point)
  : Lemma (requires affine q) (ensures madd p (to_niels q) == point_add p q)
  = let (x1, y1, z1, t1) = p in
    let (x2, y2, z2, t2) = q in
    fmul_assoc t1 d2 t2;
    fmul_comm t1 d2;
    fmul_one (fadd z1 z1)

(** {2 Negation} *)

let neg_niels (n: niels) : niels = let (a, b, c) = n in (b, a, fsub 0 c)

let fadd_neg (y x: elem) : Lemma (fadd y (fsub 0 x) == fsub y x)
  = Math.lemma_mod_add_distr y (prime - x) prime

let fsub_neg (y x: elem) : Lemma (fsub y (fsub 0 x) == fadd y x)
  = if x = 0 then Math.lemma_mod_plus y 1 prime
    else begin
      Math.small_mod (prime - x) prime;
      assert (y + prime - (prime - x) == y + x)
    end

let fmul_neg (c t: elem) : Lemma (fmul c (fsub 0 t) == fsub 0 (fmul c t))
  = Math.lemma_mod_mul_distr_r c (prime - t) prime;
    Math.distributivity_sub_right c prime t;
    Math.lemma_mod_plus (- (c * t)) c prime;
    Math.lemma_mod_sub_distr prime (c * t) prime;
    Math.lemma_mod_plus (- (c * t)) 1 prime

let to_niels_negate (q: ext_point)
  : Lemma (to_niels (point_negate q) == neg_niels (to_niels q) /\
           (affine q ==> affine (point_negate q)))
  = let (x, y, _, t) = q in
    fadd_neg y x;
    fsub_neg y x;
    fmul_neg d2 t

(** {2 Natural multiples, for the tables}

    The table proofs chain hundreds of these facts, each about a point
    whose coordinates the normaliser has just checked; left transparent,
    every query in those modules would carry the curve equation and
    projective equality of a dozen points and Z3 drowns in the nonlinear
    arithmetic.  Opaque, each step is one application of a lemma below. *)
[@@"opaque_to_smt"]
let isq (p: ext_point) (n: nat) : prop =
  on_curve p /\ point_equal p (SM.smul n g)

let isq_intro (p: ext_point) (n: nat)
  : Lemma (requires on_curve p /\ point_equal p (SM.smul n g)) (ensures isq p n)
  = reveal_opaque (`%isq) (isq p n)

let isq_elim (p: ext_point) (n: nat)
  : Lemma (requires isq p n) (ensures on_curve p /\ point_equal p (SM.smul n g))
  = reveal_opaque (`%isq) (isq p n)

let isq_one (p: ext_point) (n: nat)
  : Lemma (requires isq p n) (ensures isq p (1 * n)) = ()

let isq_zero (k: nat)
  : Lemma (requires k == 0) (ensures isq point_at_infinity k)
  = reveal_opaque (`%isq) (isq point_at_infinity k);
    point_at_infinity_on_curve ();
    SM.smul_zero g;
    point_equal_refl point_at_infinity

(** What the normaliser checks of each entry: it is on the curve and it
    is the previous entry plus the base point.  [assert_norm] sees through
    the opacity; the solver does not, which is the point. *)
[@@"opaque_to_smt"]
let ncheck (e a b: ext_point) : prop =
  on_curve e /\ point_equal e (point_add a b)

(** Entry [m + 1] is entry [m] plus the base point. *)
let isq_step (a b e: ext_point) (m n: nat)
  : Lemma (requires isq a (m * n) /\ isq b n /\ ncheck e a b)
          (ensures isq e (m * n + n))
  = reveal_opaque (`%isq) (isq a (m * n));
    reveal_opaque (`%isq) (isq b n);
    reveal_opaque (`%isq) (isq e (m * n + n));
    reveal_opaque (`%ncheck) (ncheck e a b);
    g_on_curve ();
    SM.smul_add_congr (m * n) n g a b;
    SM.smul_ok (m * n + n) g;
    point_equal_trans e (point_add a b) (SM.smul (m * n + n) g)

(** {2 Integer multiples of the base point} *)

(** [p] is the [n]-th multiple of [G], for an integer [n] taken modulo
    the group order.  Opaque, so that the loop invariants which carry it
    do not drag [point_equal]'s arithmetic into every query. *)
[@@"opaque_to_smt"]
let repq (p: ext_point) (n: int) : prop =
  on_curve p /\ point_equal p (SM.smul (n % q) g)

let repq_on_curve (p: ext_point) (n: int)
  : Lemma (requires repq p n) (ensures on_curve p)
  = reveal_opaque (`%repq) (repq p n)

(** Any natural multiple is one. *)
let repq_intro (p: ext_point) (n: nat)
  : Lemma (requires on_curve p /\ point_equal p (SM.smul n g)) (ensures repq p n)
  = reveal_opaque (`%repq) (repq p n);
    g_on_curve ();
    SM.smul_ok n g;
    SM.smul_ok (n % q) g;
    O.smul_mod_q n;
    point_equal_trans p (SM.smul n g) (SM.smul (n % q) g)

(** And a natural one below the order can be read back. *)
let repq_elim (p: ext_point) (n: nat)
  : Lemma (requires repq p n /\ n < q)
          (ensures on_curve p /\ point_equal p (SM.smul n g))
  = reveal_opaque (`%repq) (repq p n);
    Math.small_mod n q

let repq_cong (p: ext_point) (a b: int)
  : Lemma (requires repq p a /\ a == b) (ensures repq p b) = ()

let repq_zero (_: unit) : Lemma (repq point_at_infinity 0)
  = reveal_opaque (`%repq) (repq point_at_infinity 0);
    point_at_infinity_on_curve ();
    SM.smul_zero g;
    point_equal_refl point_at_infinity

let repq_add (p r: ext_point) (a b: int)
  : Lemma (requires repq p a /\ repq r b) (ensures repq (point_add p r) (a + b))
  = reveal_opaque (`%repq) (repq p a);
    reveal_opaque (`%repq) (repq r b);
    reveal_opaque (`%repq) (repq (point_add p r) (a + b));
    g_on_curve ();
    SM.smul_add_congr (a % q) (b % q) g p r;
    SM.smul_ok (a % q + b % q) g;
    SM.smul_ok ((a + b) % q) g;
    O.smul_mod_q (a % q + b % q);
    Math.lemma_mod_plus_distr_l a (b % q) q;
    Math.lemma_mod_plus_distr_r a b q;
    point_equal_trans (point_add p r) (SM.smul (a % q + b % q) g)
                      (SM.smul ((a + b) % q) g)

let repq_dbl (p: ext_point) (a: int)
  : Lemma (requires repq p a) (ensures repq (point_double p) (2 * a))
  = reveal_opaque (`%repq) (repq p a);
    reveal_opaque (`%repq) (repq (point_double p) (2 * a));
    g_on_curve ();
    SM.smul_dbl_congr (a % q) g p;
    SM.smul_ok (2 * (a % q)) g;
    SM.smul_ok ((2 * a) % q) g;
    O.smul_mod_q (2 * (a % q));
    Math.lemma_mod_mul_distr_r 2 a q;
    point_equal_trans (point_double p) (SM.smul (2 * (a % q)) g)
                      (SM.smul ((2 * a) % q) g)

let negmod (b: int) : Lemma (((- b) % q + b % q) % q == 0)
  = Math.lemma_mod_plus_distr_l (- b) (b % q) q;
    Math.lemma_mod_plus_distr_r (- b) b q

#restart-solver
(** The inverse is unique, so the negation of the [b]-th multiple is the
    [(-b)]-th: [-r = -r + (n + r) = (-r + r) + n = n] up to commuting,
    where [n] is the [(-b)]-th multiple and [n + r] is therefore zero. *)
let repq_neg (r: ext_point) (b: int)
  : Lemma (requires repq r b) (ensures repq (point_negate r) (- b))
  = reveal_opaque (`%repq) (repq r b);
    reveal_opaque (`%repq) (repq (point_negate r) (- b));
    let o = point_at_infinity in
    let nr = point_negate r in
    let s = SM.smul (b % q) g in
    let n = SM.smul ((- b) % q) g in
    g_on_curve ();
    point_at_infinity_on_curve ();
    point_negate_on_curve r;
    SM.smul_ok (b % q) g;
    SM.smul_ok ((- b) % q) g;
    SM.smul_ok ((- b) % q + b % q) g;
    SM.smul_ok 0 g;
    (* n + r is zero *)
    point_equal_refl n;
    SM.smul_add_congr ((- b) % q) (b % q) g n r;
    O.smul_mod_q ((- b) % q + b % q);
    negmod b;
    SM.smul_zero g;
    point_equal_trans (point_add n r) (SM.smul ((- b) % q + b % q) g) o;
    point_add_on_curve n r;
    (* -r = 0 + -r *)
    point_add_identity nr;
    point_add_on_curve o nr;
    point_equal_sym (point_add o nr) nr;
    (* 0 + -r = (n + r) + -r *)
    point_equal_sym (point_add n r) o;
    point_equal_refl nr;
    point_add_congr o (point_add n r) nr nr;
    point_add_on_curve (point_add n r) nr;
    point_equal_trans nr (point_add o nr) (point_add (point_add n r) nr);
    (* = n + (r + -r) *)
    point_add_assoc_law n r nr;
    point_add_on_curve r nr;
    point_add_on_curve n (point_add r nr);
    point_equal_trans nr (point_add (point_add n r) nr) (point_add n (point_add r nr));
    (* r + -r = 0 *)
    point_add_comm_law r nr;
    point_add_negate r;
    point_add_on_curve nr r;
    point_equal_trans (point_add r nr) (point_add nr r) o;
    point_add_congr n n (point_add r nr) o;
    point_add_on_curve n o;
    point_equal_trans nr (point_add n (point_add r nr)) (point_add n o);
    (* n + 0 = 0 + n = n *)
    point_add_comm_law n o;
    point_add_identity n;
    point_add_on_curve o n;
    point_equal_trans (point_add n o) (point_add o n) n;
    point_equal_trans nr (point_add n o) n

(** {2 Recoding}

    Digit [i] of [k] in radix sixteen is [nib k i].  The signed digit adds
    eight, keeps the low four bits and subtracts eight again, passing the
    high bit on as a carry, so it lands in [[-8, 7]]. *)

let nib (k: nat) (i: nat) : nat = k / pow2 (4 * i) % 16

let rec carry (k: nat) (i: nat) : Tot nat (decreases i) =
  if i = 0 then 0 else (nib k (i - 1) + carry k (i - 1) + 8) / 16

let dig (k: nat) (i: nat) : int = (nib k i + carry k i + 8) % 16 - 8

let rec psum (k: nat) (j: nat) : Tot int (decreases j) =
  if j = 0 then 0 else psum k (j - 1) + dig k (j - 1) * pow2 (4 * (j - 1))

(** The odd and even digits, each against the table that serves it:
    digits [2i] and [2i + 1] both come out of table [i]. *)
let rec osum (k: nat) (j: nat) : Tot int (decreases j) =
  if j = 0 then 0 else osum k (j - 1) + dig k (2 * (j - 1) + 1) * pow2 (8 * (j - 1))

let rec esum (k: nat) (j: nat) : Tot int (decreases j) =
  if j = 0 then 0 else esum k (j - 1) + dig k (2 * (j - 1)) * pow2 (8 * (j - 1))

#push-options "--fuel 1"

let carry_succ (k: nat) (i: nat)
  : Lemma (carry k (i + 1) == (nib k i + carry k i + 8) / 16) = ()

let rec carry_le (k: nat) (i: nat)
  : Lemma (ensures carry k i <= 1) (decreases i)
  = if i = 0 then () else carry_le k (i - 1)

let dig_range (k: nat) (i: nat) : Lemma (-8 <= dig k i /\ dig k i < 8) = ()

let osum_succ (k: nat) (j: nat)
  : Lemma (osum k (j + 1) == osum k j + dig k (2 * j + 1) * pow2 (8 * j)) = ()

let esum_succ (k: nat) (j: nat)
  : Lemma (esum k (j + 1) == esum k j + dig k (2 * j) * pow2 (8 * j)) = ()

let osum_zero (k: nat) : Lemma (osum k 0 == 0) = ()
let esum_zero (k: nat) : Lemma (esum k 0 == 0) = ()

(** One more digit of [k % 16^j]. *)
let mod_step (k: nat) (j: nat)
  : Lemma (k % pow2 (4 * (j + 1)) == k % pow2 (4 * j) + nib k j * pow2 (4 * j))
  = let a = pow2 (4 * j) in
    Math.pow2_plus (4 * j) 4;
    assert_norm (pow2 4 == 16);
    let y = k % (a * 16) in
    Math.euclidean_division_definition y a;
    Math.modulo_modulo_lemma k a 16;
    Math.modulo_division_lemma k a 16

let rec psum_inv (k: nat) (j: nat)
  : Lemma (ensures psum k j + carry k j * pow2 (4 * j) == k % pow2 (4 * j))
          (decreases j)
  = if j = 0 then assert_norm (pow2 0 == 1)
    else begin
      let i = j - 1 in
      psum_inv k i;
      mod_step k i;
      let t = nib k i + carry k i + 8 in
      Math.euclidean_division_definition t 16;
      Math.pow2_plus (4 * i) 4;
      assert_norm (pow2 4 == 16);
      assert (pow2 (4 * j) == pow2 (4 * i) * 16);
      Math.distributivity_add_left (t % 16 - 8) (16 * (t / 16)) (pow2 (4 * i));
      Math.paren_mul_right (t / 16) 16 (pow2 (4 * i))
    end

let psum_succ (k: nat) (j: nat)
  : Lemma (psum k (j + 1) == psum k j + dig k j * pow2 (4 * j)) = ()

#pop-options

let rec halves (k: nat) (j: nat)
  : Lemma (ensures 16 * osum k j + esum k j == psum k (2 * j)) (decreases j)
  = if j = 0 then begin
      osum_zero k; esum_zero k; assert_norm (psum k 0 == 0)
    end else begin
      let i = j - 1 in
      halves k i;
      osum_succ k i;
      esum_succ k i;
      psum_succ k (2 * i);
      psum_succ k (2 * i + 1);
      let a = pow2 (8 * i) in
      let d0 = dig k (2 * i) in
      let d1 = dig k (2 * i + 1) in
      assert (4 * (2 * i) == 8 * i);
      assert (4 * (2 * i + 1) == 8 * i + 4);
      Math.pow2_plus (8 * i) 4;
      assert_norm (pow2 4 == 16);
      assert (pow2 (8 * i + 4) == a * 16);
      Math.paren_mul_right d1 a 16;
      Math.swap_mul (d1 * a) 16;
      assert (d1 * pow2 (8 * i + 4) == 16 * (d1 * a));
      Math.distributivity_add_right 16 (osum k i) (d1 * a);
      assert (2 * j == 2 * i + 1 + 1)
    end


(** A scalar below [2^253] -- anything reduced modulo the order -- is its
    sixty-four signed digits, with nothing carried out of the top. *)
let recode_ok (k: nat)
  : Lemma (requires k < pow2 253)
          (ensures 16 * osum k 32 + esum k 32 == k)
  = halves k 32;
    psum_inv k 64;
    psum_inv k 63;
    carry_le k 63;
    Math.lemma_div_lt_nat k 253 252;
    assert_norm (pow2 (253 - 252) == 2);
    assert (4 * 63 == 252);
    Math.small_mod (k / pow2 252) 16;
    assert (nib k 63 <= 1);
    carry_succ k 63;
    assert (carry k 64 == 0);
    Math.pow2_lt_compat 256 253;
    Math.small_mod k (pow2 256)

#pop-options
