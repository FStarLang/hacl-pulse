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


(** [Z_q] as a commutative ring, and multiplication in
    [R_q = Z_q[X]/(X^256 + 1)].

    {!Spec.MLDSA.Zq} defines the operations; the algebra is here, in a
    module of its own, because nothing the implementation proves needs it
    -- only the round-trip theorems do ({!Spec.MLDSA.NTT.Lemmas},
    {!Spec.MLDSA.Correctness}).  The laws are {!Spec.MLKEM.Zq}'s with
    [q = 8380417], packaged for [FStar.Tactics.CanonCommSemiring] as
    {!Spec.MLKEM.NTT.Lemmas} does.

    {!Spec.MLDSA.Zq.poly_mul} is the pointwise product of the NTT domain.
    The product it stands for, the negacyclic schoolbook product, is
    {!ring_mul} here. *)
module Spec.MLDSA.Ring

open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring
open FStar.Algebra.CommMonoid
open Spec.MLDSA.Zq

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0"

(** {2 The laws} *)

let add_comm (a b: zq) : Lemma (add a b == add b a) = ()

let add_assoc (a b c: zq) : Lemma (add (add a b) c == add a (add b c))
  = Math.lemma_mod_add_distr c (a + b) q;
    Math.lemma_mod_add_distr a (b + c) q

let add_zero (a: zq) : Lemma (add a 0 == a) = Math.small_mod a q

let add_neg (a: zq) : Lemma (add a (neg a) == 0)
  = if a = 0 then assert_norm ((0 + (q - 0) % q) % q == 0)
    else begin
      Math.small_mod (q - a) q;
      assert (a + (q - a) == q)
    end

let mul_comm (a b: zq) : Lemma (mul a b == mul b a)
  = Math.swap_mul a b

let mul_assoc (a b c: zq) : Lemma (mul (mul a b) c == mul a (mul b c))
  = Math.lemma_mod_mul_distr_l (a * b) c q;
    Math.paren_mul_right a b c;
    Math.lemma_mod_mul_distr_r a (b * c) q

let mul_one (a: zq) : Lemma (mul a 1 == a) = Math.small_mod a q

let mul_zero (a: zq) : Lemma (mul a 0 == 0) = ()

let mul_add_distr (a b c: zq) : Lemma (mul a (add b c) == add (mul a b) (mul a c))
  = Math.lemma_mod_mul_distr_r a (b + c) q;
    Math.distributivity_add_right a b c;
    Math.modulo_distributivity (a * b) (a * c) q

let sub_is_add_neg (a b: zq) : Lemma (sub a b == add a (neg b))
  = if b = 0 then Math.small_mod a q
    else Math.small_mod (q - b) q

[@@canon_attr]
let zq_add_cm : cm zq = CM 0 add (fun a -> add_comm 0 a; add_zero a) add_assoc add_comm

[@@canon_attr]
let zq_mul_cm : cm zq = CM 1 mul (fun a -> mul_comm 1 a; mul_one a) mul_assoc mul_comm

[@@canon_attr]
let zq_cr : cr zq = CR zq_add_cm zq_mul_cm neg add_neg mul_add_distr (fun a -> mul_comm 0 a)

let zring () : Tac unit = canon_semiring zq_cr

let add_swap4 (a b c d: zq) : Lemma (add (add a b) (add c d) == add (add a c) (add b d))
  = assert (add (add a b) (add c d) == add (add a c) (add b d)) by (zring ())

let mul_one_l (a: zq) : Lemma (mul 1 a == a) = mul_comm 1 a; mul_one a

let mul_zero_l (a: zq) : Lemma (mul 0 a == 0) = mul_comm 0 a

(** [-1] is [q - 1]. *)
let mul_neg_one (a: zq) : Lemma (mul a (q - 1) == neg a)
  = Math.lemma_mod_plus (q - a) (a - 1) q

(** {2 Negation}

    The tactic cannot normalise coefficients built from [neg], so
    identities with negation go through the uniqueness of inverses. *)

let neg_unique (a b: zq) : Lemma (requires add a b == 0) (ensures b == neg a)
  = if a = 0 then () else Math.small_mod (q - a) q

let neg_mul (z y: zq) : Lemma (neg (mul z y) == mul (neg z) y)
  = mul_add_distr y z (neg z);
    add_neg z;
    mul_comm y z;
    mul_comm y (neg z);
    neg_unique (mul z y) (mul (neg z) y)

let neg_add (a b: zq) : Lemma (neg (add a b) == add (neg a) (neg b))
  = add_swap4 a b (neg a) (neg b);
    add_neg a; add_neg b; add_zero 0;
    neg_unique (add a b) (add (neg a) (neg b))

let neg_neg (a: zq) : Lemma (neg (neg a) == a)
  = add_neg a; add_comm a (neg a);
    neg_unique (neg a) a

let mul_neg_r (w x: zq) : Lemma (mul w (neg x) == neg (mul w x))
  = neg_mul x w; mul_comm x w; mul_comm (neg x) w

let mul_sub_distr (c a b: zq) : Lemma (mul c (sub a b) == sub (mul c a) (mul c b))
  = sub_is_add_neg a b;
    sub_is_add_neg (mul c a) (mul c b);
    mul_add_distr c a (neg b);
    mul_neg_r c b

(** {2 Powers} *)

#push-options "--fuel 1"

let pow_zero (a: zq) : Lemma (pow a 0 == 1) = ()

#push-options "--fuel 2"
let pow_one (a: zq) : Lemma (pow a 1 == a) = mul_one a; mul_comm a 1
#pop-options

let rec pow_add (a: zq) (j k: nat)
  : Lemma (ensures pow a (j + k) == mul (pow a j) (pow a k)) (decreases j)
  = if j = 0 then (mul_comm (pow a 0) (pow a k); mul_one (pow a k))
    else begin
      pow_add a (j - 1) k;
      mul_assoc a (pow a (j - 1)) (pow a k)
    end

let rec pow_mul (a: zq) (b c: nat)
  : Lemma (ensures pow a (b * c) == pow (pow a b) c) (decreases c)
  = if c > 0 then begin
      pow_mul a b (c - 1);
      pow_add a b (b * (c - 1));
      Math.distributivity_sub_right b c 1
    end

let rec pow_one_base (m: nat) : Lemma (ensures pow 1 m == 1) (decreases m)
  = if m > 0 then pow_one_base (m - 1)

#pop-options

(** [zeta] has order 512 ... *)
let zeta_512 () : Lemma (pow zeta 512 == 1)
  = pow_add zeta 256 256;
    zeta_256 ();
    assert_norm (mul (q - 1) (q - 1) == 1)

(** ... so only the exponent modulo 512 matters ... *)
let zeta_mod (x: nat) : Lemma (pow zeta x == pow zeta (x % 512))
  = Math.euclidean_division_definition x 512;
    pow_add zeta (512 * (x / 512)) (x % 512);
    pow_mul zeta 512 (x / 512);
    zeta_512 ();
    pow_one_base (x / 512);
    mul_one_l (pow zeta (x % 512))

(** ... and [zeta^256 = -1]. *)
let zeta_neg (x: nat) : Lemma (pow zeta (x + 256) == neg (pow zeta x))
  = pow_add zeta x 256;
    zeta_256 ();
    mul_neg_one (pow zeta x)

(** {2 Finite sums}

    As in {!Spec.MLKEM.NTT.Lemmas}, every lemma takes its summands as
    named functions and their relationship as a pointwise hypothesis. *)

#push-options "--fuel 1"

(** [sum m f] is [f 0 + f 1 + ... + f (m - 1)]. *)
let rec sum (m: nat) (f: nat -> zq) : Tot zq (decreases m)
  = if m = 0 then 0 else add (sum (m - 1) f) (f (m - 1))

let rec sum_ext (m: nat) (f g: nat -> zq)
  : Lemma (requires forall (i: nat). i < m ==> f i == g i)
          (ensures sum m f == sum m g) (decreases m)
  = if m > 0 then sum_ext (m - 1) f g

let rec sum_zero (m: nat) (f: nat -> zq)
  : Lemma (requires forall (i: nat). i < m ==> f i == 0)
          (ensures sum m f == 0) (decreases m)
  = if m > 0 then sum_zero (m - 1) f

let rec sum_add (m: nat) (f g h: nat -> zq)
  : Lemma (requires forall (i: nat). i < m ==> h i == add (f i) (g i))
          (ensures sum m h == add (sum m f) (sum m g)) (decreases m)
  = if m > 0 then begin
      sum_add (m - 1) f g h;
      add_swap4 (sum (m - 1) f) (sum (m - 1) g) (f (m - 1)) (g (m - 1))
    end

let rec sum_scale (m: nat) (c: zq) (f h: nat -> zq)
  : Lemma (requires forall (i: nat). i < m ==> h i == mul c (f i))
          (ensures sum m h == mul c (sum m f)) (decreases m)
  = if m > 0 then begin
      sum_scale (m - 1) c f h;
      mul_add_distr c (sum (m - 1) f) (f (m - 1))
    end

let rec sum_split (m1 m2: nat) (f g: nat -> zq)
  : Lemma (requires forall (i: nat). i < m2 ==> g i == f (m1 + i))
          (ensures sum (m1 + m2) f == add (sum m1 f) (sum m2 g)) (decreases m2)
  = if m2 = 0 then add_zero (sum m1 f)
    else begin
      sum_split m1 (m2 - 1) f g;
      add_assoc (sum m1 f) (sum (m2 - 1) g) (g (m2 - 1))
    end

let sum_first (m: nat) (f g: nat -> zq)
  : Lemma (requires forall (i: nat). i < m ==> g i == f (i + 1))
          (ensures sum (m + 1) f == add (f 0) (sum m g))
  = sum_split 1 m f g;
    assert (sum 0 f == 0);
    assert (sum 1 f == add (sum 0 f) (f 0))

let sum_last (m: nat) (f: nat -> zq)
  : Lemma (sum (m + 1) f == add (sum m f) (f m))
  = ()

(** Exchanging the order of a double sum. *)
let rec sum_swap (m1 m2: nat) (f: nat -> nat -> zq)
  : Lemma (ensures sum m1 (fun i -> sum m2 (f i)) == sum m2 (fun j -> sum m1 (fun i -> f i j)))
          (decreases m1)
  = if m1 = 0 then sum_zero m2 (fun j -> sum m1 (fun i -> f i j))
    else begin
      sum_swap (m1 - 1) m2 f;
      sum_add m2 (fun j -> sum (m1 - 1) (fun i -> f i j)) (f (m1 - 1))
                 (fun j -> sum m1 (fun i -> f i j))
    end

#pop-options

(** {2 Multiplication in [R_q]}

    The schoolbook product.  [X^256 = -1], so a term whose degree reaches
    [256] wraps around with its sign flipped. *)

(** The [j]th summand of coefficient [k] of [f * g]: [f_j g_(k-j)], or
    [-f_j g_(k+256-j)] when the degree wraps. *)
let ring_mul_at (f g: poly) (k: nat { k < n }) (j: nat) : zq
  = if j >= n then 0
    else if j <= k then mul (Seq.index f j) (Seq.index g (k - j))
    else neg (mul (Seq.index f j) (Seq.index g (k + n - j)))

let ring_mul (f g: poly) : poly
  = Seq.init n (fun k -> sum n (ring_mul_at f g k))

let ring_mul_index (f g: poly) (k: nat { k < n })
  : Lemma (Seq.index (ring_mul f g) k == sum n (ring_mul_at f g k))
  = Seq.init_index_ n (fun k -> sum n (ring_mul_at f g k)) k

#pop-options
