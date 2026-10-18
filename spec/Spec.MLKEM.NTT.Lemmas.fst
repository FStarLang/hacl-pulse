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

(** The algebra behind {!Spec.MLKEM.NTT}: the butterfly network FIPS 203
    specifies is a ring isomorphism

    [R_q = Z_q[X]/(X^256 + 1)  ~  prod_(i < 128) Z_q[X]/(X^2 - gammas i)]

    with [multiply_ntts] the product on the right.  The headline is
    [intt_multiply_ntts]:

    [intt (multiply_ntts (ntt f) (ntt g)) == poly_mul f g]

    The proof has three parts, none of which looks at the implementation.

    - {b What [ntt] computes} ([ntt_eval]).  Output pair [i] is [f] reduced
      modulo [X^2 - gammas i].  Reduction is phrased as evaluation: if [x]
      is the class of [X] in [Z_q[x]/(x^2 - gamma)] then [x^k] is
      [gamma^(k/2)] in the constant or the linear slot according to the
      parity of [k], and [f(x)] is a pair of sums, [ev gamma 0] and
      [ev gamma 1].  The invariant after each layer is that every block
      evaluates, at the [x] of every final factor below it, to the same
      thing as [f]; one layer preserves it because [x^len = +/- zeta] for
      the [zeta] that layer uses -- a fact about bit reversal, which is
      checked exhaustively by normalization rather than proved.

    - {b Evaluation is multiplicative} ([ev_poly_mul]).  Multiplication by
      [X] in [R_q] is a negacyclic shift, and evaluation turns it into
      multiplication by [x] because [x^256 = gamma^128 = -1].  Column [j] of
      the schoolbook product is [g] shifted [j] times, so it evaluates to
      [x^j g(x)], and summing the columns gives [f(x) g(x)].

    - {b [intt] undoes [ntt]} ([intt_ntt]).  Layer by layer:
      [intt_layer e (ntt_layer e f)] is [2 f], because the twiddle the
      inverse layer uses is minus the inverse of the forward one -- again
      bit reversal, again by normalization.  Seven doublings and the final
      scaling by [128^-1] cancel.

    The converse [ntt (intt f) == f] and additivity are proved the same way,
    so [ntt] is a bijection that preserves both operations. *)
module Spec.MLKEM.NTT.Lemmas

open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring
open FStar.Algebra.CommMonoid
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0"

(** {2 [Z_q] as a commutative ring}

    The laws are all in {!Spec.MLKEM.Zq}; packaging them lets
    [FStar.Tactics.CanonCommSemiring] decide the identities below, which
    would otherwise be chains of a dozen [add_assoc]s each.  Subtraction is
    not part of the structure, so it is rewritten with [sub_is_add_neg]
    before the tactic sees it. *)

[@@canon_attr]
let zq_add_cm : cm zq = CM 0 add (fun a -> add_comm 0 a; add_zero a) add_assoc add_comm

[@@canon_attr]
let zq_mul_cm : cm zq = CM 1 mul (fun a -> mul_comm 1 a; mul_one a) mul_assoc mul_comm

[@@canon_attr]
let zq_cr : cr zq = CR zq_add_cm zq_mul_cm neg add_neg mul_add_distr (fun a -> mul_comm 0 a)

let zring () : Tac unit = canon_semiring zq_cr

let add_swap4 (a b c d: zq) : Lemma (add (add a b) (add c d) == add (add a c) (add b d))
  = assert (add (add a b) (add c d) == add (add a c) (add b d)) by (zring ())

(** [-1] is [q - 1]. *)
let mul_neg_one (a: zq) : Lemma (mul a (q - 1) == neg a)
  = Math.lemma_mod_plus (q - a) (a - 1) q

(** {2 Finite sums}

    Every lemma takes the summands as named functions and the relationship
    between them as a pointwise hypothesis, rather than writing a [fun] in
    its statement: the caller then never has to make two lambdas agree. *)

#push-options "--fuel 1"

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

(** {2 Powers of [zeta]} *)

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

(** [zeta] has order 256, so only the exponent modulo 256 matters ... *)
let zeta_mod (x: nat) : Lemma (pow zeta x == pow zeta (x % 256))
  = Math.euclidean_division_definition x 256;
    pow_add zeta (256 * (x / 256)) (x % 256);
    pow_mul zeta 256 (x / 256);
    zeta_256 ();
    pow_one_base (x / 256);
    mul_comm 1 (pow zeta (x % 256));
    mul_one (pow zeta (x % 256))

(** ... and [zeta^128 = -1]. *)
let zeta_neg (x: nat) : Lemma (pow zeta (x + 128) == neg (pow zeta x))
  = pow_add zeta x 128;
    zeta_128 ();
    mul_neg_one (pow zeta x)

(** {2 Evaluation in [Z_q[x]/(x^2 - gamma)]}

    [es gamma s k] is component [s] of [x^k]: [x^(2j) = gamma^j] and
    [x^(2j+1) = gamma^j x].  [ev gamma s m a] is component [s] of
    [sum_(k < m) a_k x^k]. *)

let es (g: zq) (s: nat { s < 2 }) (k: nat) : zq
  = if k % 2 = s then pow g (k / 2) else 0

let ev (g: zq) (s: nat { s < 2 }) (m: nat) (a: nat -> zq) : zq
  = sum m (fun k -> mul (a k) (es g s k))

(** Multiplying by [x] swaps the components and scales one by [gamma]. *)
let es_succ (g: zq) (k: nat)
  : Lemma (es g 1 (k + 1) == es g 0 k /\ es g 0 (k + 1) == mul g (es g 1 k))
  = if k % 2 = 1 then begin
      assert ((k + 1) / 2 == k / 2 + 1);
      pow_add g 1 (k / 2);
      pow_one g
    end
    else assert ((k + 1) / 2 == k / 2)

(** [x^(2m + k) = gamma^m x^k]. *)
let es_shift (g: zq) (s: nat { s < 2 }) (m k: nat)
  : Lemma (es g s (2 * m + k) == mul (pow g m) (es g s k))
  = Math.lemma_mod_plus k m 2;
    Math.lemma_div_plus k m 2;
    if k % 2 = s then pow_add g m (k / 2)
    else mul_zero (pow g m)

(** Unfolding [ev] against a named summand. *)
let ev_sum (g: zq) (s: nat { s < 2 }) (m: nat) (a t: nat -> zq)
  : Lemma (requires forall (k: nat). k < m ==> t k == mul (a k) (es g s k))
          (ensures ev g s m a == sum m t)
  = sum_ext m (fun k -> mul (a k) (es g s k)) t

let ev_ext (g: zq) (s: nat { s < 2 }) (m: nat) (a b: nat -> zq)
  : Lemma (requires forall (k: nat). k < m ==> a k == b k)
          (ensures ev g s m a == ev g s m b)
  = sum_ext m (fun k -> mul (a k) (es g s k)) (fun k -> mul (b k) (es g s k))

let lin_term (a b z e: zq)
  : Lemma (mul (add a (mul z b)) e == add (mul a e) (mul z (mul b e)))
  = assert (mul (add a (mul z b)) e == add (mul a e) (mul z (mul b e))) by (zring ())

(** Evaluation is linear. *)
let ev_lin (g: zq) (s: nat { s < 2 }) (m: nat) (z: zq) (a b c: nat -> zq)
  : Lemma (requires forall (k: nat). k < m ==> c k == add (a k) (mul z (b k)))
          (ensures ev g s m c == add (ev g s m a) (mul z (ev g s m b)))
  = let ta (k: nat) : zq = mul (a k) (es g s k) in
    let tb (k: nat) : zq = mul (b k) (es g s k) in
    let tzb (k: nat) : zq = mul z (tb k) in
    let tc (k: nat) : zq = mul (c k) (es g s k) in
    introduce forall (k: nat). k < m ==> tc k == add (ta k) (tzb k)
    with introduce _ ==> _ with lin_term (a k) (b k) z (es g s k);
    sum_add m ta tzb tc;
    sum_scale m z tb tzb;
    assert (ev g s m c == sum m tc);
    assert (ev g s m a == sum m ta);
    assert (ev g s m b == sum m tb)

(** A polynomial of degree [< 2 h + 2 h] is its low half plus [x^(2h)]
    times its high half, and [x^(2h) = gamma^h] is a scalar. *)
let ev_split (g: zq) (s: nat { s < 2 }) (h: nat) (a b: nat -> zq)
  : Lemma (requires forall (k: nat). k < h + h ==> b k == a (h + h + k))
          (ensures ev g s (h + h + (h + h)) a ==
                   add (ev g s (h + h) a) (mul (pow g h) (ev g s (h + h) b)))
  = let l = h + h in
    let ta (k: nat) : zq = mul (a k) (es g s k) in
    let ta' (k: nat) : zq = ta (l + k) in
    let tb (k: nat) : zq = mul (b k) (es g s k) in
    introduce forall (k: nat). k < l ==> ta' k == mul (pow g h) (tb k)
    with introduce _ ==> _ with begin
      es_shift g s h k;
      let x = b k in
      let y = es g s k in
      let p = pow g h in
      assert (mul x (mul p y) == mul p (mul x y)) by (zring ())
    end;
    sum_split l l ta ta';
    sum_scale l (pow g h) tb ta';
    assert (ev g s (l + l) a == sum (l + l) ta);
    assert (ev g s l a == sum l ta);
    assert (ev g s l b == sum l tb)

(** The tactic cannot reduce coefficients built from [neg], so identities
    involving negation go through the uniqueness of additive inverses. *)
let neg_unique (a b: zq) : Lemma (requires add a b == 0) (ensures b == neg a)
  = if a = 0 then () else Math.small_mod (q - a) q

let neg_mul (z y: zq) : Lemma (neg (mul z y) == mul (neg z) y)
  = mul_add_distr y z (neg z);
    add_neg z;
    mul_comm y z;
    mul_comm y (neg z);
    neg_unique (mul z y) (mul (neg z) y)
(** {2 The twiddle factors, by computation}

    Layer [e] (half-width [2^e]) splits a block modulo [X^(2^(e+1)) - c]
    into [X^(2^e) - zeta'] and [X^(2^e) + zeta'], [zeta' = zetas m] with [m]
    as in [zidx].  What the invariant needs is that the [x] of every final
    factor [X^2 - gammas i] below the block satisfies [x^(2^e) = +/- zeta'],
    with the sign given by which half of the block [i] lies in.  Writing
    both sides as powers of [zeta], that is a congruence modulo 256 between
    two expressions in [bitrev7]; there are [7 * 128] instances, and the
    normalizer checks them all faster than one could write the induction. *)

let rec all_below (k: nat) (p: nat -> bool) : bool
  = if k = 0 then true else p (k - 1) && all_below (k - 1) p

#push-options "--fuel 1"
let rec all_below_elim (k: nat) (p: nat -> bool) (i: nat)
  : Lemma (requires all_below k p /\ i < k) (ensures p i) (decreases k)
  = if i < k - 1 then all_below_elim (k - 1) p i
#pop-options

let root_ok (e: nat { 1 <= e /\ e <= 7 }) (i: nat) : bool
  = let m = pow2 (7 - e) + (2 * i) / pow2 (e + 1) in
    if m < 128 && i < 128 then
      ((2 * bitrev7 i + 1) * pow2 (e - 1)) % 256 =
      (bitrev7 m + 128 * ((2 * i) / pow2 e % 2)) % 256
    else false

let root_ok_holds (e: nat { 1 <= e /\ e <= 7 }) (i: nat { i < 128 }) : Lemma (root_ok e i)
  = begin match e with
    | 1 -> assert_norm (all_below 128 (root_ok 1))
    | 2 -> assert_norm (all_below 128 (root_ok 2))
    | 3 -> assert_norm (all_below 128 (root_ok 3))
    | 4 -> assert_norm (all_below 128 (root_ok 4))
    | 5 -> assert_norm (all_below 128 (root_ok 5))
    | 6 -> assert_norm (all_below 128 (root_ok 6))
    | 7 -> assert_norm (all_below 128 (root_ok 7))
    end;
    all_below_elim 128 (root_ok e) i

let root_of_exponents (gi zm: zq) (x b: nat) (c: nat { c < 2 })
  : Lemma (requires gi == pow zeta x /\ zm == pow zeta b /\ x % 256 == (b + 128 * c) % 256)
          (ensures gi == (if c = 0 then zm else neg zm))
  = zeta_mod x;
    zeta_mod (b + 128 * c);
    if c = 1 then zeta_neg b

let root_lemma (e: nat { 1 <= e /\ e <= 7 }) (i: nat { i < 128 })
  : Lemma (let m = pow2 (7 - e) + (2 * i) / pow2 (e + 1) in
           m < 128 /\
           pow (gammas i) (pow2 (e - 1)) ==
             (if (2 * i) / pow2 e % 2 = 0 then zetas m else neg (zetas m)))
  = root_ok_holds e i;
    let m = pow2 (7 - e) + (2 * i) / pow2 (e + 1) in
    let x = (2 * bitrev7 i + 1) * pow2 (e - 1) in
    pow_mul zeta (2 * bitrev7 i + 1) (pow2 (e - 1));
    root_of_exponents (pow (gammas i) (pow2 (e - 1))) (zetas m) x (bitrev7 m)
                      ((2 * i) / pow2 e % 2)

(** {2 What [ntt] computes} *)

(** Coefficients [start] to [start + len - 1] of [st], as a polynomial. *)
let blk (st: poly) (start len: nat) (k: nat) : zq
  = if k < len && start + k < n then Seq.index st (start + k) else 0

(** After the layers down to half-width [2^e], the block of size [2^e]
    holding output pair [i] has the same image as [f] in
    [Z_q[x]/(x^2 - gammas i)]. *)
let inv_at (e: nat { 1 <= e /\ e <= 8 }) (f st: poly) (i: nat { i < 128 }) (s: nat { s < 2 }) : prop
  = ev (gammas i) s (pow2 e) (blk st ((2 * i) / pow2 e * pow2 e) (pow2 e)) ==
    ev (gammas i) s n (blk f 0 n)

(** The index arithmetic of one step, for coefficient [k] of the child
    block: [c] is the child block, [pp] its parent. *)
let step_index (e: nat { 1 <= e /\ e <= 7 }) (i: nat { i < 128 }) (k: nat)
  : Lemma (requires k < pow2 e)
          (ensures (let l = pow2 e in
                    let c = (2 * i) / l in
                    let pp = (2 * i) / pow2 (e + 1) in
                    let t = c * l + k in
                    pow2 (e + 1) == l + l /\
                    l == pow2 (e - 1) + pow2 (e - 1) /\
                    c * l == pp * pow2 (e + 1) + (c % 2) * l /\
                    t < n /\ t / l == c /\ t / pow2 (e + 1) == pp))
  = let l = pow2 e in
    let c = (2 * i) / l in
    let pp = (2 * i) / pow2 (e + 1) in
    let t = c * l + k in
    Math.pow2_double_sum e;
    Math.pow2_double_sum (e - 1);
    Math.division_multiplication_lemma (2 * i) l 2;
    assert (pp == c / 2);
    Math.distributivity_add_left (2 * pp) (c % 2) l;
    Math.paren_mul_right pp 2 l;
    Math.paren_mul_left pp 2 l;
    Math.lemma_div_plus k c l;
    Math.small_div k l;
    Math.division_multiplication_lemma t l 2;
    n_pow2 ();
    Math.pow2_plus (8 - e) e;
    div_lt (2 * i) (pow2 (8 - e)) l;
    Math.lemma_mult_le_right l (c + 1) (pow2 (8 - e));
    Math.distributivity_add_left c 1 l

(** One coefficient of a child block after a layer: the lower child is
    [lo + zeta' hi] and the upper [lo - zeta' hi], where [lo] and [hi] are
    the halves of the parent. *)
let layer_child (e: nat { 1 <= e /\ e <= 7 }) (st: poly) (l c pp p cs m: nat) (z w: zq) (k: nat)
  : Lemma (requires l == pow2 e /\ k < l /\ cs == p + (c % 2) * l /\ cs + k < n /\
                    (cs + k) / l == c /\ (cs + k) / pow2 (e + 1) == pp /\
                    m == pow2 (7 - e) + pp /\ m < 128 /\ z == zetas m /\
                    w == (if c % 2 = 0 then z else neg z))
          (ensures blk (ntt_layer e st) cs l k == add (blk st p l k) (mul w (blk st (p + l) l k)))
  = let t = cs + k in
    ntt_layer_index e st t;
    assert (zidx e t == m);
    if c % 2 = 0 then even_step e t
    else begin
      odd_step e t;
      sub_is_add_neg (Seq.index st (t - l)) (mul z (Seq.index st t));
      neg_mul z (Seq.index st t)
    end

let inv_step (e: nat { 1 <= e /\ e <= 7 }) (f st: poly) (i: nat { i < 128 }) (s: nat { s < 2 })
  : Lemma (requires inv_at (e + 1) f st i s) (ensures inv_at e f (ntt_layer e st) i s)
  = let h = pow2 (e - 1) in
    let l = pow2 e in
    let c = (2 * i) / l in
    let pp = (2 * i) / pow2 (e + 1) in
    Math.nat_times_nat_is_nat pp (pow2 (e + 1));
    Math.nat_times_nat_is_nat c l;
    let p : nat = pp * pow2 (e + 1) in
    let cs : nat = c * l in
    let st' = ntt_layer e st in
    let g = gammas i in
    step_index e i 0;
    root_lemma e i;
    let m = pow2 (7 - e) + pp in
    let z = zetas m in
    let w = if c % 2 = 0 then z else neg z in
    assert (pow g h == w);
    introduce forall (k: nat). k < l ==>
        blk st' cs l k == add (blk st p l k) (mul w (blk st (p + l) l k))
    with introduce _ ==> _ with begin
      step_index e i k;
      layer_child e st l c pp p cs m z w k
    end;
    ev_lin g s l w (blk st p l) (blk st (p + l) l) (blk st' cs l);
    ev_split g s h (blk st p (pow2 (e + 1))) (blk st (p + l) l);
    ev_ext g s l (blk st p (pow2 (e + 1))) (blk st p l)

let inv_top (f: poly) (i: nat { i < 128 }) (s: nat { s < 2 }) : Lemma (inv_at 8 f f i s)
  = assert_norm (pow2 8 == 256);
    Math.small_div (2 * i) 256

#push-options "--fuel 1"
let inv_bot (f st: poly) (i: nat { i < 128 }) (s: nat { s < 2 })
  : Lemma (requires inv_at 1 f st i s)
          (ensures Seq.index st (2 * i + s) == ev (gammas i) s n (blk f 0 n))
  = assert_norm (pow2 1 == 2);
    let g = gammas i in
    let x0 = Seq.index st (2 * i) in
    let x1 = Seq.index st (2 * i + 1) in
    let tm (k: nat) : zq = mul (blk st (2 * i) 2 k) (es g s k) in
    ev_sum g s 2 (blk st (2 * i) 2) tm;
    assert (sum 2 tm == add (sum 1 tm) (tm 1));
    assert (sum 1 tm == add (sum 0 tm) (tm 0));
    assert (sum 0 tm == 0);
    pow_zero g;
    assert (es g s 0 == (if s = 0 then 1 else 0));
    assert (es g s 1 == (if s = 1 then 1 else 0));
    mul_one x0; mul_one x1; mul_zero x0; mul_zero x1;
    add_comm 0 (tm 0); add_zero (tm 0); add_zero x0;
    add_comm 0 x1; add_zero x1
#pop-options

(** Output pair [i] of [ntt f] is [f] modulo [X^2 - gammas i]. *)
let ntt_eval (f: poly) (i: nat { i < 128 }) (s: nat { s < 2 })
  : Lemma (Seq.index (ntt f) (2 * i + s) == ev (gammas i) s n (blk f 0 n))
  = ntt_unfold f;
    let s7 = ntt_layer 7 f in
    let s6 = ntt_layer 6 s7 in
    let s5 = ntt_layer 5 s6 in
    let s4 = ntt_layer 4 s5 in
    let s3 = ntt_layer 3 s4 in
    let s2 = ntt_layer 2 s3 in
    let s1 = ntt_layer 1 s2 in
    inv_top f i s;
    inv_step 7 f f i s;
    inv_step 6 f s7 i s;
    inv_step 5 f s6 i s;
    inv_step 4 f s5 i s;
    inv_step 3 f s4 i s;
    inv_step 2 f s3 i s;
    inv_step 1 f s2 i s;
    inv_bot f s1 i s

(** {2 Evaluation is multiplicative} *)

(** [x^256 = -1] in every factor, which is why [X^256 + 1] is the right
    modulus. *)
let gamma_128 (i: nat { i < 128 }) : Lemma (pow (gammas i) 128 == q - 1)
  = let b = bitrev7 i in
    pow_mul zeta (2 * b + 1) 128;
    zeta_mod ((2 * b + 1) * 128);
    Math.lemma_mod_plus 128 b 256;
    zeta_128 ()

(** Multiplication by [X] in [R_q] is a negacyclic shift. *)
let xshift (a: nat -> zq) (k: nat) : zq
  = if k = 0 then neg (a (n - 1)) else a (k - 1)

let shift_term (g a e: zq) : Lemma (mul a (mul g e) == mul g (mul a e))
  = assert (mul a (mul g e) == mul g (mul a e)) by (zring ())

let mul_one_l (a: zq) : Lemma (mul 1 a == a) = mul_comm 1 a; mul_one a

let mul_zero_l (a: zq) : Lemma (mul 0 a == 0) = mul_comm 0 a

let es_odd_255 (g: zq) : Lemma (es g 1 255 == pow g 127)
  = assert_norm (255 % 2 = 1 /\ 255 / 2 = 127)

let es_even_0 (g: zq) : Lemma (es g 0 0 == 1 /\ es g 1 0 == 0)
  = assert_norm (0 % 2 = 0 /\ 0 / 2 = 0); pow_zero g

let es_even_255 (g: zq) : Lemma (es g 0 255 == 0)
  = assert_norm (255 % 2 = 1)

let xshift_0 (a: nat -> zq) : Lemma (xshift a 0 == neg (a 255))
  = assert_norm (n - 1 = 255)

let xshift_succ (a: nat -> zq) (k: nat) : Lemma (xshift a (k + 1) == a k) = ()

let gamma_top (g a255: zq)
  : Lemma (requires pow g 128 == q - 1)
          (ensures mul g (mul a255 (pow g 127)) == neg a255)
  = shift_term g a255 (pow g 127);
    pow_add g 1 127; pow_one g;
    mul_neg_one a255

#push-options "--fuel 1"
let sum_256 (t: nat -> zq) : Lemma (sum 256 t == add (sum 255 t) (t 255)) = ()
#pop-options

(** ... and evaluation turns it into multiplication by [x]: the image of
    [X a] is [(gamma a_1, a_0)] where [a] maps to [(a_0, a_1)]. *)
let ev_xshift_odd (g: zq) (a: nat -> zq)
  : Lemma (ev g 1 n (xshift a) == ev g 0 n a)
  = let t1 (k: nat) : zq = mul (xshift a k) (es g 1 k) in
    let u0 (k: nat) : zq = mul (a k) (es g 0 k) in
    introduce forall (k: nat). k < 255 ==> u0 k == t1 (k + 1)
    with introduce _ ==> _ with (es_succ g k; xshift_succ a k);
    sum_first 255 t1 u0;
    ev_sum g 1 n (xshift a) t1;
    es_even_0 g;
    mul_zero (xshift a 0);
    add_comm 0 (sum 255 u0);
    add_zero (sum 255 u0);
    ev_sum g 0 n a u0;
    sum_256 u0;
    es_even_255 g;
    mul_zero (a 255);
    add_zero (sum 255 u0)

let ev_xshift_even (g: zq) (a: nat -> zq)
  : Lemma (requires pow g 128 == q - 1)
          (ensures ev g 0 n (xshift a) == mul g (ev g 1 n a))
  = let a255 = a 255 in
    let t0 (k: nat) : zq = mul (xshift a k) (es g 0 k) in
    let u1 (k: nat) : zq = mul (a k) (es g 1 k) in
    let gu1 (k: nat) : zq = mul g (u1 k) in
    introduce forall (k: nat). k < 255 ==> gu1 k == t0 (k + 1)
    with introduce _ ==> _ with begin
      es_succ g k; xshift_succ a k;
      shift_term g (a k) (es g 1 k)
    end;
    sum_first 255 t0 gu1;
    ev_sum g 0 n (xshift a) t0;
    es_even_0 g; xshift_0 a;
    mul_one (neg a255);
    sum_scale 255 g u1 gu1;
    ev_sum g 1 n a u1;
    sum_256 u1;
    es_odd_255 g;
    mul_add_distr g (sum 255 u1) (u1 255);
    gamma_top g a255;
    add_comm (neg a255) (mul g (sum 255 u1))

let ev_xshift (g: zq) (a: nat -> zq)
  : Lemma (requires pow g 128 == q - 1)
          (ensures ev g 1 n (xshift a) == ev g 0 n a /\
                   ev g 0 n (xshift a) == mul g (ev g 1 n a))
  = ev_xshift_odd g a; ev_xshift_even g a

(** Column [j] of the schoolbook product: [X^j g]. *)
let col (g: poly) (j: nat) (k: nat) : zq
  = if k < n && j < n then
      (if j <= k then Seq.index g (k - j) else neg (Seq.index g (k + n - j)))
    else 0

let col_ev_step (g e0 e1 g0 g1: zq)
  : Lemma (mul g (add (mul e0 g1) (mul e1 g0)) ==
           add (mul (mul g e1) g0) (mul g (mul e0 g1)) /\
           add (mul e0 g0) (mul g (mul e1 g1)) ==
           add (mul (mul g e1) g1) (mul e0 g0))
  = assert (mul g (add (mul e0 g1) (mul e1 g0)) ==
            add (mul (mul g e1) g0) (mul g (mul e0 g1))) by (zring ());
    assert (add (mul e0 g0) (mul g (mul e1 g1)) ==
            add (mul (mul g e1) g1) (mul e0 g0)) by (zring ())

(** The image of [X^j g] is [x^j] times the image of [g]. *)
let rec ev_col (gm: zq) (g: poly) (j: nat)
  : Lemma (requires pow gm 128 == q - 1 /\ j < n)
          (ensures (let g0 = ev gm 0 n (blk g 0 n) in
                    let g1 = ev gm 1 n (blk g 0 n) in
                    ev gm 0 n (col g j) == add (mul (es gm 0 j) g0) (mul gm (mul (es gm 1 j) g1)) /\
                    ev gm 1 n (col g j) == add (mul (es gm 0 j) g1) (mul (es gm 1 j) g0)))
          (decreases j)
  = let g0 = ev gm 0 n (blk g 0 n) in
    let g1 = ev gm 1 n (blk g 0 n) in
    if j = 0 then begin
      ev_ext gm 0 n (col g 0) (blk g 0 n);
      ev_ext gm 1 n (col g 0) (blk g 0 n);
      assert_norm (pow gm 0 == 1);
      mul_one_l g0; mul_one_l g1; mul_zero_l g0; mul_zero_l g1; mul_zero gm;
      add_zero g0; add_zero g1; add_comm 0 g1
    end
    else begin
      ev_col gm g (j - 1);
      ev_ext gm 0 n (col g j) (xshift (col g (j - 1)));
      ev_ext gm 1 n (col g j) (xshift (col g (j - 1)));
      ev_xshift gm (col g (j - 1));
      es_succ gm (j - 1);
      col_ev_step gm (es gm 0 (j - 1)) (es gm 1 (j - 1)) g0 g1
    end

let prod_term (fj cjk ek: zq) : Lemma (mul ek (mul fj cjk) == mul (mul fj cjk) ek)
  = mul_comm ek (mul fj cjk)

let col_term (fj cjk ek: zq) : Lemma (mul (mul fj cjk) ek == mul fj (mul cjk ek))
  = mul_assoc fj cjk ek

(** The image of [f * g] is the sum over the columns. *)
let ev_poly_mul_cols (gm: zq) (s: nat { s < 2 }) (f g: poly) (ct: nat -> zq)
  : Lemma (requires forall (j: nat). j < n ==> ct j == mul (blk f 0 n j) (ev gm s n (col g j)))
          (ensures ev gm s n (blk (poly_mul f g) 0 n) == sum n ct)
  = let h = poly_mul f g in
    let tt (k: nat) (j: nat) : zq = mul (mul (blk f 0 n j) (col g j k)) (es gm s k) in
    let row (k: nat) : zq = sum n (tt k) in
    let hk (k: nat) : zq = mul (blk h 0 n k) (es gm s k) in
    introduce forall (k: nat). k < n ==> hk k == row k
    with introduce _ ==> _ with begin
      let pm (j: nat) : zq = if k < n then poly_mul_at f g k j else 0 in
      Seq.init_index_ n (fun k -> sum n (poly_mul_at f g k)) k;
      sum_ext n (poly_mul_at f g k) pm;
      introduce forall (j: nat). j < n ==> tt k j == mul (es gm s k) (pm j)
      with introduce _ ==> _ with begin
        mul_comm (es gm s k) (pm j);
        if j > k then begin
          mul_comm (Seq.index f j) (neg (Seq.index g (k + n - j)));
          neg_mul (Seq.index g (k + n - j)) (Seq.index f j);
          mul_comm (Seq.index g (k + n - j)) (Seq.index f j)
        end
      end;
      sum_scale n (es gm s k) pm (tt k);
      mul_comm (blk h 0 n k) (es gm s k)
    end;
    ev_sum gm s n (blk h 0 n) hk;
    sum_ext n hk row;
    sum_swap n n tt;
    sum_ext n row (fun i -> sum n (tt i));
    introduce forall (j: nat). j < n ==> sum n (fun i -> tt i j) == ct j
    with introduce _ ==> _ with begin
      let cj (k: nat) : zq = mul (col g j k) (es gm s k) in
      introduce forall (k: nat). k < n ==> tt k j == mul (blk f 0 n j) (cj k)
      with introduce _ ==> _ with col_term (blk f 0 n j) (col g j k) (es gm s k);
      sum_ext n (fun i -> tt i j) (fun k -> mul (blk f 0 n j) (cj k));
      sum_scale n (blk f 0 n j) cj (fun k -> mul (blk f 0 n j) (cj k));
      ev_sum gm s n (col g j) cj
    end;
    sum_ext n (fun j -> sum n (fun i -> tt i j)) ct


let dist_term (fj e0 e1 c0 c1: zq)
  : Lemma (mul fj (add (mul e0 c0) (mul e1 c1)) ==
           add (mul c0 (mul fj e0)) (mul c1 (mul fj e1)))
  = assert (mul fj (add (mul e0 c0) (mul e1 c1)) ==
            add (mul c0 (mul fj e0)) (mul c1 (mul fj e1))) by (zring ())

(** If every column [X^j g] maps to [c0 x^j_0 + c1 x^j_1] (componentwise),
    then [f * g] maps to [c0 F0 + c1 F1]. *)
let ev_poly_mul_gen (gm: zq) (s: nat { s < 2 }) (f g: poly) (c0 c1: zq)
  : Lemma (requires forall (j: nat). j < n ==>
             ev gm s n (col g j) == add (mul (es gm 0 j) c0) (mul (es gm 1 j) c1))
          (ensures ev gm s n (blk (poly_mul f g) 0 n) ==
                   add (mul c0 (ev gm 0 n (blk f 0 n))) (mul c1 (ev gm 1 n (blk f 0 n))))
  = let fb = blk f 0 n in
    let ct (j: nat) : zq = mul (fb j) (ev gm s n (col g j)) in
    let a (j: nat) : zq = mul (fb j) (es gm 0 j) in
    let b (j: nat) : zq = mul (fb j) (es gm 1 j) in
    let ca (j: nat) : zq = mul c0 (a j) in
    let cb (j: nat) : zq = mul c1 (b j) in
    ev_poly_mul_cols gm s f g ct;
    introduce forall (j: nat). j < n ==> ct j == add (ca j) (cb j)
    with introduce _ ==> _ with dist_term (fb j) (es gm 0 j) (es gm 1 j) c0 c1;
    sum_add n ca cb ct;
    sum_scale n c0 a ca;
    sum_scale n c1 b cb;
    ev_sum gm 0 n fb a;
    ev_sum gm 1 n fb b

let ev0_col_form (e0 e1 g0 g1 gm: zq)
  : Lemma (add (mul e0 g0) (mul gm (mul e1 g1)) == add (mul e0 g0) (mul e1 (mul gm g1)))
  = assert (add (mul e0 g0) (mul gm (mul e1 g1)) == add (mul e0 g0) (mul e1 (mul gm g1)))
      by (zring ())

let bcm_0 (f0 f1 g0 g1 gm: zq)
  : Lemma (add (mul g0 f0) (mul (mul gm g1) f1) == add (mul f0 g0) (mul (mul f1 g1) gm))
  = assert (add (mul g0 f0) (mul (mul gm g1) f1) == add (mul f0 g0) (mul (mul f1 g1) gm))
      by (zring ())

let bcm_1 (f0 f1 g0 g1: zq)
  : Lemma (add (mul g1 f0) (mul g0 f1) == add (mul f0 g1) (mul f1 g0))
  = assert (add (mul g1 f0) (mul g0 f1) == add (mul f0 g1) (mul f1 g0)) by (zring ())

(** Evaluation at [x^2 = gamma] is a ring homomorphism from [R_q]: the
    image of [f * g] is the product in [Z_q[x]/(x^2 - gamma)]. *)
let ev_poly_mul (gm: zq) (f g: poly)
  : Lemma (requires pow gm 128 == q - 1)
          (ensures (let f0 = ev gm 0 n (blk f 0 n) in
                    let f1 = ev gm 1 n (blk f 0 n) in
                    let g0 = ev gm 0 n (blk g 0 n) in
                    let g1 = ev gm 1 n (blk g 0 n) in
                    let h = poly_mul f g in
                    (ev gm 0 n (blk h 0 n), ev gm 1 n (blk h 0 n)) ==
                    base_case_multiply f0 f1 g0 g1 gm))
  = let f0 = ev gm 0 n (blk f 0 n) in
    let f1 = ev gm 1 n (blk f 0 n) in
    let g0 = ev gm 0 n (blk g 0 n) in
    let g1 = ev gm 1 n (blk g 0 n) in
    introduce forall (j: nat). j < n ==>
        ev gm 0 n (col g j) == add (mul (es gm 0 j) g0) (mul (es gm 1 j) (mul gm g1)) /\
        ev gm 1 n (col g j) == add (mul (es gm 0 j) g1) (mul (es gm 1 j) g0)
    with introduce _ ==> _ with begin
      ev_col gm g j;
      ev0_col_form (es gm 0 j) (es gm 1 j) g0 g1 gm
    end;
    ev_poly_mul_gen gm 0 f g g0 (mul gm g1);
    ev_poly_mul_gen gm 1 f g g1 g0;
    bcm_0 f0 f1 g0 g1 gm;
    bcm_1 f0 f1 g0 g1

(** {2 [multiply_ntts] is multiplication in [R_q]} *)

let multiply_ntts_ntt (f g: poly)
  : Lemma (multiply_ntts (ntt f) (ntt g) == ntt (poly_mul f g))
  = let a = multiply_ntts (ntt f) (ntt g) in
    let b = ntt (poly_mul f g) in
    introduce forall (t: nat). t < n ==> Seq.index a t == Seq.index b t
    with introduce _ ==> _ with begin
      let i = t / 2 in
      let s = t % 2 in
      div_lt t 128 2;
      Math.lemma_div_mod t 2;
      multiply_ntts_index (ntt f) (ntt g) t;
      gamma_128 i;
      ntt_eval f i 0; ntt_eval f i 1;
      ntt_eval g i 0; ntt_eval g i 1;
      ntt_eval (poly_mul f g) i s;
      ev_poly_mul (gammas i) f g
    end;
    Seq.lemma_eq_intro a b


(** {1 The inverse transform}

    Each Gentleman-Sande layer undoes the Cooley-Tukey layer with the same
    half-width, up to a factor of 2: the twiddle factors it reads are the
    negated inverses of the forward ones.  Seven factors of 2 are exactly
    what [inv_128] cancels. *)

(** {2 Negation} *)

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

let two_mul (a: zq) : Lemma (mul 2 a == add a a) = ()

(** [w] and [z] are a pair of twiddle factors with [w z = -1]. *)
let twiddle_inv (w z b: zq)
  : Lemma (requires mul w z == q - 1) (ensures mul w (mul z b) == neg b)
  = mul_assoc w z b;
    mul_comm (q - 1) b;
    mul_neg_one b

(** {2 The four butterfly identities} *)

let add_sub_cancel (a x: zq) : Lemma (add (add a x) (sub a x) == add a a)
  = sub_is_add_neg a x;
    add_swap4 a x a (neg x);
    add_neg x;
    add_zero (add a a)

let sub_add_cancel (a b: zq) : Lemma (sub (add a b) (sub a b) == add b b)
  = sub_is_add_neg (add a b) (sub a b);
    sub_is_add_neg a b;
    neg_add a (neg b);
    neg_neg b;
    add_swap4 a b (neg a) b;
    add_neg a;
    add_comm 0 (add b b);
    add_zero (add b b)

(** Forward then inverse, upper half of the butterfly. *)
let fwd_inv_odd (w z a b: zq)
  : Lemma (requires mul w z == q - 1)
          (ensures mul w (sub (sub a (mul z b)) (add a (mul z b))) == add b b)
  = let x = mul z b in
    let nx = neg x in
    sub_is_add_neg a x;
    sub_is_add_neg (add a nx) (add a x);
    neg_add a x;
    add_swap4 a nx (neg a) nx;
    add_neg a;
    add_comm 0 (add nx nx);
    add_zero (add nx nx);
    mul_add_distr w nx nx;
    mul_neg_r w x;
    twiddle_inv w z b;
    neg_neg b

(** Inverse then forward: the lower half reads [a + b + z w (b - a)]. *)
let inv_fwd_even (z w a b: zq)
  : Lemma (requires mul z w == q - 1)
          (ensures add (add a b) (mul z (mul w (sub b a))) == add a a)
  = twiddle_inv z w (sub b a);
    sub_is_add_neg b a;
    neg_add b (neg a);
    neg_neg a;
    add_comm (neg b) a;
    sub_is_add_neg a b;
    add_sub_cancel a b

let inv_fwd_odd (z w a b: zq)
  : Lemma (requires mul z w == q - 1)
          (ensures sub (add a b) (mul z (mul w (sub b a))) == add b b)
  = twiddle_inv z w (sub b a);
    sub_is_add_neg b a;
    neg_add b (neg a);
    neg_neg a;
    add_comm (neg b) a;
    sub_is_add_neg a b;
    sub_add_cancel a b

(** {2 Index facts, by computation}

    For every layer and coefficient: the butterfly partner is in range and
    in the same block (so it uses the same twiddle factor), and the forward
    and inverse twiddle exponents sum to 128, i.e. [zetas (zidx e t) *
    zetas (zidx_inv e t) = zeta^128 = -1]. *)

let pair_ok (e: nat { 1 <= e /\ e <= 7 }) (t: nat) : bool
  = let l = pow2 e in
    let b = t / pow2 (e + 1) in
    let zf = pow2 (7 - e) + b in
    let zi = pow2 (8 - e) - 1 - b in
    if zf < 128 && 0 <= zi && zi < 128 then
      bitrev7 zf + bitrev7 zi = 128 &&
      (if (t / l) % 2 = 0
       then t + l < 256 && ((t + l) / l) % 2 = 1 && (t + l) / pow2 (e + 1) = b
       else t >= l && ((t - l) / l) % 2 = 0 && (t - l) / pow2 (e + 1) = b)
    else false

let pair_ok_holds (e: nat { 1 <= e /\ e <= 7 }) (t: nat { t < n }) : Lemma (pair_ok e t)
  = begin match e with
    | 1 -> assert_norm (all_below 256 (pair_ok 1))
    | 2 -> assert_norm (all_below 256 (pair_ok 2))
    | 3 -> assert_norm (all_below 256 (pair_ok 3))
    | 4 -> assert_norm (all_below 256 (pair_ok 4))
    | 5 -> assert_norm (all_below 256 (pair_ok 5))
    | 6 -> assert_norm (all_below 256 (pair_ok 6))
    | 7 -> assert_norm (all_below 256 (pair_ok 7))
    end;
    all_below_elim 256 (pair_ok e) t

let twiddle_pair (e: nat { 1 <= e /\ e <= 7 }) (t: nat { t < n })
  : Lemma (mul (zetas (zidx e t)) (zetas (zidx_inv e t)) == q - 1 /\
           mul (zetas (zidx_inv e t)) (zetas (zidx e t)) == q - 1)
  = pair_ok_holds e t;
    let b = t / pow2 (e + 1) in
    assert (zidx e t == pow2 (7 - e) + b);
    assert (zidx_inv e t == pow2 (8 - e) - 1 - b);
    pow_add zeta (bitrev7 (zidx e t)) (bitrev7 (zidx_inv e t));
    zeta_128 ();
    mul_comm (zetas (zidx e t)) (zetas (zidx_inv e t))

(** The partner of a lower-half coefficient. *)
let partner_up (e: nat { 1 <= e /\ e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 == 0)
          (ensures t + pow2 e < n /\ ((t + pow2 e) / pow2 e) % 2 == 1 /\
                   zidx e (t + pow2 e) == zidx e t /\ zidx_inv e (t + pow2 e) == zidx_inv e t)
  = pair_ok_holds e t;
    let b = t / pow2 (e + 1) in
    assert (zidx e t == pow2 (7 - e) + b);
    assert (zidx_inv e t == pow2 (8 - e) - 1 - b);
    assert (zidx e (t + pow2 e) == pow2 (7 - e) + b);
    assert (zidx_inv e (t + pow2 e) == pow2 (8 - e) - 1 - b)

(** The partner of an upper-half coefficient. *)
let partner_down (e: nat { 1 <= e /\ e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 <> 0)
          (ensures t >= pow2 e /\ ((t - pow2 e) / pow2 e) % 2 == 0 /\
                   zidx e (t - pow2 e) == zidx e t /\ zidx_inv e (t - pow2 e) == zidx_inv e t)
  = pair_ok_holds e t;
    let b = t / pow2 (e + 1) in
    assert (zidx e t == pow2 (7 - e) + b);
    assert (zidx_inv e t == pow2 (8 - e) - 1 - b);
    assert (zidx e (t - pow2 e) == pow2 (7 - e) + b);
    assert (zidx_inv e (t - pow2 e) == pow2 (8 - e) - 1 - b)

(** {2 One layer each way} *)

let intt_ntt_layer_at (e: nat { 1 <= e /\ e <= 7 }) (st: poly) (t: nat { t < n })
  : Lemma (Seq.index (intt_layer e (ntt_layer e st)) t == mul 2 (Seq.index st t))
  = let l = pow2 e in
    let fw = ntt_layer e st in
    intt_layer_index e fw t;
    ntt_layer_index e st t;
    twiddle_pair e t;
    let z = zetas (zidx e t) in
    let w = zetas (zidx_inv e t) in
    if (t / l) % 2 = 0 then begin
      partner_up e t;
      ntt_layer_index e st (t + l);
      add_sub_cancel (Seq.index st t) (mul z (Seq.index st (t + l)))
    end else begin
      partner_down e t;
      ntt_layer_index e st (t - l);
      let a = Seq.index st (t - l) in
      let b = Seq.index st t in
      assert ((t - l) + l == t);
      assert (Seq.index fw (t - l) == add a (mul z b));
      assert (Seq.index fw t == sub a (mul z b));
      assert (Seq.index (intt_layer e fw) t == mul w (sub (Seq.index fw t) (Seq.index fw (t - l))));
      fwd_inv_odd w z a b;
      two_mul b
    end

let ntt_intt_layer_at (e: nat { 1 <= e /\ e <= 7 }) (st: poly) (t: nat { t < n })
  : Lemma (Seq.index (ntt_layer e (intt_layer e st)) t == mul 2 (Seq.index st t))
  = let l = pow2 e in
    let iv = intt_layer e st in
    ntt_layer_index e iv t;
    intt_layer_index e st t;
    twiddle_pair e t;
    let z = zetas (zidx e t) in
    let w = zetas (zidx_inv e t) in
    if (t / l) % 2 = 0 then begin
      partner_up e t;
      intt_layer_index e st (t + l);
      let a = Seq.index st t in
      let b = Seq.index st (t + l) in
      assert ((t + l) - l == t);
      assert (Seq.index iv t == add a b);
      assert (Seq.index iv (t + l) == mul w (sub b a));
      assert (Seq.index (ntt_layer e iv) t == add (Seq.index iv t) (mul z (Seq.index iv (t + l))));
      inv_fwd_even z w a b;
      two_mul a
    end else begin
      partner_down e t;
      intt_layer_index e st (t - l);
      let a = Seq.index st (t - l) in
      let b = Seq.index st t in
      assert ((t - l) + l == t);
      assert (Seq.index iv (t - l) == add a b);
      assert (Seq.index iv t == mul w (sub b a));
      assert (Seq.index (ntt_layer e iv) t == sub (Seq.index iv (t - l)) (mul z (Seq.index iv t)));
      inv_fwd_odd z w a b;
      two_mul b
    end

let intt_ntt_layer (e: nat { 1 <= e /\ e <= 7 }) (st: poly)
  : Lemma (intt_layer e (ntt_layer e st) == poly_scale 2 st)
  = introduce forall (t: nat { t < n }).
        Seq.index (intt_layer e (ntt_layer e st)) t == Seq.index (poly_scale 2 st) t
    with intt_ntt_layer_at e st t;
    Seq.lemma_eq_intro (intt_layer e (ntt_layer e st)) (poly_scale 2 st)

let ntt_intt_layer (e: nat { 1 <= e /\ e <= 7 }) (st: poly)
  : Lemma (ntt_layer e (intt_layer e st) == poly_scale 2 st)
  = introduce forall (t: nat { t < n }).
        Seq.index (ntt_layer e (intt_layer e st)) t == Seq.index (poly_scale 2 st) t
    with ntt_intt_layer_at e st t;
    Seq.lemma_eq_intro (ntt_layer e (intt_layer e st)) (poly_scale 2 st)

(** {2 Layers are linear} *)

let scale_comm (c z b: zq) : Lemma (mul z (mul c b) == mul c (mul z b))
  = assert (mul z (mul c b) == mul c (mul z b)) by (zring ())

let ntt_layer_scale (e: nat { 1 <= e /\ e <= 7 }) (c: zq) (st: poly)
  : Lemma (ntt_layer e (poly_scale c st) == poly_scale c (ntt_layer e st))
  = let a = ntt_layer e (poly_scale c st) in
    let b = poly_scale c (ntt_layer e st) in
    introduce forall (t: nat { t < n }). Seq.index a t == Seq.index b t
    with begin
      let l = pow2 e in
      let z = zetas (zidx e t) in
      ntt_layer_index e (poly_scale c st) t;
      ntt_layer_index e st t;
      if (t / l) % 2 = 0 then begin
        even_step e t;
        scale_comm c z (Seq.index st (t + l));
        mul_add_distr c (Seq.index st t) (mul z (Seq.index st (t + l)))
      end else begin
        odd_step e t;
        scale_comm c z (Seq.index st t);
        mul_sub_distr c (Seq.index st (t - l)) (mul z (Seq.index st t))
      end
    end;
    Seq.lemma_eq_intro a b

let intt_layer_scale (e: nat { 1 <= e /\ e <= 7 }) (c: zq) (st: poly)
  : Lemma (intt_layer e (poly_scale c st) == poly_scale c (intt_layer e st))
  = let a = intt_layer e (poly_scale c st) in
    let b = poly_scale c (intt_layer e st) in
    introduce forall (t: nat { t < n }). Seq.index a t == Seq.index b t
    with begin
      let l = pow2 e in
      let w = zetas (zidx_inv e t) in
      intt_layer_index e (poly_scale c st) t;
      intt_layer_index e st t;
      if (t / l) % 2 = 0 then begin
        even_step e t;
        mul_add_distr c (Seq.index st t) (Seq.index st (t + l))
      end else begin
        odd_step e t;
        mul_sub_distr c (Seq.index st t) (Seq.index st (t - l));
        scale_comm c w (sub (Seq.index st t) (Seq.index st (t - l)))
      end
    end;
    Seq.lemma_eq_intro a b

let poly_scale_scale (c d: zq) (st: poly)
  : Lemma (poly_scale c (poly_scale d st) == poly_scale (mul c d) st)
  = introduce forall (t: nat { t < n }).
        Seq.index (poly_scale c (poly_scale d st)) t == Seq.index (poly_scale (mul c d) st) t
    with mul_assoc c d (Seq.index st t);
    Seq.lemma_eq_intro (poly_scale c (poly_scale d st)) (poly_scale (mul c d) st)

let poly_scale_one (st: poly) : Lemma (poly_scale 1 st == st)
  = introduce forall (t: nat { t < n }). Seq.index (poly_scale 1 st) t == Seq.index st t
    with mul_one_l (Seq.index st t);
    Seq.lemma_eq_intro (poly_scale 1 st) st

(** {2 The round trips} *)

let intt_ntt_step (e: nat { 1 <= e /\ e <= 7 }) (c: zq) (st: poly)
  : Lemma (intt_layer e (poly_scale c (ntt_layer e st)) == poly_scale (mul c 2) st)
  = intt_layer_scale e c (ntt_layer e st);
    intt_ntt_layer e st;
    poly_scale_scale c 2 st

let ntt_intt_step (e: nat { 1 <= e /\ e <= 7 }) (c: zq) (st: poly)
  : Lemma (ntt_layer e (poly_scale c (intt_layer e st)) == poly_scale (mul c 2) st)
  = ntt_layer_scale e c (intt_layer e st);
    ntt_intt_layer e st;
    poly_scale_scale c 2 st

(** [intt] is a left inverse of [ntt]. *)
let intt_ntt (f: poly) : Lemma (intt (ntt f) == f)
  = ntt_unfold f;
    let x7 = ntt_layer 7 f in
    let x6 = ntt_layer 6 x7 in
    let x5 = ntt_layer 5 x6 in
    let x4 = ntt_layer 4 x5 in
    let x3 = ntt_layer 3 x4 in
    let x2 = ntt_layer 2 x3 in
    let x1 = ntt_layer 1 x2 in
    intt_unfold x1;
    poly_scale_one x1;
    intt_ntt_step 1 1 x2;
    intt_ntt_step 2 (mul 1 2) x3;
    intt_ntt_step 3 (mul (mul 1 2) 2) x4;
    intt_ntt_step 4 (mul (mul (mul 1 2) 2) 2) x5;
    intt_ntt_step 5 (mul (mul (mul (mul 1 2) 2) 2) 2) x6;
    intt_ntt_step 6 (mul (mul (mul (mul (mul 1 2) 2) 2) 2) 2) x7;
    intt_ntt_step 7 (mul (mul (mul (mul (mul (mul 1 2) 2) 2) 2) 2) 2) f;
    assert_norm (mul (mul (mul (mul (mul (mul (mul 1 2) 2) 2) 2) 2) 2) 2 == 128);
    poly_scale_scale inv_128 128 f;
    inv_128_correct ();
    mul_comm inv_128 128;
    poly_scale_one f

(** ... and a right inverse. *)
let ntt_intt (f: poly) : Lemma (ntt (intt f) == f)
  = let y1 = intt_layer 1 f in
    let y2 = intt_layer 2 y1 in
    let y3 = intt_layer 3 y2 in
    let y4 = intt_layer 4 y3 in
    let y5 = intt_layer 5 y4 in
    let y6 = intt_layer 6 y5 in
    let y7 = intt_layer 7 y6 in
    intt_unfold f;
    ntt_unfold (poly_scale inv_128 y7);
    let c1 = mul inv_128 2 in
    let c2 = mul c1 2 in
    let c3 = mul c2 2 in
    let c4 = mul c3 2 in
    let c5 = mul c4 2 in
    let c6 = mul c5 2 in
    let c7 = mul c6 2 in
    ntt_intt_step 7 inv_128 y6;
    ntt_intt_step 6 c1 y5;
    ntt_intt_step 5 c2 y4;
    ntt_intt_step 4 c3 y3;
    ntt_intt_step 3 c4 y2;
    ntt_intt_step 2 c5 y1;
    ntt_intt_step 1 c6 f;
    assert_norm (mul (mul (mul (mul (mul (mul (mul inv_128 2) 2) 2) 2) 2) 2) 2 == 1);
    poly_scale_one f

(** {2 Additivity} *)

let ntt_layer_add (e: nat { 1 <= e /\ e <= 7 }) (f g: poly)
  : Lemma (ntt_layer e (poly_add f g) == poly_add (ntt_layer e f) (ntt_layer e g))
  = let a = ntt_layer e (poly_add f g) in
    let b = poly_add (ntt_layer e f) (ntt_layer e g) in
    introduce forall (t: nat { t < n }). Seq.index a t == Seq.index b t
    with begin
      let l = pow2 e in
      let z = zetas (zidx e t) in
      ntt_layer_index e (poly_add f g) t;
      ntt_layer_index e f t;
      ntt_layer_index e g t;
      if (t / l) % 2 = 0 then begin
        even_step e t;
        let f0 = Seq.index f t in let f1 = Seq.index f (t + l) in
        let g0 = Seq.index g t in let g1 = Seq.index g (t + l) in
        assert (add (add f0 g0) (mul z (add f1 g1)) ==
                add (add f0 (mul z f1)) (add g0 (mul z g1))) by (zring ())
      end else begin
        odd_step e t;
        let f0 = Seq.index f (t - l) in let f1 = Seq.index f t in
        let g0 = Seq.index g (t - l) in let g1 = Seq.index g t in
        let zf = mul z f1 in let zg = mul z g1 in
        mul_add_distr z f1 g1;
        sub_is_add_neg (add f0 g0) (add zf zg);
        sub_is_add_neg f0 zf;
        sub_is_add_neg g0 zg;
        neg_add zf zg;
        add_swap4 f0 g0 (neg zf) (neg zg)
      end
    end;
    Seq.lemma_eq_intro a b

let ntt_add (f g: poly) : Lemma (ntt (poly_add f g) == poly_add (ntt f) (ntt g))
  = ntt_unfold (poly_add f g); ntt_unfold f; ntt_unfold g;
    let f7 = ntt_layer 7 f in let g7 = ntt_layer 7 g in
    let f6 = ntt_layer 6 f7 in let g6 = ntt_layer 6 g7 in
    let f5 = ntt_layer 5 f6 in let g5 = ntt_layer 5 g6 in
    let f4 = ntt_layer 4 f5 in let g4 = ntt_layer 4 g5 in
    let f3 = ntt_layer 3 f4 in let g3 = ntt_layer 3 g4 in
    let f2 = ntt_layer 2 f3 in let g2 = ntt_layer 2 g3 in
    ntt_layer_add 7 f g;
    ntt_layer_add 6 f7 g7;
    ntt_layer_add 5 f6 g6;
    ntt_layer_add 4 f5 g5;
    ntt_layer_add 3 f4 g4;
    ntt_layer_add 2 f3 g3;
    ntt_layer_add 1 f2 g2

(** {1 The ring isomorphism} *)

(** [ntt] is a bijection [R_q -> T_q] ... *)
let ntt_injective (f g: poly) : Lemma (requires ntt f == ntt g) (ensures f == g)
  = intt_ntt f; intt_ntt g

(** ... that is additive and turns multiplication in [R_q] into
    [multiply_ntts]: so [R_q] and [T_q] are isomorphic rings, and the
    schoolbook product can be computed as FIPS 203 does. *)
let intt_multiply_ntts (f g: poly)
  : Lemma (intt (multiply_ntts (ntt f) (ntt g)) == poly_mul f g)
  = multiply_ntts_ntt f g;
    intt_ntt (poly_mul f g)

#pop-options
