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


(** The algebra behind {!Spec.MLDSA.NTT}: the butterfly network FIPS 204
    specifies is the ring isomorphism

    [R_q = Z_q[X]/(X^256 + 1)  ~  Z_q^256]

    that evaluates a polynomial at the 256 roots [gammas i] of [X^256 + 1],
    with the pointwise product {!Spec.MLDSA.Zq.poly_mul} on the right.  The
    headline is [intt_poly_mul_ntt]:

    [intt (poly_mul (ntt f) (ntt g)) == ring_mul f g]

    The proof is {!Spec.MLKEM.NTT.Lemmas}', and simpler, because [q - 1] is
    divisible by 512: the eighth layer splits every quadratic factor into
    two linear ones, so output coefficient [t] is [f(gammas t)] itself
    rather than a residue modulo [X^2 - gamma], and evaluation is a single
    sum.

    - {b What [ntt] computes} ([ntt_eval]).  The invariant after each layer
      is that every block evaluates, at the root of every final factor
      below it, to [f] evaluated there; one layer preserves it because
      [gamma^len = +/- zeta'] for the [zeta'] the layer uses, a fact about
      bit reversal checked exhaustively by normalisation.

    - {b Evaluation is multiplicative} ([ev_ring_mul]).  Multiplication by
      [X] is a negacyclic shift and evaluation turns it into multiplication
      by [gamma], because [gamma^256 = -1].

    - {b [intt] undoes [ntt]} ([intt_ntt], [ntt_intt]).  Layer by layer the
      inverse butterfly doubles, because the twiddle factors are negated
      inverses of each other; eight doublings and the scaling by
      [256^-1] cancel.

    Additivity and scaling are proved the same way, so [ntt] and [intt]
    are mutually inverse linear bijections and the products agree. *)
module Spec.MLDSA.NTT.Lemmas

open FStar.Tactics.V2
open Spec.MLDSA.Zq
open Spec.MLDSA.Ring
open Spec.MLDSA.NTT

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0"

(** {2 Evaluation} *)

(** The root of the [i]th linear factor of [X^256 + 1]. *)
let gammas (i: nat { i < 256 }) : zq = pow zeta (2 * bitrev8 i + 1)

(** [sum_(k < m) a_k gamma^k]. *)
let ev (g: zq) (m: nat) (a: nat -> zq) : zq
  = sum m (fun k -> mul (a k) (pow g k))

let ev_sum (g: zq) (m: nat) (a t: nat -> zq)
  : Lemma (requires forall (k: nat). k < m ==> t k == mul (a k) (pow g k))
          (ensures ev g m a == sum m t)
  = sum_ext m (fun k -> mul (a k) (pow g k)) t

let ev_ext (g: zq) (m: nat) (a b: nat -> zq)
  : Lemma (requires forall (k: nat). k < m ==> a k == b k)
          (ensures ev g m a == ev g m b)
  = sum_ext m (fun k -> mul (a k) (pow g k)) (fun k -> mul (b k) (pow g k))

let lin_term (a b z e: zq)
  : Lemma (mul (add a (mul z b)) e == add (mul a e) (mul z (mul b e)))
  = assert (mul (add a (mul z b)) e == add (mul a e) (mul z (mul b e))) by (zring ())

let ev_lin (g: zq) (m: nat) (z: zq) (a b c: nat -> zq)
  : Lemma (requires forall (k: nat). k < m ==> c k == add (a k) (mul z (b k)))
          (ensures ev g m c == add (ev g m a) (mul z (ev g m b)))
  = let ta (k: nat) : zq = mul (a k) (pow g k) in
    let tb (k: nat) : zq = mul (b k) (pow g k) in
    let tzb (k: nat) : zq = mul z (tb k) in
    let tc (k: nat) : zq = mul (c k) (pow g k) in
    introduce forall (k: nat). k < m ==> tc k == add (ta k) (tzb k)
    with introduce _ ==> _ with lin_term (a k) (b k) z (pow g k);
    sum_add m ta tzb tc;
    sum_scale m z tb tzb;
    assert (ev g m c == sum m tc);
    assert (ev g m a == sum m ta);
    assert (ev g m b == sum m tb)

(** A polynomial of degree [< 2h] is its low half plus [X^h] times its
    high half. *)
let ev_split (g: zq) (h: nat) (a b: nat -> zq)
  : Lemma (requires forall (k: nat). k < h ==> b k == a (h + k))
          (ensures ev g (h + h) a == add (ev g h a) (mul (pow g h) (ev g h b)))
  = let ta (k: nat) : zq = mul (a k) (pow g k) in
    let ta' (k: nat) : zq = ta (h + k) in
    let tb (k: nat) : zq = mul (b k) (pow g k) in
    introduce forall (k: nat). k < h ==> ta' k == mul (pow g h) (tb k)
    with introduce _ ==> _ with begin
      pow_add g h k;
      let x = b k in
      let y = pow g k in
      let p = pow g h in
      assert (mul x (mul p y) == mul p (mul x y)) by (zring ())
    end;
    sum_split h h ta ta';
    sum_scale h (pow g h) tb ta';
    assert (ev g (h + h) a == sum (h + h) ta);
    assert (ev g h a == sum h ta);
    assert (ev g h b == sum h tb)

(** {2 The twiddle factors, by computation}

    Layer [e] (half-width [2^e]) splits a block modulo [X^(2^(e+1)) - c]
    into [X^(2^e) - zeta'] and [X^(2^e) + zeta'] with [zeta' = zetas m],
    [m = zidx e t].  What the invariant needs is that the root of every
    final factor below the block satisfies [gamma^(2^e) = +/- zeta'], with
    the sign given by the half [t] lies in.  As powers of [zeta] that is a
    congruence modulo 512 between two expressions in [bitrev8]; the
    normalizer checks all [8 * 256] instances. *)

let rec all_below (k: nat) (p: nat -> bool) : bool
  = if k = 0 then true else p (k - 1) && all_below (k - 1) p

#push-options "--fuel 1"
let rec all_below_elim (k: nat) (p: nat -> bool) (i: nat)
  : Lemma (requires all_below k p /\ i < k) (ensures p i) (decreases k)
  = if i < k - 1 then all_below_elim (k - 1) p i
#pop-options

let root_ok (e: nat { e <= 7 }) (t: nat) : bool
  = let m = pow2 (7 - e) + t / pow2 (e + 1) in
    if m < 256 && t < 256 then
      ((2 * bitrev8 t + 1) * pow2 e) % 512 = (bitrev8 m + 256 * ((t / pow2 e) % 2)) % 512
    else false

let root_ok_holds (e: nat { e <= 7 }) (t: nat { t < 256 }) : Lemma (root_ok e t)
  = begin match e with
    | 0 -> assert_norm (all_below 256 (root_ok 0))
    | 1 -> assert_norm (all_below 256 (root_ok 1))
    | 2 -> assert_norm (all_below 256 (root_ok 2))
    | 3 -> assert_norm (all_below 256 (root_ok 3))
    | 4 -> assert_norm (all_below 256 (root_ok 4))
    | 5 -> assert_norm (all_below 256 (root_ok 5))
    | 6 -> assert_norm (all_below 256 (root_ok 6))
    | 7 -> assert_norm (all_below 256 (root_ok 7))
    end;
    all_below_elim 256 (root_ok e) t

let root_of_exponents (gi zm: zq) (x b: nat) (c: nat { c < 2 })
  : Lemma (requires gi == pow zeta x /\ zm == pow zeta b /\ x % 512 == (b + 256 * c) % 512)
          (ensures gi == (if c = 0 then zm else neg zm))
  = zeta_mod x;
    zeta_mod (b + 256 * c);
    if c = 1 then zeta_neg b

let root_lemma (e: nat { e <= 7 }) (t: nat { t < 256 })
  : Lemma (pow (gammas t) (pow2 e) ==
           (if (t / pow2 e) % 2 = 0 then zetas (zidx e t) else neg (zetas (zidx e t))))
  = root_ok_holds e t;
    let m = zidx e t in
    let x = (2 * bitrev8 t + 1) * pow2 e in
    pow_mul zeta (2 * bitrev8 t + 1) (pow2 e);
    root_of_exponents (pow (gammas t) (pow2 e)) (zetas m) x (bitrev8 m) ((t / pow2 e) % 2)

(** {2 What [ntt] computes} *)

(** Coefficients [start] to [start + len - 1] of [st], as a polynomial. *)
let blk (st: poly) (start len: nat) (k: nat) : zq
  = if k < len && start + k < n then Seq.index st (start + k) else 0

(** After the layers down to half-width [2^e], the block of size [2^e]
    holding coefficient [t] has the same value as [f] at [gammas t]. *)
let inv_at (e: nat { e <= 8 }) (f st: poly) (t: nat { t < 256 }) : prop
  = ev (gammas t) (pow2 e) (blk st (t / pow2 e * pow2 e) (pow2 e)) ==
    ev (gammas t) n (blk f 0 n)

(** The index arithmetic of one step, for coefficient [k] of the child
    block [c]; [pp] is its parent. *)
let step_index (e: nat { e <= 7 }) (t: nat { t < 256 }) (k: nat)
  : Lemma (requires k < pow2 e)
          (ensures (let l = pow2 e in
                    let c = t / l in
                    let pp = t / pow2 (e + 1) in
                    let u = c * l + k in
                    pow2 (e + 1) == l + l /\
                    c * l == pp * pow2 (e + 1) + (c % 2) * l /\
                    u < n /\ u / l == c /\ u / pow2 (e + 1) == pp))
  = let l = pow2 e in
    let c = t / l in
    let pp = t / pow2 (e + 1) in
    let u = c * l + k in
    Math.pow2_double_sum e;
    Math.division_multiplication_lemma t l 2;
    assert (pp == c / 2);
    Math.distributivity_add_left (2 * pp) (c % 2) l;
    Math.paren_mul_right pp 2 l;
    Math.paren_mul_left pp 2 l;
    Math.lemma_div_plus k c l;
    Math.small_div k l;
    Math.division_multiplication_lemma u l 2;
    n_pow2 ();
    Math.pow2_plus (8 - e) e;
    KZ.div_lt t (pow2 (8 - e)) l;
    Math.lemma_mult_le_right l (c + 1) (pow2 (8 - e));
    Math.distributivity_add_left c 1 l

(** One coefficient of a child block after a layer: the lower child is
    [lo + zeta' hi] and the upper [lo - zeta' hi]. *)
let layer_child (e: nat { e <= 7 }) (st: poly) (l c pp p cs m: nat) (z w: zq) (k: nat)
  : Lemma (requires l == pow2 e /\ k < l /\ cs == p + (c % 2) * l /\ cs + k < n /\
                    (cs + k) / l == c /\ (cs + k) / pow2 (e + 1) == pp /\
                    m == pow2 (7 - e) + pp /\ m < 256 /\ z == zetas m /\
                    w == (if c % 2 = 0 then z else neg z))
          (ensures blk (ntt_layer e st) cs l k == add (blk st p l k) (mul w (blk st (p + l) l k)))
  = let u = cs + k in
    ntt_layer_index e st u;
    assert (zidx e u == m);
    if c % 2 = 0 then even_step e u
    else begin
      odd_step e u;
      sub_is_add_neg (Seq.index st (u - l)) (mul z (Seq.index st u));
      neg_mul z (Seq.index st u)
    end

let inv_step (e: nat { e <= 7 }) (f st: poly) (t: nat { t < 256 })
  : Lemma (requires inv_at (e + 1) f st t) (ensures inv_at e f (ntt_layer e st) t)
  = let l = pow2 e in
    let c = t / l in
    let pp = t / pow2 (e + 1) in
    Math.nat_times_nat_is_nat pp (pow2 (e + 1));
    Math.nat_times_nat_is_nat c l;
    let p : nat = pp * pow2 (e + 1) in
    let cs : nat = c * l in
    let st' = ntt_layer e st in
    let g = gammas t in
    step_index e t 0;
    root_lemma e t;
    let m = zidx e t in
    let z = zetas m in
    let w = if c % 2 = 0 then z else neg z in
    assert (pow g l == w);
    introduce forall (k: nat). k < l ==>
        blk st' cs l k == add (blk st p l k) (mul w (blk st (p + l) l k))
    with introduce _ ==> _ with begin
      step_index e t k;
      layer_child e st l c pp p cs m z w k
    end;
    ev_lin g l w (blk st p l) (blk st (p + l) l) (blk st' cs l);
    ev_split g l (blk st p (pow2 (e + 1))) (blk st (p + l) l);
    ev_ext g l (blk st p (pow2 (e + 1))) (blk st p l)

let inv_top (f: poly) (t: nat { t < 256 }) : Lemma (inv_at 8 f f t)
  = assert_norm (pow2 8 == 256);
    Math.small_div t 256

#push-options "--fuel 1"
let inv_bot (f st: poly) (t: nat { t < 256 })
  : Lemma (requires inv_at 0 f st t)
          (ensures Seq.index st t == ev (gammas t) n (blk f 0 n))
  = assert_norm (pow2 0 == 1);
    let g = gammas t in
    let tm (k: nat) : zq = mul (blk st t 1 k) (pow g k) in
    ev_sum g 1 (blk st t 1) tm;
    assert (sum 1 tm == add (sum 0 tm) (tm 0));
    pow_zero g;
    mul_one (Seq.index st t);
    add_comm 0 (tm 0); add_zero (tm 0)
#pop-options

(** Coefficient [t] of [ntt f] is [f(gammas t)]. *)
let ntt_eval (f: poly) (t: nat { t < 256 })
  : Lemma (Seq.index (ntt f) t == ev (gammas t) n (blk f 0 n))
  = ntt_unfold f;
    let s7 = ntt_layer 7 f in
    let s6 = ntt_layer 6 s7 in
    let s5 = ntt_layer 5 s6 in
    let s4 = ntt_layer 4 s5 in
    let s3 = ntt_layer 3 s4 in
    let s2 = ntt_layer 2 s3 in
    let s1 = ntt_layer 1 s2 in
    let s0 = ntt_layer 0 s1 in
    inv_top f t;
    inv_step 7 f f t;
    inv_step 6 f s7 t;
    inv_step 5 f s6 t;
    inv_step 4 f s5 t;
    inv_step 3 f s4 t;
    inv_step 2 f s3 t;
    inv_step 1 f s2 t;
    inv_step 0 f s1 t;
    inv_bot f s0 t

(** {2 Evaluation is multiplicative} *)

(** Every [gammas i] is a root of [X^256 + 1]. *)
let gamma_256 (i: nat { i < 256 }) : Lemma (pow (gammas i) 256 == q - 1)
  = let b = bitrev8 i in
    pow_mul zeta (2 * b + 1) 256;
    zeta_mod ((2 * b + 1) * 256);
    Math.lemma_mod_plus 256 b 512;
    zeta_256 ()

(** Multiplication by [X] in [R_q] is a negacyclic shift. *)
let xshift (a: nat -> zq) (k: nat) : zq
  = if k = 0 then neg (a (n - 1)) else a (k - 1)

let shift_term (g a e: zq) : Lemma (mul a (mul g e) == mul g (mul a e))
  = assert (mul a (mul g e) == mul g (mul a e)) by (zring ())

#push-options "--fuel 1"
let pow_succ (g: zq) (k: nat) : Lemma (pow g (k + 1) == mul g (pow g k)) = ()

let sum_256 (t: nat -> zq) : Lemma (sum 256 t == add (sum 255 t) (t 255)) = ()
#pop-options

let gamma_top (g a255: zq)
  : Lemma (requires pow g 256 == q - 1)
          (ensures mul g (mul a255 (pow g 255)) == neg a255)
  = shift_term g a255 (pow g 255);
    pow_succ g 255;
    mul_neg_one a255

(** ... and evaluation turns it into multiplication by [gamma]. *)
let ev_xshift (g: zq) (a: nat -> zq)
  : Lemma (requires pow g 256 == q - 1)
          (ensures ev g n (xshift a) == mul g (ev g n a))
  = let a255 = a 255 in
    let t0 (k: nat) : zq = mul (xshift a k) (pow g k) in
    let u (k: nat) : zq = mul (a k) (pow g k) in
    let gu (k: nat) : zq = mul g (u k) in
    introduce forall (k: nat). k < 255 ==> gu k == t0 (k + 1)
    with introduce _ ==> _ with begin
      pow_succ g k;
      shift_term g (a k) (pow g k)
    end;
    sum_first 255 t0 gu;
    ev_sum g n (xshift a) t0;
    assert_norm (n - 1 == 255);
    pow_zero g;
    mul_one (neg a255);
    sum_scale 255 g u gu;
    ev_sum g n a u;
    sum_256 u;
    mul_add_distr g (sum 255 u) (u 255);
    gamma_top g a255;
    add_comm (neg a255) (mul g (sum 255 u))

(** Column [j] of the schoolbook product: [X^j g]. *)
let col (g: poly) (j: nat) (k: nat) : zq
  = if k < n && j < n then
      (if j <= k then Seq.index g (k - j) else neg (Seq.index g (k + n - j)))
    else 0

(** The value of [X^j g] is [gamma^j] times the value of [g]. *)
let rec ev_col (gm: zq) (g: poly) (j: nat)
  : Lemma (requires pow gm 256 == q - 1 /\ j < n)
          (ensures ev gm n (col g j) == mul (pow gm j) (ev gm n (blk g 0 n)))
          (decreases j)
  = let gv = ev gm n (blk g 0 n) in
    if j = 0 then begin
      ev_ext gm n (col g 0) (blk g 0 n);
      pow_zero gm;
      mul_one_l gv
    end
    else begin
      ev_col gm g (j - 1);
      ev_ext gm n (col g j) (xshift (col g (j - 1)));
      ev_xshift gm (col g (j - 1));
      pow_succ gm (j - 1);
      mul_assoc gm (pow gm (j - 1)) gv
    end

let col_term (fj cjk ek: zq) : Lemma (mul (mul fj cjk) ek == mul fj (mul cjk ek))
  = mul_assoc fj cjk ek

(** The value of [f * g] is the sum over the columns. *)
let ev_ring_mul_cols (gm: zq) (f g: poly) (ct: nat -> zq)
  : Lemma (requires forall (j: nat). j < n ==> ct j == mul (blk f 0 n j) (ev gm n (col g j)))
          (ensures ev gm n (blk (ring_mul f g) 0 n) == sum n ct)
  = let h = ring_mul f g in
    let tt (k: nat) (j: nat) : zq = mul (mul (blk f 0 n j) (col g j k)) (pow gm k) in
    let row (k: nat) : zq = sum n (tt k) in
    let hk (k: nat) : zq = mul (blk h 0 n k) (pow gm k) in
    introduce forall (k: nat). k < n ==> hk k == row k
    with introduce _ ==> _ with begin
      let pm (j: nat) : zq = if k < n then ring_mul_at f g k j else 0 in
      ring_mul_index f g k;
      sum_ext n (ring_mul_at f g k) pm;
      introduce forall (j: nat). j < n ==> tt k j == mul (pow gm k) (pm j)
      with introduce _ ==> _ with begin
        mul_comm (pow gm k) (pm j);
        if j > k then begin
          mul_comm (Seq.index f j) (neg (Seq.index g (k + n - j)));
          neg_mul (Seq.index g (k + n - j)) (Seq.index f j);
          mul_comm (Seq.index g (k + n - j)) (Seq.index f j)
        end
      end;
      sum_scale n (pow gm k) pm (tt k);
      mul_comm (blk h 0 n k) (pow gm k)
    end;
    ev_sum gm n (blk h 0 n) hk;
    sum_ext n hk row;
    sum_swap n n tt;
    sum_ext n row (fun i -> sum n (tt i));
    introduce forall (j: nat). j < n ==> sum n (fun i -> tt i j) == ct j
    with introduce _ ==> _ with begin
      let cj (k: nat) : zq = mul (col g j k) (pow gm k) in
      introduce forall (k: nat). k < n ==> tt k j == mul (blk f 0 n j) (cj k)
      with introduce _ ==> _ with col_term (blk f 0 n j) (col g j k) (pow gm k);
      sum_ext n (fun i -> tt i j) (fun k -> mul (blk f 0 n j) (cj k));
      sum_scale n (blk f 0 n j) cj (fun k -> mul (blk f 0 n j) (cj k));
      ev_sum gm n (col g j) cj
    end;
    sum_ext n (fun j -> sum n (fun i -> tt i j)) ct

let ct_term (fj pj gv: zq) : Lemma (mul fj (mul pj gv) == mul gv (mul fj pj))
  = assert (mul fj (mul pj gv) == mul gv (mul fj pj)) by (zring ())

(** Evaluation at a root of [X^256 + 1] is a ring homomorphism from
    [R_q]. *)
let ev_ring_mul (gm: zq) (f g: poly)
  : Lemma (requires pow gm 256 == q - 1)
          (ensures ev gm n (blk (ring_mul f g) 0 n) ==
                   mul (ev gm n (blk f 0 n)) (ev gm n (blk g 0 n)))
  = let fb = blk f 0 n in
    let gv = ev gm n (blk g 0 n) in
    let a (j: nat) : zq = mul (fb j) (pow gm j) in
    let ct (j: nat) : zq = mul (fb j) (ev gm n (col g j)) in
    introduce forall (j: nat). j < n ==> ct j == mul gv (a j)
    with introduce _ ==> _ with begin
      ev_col gm g j;
      ct_term (fb j) (pow gm j) gv
    end;
    ev_ring_mul_cols gm f g ct;
    sum_scale n gv a ct;
    ev_sum gm n fb a;
    mul_comm gv (ev gm n fb)

(** {2 The pointwise product is multiplication in [R_q]} *)

let poly_mul_ntt (f g: poly)
  : Lemma (poly_mul (ntt f) (ntt g) == ntt (ring_mul f g))
  = let a = poly_mul (ntt f) (ntt g) in
    let b = ntt (ring_mul f g) in
    introduce forall (t: nat). t < n ==> Seq.index a t == Seq.index b t
    with introduce _ ==> _ with begin
      gamma_256 t;
      ntt_eval f t;
      ntt_eval g t;
      ntt_eval (ring_mul f g) t;
      ev_ring_mul (gammas t) f g
    end;
    Seq.lemma_eq_intro a b

(** {1 The inverse transform} *)

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
    in the same block, and the forward and inverse twiddle exponents sum to
    256, i.e. [zetas (zidx e t) * zetas (zidx_inv e t) = zeta^256 = -1]. *)

let pair_ok (e: nat { e <= 7 }) (t: nat) : bool
  = let l = pow2 e in
    let b = t / pow2 (e + 1) in
    let zf = pow2 (7 - e) + b in
    let zi = pow2 (8 - e) - 1 - b in
    if zf < 256 && 0 <= zi && zi < 256 then
      bitrev8 zf + bitrev8 zi = 256 &&
      (if (t / l) % 2 = 0
       then t + l < 256 && ((t + l) / l) % 2 = 1 && (t + l) / pow2 (e + 1) = b
       else t >= l && ((t - l) / l) % 2 = 0 && (t - l) / pow2 (e + 1) = b)
    else false

let pair_ok_holds (e: nat { e <= 7 }) (t: nat { t < n }) : Lemma (pair_ok e t)
  = begin match e with
    | 0 -> assert_norm (all_below 256 (pair_ok 0))
    | 1 -> assert_norm (all_below 256 (pair_ok 1))
    | 2 -> assert_norm (all_below 256 (pair_ok 2))
    | 3 -> assert_norm (all_below 256 (pair_ok 3))
    | 4 -> assert_norm (all_below 256 (pair_ok 4))
    | 5 -> assert_norm (all_below 256 (pair_ok 5))
    | 6 -> assert_norm (all_below 256 (pair_ok 6))
    | 7 -> assert_norm (all_below 256 (pair_ok 7))
    end;
    all_below_elim 256 (pair_ok e) t

let twiddle_pair (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (mul (zetas (zidx e t)) (zetas (zidx_inv e t)) == q - 1 /\
           mul (zetas (zidx_inv e t)) (zetas (zidx e t)) == q - 1)
  = pair_ok_holds e t;
    pow_add zeta (bitrev8 (zidx e t)) (bitrev8 (zidx_inv e t));
    zeta_256 ();
    mul_comm (zetas (zidx e t)) (zetas (zidx_inv e t))

let partner_up (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 == 0)
          (ensures t + pow2 e < n /\ ((t + pow2 e) / pow2 e) % 2 == 1 /\
                   zidx e (t + pow2 e) == zidx e t /\ zidx_inv e (t + pow2 e) == zidx_inv e t)
  = pair_ok_holds e t

let partner_down (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 <> 0)
          (ensures t >= pow2 e /\ ((t - pow2 e) / pow2 e) % 2 == 0 /\
                   zidx e (t - pow2 e) == zidx e t /\ zidx_inv e (t - pow2 e) == zidx_inv e t)
  = pair_ok_holds e t

(** {2 One layer each way} *)

let intt_ntt_layer_at (e: nat { e <= 7 }) (st: poly) (t: nat { t < n })
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

let ntt_intt_layer_at (e: nat { e <= 7 }) (st: poly) (t: nat { t < n })
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

let intt_ntt_layer (e: nat { e <= 7 }) (st: poly)
  : Lemma (intt_layer e (ntt_layer e st) == poly_scale 2 st)
  = introduce forall (t: nat { t < n }).
        Seq.index (intt_layer e (ntt_layer e st)) t == Seq.index (poly_scale 2 st) t
    with intt_ntt_layer_at e st t;
    Seq.lemma_eq_intro (intt_layer e (ntt_layer e st)) (poly_scale 2 st)

let ntt_intt_layer (e: nat { e <= 7 }) (st: poly)
  : Lemma (ntt_layer e (intt_layer e st) == poly_scale 2 st)
  = introduce forall (t: nat { t < n }).
        Seq.index (ntt_layer e (intt_layer e st)) t == Seq.index (poly_scale 2 st) t
    with ntt_intt_layer_at e st t;
    Seq.lemma_eq_intro (ntt_layer e (intt_layer e st)) (poly_scale 2 st)

(** {2 Layers are linear} *)

let scale_comm (c z b: zq) : Lemma (mul z (mul c b) == mul c (mul z b))
  = assert (mul z (mul c b) == mul c (mul z b)) by (zring ())

let ntt_layer_scale (e: nat { e <= 7 }) (c: zq) (st: poly)
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

let intt_layer_scale (e: nat { e <= 7 }) (c: zq) (st: poly)
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

let intt_ntt_step (e: nat { e <= 7 }) (c: zq) (st: poly)
  : Lemma (intt_layer e (poly_scale c (ntt_layer e st)) == poly_scale (mul c 2) st)
  = intt_layer_scale e c (ntt_layer e st);
    intt_ntt_layer e st;
    poly_scale_scale c 2 st

let ntt_intt_step (e: nat { e <= 7 }) (c: zq) (st: poly)
  : Lemma (ntt_layer e (poly_scale c (intt_layer e st)) == poly_scale (mul c 2) st)
  = ntt_layer_scale e c (intt_layer e st);
    ntt_intt_layer e st;
    poly_scale_scale c 2 st

(** [intt] is a left inverse of [ntt] ... *)
let intt_ntt (f: poly) : Lemma (intt (ntt f) == f)
  = ntt_unfold f;
    let x7 = ntt_layer 7 f in
    let x6 = ntt_layer 6 x7 in
    let x5 = ntt_layer 5 x6 in
    let x4 = ntt_layer 4 x5 in
    let x3 = ntt_layer 3 x4 in
    let x2 = ntt_layer 2 x3 in
    let x1 = ntt_layer 1 x2 in
    let x0 = ntt_layer 0 x1 in
    intt_unfold x0;
    poly_scale_one x0;
    let c1 = mul 1 2 in
    let c2 = mul c1 2 in
    let c3 = mul c2 2 in
    let c4 = mul c3 2 in
    let c5 = mul c4 2 in
    let c6 = mul c5 2 in
    let c7 = mul c6 2 in
    intt_ntt_step 0 1 x1;
    intt_ntt_step 1 c1 x2;
    intt_ntt_step 2 c2 x3;
    intt_ntt_step 3 c3 x4;
    intt_ntt_step 4 c4 x5;
    intt_ntt_step 5 c5 x6;
    intt_ntt_step 6 c6 x7;
    intt_ntt_step 7 c7 f;
    assert_norm (mul (mul (mul (mul (mul (mul (mul (mul 1 2) 2) 2) 2) 2) 2) 2) 2 == 256);
    poly_scale_scale inv_256 256 f;
    inv_256_correct ();
    mul_comm inv_256 256;
    poly_scale_one f

(** ... and a right inverse. *)
let ntt_intt (f: poly) : Lemma (ntt (intt f) == f)
  = let y0 = intt_layer 0 f in
    let y1 = intt_layer 1 y0 in
    let y2 = intt_layer 2 y1 in
    let y3 = intt_layer 3 y2 in
    let y4 = intt_layer 4 y3 in
    let y5 = intt_layer 5 y4 in
    let y6 = intt_layer 6 y5 in
    let y7 = intt_layer 7 y6 in
    intt_unfold f;
    ntt_unfold (poly_scale inv_256 y7);
    let c1 = mul inv_256 2 in
    let c2 = mul c1 2 in
    let c3 = mul c2 2 in
    let c4 = mul c3 2 in
    let c5 = mul c4 2 in
    let c6 = mul c5 2 in
    let c7 = mul c6 2 in
    ntt_intt_step 7 inv_256 y6;
    ntt_intt_step 6 c1 y5;
    ntt_intt_step 5 c2 y4;
    ntt_intt_step 4 c3 y3;
    ntt_intt_step 3 c4 y2;
    ntt_intt_step 2 c5 y1;
    ntt_intt_step 1 c6 y0;
    ntt_intt_step 0 c7 f;
    assert_norm (mul (mul (mul (mul (mul (mul (mul (mul inv_256 2) 2) 2) 2) 2) 2) 2) 2 == 1);
    poly_scale_one f

(** {2 Linearity} *)

let ntt_layer_add (e: nat { e <= 7 }) (f g: poly)
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
    let f1 = ntt_layer 1 f2 in let g1 = ntt_layer 1 g2 in
    ntt_layer_add 7 f g;
    ntt_layer_add 6 f7 g7;
    ntt_layer_add 5 f6 g6;
    ntt_layer_add 4 f5 g5;
    ntt_layer_add 3 f4 g4;
    ntt_layer_add 2 f3 g3;
    ntt_layer_add 1 f2 g2;
    ntt_layer_add 0 f1 g1

let ntt_scale (c: zq) (f: poly) : Lemma (ntt (poly_scale c f) == poly_scale c (ntt f))
  = ntt_unfold (poly_scale c f); ntt_unfold f;
    let f7 = ntt_layer 7 f in
    let f6 = ntt_layer 6 f7 in
    let f5 = ntt_layer 5 f6 in
    let f4 = ntt_layer 4 f5 in
    let f3 = ntt_layer 3 f4 in
    let f2 = ntt_layer 2 f3 in
    let f1 = ntt_layer 1 f2 in
    ntt_layer_scale 7 c f;
    ntt_layer_scale 6 c f7;
    ntt_layer_scale 5 c f6;
    ntt_layer_scale 4 c f5;
    ntt_layer_scale 3 c f4;
    ntt_layer_scale 2 c f3;
    ntt_layer_scale 1 c f2;
    ntt_layer_scale 0 c f1

let poly_sub_scale (f g: poly) : Lemma (poly_sub f g == poly_add f (poly_scale (q - 1) g))
  = introduce forall (t: nat { t < n }).
        Seq.index (poly_sub f g) t == Seq.index (poly_add f (poly_scale (q - 1) g)) t
    with begin
      sub_is_add_neg (Seq.index f t) (Seq.index g t);
      mul_comm (q - 1) (Seq.index g t);
      mul_neg_one (Seq.index g t)
    end;
    Seq.lemma_eq_intro (poly_sub f g) (poly_add f (poly_scale (q - 1) g))

let ntt_sub (f g: poly) : Lemma (ntt (poly_sub f g) == poly_sub (ntt f) (ntt g))
  = poly_sub_scale f g;
    ntt_add f (poly_scale (q - 1) g);
    ntt_scale (q - 1) g;
    poly_sub_scale (ntt f) (ntt g)

(** [intt] is linear because it is [ntt]'s inverse. *)
let intt_add (f g: poly) : Lemma (intt (poly_add f g) == poly_add (intt f) (intt g))
  = ntt_add (intt f) (intt g);
    ntt_intt f; ntt_intt g;
    intt_ntt (poly_add (intt f) (intt g))

let intt_sub (f g: poly) : Lemma (intt (poly_sub f g) == poly_sub (intt f) (intt g))
  = ntt_sub (intt f) (intt g);
    ntt_intt f; ntt_intt g;
    intt_ntt (poly_sub (intt f) (intt g))

(** {1 The ring isomorphism} *)

let ntt_injective (f g: poly) : Lemma (requires ntt f == ntt g) (ensures f == g)
  = intt_ntt f; intt_ntt g

(** Multiplication in [R_q] is computed as FIPS 204 computes it. *)
let intt_poly_mul_ntt (f g: poly)
  : Lemma (intt (poly_mul (ntt f) (ntt g)) == ring_mul f g)
  = poly_mul_ntt f g;
    intt_ntt (ring_mul f g)

#pop-options
