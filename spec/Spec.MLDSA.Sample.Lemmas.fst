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


(** Norm bounds for the sign-then-verify correctness proof: {!norm} is
    subadditive and submultiplicative, so the negacyclic product of the
    challenge [c] with a secret bounded by [eta] is bounded by [eta] times
    the [l1] norm of [c]; the challenge has [l1] norm at most [tau]; and the
    secret vectors are bounded by [eta]. *)
module Spec.MLDSA.Sample.Lemmas

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Ring
open Spec.MLDSA.Sample

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module KZ = Spec.MLKEM.Zq
module Classical = FStar.Classical

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(** {2 The norm} *)

(** Any integer representative is at least as large as the centred one. *)
let norm_le (x: zq) (u: int)
  : Lemma (requires x == u % q) (ensures norm x <= abs u)
  = Math.euclidean_division_definition u q;
    let k = u / q in
    if k >= 1 then Math.lemma_mult_le_right q 1 k
    else if k <= -1 then Math.lemma_mult_le_right q k (-1)

let centre_mod (a: zq) : Lemma (centre a % q == a /\ abs (centre a) == norm a)
  = if a > half_q then Math.lemma_mod_plus a (-1) q else Math.small_mod a q

let abs_mul (x y: int) : Lemma (abs (x * y) == abs x * abs y)
  = if x >= 0 then (if y >= 0 then () else Math.neg_mul_right x y)
    else (if y >= 0 then Math.neg_mul_left x y else Math.neg_mul_left x y)

let norm_neg (a: zq) : Lemma (norm (neg a) == norm a)
  = if a = 0 then () else Math.small_mod (q - a) q

let norm_add (a b: zq) : Lemma (norm (add a b) <= norm a + norm b)
  = centre_mod a; centre_mod b;
    Math.lemma_mod_plus_distr_l (centre a) (centre b) q;
    Math.lemma_mod_plus_distr_r a (centre b) q;
    norm_le (add a b) (centre a + centre b)

let norm_mul (a b: zq) : Lemma (norm (mul a b) <= norm a * norm b)
  = centre_mod a; centre_mod b;
    Math.lemma_mod_mul_distr_l (centre a) (centre b) q;
    Math.lemma_mod_mul_distr_r a (centre b) q;
    norm_le (mul a b) (centre a * centre b);
    abs_mul (centre a) (centre b)

(** {2 The negacyclic product} *)

(** the l1 norm of the first m coefficients *)
let rec l1 (c: poly) (m: nat { m <= n }) : Tot nat (decreases m)
  = if m = 0 then 0 else l1 c (m - 1) + norm (Seq.index c (m - 1))

let ring_mul_at_bound (c s: poly) (e: nat) (k: nat { k < n }) (j: nat { j < n })
  : Lemma (requires forall (j: nat). j < n ==> norm (Seq.index s j) <= e)
          (ensures norm (ring_mul_at c s k j) <= e * norm (Seq.index c j))
  = let x = if j <= k then k - j else k + n - j in
    norm_mul (Seq.index c j) (Seq.index s x);
    norm_neg (mul (Seq.index c j) (Seq.index s x));
    Math.lemma_mult_le_left (norm (Seq.index c j)) (norm (Seq.index s x)) e;
    Math.swap_mul (norm (Seq.index c j)) e

#push-options "--fuel 1"
let rec sum_bound (c s: poly) (e: nat) (k: nat { k < n }) (m: nat { m <= n })
  : Lemma (requires forall (j: nat). j < n ==> norm (Seq.index s j) <= e)
          (ensures norm (sum m (ring_mul_at c s k)) <= e * l1 c m)
          (decreases m)
  = if m = 0 then ()
    else begin
      sum_bound c s e k (m - 1);
      norm_add (sum (m - 1) (ring_mul_at c s k)) (ring_mul_at c s k (m - 1));
      ring_mul_at_bound c s e k (m - 1);
      Math.distributivity_add_right e (l1 c (m - 1)) (norm (Seq.index c (m - 1)))
    end
#pop-options

(** the negacyclic product of c with a polynomial bounded by e *)
let ring_mul_bound (c s: poly) (e: nat) (k: nat { k < n })
  : Lemma (requires forall (j: nat). j < n ==> norm (Seq.index s j) <= e)
          (ensures norm (Seq.index (ring_mul c s) k) <= e * l1 c n)
  = ring_mul_index c s k;
    sum_bound c s e k n

(** {2 The challenge} *)

#push-options "--fuel 1"
let rec l1_zero (m: nat { m <= n }) : Lemma (ensures l1 poly_zero m == 0) (decreases m)
  = if m > 0 then l1_zero (m - 1)

let rec l1_upd_m (c: poly) (x: nat { x < n }) (v: zq) (m: nat { m <= n })
  : Lemma (ensures (if x < m then l1 (Seq.upd c x v) m + norm (Seq.index c x) == l1 c m + norm v
                    else l1 (Seq.upd c x v) m == l1 c m))
          (decreases m)
  = if m > 0 then l1_upd_m c x v (m - 1)
#pop-options

let l1_upd (c: poly) (x: nat { x < n }) (v: zq)
  : Lemma (l1 (Seq.upd c x v) n + norm (Seq.index c x) == l1 c n + norm v)
  = l1_upd_m c x v n

let ball_inv (tau: pos { tau <= 60 }) (st: ball_state) : prop
  = n - tau <= st.ball_i /\ st.ball_i <= n /\
    (forall (j: nat). st.ball_i <= j /\ j < n ==> Seq.index st.ball_c j == 0) /\
    l1 st.ball_c n <= st.ball_i - (n - tau)

let ball_step_inv (tau: pos { tau <= 60 }) (seed: Seq.seq S8.t) (t: nat) (st: ball_state)
  : Lemma (requires ball_inv tau st) (ensures ball_inv tau (ball_step tau seed t st))
  = if st.ball_i >= n || st.ball_i < n - tau then ()
    else begin
      let i = st.ball_i in
      let j = S8.v (shake256_byte seed (8 + t)) in
      if j <= i then begin
        let c = st.ball_c in
        let c1 = Seq.upd c i (Seq.index c j) in
        let v : zq = if sign_bit seed (i + tau - n) then q - 1 else 1 in
        let c2 = Seq.upd c1 j v in
        l1_upd c i (Seq.index c j);
        l1_upd c1 j v;
        assert (Seq.index c1 j == Seq.index c j);
        assert (norm v == 1);
        assert (ball_step tau seed t st == { ball_c = c2; ball_i = i + 1 })
      end
      else ()
    end

#push-options "--fuel 1"
let rec ball_sampled_inv (tau: pos { tau <= 60 }) (seed: Seq.seq S8.t) (m: nat)
  : Lemma (ensures ball_inv tau (ball_sampled tau seed m)) (decreases m)
  = if m = 0 then begin
      Loops.repeati_g_zero (ball_step tau seed) (ball_init tau);
      l1_zero n
    end
    else begin
      ball_sampled_inv tau seed (m - 1);
      Loops.unfold_repeati_g (m - 1) (ball_step tau seed) (ball_init tau);
      ball_step_inv tau seed (m - 1) (ball_sampled tau seed (m - 1))
    end
#pop-options

(** the challenge has l1 norm at most tau *)
let sample_in_ball_l1 (p: params) (seed: Seq.seq S8.t)
  : Lemma (l1 (sample_in_ball p seed) n <= p.tau)
  = ball_sampled_inv p.tau seed max_ball;
    l1_zero n

(** {2 The secret vectors} *)

let bounded_by (s: Seq.seq zq) (e: nat) : prop
  = forall (i: nat). i < Seq.length s ==> norm (Seq.index s i) <= e

let coeff_of_bound (eta: pos { eta == 2 \/ eta == 4 }) (z: nat)
  : Lemma (requires coeff_ok eta z) (ensures norm (coeff_of eta z) <= eta)
  = if eta = 2 then norm_le (coeff_of eta z) (2 - z % 5)
    else norm_le (coeff_of eta z) (4 - z)

let snoc_bounded (s: Seq.seq zq) (x: zq) (e: nat)
  : Lemma (requires bounded_by s e /\ norm x <= e) (ensures bounded_by (Seq.snoc s x) e)
  = let s' = Seq.snoc s x in
    introduce forall (i: nat). i < Seq.length s' ==> norm (Seq.index s' i) <= e
    with introduce _ ==> _
    with if i < Seq.length s then Seq.lemma_index_app1 s (Seq.create 1 x) i
            else Seq.lemma_index_app2 s (Seq.create 1 x) i

let push_half_bounded (eta: pos { eta == 2 \/ eta == 4 }) (acc: partial) (z: nat)
  : Lemma (requires bounded_by acc eta) (ensures bounded_by (push_half eta acc z) eta)
  = if Seq.length acc < n && coeff_ok eta z then begin
      coeff_of_bound eta z;
      snoc_bounded acc (coeff_of eta z) eta
    end

#push-options "--fuel 1"
let rec bounded_sampled_bounded (eta: pos { eta == 2 \/ eta == 4 }) (seed: Seq.seq S8.t) (m: nat)
  : Lemma (ensures bounded_by (bounded_sampled eta seed m) eta) (decreases m)
  = if m = 0 then Loops.repeati_g_zero (bounded_step eta seed) Seq.empty
    else begin
      bounded_sampled_bounded eta seed (m - 1);
      Loops.unfold_repeati_g (m - 1) (bounded_step eta seed) Seq.empty;
      let acc = bounded_sampled eta seed (m - 1) in
      let b = S8.v (shake256_byte seed (m - 1)) in
      push_half_bounded eta acc (b % 16);
      push_half_bounded eta (push_half eta acc (b % 16)) (b / 16)
    end
#pop-options

let rej_bounded_poly_bound (eta: pos { eta == 2 \/ eta == 4 }) (seed: Seq.seq S8.t)
  : Lemma (forall (j: nat). j < n ==> norm (Seq.index (rej_bounded_poly eta seed) j) <= eta)
  = bounded_sampled_bounded eta seed max_bounded

let vec_bound (k: pos) (f: (i: nat { i < k }) -> GTot poly) (e: nat)
  : Lemma (requires forall (r: nat { r < k }) (j: nat). j < n ==> norm (Seq.index (f r) j) <= e)
          (ensures forall (i: nat). i < k * n ==> norm (Seq.index (vec_of_fun_g k f) i) <= e)
  = introduce forall (i: nat). i < k * n ==> norm (Seq.index (vec_of_fun_g k f) i) <= e
    with introduce _ ==> _
    with KZ.div_lt i k n

(** the secret vectors are bounded by eta *)
let expand_s1_bound (p: params) (rho': Seq.lseq S8.t 64)
  : Lemma (forall (i: nat). i < p.l * n ==> norm (Seq.index (expand_s1 p rho') i) <= p.eta)
  = assert_norm (pow2 16 == 65536);
    Classical.forall_intro (rej_bounded_poly_bound p.eta);
    vec_bound p.l (fun r -> rej_bounded_poly p.eta (seed_16 rho' r)) p.eta

let expand_s2_bound (p: params) (rho': Seq.lseq S8.t 64)
  : Lemma (forall (i: nat). i < p.k * n ==> norm (Seq.index (expand_s2 p rho') i) <= p.eta)
  = assert_norm (pow2 16 == 65536);
    Classical.forall_intro (rej_bounded_poly_bound p.eta);
    vec_bound p.k (fun r -> rej_bounded_poly p.eta (seed_16 rho' (r + p.l))) p.eta

#pop-options
