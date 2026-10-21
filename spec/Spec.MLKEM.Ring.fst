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

(** Module algebra over [R_q] and [T_q] for the K-PKE correctness proof.

    {!Spec.MLKEM.NTT.Lemmas} shows that [ntt] is a ring isomorphism
    [R_q ~ T_q].  What the correctness argument additionally needs is that
    [T_q], with [poly_add] and [multiply_ntts], is a commutative ring, and
    the bookkeeping to move that up to the vectors and matrices FIPS 203
    computes with:

    - [multiply_ntts] is commutative, associative and distributes over
      [poly_add].  [T_q] is a product of the rings [Z_q[X]/(X^2 - gamma)],
      so all three are checked one quadratic factor at a time by the ring
      tactic;
    - [dot] is a finite sum [poly_sum] of [multiply_ntts] products
      ([dot_sum]), hence bilinear;
    - the identity behind the scheme ([dot_mat_vec_transpose]):

      [(A s) . y == s . (A^T y)]

      by exchanging a double sum and reassociating each term;
    - [intt] is additive, so it commutes with sums, and the [R_q] inner
      product [rq_dot a b = sum_i a_i * b_i] (schoolbook [poly_mul]) is
      what [intt (dot (vec_ntt a) (vec_ntt b))] computes ([rq_dot_ntt]). *)
module Spec.MLKEM.Ring

open FStar.Tactics.V2
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Spec.MLKEM.NTT.Lemmas
open Spec.MLKEM.Encode.Lemmas

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0"

(** {2 Addition of polynomials} *)

let poly_add_comm (f g: poly) : Lemma (poly_add f g == poly_add g f)
  = Seq.lemma_eq_intro (poly_add f g) (poly_add g f)

let poly_add_zero (f: poly) : Lemma (poly_add f poly_zero == f)
  = introduce forall (i: nat { i < n }). Seq.index (poly_add f poly_zero) i == Seq.index f i
    with add_zero (Seq.index f i);
    Seq.lemma_eq_intro (poly_add f poly_zero) f

let poly_add_swap4 (a b c d: poly)
  : Lemma (poly_add (poly_add a b) (poly_add c d) == poly_add (poly_add a c) (poly_add b d))
  = introduce forall (i: nat { i < n }).
      Seq.index (poly_add (poly_add a b) (poly_add c d)) i ==
      Seq.index (poly_add (poly_add a c) (poly_add b d)) i
    with add_swap4 (Seq.index a i) (Seq.index b i) (Seq.index c i) (Seq.index d i);
    Seq.lemma_eq_intro (poly_add (poly_add a b) (poly_add c d))
                       (poly_add (poly_add a c) (poly_add b d))

(** {2 [T_q] is a commutative ring}

    The two components of a base-case product, named so that the ring
    identities below are about [zq] values only. *)

let bc0 (a0 a1 b0 b1 g: zq) : zq = add (mul a0 b0) (mul (mul a1 b1) g)
let bc1 (a0 a1 b0 b1: zq) : zq = add (mul a0 b1) (mul a1 b0)

let pair_idx (t: nat { t < n })
  : Lemma (t / 2 < 128 /\ (t % 2 == 0 ==> t == 2 * (t / 2)) /\ (t % 2 <> 0 ==> t == 2 * (t / 2) + 1))
  = div_lt t 128 2;
    Math.euclidean_division_definition t 2

let mntt_even (f g: poly) (i: nat { i < 128 })
  : Lemma (Seq.index (multiply_ntts f g) (2 * i) ==
           bc0 (Seq.index f (2 * i)) (Seq.index f (2 * i + 1))
               (Seq.index g (2 * i)) (Seq.index g (2 * i + 1)) (gammas i))
  = multiply_ntts_index f g (2 * i);
    Math.cancel_mul_div i 2;
    Math.cancel_mul_mod i 2

let mntt_odd (f g: poly) (i: nat { i < 128 })
  : Lemma (Seq.index (multiply_ntts f g) (2 * i + 1) ==
           bc1 (Seq.index f (2 * i)) (Seq.index f (2 * i + 1))
               (Seq.index g (2 * i)) (Seq.index g (2 * i + 1)))
  = multiply_ntts_index f g (2 * i + 1);
    Math.lemma_div_plus 1 i 2;
    Math.lemma_mod_plus 1 i 2

let bc_comm (a0 a1 b0 b1 g: zq)
  : Lemma (bc0 a0 a1 b0 b1 g == bc0 b0 b1 a0 a1 g /\ bc1 a0 a1 b0 b1 == bc1 b0 b1 a0 a1)
  = assert (bc0 a0 a1 b0 b1 g == bc0 b0 b1 a0 a1 g) by (norm [delta_only [`%bc0]]; zring ());
    assert (bc1 a0 a1 b0 b1 == bc1 b0 b1 a0 a1) by (norm [delta_only [`%bc1]]; zring ())

let bc_assoc (a0 a1 b0 b1 c0 c1 g: zq)
  : Lemma (bc0 (bc0 a0 a1 b0 b1 g) (bc1 a0 a1 b0 b1) c0 c1 g ==
           bc0 a0 a1 (bc0 b0 b1 c0 c1 g) (bc1 b0 b1 c0 c1) g /\
           bc1 (bc0 a0 a1 b0 b1 g) (bc1 a0 a1 b0 b1) c0 c1 ==
           bc1 a0 a1 (bc0 b0 b1 c0 c1 g) (bc1 b0 b1 c0 c1))
  = assert (bc0 (bc0 a0 a1 b0 b1 g) (bc1 a0 a1 b0 b1) c0 c1 g ==
            bc0 a0 a1 (bc0 b0 b1 c0 c1 g) (bc1 b0 b1 c0 c1) g)
      by (norm [delta_only [`%bc0; `%bc1]]; zring ());
    assert (bc1 (bc0 a0 a1 b0 b1 g) (bc1 a0 a1 b0 b1) c0 c1 ==
            bc1 a0 a1 (bc0 b0 b1 c0 c1 g) (bc1 b0 b1 c0 c1))
      by (norm [delta_only [`%bc0; `%bc1]]; zring ())

let bc_distr (a0 a1 b0 b1 c0 c1 g: zq)
  : Lemma (bc0 a0 a1 (add b0 c0) (add b1 c1) g == add (bc0 a0 a1 b0 b1 g) (bc0 a0 a1 c0 c1 g) /\
           bc1 a0 a1 (add b0 c0) (add b1 c1) == add (bc1 a0 a1 b0 b1) (bc1 a0 a1 c0 c1))
  = assert (bc0 a0 a1 (add b0 c0) (add b1 c1) g == add (bc0 a0 a1 b0 b1 g) (bc0 a0 a1 c0 c1 g))
      by (norm [delta_only [`%bc0]]; zring ());
    assert (bc1 a0 a1 (add b0 c0) (add b1 c1) == add (bc1 a0 a1 b0 b1) (bc1 a0 a1 c0 c1))
      by (norm [delta_only [`%bc1]]; zring ())

let bc_zero (a0 a1 g: zq) : Lemma (bc0 a0 a1 0 0 g == 0 /\ bc1 a0 a1 0 0 == 0)
  = mul_zero a0; mul_zero a1; mul_comm 0 g

let mntt_comm (f g: poly) : Lemma (multiply_ntts f g == multiply_ntts g f)
  = introduce forall (t: nat { t < n }).
      Seq.index (multiply_ntts f g) t == Seq.index (multiply_ntts g f) t
    with begin
      let i = t / 2 in
      pair_idx t;
      mntt_even f g i; mntt_even g f i; mntt_odd f g i; mntt_odd g f i;
      bc_comm (Seq.index f (2 * i)) (Seq.index f (2 * i + 1))
              (Seq.index g (2 * i)) (Seq.index g (2 * i + 1)) (gammas i)
    end;
    Seq.lemma_eq_intro (multiply_ntts f g) (multiply_ntts g f)

let mntt_assoc (f g h: poly)
  : Lemma (multiply_ntts (multiply_ntts f g) h == multiply_ntts f (multiply_ntts g h))
  = let l = multiply_ntts (multiply_ntts f g) h in
    let r = multiply_ntts f (multiply_ntts g h) in
    introduce forall (t: nat { t < n }). Seq.index l t == Seq.index r t
    with begin
      let i = t / 2 in
      pair_idx t;
      mntt_even (multiply_ntts f g) h i; mntt_odd (multiply_ntts f g) h i;
      mntt_even f (multiply_ntts g h) i; mntt_odd f (multiply_ntts g h) i;
      mntt_even f g i; mntt_odd f g i; mntt_even g h i; mntt_odd g h i;
      bc_assoc (Seq.index f (2 * i)) (Seq.index f (2 * i + 1))
               (Seq.index g (2 * i)) (Seq.index g (2 * i + 1))
               (Seq.index h (2 * i)) (Seq.index h (2 * i + 1)) (gammas i)
    end;
    Seq.lemma_eq_intro l r

let mntt_add_r (f g h: poly)
  : Lemma (multiply_ntts f (poly_add g h) == poly_add (multiply_ntts f g) (multiply_ntts f h))
  = let l = multiply_ntts f (poly_add g h) in
    let r = poly_add (multiply_ntts f g) (multiply_ntts f h) in
    introduce forall (t: nat { t < n }). Seq.index l t == Seq.index r t
    with begin
      let i = t / 2 in
      pair_idx t;
      mntt_even f (poly_add g h) i; mntt_odd f (poly_add g h) i;
      mntt_even f g i; mntt_odd f g i; mntt_even f h i; mntt_odd f h i;
      bc_distr (Seq.index f (2 * i)) (Seq.index f (2 * i + 1))
               (Seq.index g (2 * i)) (Seq.index g (2 * i + 1))
               (Seq.index h (2 * i)) (Seq.index h (2 * i + 1)) (gammas i)
    end;
    Seq.lemma_eq_intro l r

let mntt_add_l (f g h: poly)
  : Lemma (multiply_ntts (poly_add f g) h == poly_add (multiply_ntts f h) (multiply_ntts g h))
  = mntt_comm (poly_add f g) h;
    mntt_add_r h f g;
    mntt_comm h f;
    mntt_comm h g

let mntt_zero_r (f: poly) : Lemma (multiply_ntts f poly_zero == poly_zero)
  = introduce forall (t: nat { t < n }).
      Seq.index (multiply_ntts f poly_zero) t == Seq.index poly_zero t
    with begin
      let i = t / 2 in
      pair_idx t;
      mntt_even f poly_zero i; mntt_odd f poly_zero i;
      bc_zero (Seq.index f (2 * i)) (Seq.index f (2 * i + 1)) (gammas i)
    end;
    Seq.lemma_eq_intro (multiply_ntts f poly_zero) poly_zero

(** {2 Finite sums of polynomials} *)

let rec poly_sum (m: nat) (f: nat -> poly) : Tot poly (decreases m)
  = if m = 0 then poly_zero else poly_add (poly_sum (m - 1) f) (f (m - 1))

#push-options "--fuel 1"

let rec poly_sum_ext (m: nat) (f g: nat -> poly)
  : Lemma (requires forall (i: nat). i < m ==> f i == g i)
          (ensures poly_sum m f == poly_sum m g) (decreases m)
  = if m > 0 then poly_sum_ext (m - 1) f g

let rec poly_sum_zero (m: nat) (f: nat -> poly)
  : Lemma (requires forall (i: nat). i < m ==> f i == poly_zero)
          (ensures poly_sum m f == poly_zero) (decreases m)
  = if m > 0 then begin poly_sum_zero (m - 1) f; poly_add_zero poly_zero end

let rec poly_sum_add (m: nat) (f g h: nat -> poly)
  : Lemma (requires forall (i: nat). i < m ==> h i == poly_add (f i) (g i))
          (ensures poly_sum m h == poly_add (poly_sum m f) (poly_sum m g)) (decreases m)
  = if m = 0 then poly_add_zero poly_zero
    else begin
      poly_sum_add (m - 1) f g h;
      poly_add_swap4 (poly_sum (m - 1) f) (poly_sum (m - 1) g) (f (m - 1)) (g (m - 1))
    end

let rec poly_sum_mul_l (m: nat) (a: poly) (f h: nat -> poly)
  : Lemma (requires forall (i: nat). i < m ==> h i == multiply_ntts a (f i))
          (ensures poly_sum m h == multiply_ntts a (poly_sum m f)) (decreases m)
  = if m = 0 then mntt_zero_r a
    else begin
      poly_sum_mul_l (m - 1) a f h;
      mntt_add_r a (poly_sum (m - 1) f) (f (m - 1))
    end

let rec poly_sum_mul_r (m: nat) (a: poly) (f h: nat -> poly)
  : Lemma (requires forall (i: nat). i < m ==> h i == multiply_ntts (f i) a)
          (ensures poly_sum m h == multiply_ntts (poly_sum m f) a) (decreases m)
  = if m = 0 then (mntt_zero_r a; mntt_comm a poly_zero)
    else begin
      poly_sum_mul_r (m - 1) a f h;
      mntt_add_l (poly_sum (m - 1) f) (f (m - 1)) a
    end

let rec poly_sum_swap (m1 m2: nat) (f: nat -> nat -> poly)
  : Lemma (ensures poly_sum m1 (fun i -> poly_sum m2 (f i)) ==
                   poly_sum m2 (fun j -> poly_sum m1 (fun i -> f i j)))
          (decreases m1)
  = if m1 = 0 then poly_sum_zero m2 (fun j -> poly_sum m1 (fun i -> f i j))
    else begin
      poly_sum_swap (m1 - 1) m2 f;
      poly_sum_add m2 (fun j -> poly_sum (m1 - 1) (fun i -> f i j)) (f (m1 - 1))
                      (fun j -> poly_sum m1 (fun i -> f i j))
    end

#pop-options

(** {2 [intt] is additive} *)

let ntt_zero () : Lemma (ntt poly_zero == poly_zero)
  = ntt_add poly_zero poly_zero;
    poly_add_zero poly_zero;
    let z = ntt poly_zero in
    introduce forall (i: nat { i < n }). Seq.index z i == Seq.index poly_zero i
    with assert (Seq.index z i == add (Seq.index z i) (Seq.index z i));
    Seq.lemma_eq_intro z poly_zero

let intt_zero () : Lemma (intt poly_zero == poly_zero)
  = ntt_zero (); intt_ntt poly_zero

let intt_add (f g: poly) : Lemma (intt (poly_add f g) == poly_add (intt f) (intt g))
  = ntt_intt (poly_add f g);
    ntt_add (intt f) (intt g);
    ntt_intt f; ntt_intt g;
    ntt_injective (intt (poly_add f g)) (poly_add (intt f) (intt g))

#push-options "--fuel 1"
let rec poly_sum_intt (m: nat) (f h: nat -> poly)
  : Lemma (requires forall (i: nat). i < m ==> h i == intt (f i))
          (ensures poly_sum m h == intt (poly_sum m f)) (decreases m)
  = if m = 0 then intt_zero ()
    else begin
      poly_sum_intt (m - 1) f h;
      intt_add (poly_sum (m - 1) f) (f (m - 1))
    end
#pop-options

(** {2 Vectors} *)

let vec_ext (#k: pos) (u v: pvec k)
  : Lemma (requires forall (i: nat { i < k }). vec_at u i == vec_at v i) (ensures u == v)
  = flat_ext k n u v

let vec_at_add (#k: pos) (u v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_add u v) i == poly_add (vec_at u i) (vec_at v i))
  = Math.lemma_mult_le_right n (i + 1) k;
    Seq.lemma_eq_intro (vec_at (vec_add u v) i) (poly_add (vec_at u i) (vec_at v i))

let vec_at_sub (#k: pos) (u v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_sub u v) i == poly_sub (vec_at u i) (vec_at v i))
  = Math.lemma_mult_le_right n (i + 1) k;
    Seq.lemma_eq_intro (vec_at (vec_sub u v) i) (poly_sub (vec_at u i) (vec_at v i))

let vec_at_ntt (#k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_ntt v) i == ntt (vec_at v i))
  = vec_at_of_fun k (fun j -> ntt (vec_at v j)) i

let vec_at_intt (#k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_intt v) i == intt (vec_at v i))
  = vec_at_of_fun k (fun j -> intt (vec_at v j)) i

let vec_ntt_add (#k: pos) (u v: pvec k)
  : Lemma (vec_ntt (vec_add u v) == vec_add (vec_ntt u) (vec_ntt v))
  = introduce forall (i: nat { i < k }).
      vec_at (vec_ntt (vec_add u v)) i == vec_at (vec_add (vec_ntt u) (vec_ntt v)) i
    with begin
      vec_at_ntt (vec_add u v) i;
      vec_at_add u v i;
      ntt_add (vec_at u i) (vec_at v i);
      vec_at_add (vec_ntt u) (vec_ntt v) i;
      vec_at_ntt u i; vec_at_ntt v i
    end;
    vec_ext (vec_ntt (vec_add u v)) (vec_add (vec_ntt u) (vec_ntt v))

let vec_ntt_intt (#k: pos) (v: pvec k) : Lemma (vec_ntt (vec_intt v) == v)
  = introduce forall (i: nat { i < k }). vec_at (vec_ntt (vec_intt v)) i == vec_at v i
    with begin
      vec_at_ntt (vec_intt v) i;
      vec_at_intt v i;
      ntt_intt (vec_at v i)
    end;
    vec_ext (vec_ntt (vec_intt v)) v

(** {2 [dot] is a sum} *)

let dot_term (#k: pos) (u v: pvec k) (i: nat) : poly
  = if i < k then multiply_ntts (vec_at u i) (vec_at v i) else poly_zero

#push-options "--fuel 1"
let rec dot_prefix (#k: pos) (u v: pvec k) (m: nat { m <= k })
  : Lemma (ensures Loops.repeati m
                     (fun i acc ->
                        if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
                        else acc)
                     poly_zero
                   == poly_sum m (dot_term u v))
          (decreases m)
  = if m > 0 then dot_prefix u v (m - 1)
#pop-options

let dot_sum (#k: pos) (u v: pvec k) : Lemma (dot u v == poly_sum k (dot_term u v))
  = dot_prefix u v k

let dot_add_l (#k: pos) (a b c: pvec k)
  : Lemma (dot (vec_add a b) c == poly_add (dot a c) (dot b c))
  = dot_sum (vec_add a b) c; dot_sum a c; dot_sum b c;
    introduce forall (i: nat). i < k ==>
      dot_term (vec_add a b) c i == poly_add (dot_term a c i) (dot_term b c i)
    with introduce _ ==> _ with begin
      vec_at_add a b i;
      mntt_add_l (vec_at a i) (vec_at b i) (vec_at c i)
    end;
    poly_sum_add k (dot_term a c) (dot_term b c) (dot_term (vec_add a b) c)

let dot_add_r (#k: pos) (a b c: pvec k)
  : Lemma (dot a (vec_add b c) == poly_add (dot a b) (dot a c))
  = dot_sum a (vec_add b c); dot_sum a b; dot_sum a c;
    introduce forall (i: nat). i < k ==>
      dot_term a (vec_add b c) i == poly_add (dot_term a b i) (dot_term a c i)
    with introduce _ ==> _ with begin
      vec_at_add b c i;
      mntt_add_r (vec_at a i) (vec_at b i) (vec_at c i)
    end;
    poly_sum_add k (dot_term a b) (dot_term a c) (dot_term a (vec_add b c))

(** {2 Matrices} *)

(** Entry [(i, j)] of a matrix. *)
let mat_at (#k: pos) (m: pmat k) (i: nat { i < k }) (j: nat { j < k }) : poly
  = vec_at (mat_row m i) j

let mat_at_flat (#k: pos) (m: pmat k) (i: nat { i < k }) (j: nat { j < k })
  : Lemma (i * k + j < k * k /\ mat_at m i j == flat_at (k * k) n m (i * k + j))
  = Math.lemma_mult_le_right k (i + 1) k;
    Math.lemma_mult_le_right n (i * k + j + 1) (k * k);
    Math.lemma_mult_le_right n (j + 1) k;
    Math.paren_mul_right k k n;
    Math.distributivity_add_left (i * k) j n;
    Math.paren_mul_right i k n;
    Seq.lemma_eq_intro (mat_at m i j) (flat_at (k * k) n m (i * k + j))

let vec_at_mat_vec_mul (#k: pos) (m: pmat k) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (mat_vec_mul m v) i == dot (mat_row m i) v)
  = vec_at_of_fun k (fun j -> dot (mat_row m j) v) i

(** The summand [(A_ji s_i) y_j] of both sides of [dot_mat_vec_transpose]. *)
let tri (#k: pos) (a: pmat k) (s y: pvec k) (j i: nat) : poly
  = if j < k && i < k
    then multiply_ntts (multiply_ntts (mat_at a j i) (vec_at s i)) (vec_at y j)
    else poly_zero

let lhs_row (#k: pos) (a: pmat k) (s y: pvec k) (j: nat { j < k })
  : Lemma (dot_term (mat_vec_mul a s) y j == poly_sum k (tri a s y j))
  = vec_at_mat_vec_mul a s j;
    dot_sum (mat_row a j) s;
    poly_sum_mul_r k (vec_at y j) (dot_term (mat_row a j) s) (tri a s y j)

let rhs_row (#k: pos) (a at: pmat k) (s y: pvec k) (i: nat { i < k })
  : Lemma (requires forall (i j: (l: nat { l < k })). mat_at at i j == mat_at a j i)
          (ensures dot_term s (mat_vec_mul at y) i == poly_sum k (fun j -> tri a s y j i))
  = vec_at_mat_vec_mul at y i;
    dot_sum (mat_row at i) y;
    introduce forall (j: nat). j < k ==>
      tri a s y j i == multiply_ntts (vec_at s i) (dot_term (mat_row at i) y j)
    with introduce _ ==> _ with begin
      let aji = mat_at a j i in
      mntt_comm aji (vec_at s i);
      mntt_assoc (vec_at s i) aji (vec_at y j)
    end;
    poly_sum_mul_l k (vec_at s i) (dot_term (mat_row at i) y) (fun j -> tri a s y j i)

(** [(A s) . y == s . (A^T y)], with [A^T] given by its entries. *)
let dot_mat_vec_transpose (#k: pos) (a at: pmat k) (s y: pvec k)
  : Lemma (requires forall (i j: (l: nat { l < k })). mat_at at i j == mat_at a j i)
          (ensures dot (mat_vec_mul a s) y == dot s (mat_vec_mul at y))
  = dot_sum (mat_vec_mul a s) y;
    dot_sum s (mat_vec_mul at y);
    introduce forall (j: nat). j < k ==>
      dot_term (mat_vec_mul a s) y j == poly_sum k (tri a s y j)
    with introduce _ ==> _ with lhs_row a s y j;
    poly_sum_ext k (dot_term (mat_vec_mul a s) y) (fun j -> poly_sum k (tri a s y j));
    introduce forall (i: nat). i < k ==>
      dot_term s (mat_vec_mul at y) i == poly_sum k (fun j -> tri a s y j i)
    with introduce _ ==> _ with rhs_row a at s y i;
    poly_sum_ext k (dot_term s (mat_vec_mul at y)) (fun i -> poly_sum k (fun j -> tri a s y j i));
    poly_sum_swap k k (tri a s y)

(** {2 The inner product in [R_q]} *)

let rq_term (#k: pos) (a b: pvec k) (i: nat) : poly
  = if i < k then poly_mul (vec_at a i) (vec_at b i) else poly_zero

(** [a^T b = sum_i a_i b_i], computed with the schoolbook product. *)
let rq_dot (#k: pos) (a b: pvec k) : poly = poly_sum k (rq_term a b)

let rq_dot_ntt (#k: pos) (a b: pvec k)
  : Lemma (intt (dot (vec_ntt a) (vec_ntt b)) == rq_dot a b)
  = dot_sum (vec_ntt a) (vec_ntt b);
    introduce forall (i: nat). i < k ==> rq_term a b i == intt (dot_term (vec_ntt a) (vec_ntt b) i)
    with introduce _ ==> _ with begin
      vec_at_ntt a i; vec_at_ntt b i;
      intt_multiply_ntts (vec_at a i) (vec_at b i)
    end;
    poly_sum_intt k (dot_term (vec_ntt a) (vec_ntt b)) (rq_term a b)

#pop-options
