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

(** The number-theoretic transform, FIPS 204 algorithms 41 and 42.

    The presentation is {!Spec.MLKEM.NTT}'s: each layer is written
    pointwise, as a function of the input computing output coefficient
    [t], and the transform is the composition of the layers.  The
    differences from ML-KEM are all consequences of [q - 1] being
    divisible by 512 rather than only by 256: there are eight layers
    rather than seven, the last one has half-width 1, the root table has
    256 entries indexed by [BitRev8], and the product in the NTT domain is
    coefficient by coefficient.

    That [NTT] is a ring isomorphism is proved separately, in
    {!Spec.MLDSA.NTT.Lemmas}; this module is the standard's pseudocode,
    which the implementation is proved to compute. *)
module Spec.MLDSA.NTT

open Spec.MLDSA.Zq

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0"

(** {2 Index arithmetic} *)

let n_pow2 () : Lemma (n == pow2 8) = assert_norm (256 == pow2 8)

let even_step (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 == 0) (ensures t + pow2 e < n)
  = let p = pow2 e in
    let m = pow2 (8 - e) in
    n_pow2 ();
    Math.pow2_plus (8 - e) e;
    assert (n == m * p);
    KZ.div_lt t m p;
    Math.pow2_plus 1 (7 - e);
    assert_norm (pow2 1 == 2);
    assert (m == 2 * pow2 (7 - e));
    assert (t / p <= m - 2);
    Math.lemma_div_mod t p;
    Math.distributivity_add_left (t / p) 1 p;
    Math.lemma_mult_le_right p (t / p + 1) (m - 1);
    Math.distributivity_sub_left m 1 p

let odd_step (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 <> 0) (ensures pow2 e <= t)
  = Math.lemma_div_mod t (pow2 e);
    Math.lemma_mult_le_right (pow2 e) 1 (t / pow2 e)

(** The root index of the butterfly [t] belongs to in the layer of
    half-width [2^e]: algorithm 41 increments [m] from 1, and the earlier
    layers have used [2^(7-e) - 1] roots. *)
let zidx (e: nat { e <= 7 }) (t: nat { t < n }) : r: nat { 0 < r /\ r < 256 }
  = let b = t / pow2 (e + 1) in
    n_pow2 ();
    Math.pow2_plus (7 - e) (e + 1);
    KZ.div_lt t (pow2 (7 - e)) (pow2 (e + 1));
    Math.pow2_plus 1 (7 - e);
    Math.pow2_le_compat 7 (7 - e);
    assert_norm (pow2 1 == 2);
    assert_norm (pow2 7 == 128);
    pow2 (7 - e) + b

(** Algorithm 42 decrements [m] from 256 instead. *)
let zidx_inv (e: nat { e <= 7 }) (t: nat { t < n }) : r: nat { 0 < r /\ r < 256 }
  = let b = t / pow2 (e + 1) in
    n_pow2 ();
    Math.pow2_plus (7 - e) (e + 1);
    KZ.div_lt t (pow2 (7 - e)) (pow2 (e + 1));
    Math.pow2_plus 1 (7 - e);
    Math.pow2_le_compat 7 (7 - e);
    assert_norm (pow2 1 == 2);
    assert_norm (pow2 7 == 128);
    pow2 (8 - e) - 1 - b

(** {2 The roots of unity}

    [zetas.[i] = zeta^BitRev8(i)], FIPS 204 appendix B. *)
let zetas (i: nat { i < 256 }) : zq = pow zeta (bitrev8 i)

(** {2 The forward transform}

    One Cooley-Tukey layer, pointwise. *)
let ntt_layer_at (e: nat { e <= 7 }) (f: poly) (t: nat { t < n }) : zq
  = let len = pow2 e in
    let z = zetas (zidx e t) in
    if (t / len) % 2 = 0 then begin
      even_step e t;
      add (Seq.index f t) (mul z (Seq.index f (t + len)))
    end else begin
      odd_step e t;
      sub (Seq.index f (t - len)) (mul z (Seq.index f t))
    end

let ntt_layer (e: nat { e <= 7 }) (f: poly) : poly
  = Seq.init n (ntt_layer_at e f)

let ntt_layer_index (e: nat { e <= 7 }) (f: poly) (t: nat { t < n })
  : Lemma (Seq.index (ntt_layer e f) t == ntt_layer_at e f t)
  = Seq.init_index_ n (ntt_layer_at e f) t

(** Algorithm 41: eight layers, half-width 128 down to 1. *)
let ntt (f: poly) : poly
  = Loops.repeati 8 (fun l acc -> if l < 8 then ntt_layer (7 - l) acc else acc) f

#push-options "--fuel 9"
let ntt_unfold (f: poly)
  : Lemma (ntt f ==
           ntt_layer 0 (ntt_layer 1 (ntt_layer 2 (ntt_layer 3 (ntt_layer 4
             (ntt_layer 5 (ntt_layer 6 (ntt_layer 7 f))))))))
  = ()
#pop-options

(** {2 The inverse transform}

    One Gentleman-Sande layer.  Algorithm 42 writes the upper output as
    [(-zetas[m]) * (t - f[j + len])]; that is [zetas[m] * (f[j + len] - t)],
    which is the form used here and the form an implementation computes. *)
let intt_layer_at (e: nat { e <= 7 }) (f: poly) (t: nat { t < n }) : zq
  = let len = pow2 e in
    let z = zetas (zidx_inv e t) in
    if (t / len) % 2 = 0 then begin
      even_step e t;
      add (Seq.index f t) (Seq.index f (t + len))
    end else begin
      odd_step e t;
      mul z (sub (Seq.index f t) (Seq.index f (t - len)))
    end

let intt_layer (e: nat { e <= 7 }) (f: poly) : poly
  = Seq.init n (intt_layer_at e f)

let intt_layer_index (e: nat { e <= 7 }) (f: poly) (t: nat { t < n })
  : Lemma (Seq.index (intt_layer e f) t == intt_layer_at e f t)
  = Seq.init_index_ n (intt_layer_at e f) t

(** [256^-1 mod q]. *)
let inv_256 : zq = 8347681

let inv_256_correct () : Lemma (mul 256 inv_256 == 1) = assert_norm (mul 256 inv_256 == 1)

let poly_scale (c: zq) (f: poly) : poly
  = Seq.init n (fun i -> mul c (Seq.index f i))

let poly_scale_index (c: zq) (f: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_scale c f) i == mul c (Seq.index f i))
          [SMTPat (Seq.index (poly_scale c f) i)]
  = Seq.init_index_ n (fun j -> mul c (Seq.index f j)) i

(** Algorithm 42: half-width 1 up to 128, then the scaling. *)
let intt (f: poly) : poly
  = poly_scale inv_256 (Loops.repeati 8 (fun l acc -> if l < 8 then intt_layer l acc else acc) f)

#push-options "--fuel 9"
let intt_unfold (f: poly)
  : Lemma (intt f ==
           poly_scale inv_256
             (intt_layer 7 (intt_layer 6 (intt_layer 5 (intt_layer 4
               (intt_layer 3 (intt_layer 2 (intt_layer 1 (intt_layer 0 f)))))))))
  = ()
#pop-options

(** {2 Vectors} *)

let vec_ntt (#k: pos) (v: pvec k) : pvec k
  = vec_of_fun k (fun i -> ntt (vec_at v i))

let vec_intt (#k: pos) (v: pvec k) : pvec k
  = vec_of_fun k (fun i -> intt (vec_at v i))

(** [c * v] for a single polynomial [c], all in the NTT domain. *)
let vec_scale (#k: pos) (c: poly) (v: pvec k) : pvec k
  = vec_of_fun k (fun i -> poly_mul c (vec_at v i))

(** The inner product of two [l]-vectors in the NTT domain. *)
let dot (#l: pos) (u v: pvec l) : poly
  = Loops.repeati l
      (fun i acc -> if i < l then poly_add acc (poly_mul (vec_at u i) (vec_at v i)) else acc)
      poly_zero

let mat_vec_mul (#k #l: pos) (m: pmat k l) (v: pvec l) : pvec k
  = vec_of_fun k (fun i -> dot (mat_row m i) v)

#pop-options
