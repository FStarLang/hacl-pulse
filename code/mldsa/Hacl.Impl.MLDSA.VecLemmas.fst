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


(** Pure lemmas for {!Hacl.Impl.MLDSA.Vec}: the per-entry loops over
    vectors and the [k x l] matrix-vector product.  They follow
    {!Hacl.Impl.MLKEM.VecLemmas}, with [k x l] matrices in place of square
    ones. *)
module Hacl.Impl.MLDSA.VecLemmas

open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq

module Seq = FStar.Seq
module S32 = Hacl.Secret.UInt32
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let flat_index (k: pos) (v: pvec k) (i: nat { i < k }) (j: nat { j < n })
  : Lemma (Seq.index v (i * n + j) == Seq.index (vec_at v i) j)
  = Math.lemma_mult_le_right n (i + 1) k;
    Seq.lemma_index_slice v (i * n) (i * n + n) j

let flat_index_all (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (forall (j: nat). j < n ==> Seq.index v (i * n + j) == Seq.index (vec_at v i) j)
  = FStar.Classical.forall_intro (flat_index k v i)

(** Entries below [i] hold [r], entry [i] has just become [b], the rest is
    the input [vv]. *)
let entry_step (k: pos) (i: nat { i < k })
               (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n) (r: pvec k)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==> S32.v (Seq.index w0 t) == Seq.index r t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == vec_at #k r i)
    (ensures
      (forall (t: nat). t < (i + 1) * n ==> S32.v (Seq.index w1 t) == Seq.index r t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = flat_index_all k r i

let entry_done (k: pos) (w: Seq.lseq zqt (k * n)) (r: pvec k)
  : Lemma (requires forall (t: nat). t < k * n ==> S32.v (Seq.index w t) == Seq.index r t)
          (ensures as_zqs w == r)
  = as_zqs_intro w r

let vec_ntt_at (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_ntt #k v) i == ntt (vec_at #k v i))
  = vec_at_of_fun k (fun j -> ntt (vec_at #k v j)) i

let vec_intt_at (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_intt #k v) i == intt (vec_at #k v i))
  = vec_at_of_fun k (fun j -> intt (vec_at #k v j)) i

let vec_scale_at (k: pos) (c: poly) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_scale #k c v) i == poly_mul c (vec_at #k v i))
  = vec_at_of_fun k (fun j -> poly_mul c (vec_at #k v j)) i

let ntt_entry_step (k: pos) (i: nat { i < k })
                   (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S32.v (Seq.index w0 t) == Seq.index (vec_ntt #k (as_zqs vv)) t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == ntt (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S32.v (Seq.index w1 t) == Seq.index (vec_ntt #k (as_zqs vv)) t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = vec_ntt_at k (as_zqs vv) i;
    entry_step k i vv w0 w1 b (vec_ntt #k (as_zqs vv))

let intt_entry_step (k: pos) (i: nat { i < k })
                    (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S32.v (Seq.index w0 t) == Seq.index (vec_intt #k (as_zqs vv)) t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == intt (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S32.v (Seq.index w1 t) == Seq.index (vec_intt #k (as_zqs vv)) t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = vec_intt_at k (as_zqs vv) i;
    entry_step k i vv w0 w1 b (vec_intt #k (as_zqs vv))

let scale_entry_step (k: pos) (i: nat { i < k }) (c: poly)
                     (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S32.v (Seq.index w0 t) == Seq.index (vec_scale #k c (as_zqs vv)) t) /\
      as_poly b == poly_mul c (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S32.v (Seq.index w1 t) == Seq.index (vec_scale #k c (as_zqs vv)) t))
  = vec_scale_at k c (as_zqs vv) i;
    entry_step k i w0 w0 w1 b (vec_scale #k c (as_zqs vv))

(** {2 The dot product} *)

let dot_acc (#l: pos) (u v: pvec l) (m: nat { m <= l }) : poly
  = Loops.repeati m
      (fun i acc -> if i < l then poly_add acc (poly_mul (vec_at u i) (vec_at v i)) else acc)
      poly_zero

let dot_acc_zero (#l: pos) (u v: pvec l)
  : Lemma (dot_acc u v 0 == poly_zero)
  = Loops.repeati_zero #poly
      (fun i acc -> if i < l then poly_add acc (poly_mul (vec_at u i) (vec_at v i)) else acc)
      poly_zero

let dot_acc_full (#l: pos) (u v: pvec l)
  : Lemma (dot_acc u v l == dot u v)
  = ()

let dot_step_done (#l: pos) (u v: pvec l) (m: nat { m < l })
                  (d c w: Seq.lseq zqt n)
  : Lemma (requires
      as_poly d == dot_acc u v m /\
      as_poly c == poly_mul (vec_at u m) (vec_at v m) /\
      (forall (t: nat). t < n ==>
         S32.v (Seq.index w t) == add (S32.v (Seq.index d t)) (S32.v (Seq.index c t))))
    (ensures as_poly w == dot_acc u v (m + 1))
  = Loops.unfold_repeati #poly m
      (fun i acc -> if i < l then poly_add acc (poly_mul (vec_at u i) (vec_at v i)) else acc)
      poly_zero;
    as_poly_intro w (dot_acc u v (m + 1))

(** {2 The matrix-vector product} *)

let as_zqs_row (k l: pos) (s: Seq.seq zqt { Seq.length s == k * l * n }) (i: nat { i < k })
  : Lemma (mat_row #k #l (as_zqs s) i ==
           as_zqs (Seq.slice s (i * (l * n)) (i * (l * n) + l * n)))
  = Math.paren_mul_right k l n;
    Math.lemma_mult_le_right (l * n) (i + 1) k;
    as_zqs_slice s (i * (l * n)) (i * (l * n) + l * n)

let mat_vec_mul_at (k l: pos) (m: pmat k l) (v: pvec l) (i: nat { i < k })
  : Lemma (vec_at (mat_vec_mul #k #l m v) i == dot (mat_row #k #l m i) v)
  = vec_at_of_fun k (fun j -> dot (mat_row #k #l m j) v) i

let mv_entry_step (k l: pos) (i: nat { i < k })
                  (vm: Seq.lseq zqt (k * l * n)) (vv: Seq.lseq zqt (l * n))
                  (w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S32.v (Seq.index w0 t) ==
           Seq.index (mat_vec_mul #k #l (as_zqs vm) (as_zqs vv)) t) /\
      as_poly b == dot (mat_row #k #l (as_zqs vm) i) (as_zqs vv))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S32.v (Seq.index w1 t) ==
           Seq.index (mat_vec_mul #k #l (as_zqs vm) (as_zqs vv)) t))
  = mat_vec_mul_at k l (as_zqs vm) (as_zqs vv) i;
    entry_step k i w0 w0 w1 b (mat_vec_mul #k #l (as_zqs vm) (as_zqs vv))

#pop-options
