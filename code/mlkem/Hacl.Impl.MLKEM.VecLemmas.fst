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

(** The pure lemmas behind the vector loops.

    These live in a module of their own, and one that deliberately does not
    open the Pulse implementation modules, because opening a large Pulse
    module puts its whole encoding into the solver's context: the very same
    lemmas take four seconds here and eight minutes when
    {!Hacl.Impl.MLKEM.NTT} is in scope. *)
module Hacl.Impl.MLKEM.VecLemmas

open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq

module Seq = FStar.Seq
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Coefficient [i m + j] of a flat sequence is coefficient [j] of block
    [i]. *)
let flat_index (#a: Type) (k: pos) (m: pos) (v: Seq.lseq a (k * m))
               (i: nat { i < k }) (j: nat { j < m })
  : Lemma (Seq.index v (i * m + j) == Seq.index (flat_at k m v i) j)
  = Math.lemma_mult_le_right m (i + 1) k;
    Seq.lemma_index_slice v (i * m) (i * m + m) j

(** Every coefficient of block [i] at once. *)
let flat_index_all (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (forall (j: nat). j < n ==> Seq.index v (i * n + j) == Seq.index (vec_at v i) j)
  = FStar.Classical.forall_intro (flat_index k n v i)

(** Two blocks of a flat sequence do not overlap. *)
let flat_disjoint (k: pos) (m: pos) (i: nat { i < k }) (j: nat { j < k })
  : Lemma (requires i <> j)
          (ensures (i < j ==> i * m + m <= j * m) /\ (j < i ==> j * m + m <= i * m))
  = if i < j then Math.lemma_mult_le_right m (i + 1) j
             else Math.lemma_mult_le_right m (j + 1) i

(** One step of a per-entry loop: entries below [i] already hold [f] applied
    to the corresponding entry of the input, entry [i] has just been replaced
    by [b], and the rest is untouched.  Stating this once, as a pure lemma,
    keeps the loop's own verification condition small. *)
let entry_step (k: pos) (i: nat { i < k })
               (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n) (r: pvec k)
  : Lemma (requires
      Seq.length vv == k * n /\ Seq.length w0 == k * n /\
      Seq.length w1 == k * n /\ Seq.length b == n /\
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==> S16.v (Seq.index w0 t) == Seq.index r t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == vec_at #k r i)
    (ensures
      (forall (t: nat). t < (i + 1) * n ==> S16.v (Seq.index w1 t) == Seq.index r t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = flat_index_all k r i

(** Entrywise characterisation of [vec_ntt]. *)
let vec_ntt_at (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_ntt #k v) i == ntt (vec_at #k v i))
  = vec_at_of_fun k (fun j -> ntt (vec_at #k v j)) i

(** The two specialisations of the lemmas above to [vec_ntt].  Their whole
    point is that a caller never has to write [vec_ntt] as an argument:
    a lemma argument mentioning it costs minutes of elaboration, whereas the
    same term inside a [pure] assertion is free. *)
let ntt_entry_step (k: pos) (i: nat { i < k })
                   (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      Seq.length vv == k * n /\ Seq.length w0 == k * n /\
      Seq.length w1 == k * n /\ Seq.length b == n /\
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) == Seq.index (vec_ntt #k (as_zqs vv)) t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == ntt (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S16.v (Seq.index w1 t) == Seq.index (vec_ntt #k (as_zqs vv)) t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = vec_ntt_at k (as_zqs vv) i;
    entry_step k i vv w0 w1 b (vec_ntt #k (as_zqs vv))

let ntt_entry_done (k: pos) (vv w: Seq.lseq zqt (k * n))
  : Lemma (requires
      Seq.length vv == k * n /\ Seq.length w == k * n /\
      (forall (t: nat). t < k * n ==>
         S16.v (Seq.index w t) == Seq.index (vec_ntt #k (as_zqs vv)) t))
    (ensures as_zqs w == vec_ntt #k (as_zqs vv))
  = as_zqs_intro w (vec_ntt #k (as_zqs vv))

(** The same three lemmas for the inverse transform. *)
let vec_intt_at (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_intt #k v) i == intt (vec_at #k v i))
  = vec_at_of_fun k (fun j -> intt (vec_at #k v j)) i

let intt_entry_step (k: pos) (i: nat { i < k })
                    (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) == Seq.index (vec_intt #k (as_zqs vv)) t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == intt (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S16.v (Seq.index w1 t) == Seq.index (vec_intt #k (as_zqs vv)) t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = vec_intt_at k (as_zqs vv) i;
    entry_step k i vv w0 w1 b (vec_intt #k (as_zqs vv))

let intt_entry_done (k: pos) (vv w: Seq.lseq zqt (k * n))
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         S16.v (Seq.index w t) == Seq.index (vec_intt #k (as_zqs vv)) t))
    (ensures as_zqs w == vec_intt #k (as_zqs vv))
  = as_zqs_intro w (vec_intt #k (as_zqs vv))

(** {2 The dot product} *)

(** The partial sum after [m] terms.  [dot] itself is the same [repeati] run
    to [k], so the two agree by definition once [m] is [k]. *)
let dot_acc (#k: pos) (u v: pvec k) (m: nat { m <= k }) : poly
  = Loops.repeati m
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

let dot_acc_zero (#k: pos) (u v: pvec k)
  : Lemma (dot_acc u v 0 == poly_zero)
  = Loops.repeati_zero #poly
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

let dot_acc_succ (#k: pos) (u v: pvec k) (m: nat { m < k })
  : Lemma (dot_acc u v (m + 1) ==
           poly_add (dot_acc u v m) (multiply_ntts (vec_at u m) (vec_at v m)))
  = Loops.unfold_repeati #poly m
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

let dot_acc_full (#k: pos) (u v: pvec k)
  : Lemma (dot_acc u v k == dot u v)
  = ()

(** One step of the accumulating loop, in the form the implementation leaves
    it in: [d] is the old accumulator, [c] the product just computed, and
    [w] the elementwise sum of the two. *)
let dot_step_done (#k: pos) (u v: pvec k) (m: nat { m < k })
                  (d c w: Seq.lseq zqt n)
  : Lemma (requires
      as_poly d == dot_acc u v m /\
      as_poly c == multiply_ntts (vec_at u m) (vec_at v m) /\
      (forall (t: nat). t < n ==>
         S16.v (Seq.index w t) == add (S16.v (Seq.index d t)) (S16.v (Seq.index c t))))
    (ensures as_poly w == dot_acc u v (m + 1))
  = dot_acc_succ u v m;
    as_poly_intro w (dot_acc u v (m + 1))
(** {2 The matrix-vector product} *)

(** A matrix row is a [k * n]-block of the flat matrix, so the view of the
    sub-array holding it is exactly that row. *)
let as_zqs_row (k: pos) (s: Seq.seq zqt { Seq.length s == k * (k * n) })
               (i: nat { i < k })
  : Lemma (requires Seq.length s == k * k * n)
          (ensures mat_row #k (as_zqs s) i ==
                   as_zqs (Seq.slice s (i * (k * n)) (i * (k * n) + k * n)))
  = as_zqs_flat_at k (k * n) s i

let mat_vec_mul_at (k: pos) (m: pmat k) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (mat_vec_mul #k m v) i == dot (mat_row #k m i) v)
  = vec_at_of_fun k (fun j -> dot (mat_row #k m j) v) i

let mv_entry_step (k: pos) (i: nat { i < k })
                  (vm: Seq.lseq zqt (k * k * n))
                  (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) ==
           Seq.index (mat_vec_mul #k (as_zqs vm) (as_zqs vv)) t) /\
      as_poly b == dot (mat_row #k (as_zqs vm) i) (as_zqs vv))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S16.v (Seq.index w1 t) ==
           Seq.index (mat_vec_mul #k (as_zqs vm) (as_zqs vv)) t))
  = mat_vec_mul_at k (as_zqs vm) (as_zqs vv) i;
    entry_step k i w0 w0 w1 b (mat_vec_mul #k (as_zqs vm) (as_zqs vv))

let mv_entry_done (k: pos) (vm: Seq.lseq zqt (k * k * n))
                  (vv w: Seq.lseq zqt (k * n))
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         S16.v (Seq.index w t) ==
           Seq.index (mat_vec_mul #k (as_zqs vm) (as_zqs vv)) t))
    (ensures as_zqs w == mat_vec_mul #k (as_zqs vm) (as_zqs vv))
  = as_zqs_intro w (mat_vec_mul #k (as_zqs vm) (as_zqs vv))

#pop-options
