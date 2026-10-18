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

(** The products of {!Spec.Frodo.Matrix}, read as integer sums.

    [Spec.Frodo.Matrix.dot] accumulates modulo [2^16] one term at a time.
    Reducing at every step or once at the end gives the same residue, so an
    entry of [mul a b] is [isum k (mterm a b i j) % 2^16], where [isum] is a
    plain sum over [int] and [mterm a b i j l = a.(i,l) * b.(l,j)]; likewise
    for the transposed product [mul_t] ([mul_t_get]).  Over [int] the matrix
    identities FrodoKEM's correctness needs -- distributivity and the
    associativity [(S' A) S = S' (A S)] -- are just facts about finite sums:
    linearity and exchanging the order of a double sum.  And since every
    modulus the specification reduces by, [2^logq], divides [2^16], all of
    it survives reduction ([mod_pow2_16]).

    As in {!Spec.MLKEM.NTT.Lemmas}, the sum lemmas take their summands as
    named functions and relate them by pointwise hypotheses, so that no
    caller ever has to equate two lambdas. *)
module Spec.Frodo.Matrix.Lemmas

module Seq = FStar.Seq
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module M = Spec.Frodo.Matrix

(** {2 Finite sums over [int]} *)

let rec isum (m: nat) (f: nat -> GTot int) : GTot int (decreases m) =
  if m = 0 then 0 else isum (m - 1) f + f (m - 1)

#push-options "--fuel 1 --ifuel 0"

let rec sum_ext (m: nat) (f g: nat -> GTot int)
  : Lemma (requires forall (i: nat). i < m ==> f i == g i)
          (ensures isum m f == isum m g) (decreases m)
  = if m > 0 then sum_ext (m - 1) f g

let rec sum_zero (m: nat) (f: nat -> GTot int)
  : Lemma (requires forall (i: nat). i < m ==> f i == 0)
          (ensures isum m f == 0) (decreases m)
  = if m > 0 then sum_zero (m - 1) f

let rec sum_add (m: nat) (f g h: nat -> GTot int)
  : Lemma (requires forall (i: nat). i < m ==> h i == f i + g i)
          (ensures isum m h == isum m f + isum m g) (decreases m)
  = if m > 0 then sum_add (m - 1) f g h

let rec sum_scale (m: nat) (c: int) (f h: nat -> GTot int)
  : Lemma (requires forall (i: nat). i < m ==> h i == f i * c)
          (ensures isum m h == isum m f * c) (decreases m)
  = if m > 0 then begin
      sum_scale (m - 1) c f h;
      Math.distributivity_add_left (isum (m - 1) f) (f (m - 1)) c
    end

(** Sums of termwise congruent summands are congruent. *)
let rec sum_mod (m: nat) (q: pos) (f g: nat -> GTot int)
  : Lemma (requires forall (i: nat). i < m ==> f i % q == g i % q)
          (ensures isum m f % q == isum m g % q) (decreases m)
  = if m > 0 then begin
      sum_mod (m - 1) q f g;
      Math.modulo_distributivity (isum (m - 1) f) (f (m - 1)) q;
      Math.modulo_distributivity (isum (m - 1) g) (g (m - 1)) q
    end

let rec sum_swap_l (m1 m2: nat) (f: nat -> nat -> GTot int)
  : Lemma (ensures isum m1 (fun x -> isum m2 (f x)) ==
                   isum m2 (fun y -> isum m1 (fun x -> f x y)))
          (decreases m1)
  = if m1 = 0 then sum_zero m2 (fun y -> isum m1 (fun x -> f x y))
    else begin
      sum_swap_l (m1 - 1) m2 f;
      sum_add m2 (fun y -> isum (m1 - 1) (fun x -> f x y)) (f (m1 - 1))
                 (fun y -> isum m1 (fun x -> f x y))
    end

#pop-options

#push-options "--fuel 0 --ifuel 0"

(** Exchanging the order of a double sum, with the flipped summand [ft]
    and both inner sums given names. *)
let sum_swap (m1 m2: nat) (f ft: nat -> nat -> GTot int) (g h: nat -> GTot int)
  : Lemma (requires (forall (x y: nat). ft y x == f x y) /\
                    (forall (x: nat). g x == isum m2 (f x)) /\
                    (forall (y: nat). h y == isum m1 (ft y)))
          (ensures isum m1 g == isum m2 h)
  = sum_ext m1 g (fun x -> isum m2 (f x));
    sum_swap_l m1 m2 f;
    introduce forall (y: nat). isum m1 (fun x -> f x y) == h y
    with sum_ext m1 (fun x -> f x y) (ft y);
    sum_ext m2 (fun y -> isum m1 (fun x -> f x y)) h

(** {2 Entries} *)

(** The value of an entry, total in the indices like {!Spec.Frodo.Matrix.at}. *)
let vat (r c: nat) (m: M.matrix r c) (i j: nat) : GTot nat = S16.v (M.at r c m i j)

let mterm (r k c: nat) (a: M.matrix r k) (b: M.matrix k c) (i j: nat) (l: nat) : GTot int =
  vat r k a i l * vat k c b l j

let tterm (r k c: nat) (a: M.matrix r k) (bt: M.matrix c k) (i j: nat) (l: nat) : GTot int =
  vat r k a i l * vat c k bt j l

let vat_get (r c: nat) (m: M.matrix r c) (i: nat { i < r }) (j: nat { j < c })
  : Lemma (vat r c m i j == S16.v (M.get r c m i j))
  = ()

(** One more addition modulo [2^16] of a product reduced modulo [2^16]. *)
let step_mod (s x: int) (acc: S16.t) (y: S16.t)
  : Lemma (requires S16.v acc == s % pow2 16 /\ S16.v y == x % pow2 16)
          (ensures S16.v (S16.add_mod acc y) == (s + x) % pow2 16)
  = Math.lemma_mod_plus_distr_l s (x % pow2 16) (pow2 16);
    Math.lemma_mod_plus_distr_r s x (pow2 16)

#push-options "--fuel 1"

let rec dot_acc (r k c: nat) (a: M.matrix r k) (b: M.matrix k c) (i j: nat)
                (m: nat { m <= k })
  : Lemma (ensures S16.v (Loops.repeati m (M.dot_step r k c a b i j) S16.zero) ==
                   isum m (mterm r k c a b i j) % pow2 16)
          (decreases m)
  = if m > 0 then begin
      dot_acc r k c a b i j (m - 1);
      Loops.unfold_repeati (m - 1) (M.dot_step r k c a b i j) S16.zero;
      step_mod (isum (m - 1) (mterm r k c a b i j)) (mterm r k c a b i j (m - 1))
        (Loops.repeati (m - 1) (M.dot_step r k c a b i j) S16.zero)
        (S16.mul_mod (M.at r k a i (m - 1)) (M.at k c b (m - 1) j))
    end

let rec dot_t_acc (r k c: nat) (a: M.matrix r k) (bt: M.matrix c k) (i j: nat)
                  (m: nat { m <= k })
  : Lemma (ensures S16.v (Loops.repeati m (M.dot_t_step r k c a bt i j) S16.zero) ==
                   isum m (tterm r k c a bt i j) % pow2 16)
          (decreases m)
  = if m > 0 then begin
      dot_t_acc r k c a bt i j (m - 1);
      Loops.unfold_repeati (m - 1) (M.dot_t_step r k c a bt i j) S16.zero;
      step_mod (isum (m - 1) (tterm r k c a bt i j)) (tterm r k c a bt i j (m - 1))
        (Loops.repeati (m - 1) (M.dot_t_step r k c a bt i j) S16.zero)
        (S16.mul_mod (M.at r k a i (m - 1)) (M.at c k bt j (m - 1)))
    end

#pop-options

(** {2 The products as sums} *)

let mul_get (r k: nat) (c: pos) (a: M.matrix r k) (b: M.matrix k c)
            (i: nat { i < r }) (j: nat { j < c })
  : Lemma (S16.v (M.get r c (M.mul r k c a b) i j) == isum k (mterm r k c a b i j) % pow2 16)
  = dot_acc r k c a b i j k

let mul_t_get (r k: nat) (c: pos) (a: M.matrix r k) (bt: M.matrix c k)
              (i: nat { i < r }) (j: nat { j < c })
  : Lemma (S16.v (M.get r c (M.mul_t r k c a bt) i j) == isum k (tterm r k c a bt i j) % pow2 16)
  = dot_t_acc r k c a bt i j k

let add_get (r: nat) (c: pos) (a b: M.matrix r c) (i: nat { i < r }) (j: nat { j < c })
  : Lemma (S16.v (M.get r c (M.add r c a b) i j) ==
           (S16.v (M.get r c a i j) + S16.v (M.get r c b i j)) % pow2 16)
  = ()

let sub_get (r: nat) (c: pos) (a b: M.matrix r c) (i: nat { i < r }) (j: nat { j < c })
  : Lemma (S16.v (M.get r c (M.sub r c a b) i j) ==
           (S16.v (M.get r c a i j) - S16.v (M.get r c b i j)) % pow2 16)
  = ()

(** Reducing modulo [2^16] first changes nothing modulo [2^d]. *)
let mod_pow2_16 (x: int) (d: nat { d <= 16 })
  : Lemma ((x % pow2 16) % pow2 d == x % pow2 d)
  = Math.pow2_modulo_modulo_lemma_1 x d 16

#pop-options
