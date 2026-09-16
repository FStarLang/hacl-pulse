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

(** Matrices of secret 16-bit integers, which is all the arithmetic FrodoKEM
    has.  Everything is modulo [2^16]; the reduction to [logq] bits happens
    only where the specification asks for it, at packing and at the
    re-encryption check.

    A matrix is a flat sequence in row-major order, and the two dimensions
    are explicit arguments rather than type indices.  That is deliberate:
    every one of these operations is called from Pulse code that carries its
    dimensions as [SZ.t] run-time values, and an implicit that the unifier
    would have to recover from [Seq.lseq S16.t (r * c)] -- a product -- is an
    implicit it cannot recover.

    [mul_t] is the one operation that is not textbook.  FrodoKEM's secret
    matrix S is always stored transposed, so that both operands of the inner
    product are walked forwards; the reference implementation does this and
    so does HACL\*, which spells it as a second indexing function rather than
    as a second multiplication.  Naming the transposed multiply instead keeps
    the *layout* in the type: [mul_t r k c a bt] takes [bt] of shape [c * k]
    and means [a * transpose bt]. *)
module Spec.Frodo.Matrix

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops

let matrix (r c: nat) = Seq.lseq S16.t (r * c)

(** Row-major indexing is in bounds.  Nonlinear, therefore not automatic. *)
let index_bound (r c: nat) (i: nat { i < r }) (j: nat { j < c })
  : Lemma (i * c + j < r * c)
  = Math.lemma_mult_le_right c (i + 1) r;
    Math.distributivity_add_left i 1 c

let get (r c: nat) (m: matrix r c) (i: nat { i < r }) (j: nat { j < c }) : S16.t =
  index_bound r c i j;
  Seq.index m (i * c + j)

(** The same, total in [i] and [j], so that a [Loops.repeati] step function
    needs no refinement (the [Spec.Curve25519.ladder_at] trick). *)
let at (r c: nat) (m: matrix r c) (i j: nat) : S16.t =
  if i < r && j < c then get r c m i j else S16.zero

let upd (r c: nat) (m: matrix r c) (i: nat { i < r }) (j: nat { j < c }) (x: S16.t)
  : matrix r c
  = index_bound r c i j;
    Seq.upd m (i * c + j) x

let get_upd (r c: nat) (m: matrix r c) (i: nat { i < r }) (j: nat { j < c }) (x: S16.t)
            (i': nat { i' < r }) (j': nat { j' < c })
  : Lemma (get r c (upd r c m i j x) i' j' ==
             (if i = i' && j = j' then x else get r c m i' j'))
  = index_bound r c i j;
    index_bound r c i' j';
    if i = i' then Math.lemma_mod_plus_distr_l 0 0 1
    else if i < i' then Math.lemma_mult_le_right c (i + 1) i'
    else Math.lemma_mult_le_right c (i' + 1) i

let create (r c: nat) : matrix r c = Seq.create (r * c) S16.zero

(** [t < r * c] puts [t / c] below [r].  Division is monotone and the top
    quotient is [r - 1]; neither step is automatic with nonlinear arithmetic
    off. *)
let div_lt (t: nat) (r: nat) (c: pos) : Lemma (requires t < r * c) (ensures t / c < r) =
  Math.distributivity_sub_left r 1 c;
  Math.lemma_div_le t (r * c - 1) c;
  Math.lemma_div_plus (c - 1) (r - 1) c;
  Math.small_div (c - 1) c

(** Pointwise construction, which is how every matrix in this library is
    actually specified. *)
let init (r: nat) (c: pos) (f: (i: nat { i < r }) -> (j: nat { j < c }) -> S16.t)
  : matrix r c
  = Seq.init (r * c) (fun t -> div_lt t r c; f (t / c) (t % c))

let init_index (r: nat) (c: pos) (f: (i: nat { i < r }) -> (j: nat { j < c }) -> S16.t)
               (i: nat { i < r }) (j: nat { j < c })
  : Lemma (get r c (init r c f) i j == f i j)
          [SMTPat (get r c (init r c f) i j)]
  = index_bound r c i j;
    Math.lemma_div_plus j i c;
    Math.small_div j c;
    Math.lemma_mod_plus j i c;
    Math.small_mod j c

(** {2 Pointwise arithmetic} *)

let add (r: nat) (c: pos) (a b: matrix r c) : matrix r c =
  init r c (fun i j -> S16.add_mod (get r c a i j) (get r c b i j))

let sub (r: nat) (c: pos) (a b: matrix r c) : matrix r c =
  init r c (fun i j -> S16.sub_mod (get r c a i j) (get r c b i j))

(** Reduce every entry modulo [2^d].  Applied to the re-encrypted matrices
    in decapsulation, where the comparison is against values that came back
    through the packing and so carry only [logq] bits. *)
let mod_pow2 (r: nat) (c: pos) (d: U32.t { U32.v d <= 16 }) (m: matrix r c) : matrix r c =
  init r c (fun i j -> S16.logand (get r c m i j) (S16.mask_low d))

(** {2 Products}

    The accumulation order is the implementation's: start at zero and add
    [a.(i,l) * b.(l,j)] for [l] increasing, which is exactly [Loops.repeati]
    unfolding on the right. *)

let dot_step (r k c: nat) (a: matrix r k) (b: matrix k c) (i j: nat)
             (l: nat) (acc: S16.t) : S16.t
  = if l < k then S16.add_mod acc (S16.mul_mod (at r k a i l) (at k c b l j)) else acc

let dot (r k c: nat) (a: matrix r k) (b: matrix k c) (i j: nat) : S16.t =
  Loops.repeati k (dot_step r k c a b i j) S16.zero

let mul (r: nat) (k: nat) (c: pos) (a: matrix r k) (b: matrix k c) : matrix r c =
  init r c (fun i j -> dot r k c a b i j)

let dot_t_step (r k c: nat) (a: matrix r k) (bt: matrix c k) (i j: nat)
               (l: nat) (acc: S16.t) : S16.t
  = if l < k then S16.add_mod acc (S16.mul_mod (at r k a i l) (at c k bt j l)) else acc

let dot_t (r k c: nat) (a: matrix r k) (bt: matrix c k) (i j: nat) : S16.t =
  Loops.repeati k (dot_t_step r k c a bt i j) S16.zero

let mul_t (r: nat) (k: nat) (c: pos) (a: matrix r k) (bt: matrix c k) : matrix r c =
  init r c (fun i j -> dot_t r k c a bt i j)

(** {2 Serialization}

    Two little-endian bytes per entry, in row-major order.  This is how the
    secret matrix S travels inside the secret key, and it is the only place
    a matrix is written out without being packed. *)

let to_bytes (r: nat) (c: nat) (m: matrix r c) : Seq.lseq S8.t (2 * (r * c)) =
  Seq.init (2 * (r * c)) (fun t ->
    let x = Seq.index m (t / 2) in
    if t % 2 = 0 then S16.lo x else S16.hi x)

let from_bytes (r: nat) (c: nat) (b: Seq.lseq S8.t (2 * (r * c))) : matrix r c =
  Seq.init (r * c) (fun t -> S16.of_bytes_le (Seq.index b (2 * t)) (Seq.index b (2 * t + 1)))

let from_to_bytes (r: nat) (c: nat) (m: matrix r c)
  : Lemma (from_bytes r c (to_bytes r c m) == m)
  = Seq.lemma_eq_intro (from_bytes r c (to_bytes r c m)) m
