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

(** The word operations of the sixty-four-bit limb, and the view that turns
    an array of them into a number.

    A limb is a {!Hacl.Secret.UInt64}; a limb operation computes in a
    {!Hacl.Secret.UInt128} and then splits.  Each function below is the
    machine instruction plus the fact that it did not wrap, so that the
    modular-arithmetic side condition is discharged once here against a
    two-line context instead of inside a loop body that also carries the
    heap.

    {b Why sixty-four bits.}  The product of two limbs plus two more limbs
    is at most [(2^64-1)^2 + 2*(2^64-1) = 2^128 - 1], so the schoolbook
    inner step is exact in a [uint128] with not one bit to spare -- the same
    argument that made thirty-two the right radix when the widest machine
    integer was sixty-four, moved up one notch now that Custard compiles
    {!Hacl.Secret.UInt128} to [unsigned __int128].  The radix is the word
    size, which is the point: a 2048-bit modulus is 32 limbs rather than 64,
    and a schoolbook multiply does a quarter as many limb multiplications.

    See {!Spec.Bignum} for the meaning of a limb sequence. *)
module Hacl.Impl.Limb64

open Spec.Bignum

module Seq = FStar.Seq
module U32 = FStar.UInt32
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 Viewing an array of secrets as a number}

    [vals] is the only bridge between the code and {!Spec.Bignum}: an array
    of [n] limbs denotes [eval (vals v)].  The result is normal by
    construction, which is why {!Spec.Bignum.norm} never has to be carried
    in a precondition. *)

let vals (v: Seq.seq S64.t)
  : GTot (s: Seq.seq nat { Seq.length s == Seq.length v /\ norm s /\
                           (forall (i: nat). i < Seq.length v ==>
                              Seq.index s i == S64.v (Seq.index v i)) })
  = Seq.init_ghost (Seq.length v) (fun i -> (S64.v (Seq.index v i) <: nat))

let vals_upd (v: Seq.seq S64.t) (k: nat { k < Seq.length v }) (x: S64.t)
  : Lemma (vals (Seq.upd v k x) == Seq.upd (vals v) k (S64.v x))
  = Seq.lemma_eq_intro (vals (Seq.upd v k x)) (Seq.upd (vals v) k (S64.v x))

let vals_slice (v: Seq.seq S64.t) (i: nat) (j: nat { i <= j /\ j <= Seq.length v })
  : Lemma (vals (Seq.slice v i j) == Seq.slice (vals v) i j)
  = Seq.lemma_eq_intro (vals (Seq.slice v i j)) (Seq.slice (vals v) i j)

let vals_eq (u v: Seq.seq S64.t)
  : Lemma (requires Seq.length u == Seq.length v /\ vals u == vals v)
          (ensures Seq.equal u v)
  = assert (forall (i: nat). i < Seq.length u ==>
              S64.v (Seq.index u i) == S64.v (Seq.index v i));
    Seq.lemma_eq_intro u v

(** {2 Widening and splitting} *)

inline_for_extraction
let widen (x: S64.t) : r: S128.t { S128.v r == S64.v x } = Cast.u64_to_u128 x

(** The low half of a double word, which is the limb a step writes. *)
inline_for_extraction
let lo (x: S128.t) : r: S64.t { S64.v r == S128.v x % base } = Cast.u128_to_u64 x

(** The high half, which is the carry a step passes on.  It is a limb
    because the double word is one. *)
inline_for_extraction
let hi (x: S128.t) : r: S64.t { S64.v r == S128.v x / base } =
  Math.lemma_div_lt (S128.v x) 128 64;
  Math.small_mod (S128.v x / base) base;
  Cast.u128_to_u64 (S128.shift_right x 64ul)

(** Splitting is exact: nothing is lost between [lo] and [hi]. *)
let lo_hi (x: S128.t) : Lemma (S128.v x == S64.v (lo x) + base * S64.v (hi x)) =
  Math.euclidean_division_definition (S128.v x) base

(** {2 The two inner steps}

    Both bounds below are tight, and both are the reason the radix is 2^64.
    A multiply-accumulate is at most [(2^64-1)^2 + 2*(2^64-1) = 2^128 - 1];
    borrowing costs one more bit than the operands have, which is why the
    subtraction step is stated with the [base] already added in. *)

(** [mac x y a b == x * y + a + b], exactly, in one double word. *)
inline_for_extraction
let mac (x y a b: S64.t) : r: S128.t { S128.v r == S64.v x * S64.v y + S64.v a + S64.v b } =
  assert_norm ((base - 1) * (base - 1) + (base - 1) + (base - 1) < pow2 128);
  Math.lemma_mult_le_left (S64.v x) (S64.v y) (base - 1);
  Math.lemma_mult_le_right (base - 1) (S64.v x) (base - 1);
  Math.small_mod (S64.v x * S64.v y + S64.v a) (pow2 128);
  Math.small_mod (S64.v x * S64.v y + S64.v a + S64.v b) (pow2 128);
  S128.add_mod (S128.add_mod (S128.mul_wide x y) (widen a)) (widen b)

(** [sum x y c == x + y + c], exactly. *)
inline_for_extraction
let sum (x y c: S64.t) : r: S128.t { S128.v r == S64.v x + S64.v y + S64.v c } =
  assert_norm ((base - 1) + (base - 1) + (base - 1) < pow2 128);
  Math.small_mod (S64.v x + S64.v y) (pow2 128);
  Math.small_mod (S64.v x + S64.v y + S64.v c) (pow2 128);
  S128.add_mod (S128.add_mod (widen x) (widen y)) (widen c)

(** [diff x y c == base + x - y - c], which is a natural number because [y]
    and [c] are both limbs and [c] is a bit.  The [base] is the borrow the
    step takes in advance: the caller reads it back as [1 - hi (diff ...)],
    and [lo (diff ...)] is the limb either way. *)
inline_for_extraction
let diff (x y c: S64.t)
  : Pure S128.t (requires S64.v c <= 1)
                (ensures fun r -> S128.v r == base + S64.v x - S64.v y - S64.v c)
  = assert_norm (base + (base - 1) < pow2 128);
    assert_norm (pow2 64 == base);
    let b = S128.pow2_64 in
    Math.small_mod (base + S64.v x) (pow2 128);
    Math.small_mod (base + S64.v x - S64.v y) (pow2 128);
    Math.small_mod (base + S64.v x - S64.v y - S64.v c) (pow2 128);
    S128.sub_mod (S128.sub_mod (S128.add_mod b (widen x)) (widen y)) (widen c)

(** The complement of a bit, as a limb: [1 - h]. *)
inline_for_extraction
let flip (h: S64.t)
  : Pure S64.t (requires S64.v h <= 1) (ensures fun r -> S64.v r == 1 - S64.v h)
  = Math.small_mod (1 - S64.v h) (pow2 64);
    S64.sub_mod (S64.classify 1uL) h

(** A borrow out is the complement of the high half, and it is a bit. *)
let diff_borrow (x y c: S64.t)
  : Lemma (requires S64.v c <= 1)
          (ensures S64.v (hi (diff x y c)) <= 1 /\
                   S64.v (lo (diff x y c)) ==
                     base * (1 - S64.v (hi (diff x y c))) + S64.v x - S64.v y - S64.v c)
  = let d = diff x y c in
    lo_hi d;
    Math.lemma_div_le (S128.v d) (2 * base - 1) base;
    Math.small_div (base - 1) base

#pop-options
