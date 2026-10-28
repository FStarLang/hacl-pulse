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

(** Four pieces, signed five-bit digits.

    {!Spec.Group.Split4} with Booth recoding.  This is
    {!Spec.Group.Booth6} for four pieces.  Each sixty-four-bit piece
    [a] of the scalar is written in thirteen signed digits

    {[ a = d_0 + 32 d_1 + ... + 32^12 d_12,   -16 <= d_i <= 16 ]}

    read off overlapping six-bit windows of [2a]: the window at [i] is
    [w = (2a / 32^i) mod 64], its top bit is the sign, and the magnitude is
    [(w + 1) / 2] or [32 - (w + 1) / 2].  A table of the sixteen multiples
    [1 .. 16] of a base point then covers every digit: zero is "add
    nothing", and a negative digit is the entry with [y] negated.

    [hb a i] is what is left of the piece above digit [i]: it starts at
    zero ([i = 13]), ends at [a], and one step multiplies by thirty-two and
    adds a signed digit.  [rv k i j] is the accumulator part-way through
    the rung at [i], after [j] of the four additions; every one of them is
    a natural number, so the window's invariant never needs a negative
    multiple. *)
module Spec.Group.Booth4

module Math = FStar.Math.Lemmas
module Split = Spec.Group.Split4

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The [j]-th sixty-four-bit piece of [k]. *)
let piece (k: nat) (j: nat) : n: nat { n < pow2 64 } = k / pow2 (64 * j) % pow2 64

(** The six-bit window of [2a] at digit [i]. *)
let win (a: nat) (i: nat) : n: nat { n < 64 } = (2 * a / pow2 (5 * i)) % 64

(** Its sign, one for a negative digit. *)
let sgn (a: nat) (i: nat) : n: nat { n < 2 } = win a i / 32

let half (a: nat) (i: nat) : n: nat { n <= 32 } = (win a i + 1) / 2

(** And its magnitude. *)
let mag (a: nat) (i: nat) : n: nat { n <= 16 } =
  if sgn a i = 0 then half a i else 32 - half a i

(** The piece above digit [i], rounded to nearest. *)
let hb (a: nat) (i: nat) : nat = (2 * a / pow2 (5 * i) + 1) / 2

let window_split (x: nat)
  : Lemma (x == 64 * (x / 64) + x % 64 /\ x / 32 == 2 * (x / 64) + x % 64 / 32)
  = Math.euclidean_division_definition x 64;
    Math.division_addition_lemma (x % 64) 32 (2 * (x / 64))

let shift5 (x: nat) (i: nat)
  : Lemma (x / pow2 (5 * (i + 1)) == x / pow2 (5 * i) / 32)
  = assert_norm (pow2 5 == 32);
    Math.pow2_plus (5 * i) 5;
    Math.division_multiplication_lemma x (pow2 (5 * i)) 32

let half_step (q r t: nat)
  : Lemma (requires r < 64 /\ t == r / 32)
          (ensures (64 * q + r + 1) / 2 == 32 * q + (r + 1) / 2 /\
                   (2 * q + t + 1) / 2 == q + t)
  = ()

(** One digit. *)
let hb_step (a: nat) (i: nat)
  : Lemma (if sgn a i = 0 then hb a i == 32 * hb a (i + 1) + mag a i
           else hb a i + mag a i == 32 * hb a (i + 1))
  = let x = 2 * a / pow2 (5 * i) in
    shift5 (2 * a) i;
    window_split x;
    half_step (x / 64) (x % 64) (x % 64 / 32)

let hb_bot (a: nat) : Lemma (hb a 0 == a) = assert_norm (pow2 0 == 1)

let hb_top (a: nat) : Lemma (requires a < pow2 64) (ensures hb a 13 == 0)
  = assert_norm (pow2 65 == 2 * pow2 64);
    Math.small_div (2 * a) (pow2 65)

(** {2 Four pieces} *)

(** The [jj]-th piece's share of the accumulator at digit [i]. *)
[@@"opaque_to_smt"]
let hw (k: nat) (i: nat) (jj: nat) : nat = hb (piece k jj) i * pow2 (64 * jj)

let h (k: nat) (i: nat) : nat =
  hw k i 0 + hw k i 1 + hw k i 2 + hw k i 3

(** One weighted term of the accumulator part-way through a rung: pieces
    below [j] have taken their digit, the rest have only been doubled. *)
let tm (k: nat) (i: nat) (j: nat) (jj: nat) : nat =
  if jj < j then hw k i jj else 32 * hw k (i + 1) jj

let rv (k: nat) (i: nat) (j: nat) : nat =
  tm k i j 0 + tm k i j 1 + tm k i j 2 + tm k i j 3

let hw_top (k: nat) (jj: nat) : Lemma (hw k 13 jj == 0)
  = reveal_opaque (`%hw) hw; hb_top (piece k jj)

let h_top (k: nat) : Lemma (h k 13 == 0)
  = hw_top k 0; hw_top k 1; hw_top k 2; hw_top k 3

let hw_bot (k: nat) (jj: nat)
  : Lemma (hw k 0 jj == Split.part k jj 0 * pow2 (64 * jj))
  = reveal_opaque (`%hw) hw; hb_bot (piece k jj)

let h_bot (k: nat) : Lemma (requires k < pow2 256) (ensures h k 0 == k)
  = hw_bot k 0; hw_bot k 1; hw_bot k 2; hw_bot k 3;
    assert_norm (pow2 (64 * 0) == 1);
    assert_norm (64 * 1 == 64); assert_norm (64 * 2 == 128);
    assert_norm (64 * 3 == 192);
    Split.hi_bot k

(** A rung starts at thirty-two times the last [h]... *)
let rv_start (k: nat) (i: nat) : Lemma (rv k i 0 == 32 * h k (i + 1)) = ()

(** ... and ends at the next. *)
let rv_end (k: nat) (i: nat) : Lemma (rv k i 4 == h k i) = ()

let weigh (x y m w: nat)
  : Lemma ((x == 32 * y + m ==> x * w == 32 * (y * w) + m * w) /\
           (x + m == 32 * y ==> x * w + m * w == 32 * (y * w)))
  = Math.distributivity_add_left x m w;
    Math.distributivity_add_left (32 * y) m w;
    Math.paren_mul_right 32 y w

let hw_step (k: nat) (i: nat) (j: nat)
  : Lemma (let m = mag (piece k j) i * pow2 (64 * j) in
           if sgn (piece k j) i = 0 then hw k i j == 32 * hw k (i + 1) j + m
           else hw k i j + m == 32 * hw k (i + 1) j)
  = reveal_opaque (`%hw) hw;
    let a = piece k j in
    hb_step a i;
    weigh (hb a i) (hb a (i + 1)) (mag a i) (pow2 (64 * j))

(** One addition: a positive digit adds [m 2^{64 j}], a negative one is
    what the next value plus [m 2^{64 j}] makes. *)
let rv_step (k: nat) (i: nat) (j: nat { j < 4 })
  : Lemma (if sgn (piece k j) i = 0
           then rv k i (j + 1) == rv k i j + mag (piece k j) i * pow2 (64 * j)
           else rv k i j == rv k i (j + 1) + mag (piece k j) i * pow2 (64 * j))
  = hw_step k i j;
    match j with
    | 0 -> () | 1 -> () | 2 -> () | 3 -> ()

(** Every partial sum is a natural number, and so is the multiple it adds. *)
let mag_nat (k: nat) (i: nat) (j: nat)
  : Lemma (mag (piece k j) i * pow2 (64 * j) >= 0)
  = Math.nat_times_nat_is_nat (mag (piece k j) i) (pow2 (64 * j))

#pop-options
