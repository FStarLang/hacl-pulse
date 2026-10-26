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

(** Splitting a scalar into six pieces.

    {!Spec.Group.Split4} for a 384-bit scalar: six sixty-four-bit pieces,

    {[ k = k0 + k1 2^64 + k2 2^128 + k3 2^192 + k4 2^256 + k5 2^320 ]}

    walked together against six base points, sixteen rungs of four
    doublings and six additions.  [hi k i] is what the accumulator holds
    after [16 - i] rungs; it starts at zero, ends at [k], and one rung
    multiplies it by sixteen and adds six digits. *)
module Spec.Group.Split6

module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Digit [i] of the [j]-th piece. *)
let dig (k: nat) (j: nat) (i: nat) : n: nat { n < 16 } = (k / pow2 (64 * j + 4 * i)) % 16

(** The [j]-th piece, shifted right by [4 i]. *)
let part (k: nat) (j: nat) (i: nat { i <= 16 }) : nat =
  (k / pow2 (64 * j + 4 * i)) % pow2 (64 - 4 * i)

(** The six pieces, reassembled. *)
let hi (k: nat) (i: nat { i <= 16 }) : nat =
  part k 0 i + part k 1 i * pow2 64 + part k 2 i * pow2 128 +
  part k 3 i * pow2 192 + part k 4 i * pow2 256 + part k 5 i * pow2 320

(** The six digits at position [i], likewise. *)
let digs (k: nat) (i: nat) : nat =
  dig k 0 i + dig k 1 i * pow2 64 + dig k 2 i * pow2 128 +
  dig k 3 i * pow2 192 + dig k 4 i * pow2 256 + dig k 5 i * pow2 320

let part_top (k: nat) (j: nat) : Lemma (part k j 16 == 0) =
  assert_norm (pow2 (64 - 4 * 16) == 1)

let hi_top (k: nat) : Lemma (hi k 16 == 0) =
  part_top k 0; part_top k 1; part_top k 2;
  part_top k 3; part_top k 4; part_top k 5

(** One step: shifting right by four more bits peels off a digit. *)
let part_step (k: nat) (j: nat) (i: nat { i < 16 })
  : Lemma (part k j i == 16 * part k j (i + 1) + dig k j i)
  = let s = 64 * j + 4 * i in
    let m = 60 - 4 * i in
    let a = k / pow2 s in
    assert_norm (pow2 4 == 16);
    Math.pow2_plus s 4;
    Math.division_multiplication_lemma k (pow2 s) (pow2 4);
    assert (k / pow2 (s + 4) == a / 16);
    Math.pow2_plus 4 m;
    assert (pow2 (64 - 4 * i) == 16 * pow2 m);
    Math.modulo_division_lemma a 16 (pow2 m);
    Math.modulo_modulo_lemma a 16 (pow2 m);
    let r = a % pow2 (64 - 4 * i) in
    assert (part k j i == r);
    assert (part k j (i + 1) == (a / 16) % pow2 m);
    assert (dig k j i == a % 16);
    assert (r / 16 == (a / 16) % pow2 m);
    assert (r % 16 == a % 16);
    Math.euclidean_division_definition r 16

(** Expanding one weighted term. *)
let term (q d: nat) (w: pos)
  : Lemma ((16 * q + d) * w == 16 * (q * w) + d * w)
  = Math.distributivity_add_left (16 * q) d w;
    Math.paren_mul_right 16 q w

let regroup (p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5: int)
  : Lemma (requires p0 == 16 * q0 + d0 /\ p1 == 16 * q1 + d1 /\
                    p2 == 16 * q2 + d2 /\ p3 == 16 * q3 + d3 /\
                    p4 == 16 * q4 + d4 /\ p5 == 16 * q5 + d5)
          (ensures p0 + p1 + p2 + p3 + p4 + p5 ==
                   16 * (q0 + q1 + q2 + q3 + q4 + q5) +
                   (d0 + d1 + d2 + d3 + d4 + d5))
  = ()

let hi_step (k: nat) (i: nat { i < 16 })
  : Lemma (hi k i == 16 * hi k (i + 1) + digs k i)
  = part_step k 0 i; part_step k 1 i; part_step k 2 i;
    part_step k 3 i; part_step k 4 i; part_step k 5 i;
    term (part k 1 (i + 1)) (dig k 1 i) (pow2 64);
    term (part k 2 (i + 1)) (dig k 2 i) (pow2 128);
    term (part k 3 (i + 1)) (dig k 3 i) (pow2 192);
    term (part k 4 (i + 1)) (dig k 4 i) (pow2 256);
    term (part k 5 (i + 1)) (dig k 5 i) (pow2 320);
    regroup (part k 0 i) (part k 1 i * pow2 64) (part k 2 i * pow2 128)
            (part k 3 i * pow2 192) (part k 4 i * pow2 256) (part k 5 i * pow2 320)
            (part k 0 (i + 1)) (part k 1 (i + 1) * pow2 64)
            (part k 2 (i + 1) * pow2 128) (part k 3 (i + 1) * pow2 192)
            (part k 4 (i + 1) * pow2 256) (part k 5 (i + 1) * pow2 320)
            (dig k 0 i) (dig k 1 i * pow2 64) (dig k 2 i * pow2 128)
            (dig k 3 i * pow2 192) (dig k 4 i * pow2 256) (dig k 5 i * pow2 320)

(** And at the bottom it is the scalar itself.  Each piece extends the
    low part of [k] by sixty-four bits. *)
let low_step (k: nat) (j: nat)
  : Lemma (k % pow2 (64 * j + 64) ==
           k % pow2 (64 * j) + part k j 0 * pow2 (64 * j))
  = let b = pow2 (64 * j) in
    Math.pow2_plus (64 * j) 64;
    assert (part k j 0 == (k / b) % pow2 64);
    Math.modulo_division_lemma k b (pow2 64);
    Math.modulo_modulo_lemma k b (pow2 64);
    Math.euclidean_division_definition (k % (b * pow2 64)) b

let hi_bot (k: nat { k < pow2 384 }) : Lemma (hi k 0 == k) =
  assert_norm (pow2 0 == 1);
  low_step k 0; low_step k 1; low_step k 2;
  low_step k 3; low_step k 4; low_step k 5;
  Math.small_mod k (pow2 384)

#pop-options
