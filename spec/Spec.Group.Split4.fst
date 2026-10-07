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

(** Splitting a scalar into four pieces.

    A fixed-base window multiplies a known point [P] by preprocessing it:
    the scalar splits into four sixty-four-bit pieces,

    {[ k = k0 + k1 2^64 + k2 2^128 + k3 2^192 ]}

    so that [k P] is [k0 P + k1 (2^64 P) + k2 (2^128 P) + k3 (2^192 P)],
    and the four pieces can be walked together against four base points
    with one doubling chain between them.  Sixteen rungs of four
    doublings suffice where a variable-base window needs sixty-four.

    What the accumulator holds after [16 - i] rungs is [hi k i]: the four
    pieces, each shifted right by [4 i], each weighted by its base
    point's power of two.  Three facts are wanted -- it starts at zero,
    it ends at [k], and one rung multiplies by sixteen and adds four
    digits -- and all three are arithmetic about natural numbers.  No
    curve appears in this module, and none of it is specific to a group;
    Ed25519 and secp256k1 both use it. *)
module Spec.Group.Split4

module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Digit [i] of the [j]-th piece. *)
let dig (k: nat) (j: nat) (i: nat) : n: nat { n < 16 } = (k / pow2 (64 * j + 4 * i)) % 16

(** The [j]-th piece, shifted right by [4 i]. *)
let part (k: nat) (j: nat) (i: nat { i <= 16 }) : nat =
  (k / pow2 (64 * j + 4 * i)) % pow2 (64 - 4 * i)

(** The four pieces, reassembled. *)
let hi (k: nat) (i: nat { i <= 16 }) : nat =
  part k 0 i + part k 1 i * pow2 64 + part k 2 i * pow2 128 + part k 3 i * pow2 192

(** The four digits at position [i], likewise. *)
let digs (k: nat) (i: nat) : nat =
  dig k 0 i + dig k 1 i * pow2 64 + dig k 2 i * pow2 128 + dig k 3 i * pow2 192

let part_top (k: nat) (j: nat) : Lemma (part k j 16 == 0) =
  assert_norm (pow2 (64 - 4 * 16) == 1)

let hi_top (k: nat) : Lemma (hi k 16 == 0) =
  part_top k 0; part_top k 1; part_top k 2; part_top k 3

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
    Math.euclidean_division_definition (a % pow2 (64 - 4 * i)) 16

(** Expanding one of the four terms.  Spelt out because the goal below is
    a sum of four products of a variable by a power of two, and left to
    itself the solver does not find the regrouping. *)
let term (q d: nat) (w: pos)
  : Lemma ((16 * q + d) * w == 16 * (q * w) + d * w)
  = Math.distributivity_add_left (16 * q) d w;
    Math.paren_mul_right 16 q w

let hi_step (k: nat) (i: nat { i < 16 })
  : Lemma (hi k i == 16 * hi k (i + 1) + digs k i)
  = part_step k 0 i; part_step k 1 i; part_step k 2 i; part_step k 3 i;
    term (part k 1 (i + 1)) (dig k 1 i) (pow2 64);
    term (part k 2 (i + 1)) (dig k 2 i) (pow2 128);
    term (part k 3 (i + 1)) (dig k 3 i) (pow2 192)

(** And at the bottom it is the scalar itself. *)
let split64 (k: nat) (j: nat)
  : Lemma (k / pow2 (64 * j) ==
           (k / pow2 (64 * j)) % pow2 64 + pow2 64 * (k / pow2 (64 * j + 64)))
  = Math.pow2_plus (64 * j) 64;
    Math.division_multiplication_lemma k (pow2 (64 * j)) (pow2 64);
    Math.euclidean_division_definition (k / pow2 (64 * j)) (pow2 64)

(** Three nested splits flattened into four weighted digits.  Stated on its
    own because it is a cubic identity in [w], and the solver will not find
    the regrouping in a context that also carries the divisions it came
    from. *)
let horner4 (a0 a1 a2 a3 k k1 k2 w: nat)
  : Lemma (requires k == a0 + w * k1 /\ k1 == a1 + w * k2 /\ k2 == a2 + w * a3)
          (ensures k == a0 + a1 * w + a2 * (w * w) + a3 * (w * w * w))
  = Math.distributivity_add_right w a2 (w * a3);
    Math.distributivity_add_right w a1 (w * a2 + w * (w * a3));
    Math.paren_mul_right w w a3;
    Math.paren_mul_right w w (w * a3)

let hi_bot (k: nat { k < pow2 256 }) : Lemma (hi k 0 == k) =
  assert_norm (pow2 0 == 1);
  split64 k 0; split64 k 1; split64 k 2; split64 k 3;
  Math.pow2_plus 192 64;
  Math.small_div k (pow2 256);
  Math.small_mod (k / pow2 192) (pow2 64);
  assert (part k 0 0 == k % pow2 64);
  assert (part k 1 0 == (k / pow2 64) % pow2 64);
  assert (part k 2 0 == (k / pow2 128) % pow2 64);
  assert (part k 3 0 == k / pow2 192);
  horner4 (part k 0 0) (part k 1 0) (part k 2 0) (part k 3 0)
          k (k / pow2 64) (k / pow2 128) (pow2 64);
  Math.pow2_plus 64 64;
  Math.pow2_plus 128 64

#pop-options
