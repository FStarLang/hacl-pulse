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

(** Edwards25519 as a commutative group, and the bridge to the ladder.

    The third instance of {!Spec.Group.Smul}, after secp256k1 and P-256,
    and the first whose ladder is indexed by a byte string rather than by
    a number.  [Spec.Ed25519.point_mul] reads bit [i] with
    {!Spec.Curve25519.ith_bit}, which digs into byte [i / 8]; the abstract
    ladder reads it with [gbit], which divides by [2^i].  So this module
    needs one thing the other two did not: {!ith_bit_gbit}, saying the
    thirty-two bytes denote {!Hacl.Spec.Bytes.le_nat} of themselves.  It is
    an arithmetic fact about byte strings and mentions no curve, so it is
    cheap. *)
module Spec.Ed25519.Smul

module G = Spec.Group.Smul
module B = Hacl.Spec.Bytes
module C = Spec.Curve25519
module Loops = Hacl.Spec.Loops
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The instance.  Every field is a lemma from {!Spec.Ed25519.Group}; this
    record is the only place in the library where they are all named at
    once.  [point_equal] is a [bool] where the record wants a [prop], which
    the coercion handles. *)
let eg : G.grp ext_point = {
  ok = on_curve;
  eqv = (fun p q -> b2t (point_equal p q));
  zero = point_at_infinity;
  add = point_add;
  dbl = point_double;

  ok_zero = point_at_infinity_on_curve;
  ok_add = point_add_on_curve;
  ok_dbl = point_double_on_curve;

  eqv_refl = point_equal_refl;
  eqv_sym = point_equal_sym;
  eqv_trans = point_equal_trans;

  add_congr = point_add_congr;
  add_assoc = point_add_assoc_law;
  add_comm = point_add_comm_law;
  add_id = point_add_identity;
  dbl_is_add = point_double_is_add;
}

(** The multiple, specialized.  Stated as a definition of its own so that
    the implementation's loop invariant does not have to mention the
    record. *)
let smul (n: nat) (p: ext_point) : ext_point = G.smul eg n p

let smul_ok (n: nat) (p: ext_point)
  : Lemma (requires on_curve p) (ensures on_curve (smul n p))
  = G.smul_ok eg n p

let smul_zero (p: ext_point) : Lemma (smul 0 p == point_at_infinity)
  = assert_norm (G.smul eg 0 p == point_at_infinity)

let smul_one (p: ext_point)
  : Lemma (requires on_curve p) (ensures point_equal (smul 1 p) p)
  = G.smul_one eg p

let smul_congr (n: nat) (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal p q)
          (ensures point_equal (smul n p) (smul n q))
  = G.smul_congr eg n p q

(** The two shapes a rung of a window produces. *)
let smul_dbl_congr (n: nat) (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal q (smul n p))
          (ensures on_curve (point_double q) /\
                   point_equal (point_double q) (smul (2 * n) p))
  = G.smul_dbl_congr eg n p q

let smul_add_congr (m n: nat) (p q r: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r /\
                    point_equal q (smul m p) /\ point_equal r (smul n p))
          (ensures on_curve (point_add q r) /\
                   point_equal (point_add q r) (smul (m + n) p))
  = G.smul_add_congr eg m n p q r

let smul_succ_congr (n: nat) (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal q (smul n p))
          (ensures on_curve (point_add q p) /\
                   point_equal (point_add q p) (smul (n + 1) p))
  = G.smul_succ_congr eg n p q

#pop-options

(** {2 The bytes denote a number}

    [ith_bit k i] is bit [i % 8] of byte [i / 8]; [gbit n i] is bit [i] of
    [n].  They agree when [n] is the little-endian value of [k], and that
    is the only arithmetic this module does. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(** Splitting off the low [j] bytes: dividing by [2^(8j)] drops them. *)
let le_nat_shift (k: Seq.seq S8.t) (j: nat { j <= Seq.length k })
  : Lemma (B.le_nat k / pow2 (8 * j) ==
           B.le_nat (Seq.slice k j (Seq.length k)))
  = let n = Seq.length k in
    let lo = Seq.slice k 0 j in
    let hi = Seq.slice k j n in
    B.le_nat_split k j;
    B.le_nat_bound lo;
    Math.lemma_div_plus (B.le_nat lo) (B.le_nat hi) (pow2 (8 * j));
    Math.small_div (B.le_nat lo) (pow2 (8 * j))

let ith_bit_gbit (k: Seq.lseq S8.t 32) (i: nat { i < 256 })
  : Lemma (C.ith_bit k i == G.gbit (B.le_nat k) i)
  = let j = i / 8 in
    let r = i % 8 in
    let c = S8.v (Seq.index k j) in
    let t = B.le_nat (Seq.slice k (j + 1) 32) in
    Math.euclidean_division_definition i 8;
    le_nat_shift k j;
    B.le_nat_cons k j;
    assert (B.le_nat k / pow2 (8 * j) == c + 256 * t);
    (* [2^i = 2^(8j) * 2^r], so one division by [2^i] is two in sequence. *)
    Math.pow2_plus (8 * j) r;
    Math.division_multiplication_lemma (B.le_nat k) (pow2 (8 * j)) (pow2 r);
    (* [256 = 2^r * 2^(8-r)], so the higher bytes contribute an even
       multiple and vanish modulo two. *)
    Math.pow2_plus r (8 - r);
    Math.paren_mul_right (pow2 r) (pow2 (8 - r)) t;
    Math.lemma_div_plus c (pow2 (8 - r) * t) (pow2 r);
    Math.pow2_le_compat (8 - r) 1;
    Math.lemma_mod_plus (c / pow2 r) ((pow2 (8 - r) / 2) * t) 2;
    Math.pow2_plus 1 (8 - r - 1)

(** And the same fact one nibble at a time, which is what a four-bit
    window reads.  A nibble never straddles a byte, because four divides
    eight: at a bit offset [i] divisible by four the shift [i % 8] is
    either zero or four, and in both cases the bytes above contribute a
    multiple of sixteen. *)
let nibble_of_bytes (k: Seq.lseq S8.t 32) (i: nat { i < 256 /\ i % 4 == 0 })
  : Lemma (B.le_nat k / pow2 i % 16 ==
           S8.v (Seq.index k (i / 8)) / pow2 (i % 8) % 16)
  = let j = i / 8 in
    let r = i % 8 in
    let c = S8.v (Seq.index k j) in
    let t = B.le_nat (Seq.slice k (j + 1) 32) in
    Math.euclidean_division_definition i 8;
    le_nat_shift k j;
    B.le_nat_cons k j;
    assert (B.le_nat k / pow2 (8 * j) == c + 256 * t);
    Math.pow2_plus (8 * j) r;
    Math.division_multiplication_lemma (B.le_nat k) (pow2 (8 * j)) (pow2 r);
    Math.pow2_plus r (8 - r);
    Math.paren_mul_right (pow2 r) (pow2 (8 - r)) t;
    Math.lemma_div_plus c (pow2 (8 - r) * t) (pow2 r);
    (* [r] is 0 or 4, so [8 - r >= 4] and [2^(8-r)] is a multiple of 16. *)
    assert (r == 0 \/ r == 4);
    Math.pow2_le_compat (8 - r) 4;
    assert_norm (pow2 4 == 16);
    Math.lemma_mod_plus (c / pow2 r) ((pow2 (8 - r) / 16) * t) 16;
    Math.pow2_plus 4 (8 - r - 4)

#pop-options

(** {2 The ladder computes the multiple}

    [point_mul] is [repeati_g] over 256 steps of [point_mul_step], which is
    {!Spec.Group.Smul.ladder_step} at this instance once the bits are
    identified.  The statement mentions no equivalence, so it is cheap
    here; everything that is not cheap was done abstractly. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

let step_is_ladder (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat)
                   (acc: ext_point)
  : Lemma (point_mul_at k p i acc ==
           G.ladder_at eg 256 (B.le_nat k) p i acc)
  = if i < 256 then ith_bit_gbit k (255 - i)

let point_mul_is_ladder (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (point_mul k p ==
           Loops.repeati_g 256 (G.ladder_at eg 256 (B.le_nat k) p)
                           point_at_infinity)
  = Classical.forall_intro_2 (step_is_ladder k p);
    Loops.repeati_g_ext 256 (point_mul_at k p)
                        (G.ladder_at eg 256 (B.le_nat k) p)
                        point_at_infinity

let point_mul_is_smul (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures on_curve (point_mul k p) /\
                   point_equal (point_mul k p) (smul (B.le_nat k) p))
  = B.le_nat_bound k;
    point_mul_is_ladder k p;
    G.ladder_is_smul eg 256 (B.le_nat k) p

#pop-options

(** {2 What the callers need}

    The windowed implementation returns a point that is only *equivalent*
    to the one the specification names, so every consumer of a scalar
    multiple has to be shown blind to the difference.  There are three
    consumers: compression, which is handled by
    {!Spec.Ed25519.Group.point_compress_congr}; addition, handled by
    [point_add_congr]; and the equality test at the end of verification,
    handled here.  All three want [on_curve] of the specification's point
    as well as of the computed one, which is the first lemma below. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let point_mul_on_curve (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (requires on_curve p) (ensures on_curve (point_mul k p))
  = point_mul_is_smul k p

let point_mul_g_on_curve (k: Seq.lseq S8.t 32)
  : Lemma (on_curve (point_mul_g k))
  = g_on_curve (); point_mul_is_smul k g

(** The equality test does not distinguish equivalent points.  This is
    not an axiom: it is reflexivity, symmetry and transitivity used four
    times, once in each direction of each implication. *)
let point_equal_congr (p p' q q': ext_point)
  : Lemma (requires on_curve p /\ on_curve p' /\ on_curve q /\ on_curve q' /\
                    point_equal p p' /\ point_equal q q')
          (ensures point_equal p q == point_equal p' q')
  = let fwd () : Lemma (requires point_equal p q) (ensures point_equal p' q') =
      point_equal_sym p p';
      point_equal_trans p' p q;
      point_equal_trans p' q q'
    in
    let bwd () : Lemma (requires point_equal p' q') (ensures point_equal p q) =
      point_equal_trans p p' q';
      point_equal_sym q q';
      point_equal_trans p q' q
    in
    Classical.move_requires fwd (); Classical.move_requires bwd ()

#pop-options
