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

(** GF(2^8) and the AES S-box, on secret bytes.

    {2 Why there is no table}

    The obvious implementation of [Spec.AES.sbox] is the 256-entry table, and
    it is the reason AES has a twenty-year history of cache-timing attacks: a
    lookup at a secret index leaks the index through the cache.  A secret here
    is a [Hacl.Secret.UInt8.t], and the only operations that type offers are
    the ones whose cost does not depend on the value, so the table is not even
    expressible.

    What is expressible is the {i definition}: the S-box is inversion in
    GF(2^8) followed by an affine map, and [Spec.AES.sbox_is_algebraic] proves
    the table agrees.  So [sbox] here computes [affine (ginv x)] with field
    operations, in constant time.

    Inversion is [x^254], and the specification's [fexp] -- ordinary binary
    exponentiation -- already {i is} an addition chain: 254, 127, 63, 31, 15,
    7, 3, 1, 0.  Unfolding it gives eight squarings and seven multiplications,
    which is what [ginv] below is, written out.  The implementation therefore
    needs no exponent algebra at all: it is the specification with the fuel
    turned up.

    {2 The cost}

    Fifteen field multiplications of eight masked steps each, per byte, per
    round.  That is a few thousand operations per byte of message, so this is
    one or two megabytes a second: correct, portable and constant-time, but
    nothing like the throughput of an AES-NI or a bitsliced implementation.
    The library has no assembly by design (see [design/changes.md]), so the
    upgrade path is bitslicing -- representing the sixteen state bytes as
    eight machine words of bit planes and running the same field arithmetic on
    all of them at once, which is a sixteen-fold speedup for the same
    algorithm.  That is a self-contained change behind this interface. *)
module Hacl.AES.Core

open Spec.Byte
open Spec.AES

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Addition} *)

inline_for_extraction
let bxor (x y: S8.t) : r: S8.t { S8.v r == S8.v x ^^ S8.v y } =
  xor_is_logxor (S8.v x) (S8.v y);
  S8.logxor x y

(** {2 Multiplication by [x]}

    The branch of [Spec.AES.xtime] is on the top bit of a secret, so it
    becomes a mask: the shift is done unconditionally and the reduction
    polynomial is added under a mask that is all ones exactly when the shift
    left the field. *)

#push-options "--ifuel 1"
inline_for_extraction
let xtime_impl (a: S8.t) : r: S8.t { S8.v r == xtime (S8.v a) } =
  assert_norm (pow2 7 == 128);
  let s = S8.shift_left a 1ul in
  let m = S8.eq_mask (S8.shift_right a 7ul) (S8.classify 1uy) in
  S8.select m (bxor s (S8.classify 0x1buy)) s
#pop-options

(** {2 Multiplication}

    [Spec.AES.fmul_aux] recurses eight times, doubling [a] and halving [b]; at
    each step bit zero of the current [b] decides whether the current [a] is
    added.  Both the doubling and the halving are unrolled here, so the
    recursion becomes a straight line and [b]'s bits are read directly.  The
    decision is again a mask. *)

(** All ones exactly when bit [i] of [b] is set. *)
inline_for_extraction
let bit_mask (b: S8.t) (i: U32.t { U32.v i < 8 })
  : r: S8.t { S8.v r == (if (S8.v b / pow2 (U32.v i)) % 2 = 1 then pow2 8 - 1 else 0) }
  = let bi = S8.shift_right b i in
    UInt.logand_mask #8 (S8.v bi) 1;
    assert_norm (pow2 1 - 1 == 1);
    S8.eq_mask (S8.logand bi (S8.classify 1uy)) (S8.classify 1uy)

inline_for_extraction
let fmul_step (a b acc: S8.t) (i: U32.t { U32.v i < 8 })
  : r: S8.t { S8.v r == (if (S8.v b / pow2 (U32.v i)) % 2 = 1
                         then S8.v a ^^ S8.v acc else S8.v acc) }
  = let m = bit_mask b i in
    S8.select m (bxor a acc) acc

(** Halving [b] once is dividing by one more power of two. *)
let div_pow2_step (x: nat) (k: nat) : Lemma ((x / pow2 k) / 2 == x / pow2 (k + 1)) =
  Math.pow2_plus k 1;
  Math.division_multiplication_lemma x (pow2 k) 2

#push-options "--fuel 1 --ifuel 1"
let fmul_aux_zero (a b: elem) : Lemma (fmul_aux a b 0 == 0) = ()
#pop-options

(** One step of [Spec.AES.fmul_aux], with the halving of [b] rewritten as a
    division by one more power of two.  Stating it at the level of numbers,
    away from the implementation, keeps its proof context to three hypotheses
    -- the same obligation inside [fmul_impl], where seven [xtime] equations
    are in scope, does not discharge. *)
#push-options "--fuel 1 --ifuel 1"
let fmul_unfold (a b: elem) (k: nat { k < 8 }) (prev: elem)
  : Lemma (requires prev == fmul_aux (xtime a) (b / pow2 (k + 1)) (7 - k))
          (ensures (if (b / pow2 k) % 2 = 1 then a ^^ prev else prev)
                   == fmul_aux a (b / pow2 k) (8 - k))
  = div_pow2_step b k
#pop-options

(** The correspondence with [Spec.AES.fmul_aux] is stated one step at a time,
    because letting the solver unfold all eight at once costs far more than
    eight separate one-step obligations. *)
(* Opaque to the solver.  What a caller needs is the refinement, and the
   bodies are large: inlining [sbox_impl] means inlining fifteen field
   multiplications of eight steps each into every query that mentions an
   S-box, which is enough to make unrelated obligations time out. *)
[@@ "opaque_to_smt"]
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let fmul_impl (a b: S8.t) : r: S8.t { S8.v r == fmul (S8.v a) (S8.v b) } =
  assert_norm (pow2 0 == 1);
  assert_norm (pow2 8 == 256);
  let a1 = xtime_impl a  in
  let a2 = xtime_impl a1 in
  let a3 = xtime_impl a2 in
  let a4 = xtime_impl a3 in
  let a5 = xtime_impl a4 in
  let a6 = xtime_impl a5 in
  let a7 = xtime_impl a6 in
  let r7 = fmul_step a7 b S8.zero 7ul in
  fmul_aux_zero (xtime (S8.v a7)) (S8.v b / pow2 8);
  fmul_unfold (S8.v a7) (S8.v b) 7 (S8.v S8.zero);
  let r6 = fmul_step a6 b r7 6ul in fmul_unfold (S8.v a6) (S8.v b) 6 (S8.v r7);
  let r5 = fmul_step a5 b r6 5ul in fmul_unfold (S8.v a5) (S8.v b) 5 (S8.v r6);
  let r4 = fmul_step a4 b r5 4ul in fmul_unfold (S8.v a4) (S8.v b) 4 (S8.v r5);
  let r3 = fmul_step a3 b r4 3ul in fmul_unfold (S8.v a3) (S8.v b) 3 (S8.v r4);
  let r2 = fmul_step a2 b r3 2ul in fmul_unfold (S8.v a2) (S8.v b) 2 (S8.v r3);
  let r1 = fmul_step a1 b r2 1ul in fmul_unfold (S8.v a1) (S8.v b) 1 (S8.v r2);
  let r0 = fmul_step a b r1 0ul in fmul_unfold (S8.v a) (S8.v b) 0 (S8.v r1);
  r0
#pop-options

(** {2 Inversion and the S-box} *)

(** [fexp a 254] with the recursion of [Spec.AES.fexp] written out.  The
    exponents are the ones its halving visits, and each step is a squaring
    followed, when the exponent is odd, by a multiplication. *)
#push-options "--fuel 1 --ifuel 1"
let fexp_zero (a: elem) : Lemma (fexp a 0 == 1) = ()

let fexp_odd (a: elem) (n: pos { n % 2 == 1 }) (h: elem)
  : Lemma (requires h == fexp a (n / 2)) (ensures fexp a n == fmul (fmul h h) a) = ()

let fexp_even (a: elem) (n: pos { n % 2 == 0 }) (h: elem)
  : Lemma (requires h == fexp a (n / 2)) (ensures fexp a n == fmul h h) = ()
#pop-options

(** Zero is the one input on which [Spec.AES.ginv] is not [fexp _ 254]; it
    maps to zero either way, so no branch is needed. *)
let ginv_zero () : Lemma (fexp 0 254 == 0) = assert_norm (fexp 0 254 == 0)

[@@ "opaque_to_smt"]
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let ginv_impl (a: S8.t) : r: S8.t { S8.v r == ginv (S8.v a) } =
  ginv_zero ();
  let one = S8.classify 1uy in
  fexp_zero (S8.v a);
  let e1   = fmul_impl (fmul_impl one one) a in fexp_odd (S8.v a) 1 (S8.v one);
  let e3   = fmul_impl (fmul_impl e1 e1) a in fexp_odd (S8.v a) 3 (S8.v e1);
  let e7   = fmul_impl (fmul_impl e3 e3) a in fexp_odd (S8.v a) 7 (S8.v e3);
  let e15  = fmul_impl (fmul_impl e7 e7) a in fexp_odd (S8.v a) 15 (S8.v e7);
  let e31  = fmul_impl (fmul_impl e15 e15) a in fexp_odd (S8.v a) 31 (S8.v e15);
  let e63  = fmul_impl (fmul_impl e31 e31) a in fexp_odd (S8.v a) 63 (S8.v e31);
  let e127 = fmul_impl (fmul_impl e63 e63) a in fexp_odd (S8.v a) 127 (S8.v e63);
  let e254 = fmul_impl e127 e127 in fexp_even (S8.v a) 254 (S8.v e127);
  e254
#pop-options

(** FIPS 197 5.1.1's affine map: the byte, four rotations of it, and
    [0x63]. *)
inline_for_extraction
let affine_impl (b: S8.t) : r: S8.t { S8.v r == affine (S8.v b) } =
  rotl8_value (S8.v b) 1;
  rotl8_value (S8.v b) 2;
  rotl8_value (S8.v b) 3;
  rotl8_value (S8.v b) 4;
  let r1 = S8.rotate_left b 1ul in
  assert (S8.v r1 == rotl8 (S8.v b) 1);
  let r2 = S8.rotate_left b 2ul in
  assert (S8.v r2 == rotl8 (S8.v b) 2);
  let r3 = S8.rotate_left b 3ul in
  assert (S8.v r3 == rotl8 (S8.v b) 3);
  let r4 = S8.rotate_left b 4ul in
  assert (S8.v r4 == rotl8 (S8.v b) 4);
  (* [^^] is right associative, so the fold nests to the right. *)
  bxor b (bxor r1 (bxor r2 (bxor r3 (bxor r4 (S8.classify 0x63uy)))))

[@@ "opaque_to_smt"]
let sbox_impl (x: S8.t) : r: S8.t { S8.v r == sbox (S8.v x) } =
  sbox_is_algebraic (S8.v x);
  affine_impl (ginv_impl x)
#pop-options
