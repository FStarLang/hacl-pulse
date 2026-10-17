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

(** Rounding, FIPS 204 algorithms 35 through 40.

    Two splittings of a coefficient into a high and a low part.
    [Power2Round] splits at a power of two and is used once, at key
    generation, to drop thirteen bits of [t].  [Decompose] splits at
    [2 gamma2], which does not divide [q - 1] evenly into a power of two,
    and it has one wrinkle: the topmost interval would produce the high
    part [(q - 1) / (2 gamma2)], which is congruent to zero, so it is
    folded down to zero with the low part shifted by one.

    The high parts are small naturals.  The low parts are signed in the
    standard and are returned in [Z_q] here, which is what every caller
    does with them: [t0] is packed and multiplied, and [r0] is only ever
    measured with {!Spec.MLDSA.Zq.norm}. *)
module Spec.MLDSA.Rounding

open Spec.MLDSA.Zq
open Spec.MLDSA.Params

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0"

(** [r mod+- a] for even [a]: the representative in [(-a/2, a/2]]. *)
let mod_pm (r: int) (a: pos { a % 2 == 0 }) : x: int { - (a / 2) < x /\ x <= a / 2 }
  = let x = r % a in if x > a / 2 then x - a else x

(** Algorithm 35. *)
let power2round (r: zq) : nat & zq
  = assert_norm (pow2 13 == 8192);
    let r0 = mod_pm r (pow2 d) in
    (r - r0) / pow2 d, of_int r0

let power2round_hi (r: zq) : nat = fst (power2round r)
let power2round_lo (r: zq) : zq = snd (power2round r)

(** Algorithm 36.  [r0] is returned as an integer; {!low_bits} is the
    view the callers want. *)
let decompose (p: params) (r: zq) : nat & int
  = let g = 2 * gamma2 p in
    assert (g % 2 == 0);
    let r0 = mod_pm r g in
    if r - r0 = q - 1 then (0, r0 - 1)
    else begin
      assert (r - r0 >= 0);
      ((r - r0) / g, r0)
    end

(** Algorithm 37. *)
let high_bits (p: params) (r: zq) : nat = fst (decompose p r)

(** Algorithm 38. *)
let low_bits (p: params) (r: zq) : zq = of_int (snd (decompose p r))

(** Algorithm 39: does adding [z] to [r] change the high part? *)
let make_hint (p: params) (z r: zq) : bool
  = high_bits p r <> high_bits p (add r z)

(** Algorithm 40: the high part of [r], corrected by one step in the
    direction its low part points when the hint says so.  The steps wrap
    modulo [m = (q - 1) / (2 gamma2)]. *)
let use_hint (p: params) (h: bool) (r: zq) : nat
  = let m : pos = (q - 1) / (2 * gamma2 p) in
    let r1, r0 = decompose p r in
    if h && r0 > 0 then (r1 + 1) % m
    else if h then (r1 - 1) % m
    else r1

(** {2 Vectors} *)

let vec_power2round_hi (#k: pos) (v: pvec k) : Seq.lseq nat (k * n)
  = Seq.init (k * n) (fun i -> power2round_hi (Seq.index v i))

let vec_power2round_lo (#k: pos) (v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> power2round_lo (Seq.index v i))

let vec_high_bits (p: params) (#k: pos) (v: pvec k) : Seq.lseq nat (k * n)
  = Seq.init (k * n) (fun i -> high_bits p (Seq.index v i))

let vec_low_bits (p: params) (#k: pos) (v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> low_bits p (Seq.index v i))

let vec_make_hint (p: params) (#k: pos) (z r: pvec k) : Seq.lseq bool (k * n)
  = Seq.init (k * n) (fun i -> make_hint p (Seq.index z i) (Seq.index r i))

let vec_use_hint (p: params) (#k: pos) (h: Seq.lseq bool (k * n)) (r: pvec k)
  : Seq.lseq nat (k * n)
  = Seq.init (k * n) (fun i -> use_hint p (Seq.index h i) (Seq.index r i))

(** The number of ones in a hint. *)
let rec count_true (s: Seq.seq bool) : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else (if Seq.index s 0 then 1 else 0) + count_true (Seq.tail s)

#pop-options
