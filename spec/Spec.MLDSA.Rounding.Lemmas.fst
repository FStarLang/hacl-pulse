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

(** Rounding lemmas: the closed form of [Decompose], the hint lemma
    ([UseHint] undoes [MakeHint]), the stability of [HighBits] under a
    small perturbation, and [Power2Round] recombination.

    [gamma2] takes two concrete values, so every proof splits on it and
    the arithmetic stays linear. *)
module Spec.MLDSA.Rounding.Lemmas

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Rounding

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let gamma2_val (p: params)
  : Lemma (gamma2 p == 95232 /\ p.gamma2_div == 88 \/ gamma2 p == 261888 /\ p.gamma2_div == 32)
  = assert_norm ((q - 1) / 88 == 95232);
    assert_norm ((q - 1) / 32 == 261888)

(** The high part, in closed form: the topmost [gamma2] values of [Z_q]
    fold to zero, and every other [r] lies in [(r1 a - g, r1 a + g]]. *)
let hb_c (g: pos) (r: zq) : nat = if r >= q - g then 0 else (r + g - 1) / (2 * g)

let lb_c (g: pos) (r: zq) : int
  = if r >= q - g then r - q else r - 2 * g * ((r + g - 1) / (2 * g))

let decompose_lit (g: pos { g == 95232 \/ g == 261888 }) (r: zq)
  : Lemma (let a = 2 * g in
           let x = r % a in
           let r0 = if x > a / 2 then x - a else x in
           (if r - r0 = q - 1 then (0, r0 - 1) else ((r - r0) / a, r0)) == (hb_c g r, lb_c g r))
  = ()

let decompose_closed (p: params) (r: zq)
  : Lemma (decompose p r == (hb_c (gamma2 p) r, lb_c (gamma2 p) r))
  = gamma2_val p;
    decompose_lit (gamma2 p) r

(** The low part as an integer lies in [-g, g] and recombines with the
    high part to [r]. *)
let lb_c_range (g: pos { g == 95232 \/ g == 261888 }) (r: zq)
  : Lemma (- g <= lb_c g r /\ lb_c g r <= g /\
           hb_c g r < (q - 1) / (2 * g) /\
           (hb_c g r * (2 * g) + lb_c g r) % q == r)
  = ()

let use_hint_lit (g: pos { g == 95232 \/ g == 261888 }) (z r: zq)
  : Lemma (requires norm z <= g)
          (ensures (let m = (q - 1) / (2 * g) in
                    let s = (r + z) % q in
                    let h = hb_c g r <> hb_c g s in
                    let r1 = hb_c g r in
                    let r0 = lb_c g r in
                    (if h && r0 > 0 then (r1 + 1) % m
                     else if h then (r1 - 1) % m
                     else r1) == hb_c g s))
  = ()

(** The hint lemma (FIPS 204, section 3.6.3): if [z] is no larger than
    [gamma2], the hint for [z] at [r] recovers the high part of [r + z]
    from [r] alone. *)
let use_hint_make_hint (p: params) (z r: zq)
  : Lemma (requires norm z <= gamma2 p)
          (ensures use_hint p (make_hint p z r) r == high_bits p (add r z))
  = gamma2_val p;
    decompose_closed p r;
    decompose_closed p (add r z);
    use_hint_lit (gamma2 p) z r

let stable_lit (g: pos { g == 95232 \/ g == 261888 }) (r s: zq) (b: nat)
  : Lemma (requires norm s <= b /\ norm (lb_c g r % q) < g - b)
          (ensures hb_c g ((r + s) % q) == hb_c g r)
  = ()

(** Adding something no larger than [b] to [r] does not move its high
    part when the low part of [r] is below [gamma2 - b]. *)
let high_bits_stable (p: params) (r s: zq) (b: nat)
  : Lemma (requires norm s <= b /\ norm (low_bits p r) < gamma2 p - b)
          (ensures high_bits p (add r s) == high_bits p r)
  = gamma2_val p;
    decompose_closed p r;
    decompose_closed p (add r s);
    stable_lit (gamma2 p) r s b

(** {2 Power2Round} *)

(** [t1] fits in ten bits, [t0] is centred in [(-2^12, 2^12]], and
    [t1 2^d + t0 = r]. *)
let power2round_props (r: zq)
  : Lemma (power2round_hi r < pow2 10 /\
           - 4096 < centre (power2round_lo r) /\ centre (power2round_lo r) <= 4096 /\
           add (of_int (power2round_hi r * pow2 d)) (power2round_lo r) == r)
  = assert_norm (pow2 13 == 8192);
    assert_norm (pow2 10 == 1024)

#pop-options
