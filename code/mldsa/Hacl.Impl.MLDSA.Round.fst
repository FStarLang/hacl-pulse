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


(** Power2Round, Decompose, MakeHint, UseHint and the infinity-norm test,
    one coefficient at a time, in constant time.

    Both splittings reduce to one division: [mod+-] at an even [g] is
    [r - g floor((r + g/2 - 1) / g)] ({!mod_pm_split}).  At [g = 2^13] the
    division is a shift.  At [g = 2 gamma2] it is a multiplication by a
    precomputed reciprocal and a shift by 48 ({!mulshift_exact}): the
    error bound makes it exact for every input below [q + gamma2], so
    there is no correction step and no data-dependent branch.  The
    folding of the top interval in Decompose is a mask.

    The parameter set is a ghost argument; the one runtime number these
    functions depend on is [gamma2]'s divisor (88 or 32), and the
    constants derived from it are selected by a branch on that public
    value, which the C compiler folds once the caller is specialised. *)
module Hacl.Impl.MLDSA.Round

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Rounding
open Hacl.Impl.MLDSA.Zq
open FStar.Ghost

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Math = FStar.Math.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 Division by a constant} *)

let div_bounds (y: nat) (p: pos) (a: nat)
  : Lemma (requires a * p <= y /\ y < (a + 1) * p) (ensures y / p == a)
  = Math.lemma_div_plus (y - a * p) a p;
    Math.small_div (y - a * p) p

(** [floor(x M / 2^s) = floor(x / D)] when [M D >= 2^s] and the excess
    [x (M D - 2^s)] stays below [2^s]. *)
let mulshift_exact (x: nat) (m: nat) (dv: pos) (s: nat)
  : Lemma (requires m * dv >= pow2 s /\ x * (m * dv - pow2 s) < pow2 s)
          (ensures (x * m) / pow2 s == x / dv)
  = let p = pow2 s in
    let a = x / dv in
    let e = m * dv - p in
    Math.lemma_div_mod x dv;
    (* (x m) dv = x p + x e *)
    Math.distributivity_add_right x p e;
    Math.paren_mul_right x m dv;
    (* lower: a dv p <= x p <= x m dv *)
    Math.lemma_mult_le_right p (a * dv) x;
    Math.paren_mul_right a dv p;
    Math.swap_mul dv p;
    Math.paren_mul_right a p dv;
    assert ((a * p) * dv <= (x * m) * dv);
    if x * m < a * p then Math.lemma_mult_lt_right dv (x * m) (a * p);
    (* upper: x m dv < (x + 1) p <= (a + 1) dv p *)
    Math.lemma_mult_le_right p (x + 1) ((a + 1) * dv);
    Math.distributivity_add_left x 1 p;
    Math.distributivity_add_left a 1 dv;
    Math.paren_mul_right (a + 1) dv p;
    Math.paren_mul_right (a + 1) p dv;
    assert ((x * m) * dv < ((a + 1) * p) * dv);
    if x * m >= (a + 1) * p then Math.lemma_mult_le_right dv ((a + 1) * p) (x * m);
    div_bounds (x * m) p a

(** [r mod+- g = r - g floor((r + g/2 - 1) / g)]. *)
let mod_pm_split (r: nat) (g: pos { g % 2 == 0 })
  : Lemma (r - mod_pm r g == g * ((r + g / 2 - 1) / g))
  = let h = g / 2 in
    let x = r % g in
    Math.lemma_div_mod r g;
    Math.lemma_mod_lt r g;
    if x > h then begin
      div_bounds (r + h - 1) g (r / g + 1);
      Math.distributivity_add_right g (r / g) 1
    end else
      div_bounds (r + h - 1) g (r / g)

(** {2 Power2Round} *)

let power2round_eq (r: zq)
  : Lemma (let r1 = (r + 4095) / 8192 in
           r1 < 1024 /\ r - 4096 <= r1 * 8192 /\ r1 * 8192 <= r + 4095 /\
           power2round_hi r == r1 /\ power2round_lo r == of_int (r - r1 * 8192))
  = assert_norm (pow2 13 == 8192);
    mod_pm_split r 8192;
    let r1 = (r + 4095) / 8192 in
    Math.lemma_div_mod (r + 4095) 8192;
    Math.lemma_mod_lt (r + 4095) 8192;
    Math.cancel_mul_div r1 8192;
    Math.swap_mul 8192 r1;
    assert_norm (q + 4095 < 1024 * 8192);
    if r1 >= 1024 then Math.lemma_mult_le_right 8192 1024 r1

inline_for_extraction
let p2r_hi (r: zqt) : x: S32.t { S32.v x == power2round_hi (S32.v r) /\ S32.v x < 1024 }
  = power2round_eq (S32.v r);
    assert_norm (q + 4095 < pow2 32);
    Math.small_mod (S32.v r + 4095) (pow2 32);
    assert_norm (pow2 13 == 8192);
    S32.shift_right (S32.add_mod r (S32.classify 4095ul)) 13ul

let reduce_shift (x: int) (k: nat)
  : Lemma ((x + k * q) % q == x % q)
  = Math.lemma_mod_plus x k q

inline_for_extraction
let p2r_lo (r: zqt) : x: zqt { S32.v x == power2round_lo (S32.v r) }
  = power2round_eq (S32.v r);
    let r1 = p2r_hi r in
    assert_norm (pow2 13 == 8192);
    assert_norm (2 * q < pow2 32);
    Math.small_mod (S32.v r1 * 8192) (pow2 32);
    let s = S32.shift_left r1 13ul in
    Math.small_mod (S32.v r + q) (pow2 32);
    Math.small_mod (S32.v r + q - S32.v s) (pow2 32);
    reduce_shift (S32.v r - S32.v s) 1;
    csub (S32.sub_mod (S32.add_mod r qw) s)

(** {2 Decompose} *)

(** The two values of [gamma2] and what follows from them: [m] is the
    number of high parts, and [2 gamma2 m = q - 1]. *)
let gamma2_cases (p: params)
  : Lemma ((p.gamma2_div == 88 /\ gamma2 p == 95232 /\ (q - 1) / (2 * gamma2 p) == 44) \/
           (p.gamma2_div == 32 /\ gamma2 p == 261888 /\ (q - 1) / (2 * gamma2 p) == 16))
  = assert_norm ((q - 1) / 88 == 95232 /\ (q - 1) / 190464 == 44);
    assert_norm ((q - 1) / 32 == 261888 /\ (q - 1) / 523776 == 16)

let hb_count (p: params) : pos = (q - 1) / (2 * gamma2 p)

let decompose_eq (p: params) (r: zq)
  : Lemma (let g2 = gamma2 p in
           let g = 2 * g2 in
           let m = hb_count p in
           let r1p = (r + g2 - 1) / g in
           let r0 = r - r1p * g in
           m * g == q - 1 /\ r1p <= m /\ - g2 < r0 /\ r0 <= g2 /\
           decompose p r == (if r1p = m then (0, r0 - 1) else (r1p, r0)))
  = gamma2_cases p;
    let g2 = gamma2 p in
    let g = 2 * g2 in
    let m = hb_count p in
    assert (m * g == q - 1);
    mod_pm_split r g;
    let r1p = (r + g2 - 1) / g in
    Math.lemma_div_mod (r + g2 - 1) g;
    Math.lemma_mod_lt (r + g2 - 1) g;
    Math.swap_mul g r1p;
    Math.cancel_mul_div r1p g;
    if r1p > m then Math.lemma_mult_le_right g (m + 1) r1p

inline_for_extraction
let g2_div_ok (p: params) (gd: U32.t) : prop = U32.v gd == p.gamma2_div

inline_for_extraction
let gamma2_w (#p: erased params) (gd: U32.t { g2_div_ok p gd }) : x: S32.t { S32.v x == gamma2 p }
  = gamma2_cases p;
    if U32.eq gd 88ul then S32.classify 95232ul else S32.classify 261888ul

inline_for_extraction
let hb_count_w (#p: erased params) (gd: U32.t { g2_div_ok p gd }) : x: S32.t { S32.v x == hb_count p }
  = gamma2_cases p;
    if U32.eq gd 88ul then S32.classify 44ul else S32.classify 16ul

(** [floor((r + gamma2 - 1) / (2 gamma2))], by a multiplication and a
    shift by 48. *)
inline_for_extraction
let decompose_r1 (#p: erased params) (gd: U32.t { g2_div_ok p gd }) (r: zqt)
  : x: S32.t { S32.v x == (S32.v r + gamma2 p - 1) / (2 * gamma2 p) /\ S32.v x <= hb_count p }
  = gamma2_cases p;
    decompose_eq p (S32.v r);
    let g2 = gamma2_w #p gd in
    let mc : S64.t =
      if U32.eq gd 88ul then S64.classify 1477838210uL else S64.classify 537395713uL in
    assert_norm (q + 261888 < pow2 24);
    assert_norm (pow2 24 < pow2 32);
    Math.small_mod (S32.v r + S32.v g2) (pow2 32);
    Math.small_mod (S32.v r + gamma2 p - 1) (pow2 32);
    let xw = S32.sub_mod (S32.add_mod r g2) (S32.classify 1ul) in
    assert_norm (pow2 24 * 1477838210 < pow2 64 /\ pow2 24 * 537395713 < pow2 64);
    Math.lemma_mult_le_right (S64.v mc) (S32.v r + gamma2 p - 1) (pow2 24);
    Math.small_mod ((S32.v r + gamma2 p - 1) * S64.v mc) (pow2 64);
    let prod = S64.mul_mod (Cast.u32_to_u64 xw) mc in
    assert_norm (1477838210 * 190464 >= pow2 48 /\ pow2 24 * (1477838210 * 190464 - pow2 48) < pow2 48);
    assert_norm (537395713 * 523776 >= pow2 48 /\ pow2 24 * (537395713 * 523776 - pow2 48) < pow2 48);
    Math.lemma_mult_le_right (S64.v mc * (2 * gamma2 p) - pow2 48) (S32.v r + gamma2 p - 1) (pow2 24);
    mulshift_exact (S32.v r + gamma2 p - 1) (S64.v mc) (2 * gamma2 p) 48;
    let t = S64.shift_right prod 48ul in
    Math.small_mod (S64.v t) (pow2 32);
    Cast.u64_to_u32 t

(** Algorithm 37. *)
inline_for_extraction
let high_bits_w (#p: erased params) (gd: U32.t { g2_div_ok p gd }) (r: zqt)
  : x: S32.t { S32.v x == high_bits p (S32.v r) /\ S32.v x < hb_count p }
  = decompose_eq p (S32.v r);
    let r1 = decompose_r1 #p gd r in
    let mw = hb_count_w #p gd in
    S32.select (S32.eq_mask r1 mw) S32.zero r1

(** Algorithm 38, as an element of [Z_q]. *)
inline_for_extraction
let low_bits_w (#p: erased params) (gd: U32.t { g2_div_ok p gd }) (r: zqt)
  : x: zqt { S32.v x == low_bits p (S32.v r) }
  = decompose_eq p (S32.v r);
    gamma2_cases p;
    let r1 = decompose_r1 #p gd r in
    let g2 = gamma2_w #p gd in
    let mw = hb_count_w #p gd in
    assert_norm (2 * q < pow2 32);
    Math.small_mod (S32.v r1 * (2 * gamma2 p)) (pow2 32);
    let s = S32.mul_mod r1 (S32.add_mod g2 g2) in
    Math.small_mod (S32.v g2 + S32.v g2) (pow2 32);
    Math.small_mod (S32.v r + q) (pow2 32);
    Math.small_mod (S32.v r + q - S32.v s) (pow2 32);
    reduce_shift (S32.v r - S32.v s) 1;
    let lo = csub (S32.sub_mod (S32.add_mod r qw) s) in
    let fold : zqt = S32.select (S32.eq_mask r1 mw) (S32.classify 1ul) S32.zero in
    Math.lemma_mod_sub_distr ((S32.v r - S32.v r1 * (2 * gamma2 p)) % q) 1 q |> ignore;
    Math.lemma_mod_plus ((S32.v r - S32.v r1 * (2 * gamma2 p)) % q - S32.v fold) 1 q;
    Math.lemma_mod_add_distr (- (S32.v fold)) (S32.v r - S32.v r1 * (2 * gamma2 p)) q;
    zq_sub lo fold

(** The signed low part of Decompose lies in [[-gamma2, gamma2]]. *)
let decompose_lo_range (p: params) (r: zq)
  : Lemma (- gamma2 p <= snd (decompose p r) /\ snd (decompose p r) <= gamma2 p)
  = decompose_eq p r; gamma2_cases p

(** For a signed [x] of magnitude at most [gamma2], [x > 0] iff its
    representative in [Z_q] lies in [[1, gamma2]]. *)
let pos_of_int (p: params) (x: int)
  : Lemma (requires - gamma2 p <= x /\ x <= gamma2 p)
          (ensures (x > 0 <==> (1 <= of_int x /\ of_int x <= gamma2 p)))
  = gamma2_cases p;
    if x >= 0 then Math.small_mod x q
    else (Math.lemma_mod_plus x 1 q; Math.small_mod (x + q) q)

let bool_w (b: bool) (x: S32.t) : prop = S32.v x == (if b then 1 else 0)

let wrap_step (m: pos) (v1: nat { v1 < m })
  : Lemma ((v1 + 1) % m == (if v1 + 1 = m then 0 else v1 + 1) /\
           (v1 - 1) % m == (if v1 = 0 then m - 1 else v1 - 1))
  = if v1 + 1 = m then Math.cancel_mul_mod 1 m else Math.small_mod (v1 + 1) m;
    if v1 = 0 then (Math.lemma_mod_plus (-1) 1 m; Math.small_mod (m - 1) m)
    else Math.small_mod (v1 - 1) m

(** [use_hint] in terms of the two outputs of Decompose as the code
    computes them. *)
let use_hint_eq (p: params) (h: bool) (r: zq)
  : Lemma (let r1 = high_bits p r in
           let lo = low_bits p r in
           let m = hb_count p in
           r1 < m /\
           use_hint p h r ==
             (if h then (if 1 <= lo && lo <= gamma2 p
                         then (if r1 + 1 = m then 0 else r1 + 1)
                         else (if r1 = 0 then m - 1 else r1 - 1))
              else r1))
  = decompose_eq p r;
    decompose_lo_range p r;
    pos_of_int p (snd (decompose p r));
    wrap_step (hb_count p) (high_bits p r)

let pos_mask_lemma (lo g2: nat)
  : Lemma (requires lo < pow2 32 /\ 0 < g2 /\ g2 < pow2 32)
          (ensures ((lo - 1) % pow2 32 < g2 <==> (1 <= lo /\ lo <= g2)))
  = if lo = 0 then (Math.lemma_mod_plus (-1) 1 (pow2 32); Math.small_mod (pow2 32 - 1) (pow2 32))
    else Math.small_mod (lo - 1) (pow2 32)

(** Algorithm 40.  The hint [h] is [0] or [1]. *)
inline_for_extraction
let use_hint_w (#p: erased params) (gd: U32.t { g2_div_ok p gd }) (h: S32.t) (r: zqt)
  : Pure S32.t (requires S32.v h == 0 \/ S32.v h == 1)
      (ensures fun x -> S32.v x == use_hint p (S32.v h = 1) (S32.v r) /\ S32.v x < hb_count p)
  = gamma2_cases p;
    use_hint_eq p (S32.v h = 1) (S32.v r);
    let r1 = high_bits_w #p gd r in
    let lo = low_bits_w #p gd r in
    let g2 = gamma2_w #p gd in
    let mw = hb_count_w #p gd in
    pos_mask_lemma (S32.v lo) (S32.v g2);
    let pos = S32.lt_mask (S32.sub_mod lo (S32.classify 1ul)) g2 in
    Math.small_mod (S32.v r1 + 1) (pow2 32);
    let r1p = S32.add_mod r1 (S32.classify 1ul) in
    let up = S32.select (S32.eq_mask r1p mw) S32.zero r1p in
    assert (S32.v up == (if S32.v r1 + 1 = hb_count p then 0 else S32.v r1 + 1));
    Math.small_mod (S32.v mw - 1) (pow2 32);
    if S32.v r1 > 0 then Math.small_mod (S32.v r1 - 1) (pow2 32);
    let down = S32.select (S32.eq_mask r1 S32.zero) (S32.sub_mod mw (S32.classify 1ul))
                 (S32.sub_mod r1 (S32.classify 1ul)) in
    assert (S32.v down == (if S32.v r1 = 0 then hb_count p - 1 else S32.v r1 - 1));
    let pu = S32.select pos up down in
    assert (S32.v pu == (if 1 <= S32.v lo && S32.v lo <= gamma2 p then S32.v up else S32.v down));
    Math.lemma_mod_plus (-1) 1 (pow2 32);
    Math.small_mod (pow2 32 - 1) (pow2 32);
    Math.small_mod 0 (pow2 32);
    let hm = S32.sub_mod S32.zero h in
    S32.select hm pu r1

(** Algorithm 39, as [0] or [1]. *)
inline_for_extraction
let make_hint_w (#p: erased params) (gd: U32.t { g2_div_ok p gd }) (z r: zqt)
  : x: S32.t { bool_w (make_hint p (S32.v z) (S32.v r)) x }
  = let h1 = high_bits_w #p gd r in
    let h2 = high_bits_w #p gd (zq_add r z) in
    S32.select (S32.eq_mask h1 h2) S32.zero (S32.classify 1ul)

(** All ones iff [norm x >= b]: the rejection test of one coefficient. *)
inline_for_extraction
let norm_ge_mask (x: zqt) (b: S32.t { S32.v b <= half_q })
  : m: S32.t { (norm (S32.v x) >= S32.v b ==> S32.v m == pow2 32 - 1) /\
               (norm (S32.v x) < S32.v b ==> S32.v m == 0) }
  = assert_norm (half_q == 4190208);
    let nx = S32.select (S32.lt_mask (S32.classify 4190208ul) x) (S32.sub_mod qw x) x in
    S32.gte_mask nx b
