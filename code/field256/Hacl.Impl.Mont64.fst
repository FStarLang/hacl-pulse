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

(** Montgomery multiplication in four sixty-four-bit words, for any odd
    modulus below [2^256].

    {!Hacl.Impl.Mont4} sums a product in columns of [__int128] and reduces
    it with a general row multiplier; this module does the same arithmetic
    the way {!Hacl.P256.Field64} does it, with the modulus as data.  The
    product is {!Hacl.Curve25519.Field64.mul8}, sixteen multiplications
    chained with [adc].  Each of four reduction steps ({!rstep0} ..
    {!rstep3}) takes the bottom word [x] of the window, forms
    [q = x mu mod 2^64] (with [mu = -m^-1 mod 2^64]), adds [q m] -- four
    widening multiplications and two [adc] chains -- and drops the bottom
    word, which [mu] has made zero.  {!csub} subtracts [m] once if it can.

    Every statement is linear except where a lemma below says otherwise:
    [w * W_(k+1) == W_k + q m], with the powers of the radix as numerals
    and [q m] an opaque product that {!qm_split} relates to the four
    double words. *)
module Hacl.Impl.Mont64

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Curve25519.Field64
open Hacl.Secret.Word.Instances

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module L = Hacl.Impl.Limb64
module K = Hacl.Carry64
module F64 = Hacl.Curve25519.Field64
module Mem = Hacl.Mem

(** {2 Numbers} *)

unfold let w9 : pos = 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136

(** Nine words from [k] up; past the end they read as zero. *)
let wv (s: Seq.seq S64.t) (k: nat) : GTot nat =
  F64.ix s k + w * F64.ix s (k + 1) + w2 * F64.ix s (k + 2) + w3 * F64.ix s (k + 3) +
  w4 * F64.ix s (k + 4) + w5 * F64.ix s (k + 5) + w6 * F64.ix s (k + 6) +
  w7 * F64.ix s (k + 7) + w8 * F64.ix s (k + 8)

(** What the caller promises about the modulus words and [mu]. *)
let mok (n0 n1 n2 n3 mu: S64.t) (m: nat) : prop =
  m == ev4 (S64.v n0) (S64.v n1) (S64.v n2) (S64.v n3) /\ 0 < m /\
  (S64.v n0 * S64.v mu + 1) % w == 0

let mok_lt (n0 n1 n2 n3 mu: S64.t) (m: nat)
  : Lemma (requires mok n0 n1 n2 n3 mu m) (ensures m < w4) = ()

(** [q m] in terms of the four double words [q n_i = lo_i + w hi_i]. *)
let qm_split (q n0 n1 n2 n3: nat) (l0 h0 l1 h1 l2 h2 l3 h3: nat)
  : Lemma (requires q * n0 == l0 + w * h0 /\ q * n1 == l1 + w * h1 /\
                    q * n2 == l2 + w * h2 /\ q * n3 == l3 + w * h3)
          (ensures q * ev4 n0 n1 n2 n3 ==
                   l0 + w * (h0 + l1) + w2 * (h1 + l2) + w3 * (h2 + l3) + w4 * h3)
  = Math.distributivity_add_right q n0 (w * n1 + w2 * n2 + w3 * n3);
    Math.distributivity_add_right q (w * n1) (w2 * n2 + w3 * n3);
    Math.distributivity_add_right q (w2 * n2) (w3 * n3);
    Math.paren_mul_right q w n1; Math.swap_mul q w; Math.paren_mul_right w q n1;
    Math.paren_mul_right q w2 n2; Math.swap_mul q w2; Math.paren_mul_right w2 q n2;
    Math.paren_mul_right q w3 n3; Math.swap_mul q w3; Math.paren_mul_right w3 q n3

let qm_lt (q m: nat)
  : Lemma (requires q < w /\ m < w4) (ensures q * m < w5)
  = prod_lt q m w w4

(** [mu] makes the bottom word vanish. *)
let kill (x mu n0: nat)
  : Lemma (requires x < w /\ (n0 * mu + 1) % w == 0)
          (ensures (x + (x * mu % w) * n0 % w) % w == 0)
  = Math.lemma_mod_mul_distr_l (x * mu) n0 w;
    Math.paren_mul_right x mu n0;
    Math.swap_mul mu n0;
    Math.lemma_mod_plus_distr_r x (x * (n0 * mu)) w;
    Math.lemma_mod_mul_distr_r x (n0 * mu) w;
    Math.lemma_mod_plus (n0 * mu) 1 w;
    Math.euclidean_division_definition (n0 * mu + 1) w;
    Math.lemma_mod_plus_distr_r x (x * ((n0 * mu) % w)) w;
    assert ((n0 * mu) % w == w - 1);
    Math.distributivity_sub_right x w 1;
    Math.lemma_mod_plus (x - x) x w

let zero_word (r c s: nat)
  : Lemma (requires r < w /\ r + w * c == s /\ s % w == 0) (ensures r == 0)
  = Math.lemma_mod_plus r c w; Math.small_mod r w

let modm_ok (x o: int) (m: pos)
  : Lemma (requires 0 <= o /\ o < m /\ (o == x \/ o == x - m))
          (ensures o == x % m)
  = Math.small_mod o m;
    Math.lemma_mod_plus o 1 m

let mask_ok (b: nat)
  : Lemma (requires b <= 1)
          (ensures (0 - b) % pow2 64 == (if b = 0 then 0 else pow2 64 - 1))
  = assert_norm (pow2 64 == w);
    if b = 0 then () else Math.lemma_mod_plus (-1) 1 w

let glue (o x t u: nat) (m: pos)
  : Lemma (requires o == x % m /\ w4 * x == t + u * m)
          (ensures w4 * o % m == t % m)
  = Math.lemma_mod_twice x m;
    Math.lemma_mod_mul_distr_r w4 o m;
    Math.lemma_mod_mul_distr_r w4 x m;
    Math.lemma_mod_plus t u m

(** [Q m] for [Q = q0 + w q1 + w2 q2 + w3 q3], term by term. *)
let qsum (q0 q1 q2 q3 m: nat)
  : Lemma (ev4 q0 q1 q2 q3 * m == q0 * m + w * (q1 * m) + w2 * (q2 * m) + w3 * (q3 * m))
  = Math.swap_mul (ev4 q0 q1 q2 q3) m;
    qm_split m q0 q1 q2 q3 (m * q0) 0 (m * q1) 0 (m * q2) 0 (m * q3) 0;
    Math.swap_mul m q0; Math.swap_mul m q1; Math.swap_mul m q2; Math.swap_mul m q3

(** The window after four steps is below [2 m]. *)
let final_lt (ab qq m x: nat)
  : Lemma (requires m < w4 /\ ab < m * m /\ qq < w4 /\ w4 * x == ab + qq * m)
          (ensures x < 2 * m)
  = Math.lemma_mult_lt_right m m w4;
    Math.lemma_mult_lt_right m qq w4;
    Math.swap_mul qq m; Math.swap_mul m w4

let sq_lt (m: nat) : Lemma (requires m < w4) (ensures m * m < w8) = prod_lt m m w4 w4

(** Nothing carries out of the top of a window that is known to be small. *)
let no_carry (b c d x wt: nat)
  : Lemma (requires w * b + wt * (c + d) == x /\ x < wt) (ensures c == 0 /\ d == 0)
  = Math.nat_times_nat_is_nat w b;
    if c + d > 0 then Math.lemma_mult_le_left wt 1 (c + d)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn put4 (o: A.array S64.t) (x0 x1 x2 x3: S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 4)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 4 /\
        F64.ev vo' == ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3))
{
  A.pts_to_len o;
  A.((o.(0sz) <- x0));
  A.((o.(1sz) <- x1));
  A.((o.(2sz) <- x2));
  A.((o.(3sz) <- x3));
}

(** {2 Montgomery reduction}

    Step [k] takes the window [W_k] (words [k] to [8]) and leaves
    [W_(k+1) = (W_k + q m) / 2^64] in words [k+1] to [8], returning [q].
    The bound in the precondition is what says nothing carries out of the
    top word. *)
#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep0 (t: A.array S64.t) (n0 n1 n2 n3 mu: S64.t) (m: erased nat) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ mok n0 n1 n2 n3 mu m /\ wv vt 0 + w5 <= w9)
returns q: S64.t
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ S64.v q * m < w5 /\ w * wv vt' 1 == wv vt 0 + S64.v q * m)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let x0 = A.(t.(0sz));
  let x1 = A.(t.(1sz));
  let x2 = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let q = S64.mul_mod x0 mu;
  let p0 = S128.mul_wide q n0;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide q n1;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide q n2;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide q n3;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  qm_split (S64.v q) (S64.v n0) (S64.v n1) (S64.v n2) (S64.v n3) (S64.v l0) (S64.v h0) (S64.v l1) (S64.v h1) (S64.v l2) (S64.v h2) (S64.v l3) (S64.v h3);
  qm_lt (S64.v q) m;
  kill (S64.v x0) (S64.v mu) (S64.v n0);
  let mut r = z0;
  let c0 = K.addc z0 x0 l0 r;
  let a0 = !r;
  let c1 = K.addc c0 x1 l1 r;
  let a1 = !r;
  let c2 = K.addc c1 x2 l2 r;
  let a2 = !r;
  let c3 = K.addc c2 x3 l3 r;
  let a3 = !r;
  let c4 = K.addc c3 x4 h3 r;
  let a4 = !r;
  let c5 = K.addc c4 x5 z0 r;
  let a5 = !r;
  let c6 = K.addc c5 x6 z0 r;
  let a6 = !r;
  let c7 = K.addc c6 x7 z0 r;
  let a7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let a8 = !r;
  zero_word (S64.v a0) (S64.v c0) (S64.v x0 + S64.v l0);
  assert (pure (S64.v a0 + w * (S64.v a1) + w2 * (S64.v a2) + w3 * (S64.v a3) + w4 * (S64.v a4) + w5 * (S64.v a5) + w6 * (S64.v a6) + w7 * (S64.v a7) + w8 * (S64.v a8) + w9 * (S64.v c8) ==
                S64.v x0 + w * (S64.v x1) + w2 * (S64.v x2) + w3 * (S64.v x3) + w4 * (S64.v x4) + w5 * (S64.v x5) + w6 * (S64.v x6) + w7 * (S64.v x7) + w8 * (S64.v x8) + S64.v l0 + w * (S64.v l1) + w2 * (S64.v l2) + w3 * (S64.v l3) + w4 * (S64.v h3)));
  let d1 = K.addc z0 a1 h0 r;
  let b1 = !r;
  let d2 = K.addc d1 a2 h1 r;
  let b2 = !r;
  let d3 = K.addc d2 a3 h2 r;
  let b3 = !r;
  let d4 = K.addc d3 a4 z0 r;
  let b4 = !r;
  let d5 = K.addc d4 a5 z0 r;
  let b5 = !r;
  let d6 = K.addc d5 a6 z0 r;
  let b6 = !r;
  let d7 = K.addc d6 a7 z0 r;
  let b7 = !r;
  let d8 = K.addc d7 a8 z0 r;
  let b8 = !r;
  assert (pure (S64.v b1 + w * (S64.v b2) + w2 * (S64.v b3) + w3 * (S64.v b4) + w4 * (S64.v b5) + w5 * (S64.v b6) + w6 * (S64.v b7) + w7 * (S64.v b8) + w8 * (S64.v d8) ==
                S64.v a1 + w * (S64.v a2) + w2 * (S64.v a3) + w3 * (S64.v a4) + w4 * (S64.v a5) + w5 * (S64.v a6) + w6 * (S64.v a7) + w7 * (S64.v a8) + S64.v h0 + w * (S64.v h1) + w2 * (S64.v h2)));
  assert (pure (w * (S64.v b1 + w * (S64.v b2) + w2 * (S64.v b3) + w3 * (S64.v b4) + w4 * (S64.v b5) + w5 * (S64.v b6) + w6 * (S64.v b7) + w7 * (S64.v b8)) + w9 * (S64.v c8 + S64.v d8) == wv vt 0 + S64.v q * m));
  no_carry (S64.v b1 + w * (S64.v b2) + w2 * (S64.v b3) + w3 * (S64.v b4) + w4 * (S64.v b5) + w5 * (S64.v b6) + w6 * (S64.v b7) + w7 * (S64.v b8)) (S64.v c8) (S64.v d8) (wv vt 0 + S64.v q * m) w9;
  assert (pure (S64.v c8 == 0 /\ S64.v d8 == 0));
  A.((t.(1sz) <- b1));
  A.((t.(2sz) <- b2));
  A.((t.(3sz) <- b3));
  A.((t.(4sz) <- b4));
  A.((t.(5sz) <- b5));
  A.((t.(6sz) <- b6));
  A.((t.(7sz) <- b7));
  A.((t.(8sz) <- b8));
  q
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep1 (t: A.array S64.t) (n0 n1 n2 n3 mu: S64.t) (m: erased nat) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ mok n0 n1 n2 n3 mu m /\ wv vt 1 + w5 <= w8)
returns q: S64.t
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ S64.v q * m < w5 /\ w * wv vt' 2 == wv vt 1 + S64.v q * m)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let x1 = A.(t.(1sz));
  let x2 = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let q = S64.mul_mod x1 mu;
  let p0 = S128.mul_wide q n0;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide q n1;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide q n2;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide q n3;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  qm_split (S64.v q) (S64.v n0) (S64.v n1) (S64.v n2) (S64.v n3) (S64.v l0) (S64.v h0) (S64.v l1) (S64.v h1) (S64.v l2) (S64.v h2) (S64.v l3) (S64.v h3);
  qm_lt (S64.v q) m;
  kill (S64.v x1) (S64.v mu) (S64.v n0);
  let mut r = z0;
  let c1 = K.addc z0 x1 l0 r;
  let a1 = !r;
  let c2 = K.addc c1 x2 l1 r;
  let a2 = !r;
  let c3 = K.addc c2 x3 l2 r;
  let a3 = !r;
  let c4 = K.addc c3 x4 l3 r;
  let a4 = !r;
  let c5 = K.addc c4 x5 h3 r;
  let a5 = !r;
  let c6 = K.addc c5 x6 z0 r;
  let a6 = !r;
  let c7 = K.addc c6 x7 z0 r;
  let a7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let a8 = !r;
  zero_word (S64.v a1) (S64.v c1) (S64.v x1 + S64.v l0);
  assert (pure (S64.v a1 + w * (S64.v a2) + w2 * (S64.v a3) + w3 * (S64.v a4) + w4 * (S64.v a5) + w5 * (S64.v a6) + w6 * (S64.v a7) + w7 * (S64.v a8) + w8 * (S64.v c8) ==
                S64.v x1 + w * (S64.v x2) + w2 * (S64.v x3) + w3 * (S64.v x4) + w4 * (S64.v x5) + w5 * (S64.v x6) + w6 * (S64.v x7) + w7 * (S64.v x8) + S64.v l0 + w * (S64.v l1) + w2 * (S64.v l2) + w3 * (S64.v l3) + w4 * (S64.v h3)));
  let d2 = K.addc z0 a2 h0 r;
  let b2 = !r;
  let d3 = K.addc d2 a3 h1 r;
  let b3 = !r;
  let d4 = K.addc d3 a4 h2 r;
  let b4 = !r;
  let d5 = K.addc d4 a5 z0 r;
  let b5 = !r;
  let d6 = K.addc d5 a6 z0 r;
  let b6 = !r;
  let d7 = K.addc d6 a7 z0 r;
  let b7 = !r;
  let d8 = K.addc d7 a8 z0 r;
  let b8 = !r;
  assert (pure (S64.v b2 + w * (S64.v b3) + w2 * (S64.v b4) + w3 * (S64.v b5) + w4 * (S64.v b6) + w5 * (S64.v b7) + w6 * (S64.v b8) + w7 * (S64.v d8) ==
                S64.v a2 + w * (S64.v a3) + w2 * (S64.v a4) + w3 * (S64.v a5) + w4 * (S64.v a6) + w5 * (S64.v a7) + w6 * (S64.v a8) + S64.v h0 + w * (S64.v h1) + w2 * (S64.v h2)));
  assert (pure (w * (S64.v b2 + w * (S64.v b3) + w2 * (S64.v b4) + w3 * (S64.v b5) + w4 * (S64.v b6) + w5 * (S64.v b7) + w6 * (S64.v b8)) + w8 * (S64.v c8 + S64.v d8) == wv vt 1 + S64.v q * m));
  no_carry (S64.v b2 + w * (S64.v b3) + w2 * (S64.v b4) + w3 * (S64.v b5) + w4 * (S64.v b6) + w5 * (S64.v b7) + w6 * (S64.v b8)) (S64.v c8) (S64.v d8) (wv vt 1 + S64.v q * m) w8;
  assert (pure (S64.v c8 == 0 /\ S64.v d8 == 0));
  A.((t.(2sz) <- b2));
  A.((t.(3sz) <- b3));
  A.((t.(4sz) <- b4));
  A.((t.(5sz) <- b5));
  A.((t.(6sz) <- b6));
  A.((t.(7sz) <- b7));
  A.((t.(8sz) <- b8));
  q
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep2 (t: A.array S64.t) (n0 n1 n2 n3 mu: S64.t) (m: erased nat) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ mok n0 n1 n2 n3 mu m /\ wv vt 2 + w5 <= w7)
returns q: S64.t
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ S64.v q * m < w5 /\ w * wv vt' 3 == wv vt 2 + S64.v q * m)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let x2 = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let q = S64.mul_mod x2 mu;
  let p0 = S128.mul_wide q n0;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide q n1;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide q n2;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide q n3;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  qm_split (S64.v q) (S64.v n0) (S64.v n1) (S64.v n2) (S64.v n3) (S64.v l0) (S64.v h0) (S64.v l1) (S64.v h1) (S64.v l2) (S64.v h2) (S64.v l3) (S64.v h3);
  qm_lt (S64.v q) m;
  kill (S64.v x2) (S64.v mu) (S64.v n0);
  let mut r = z0;
  let c2 = K.addc z0 x2 l0 r;
  let a2 = !r;
  let c3 = K.addc c2 x3 l1 r;
  let a3 = !r;
  let c4 = K.addc c3 x4 l2 r;
  let a4 = !r;
  let c5 = K.addc c4 x5 l3 r;
  let a5 = !r;
  let c6 = K.addc c5 x6 h3 r;
  let a6 = !r;
  let c7 = K.addc c6 x7 z0 r;
  let a7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let a8 = !r;
  zero_word (S64.v a2) (S64.v c2) (S64.v x2 + S64.v l0);
  assert (pure (S64.v a2 + w * (S64.v a3) + w2 * (S64.v a4) + w3 * (S64.v a5) + w4 * (S64.v a6) + w5 * (S64.v a7) + w6 * (S64.v a8) + w7 * (S64.v c8) ==
                S64.v x2 + w * (S64.v x3) + w2 * (S64.v x4) + w3 * (S64.v x5) + w4 * (S64.v x6) + w5 * (S64.v x7) + w6 * (S64.v x8) + S64.v l0 + w * (S64.v l1) + w2 * (S64.v l2) + w3 * (S64.v l3) + w4 * (S64.v h3)));
  let d3 = K.addc z0 a3 h0 r;
  let b3 = !r;
  let d4 = K.addc d3 a4 h1 r;
  let b4 = !r;
  let d5 = K.addc d4 a5 h2 r;
  let b5 = !r;
  let d6 = K.addc d5 a6 z0 r;
  let b6 = !r;
  let d7 = K.addc d6 a7 z0 r;
  let b7 = !r;
  let d8 = K.addc d7 a8 z0 r;
  let b8 = !r;
  assert (pure (S64.v b3 + w * (S64.v b4) + w2 * (S64.v b5) + w3 * (S64.v b6) + w4 * (S64.v b7) + w5 * (S64.v b8) + w6 * (S64.v d8) ==
                S64.v a3 + w * (S64.v a4) + w2 * (S64.v a5) + w3 * (S64.v a6) + w4 * (S64.v a7) + w5 * (S64.v a8) + S64.v h0 + w * (S64.v h1) + w2 * (S64.v h2)));
  assert (pure (w * (S64.v b3 + w * (S64.v b4) + w2 * (S64.v b5) + w3 * (S64.v b6) + w4 * (S64.v b7) + w5 * (S64.v b8)) + w7 * (S64.v c8 + S64.v d8) == wv vt 2 + S64.v q * m));
  no_carry (S64.v b3 + w * (S64.v b4) + w2 * (S64.v b5) + w3 * (S64.v b6) + w4 * (S64.v b7) + w5 * (S64.v b8)) (S64.v c8) (S64.v d8) (wv vt 2 + S64.v q * m) w7;
  assert (pure (S64.v c8 == 0 /\ S64.v d8 == 0));
  A.((t.(3sz) <- b3));
  A.((t.(4sz) <- b4));
  A.((t.(5sz) <- b5));
  A.((t.(6sz) <- b6));
  A.((t.(7sz) <- b7));
  A.((t.(8sz) <- b8));
  q
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep3 (t: A.array S64.t) (n0 n1 n2 n3 mu: S64.t) (m: erased nat) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ mok n0 n1 n2 n3 mu m /\ wv vt 3 + w5 <= w6)
returns q: S64.t
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ S64.v q * m < w5 /\ w * wv vt' 4 == wv vt 3 + S64.v q * m)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let q = S64.mul_mod x3 mu;
  let p0 = S128.mul_wide q n0;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide q n1;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide q n2;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide q n3;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  qm_split (S64.v q) (S64.v n0) (S64.v n1) (S64.v n2) (S64.v n3) (S64.v l0) (S64.v h0) (S64.v l1) (S64.v h1) (S64.v l2) (S64.v h2) (S64.v l3) (S64.v h3);
  qm_lt (S64.v q) m;
  kill (S64.v x3) (S64.v mu) (S64.v n0);
  let mut r = z0;
  let c3 = K.addc z0 x3 l0 r;
  let a3 = !r;
  let c4 = K.addc c3 x4 l1 r;
  let a4 = !r;
  let c5 = K.addc c4 x5 l2 r;
  let a5 = !r;
  let c6 = K.addc c5 x6 l3 r;
  let a6 = !r;
  let c7 = K.addc c6 x7 h3 r;
  let a7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let a8 = !r;
  zero_word (S64.v a3) (S64.v c3) (S64.v x3 + S64.v l0);
  assert (pure (S64.v a3 + w * (S64.v a4) + w2 * (S64.v a5) + w3 * (S64.v a6) + w4 * (S64.v a7) + w5 * (S64.v a8) + w6 * (S64.v c8) ==
                S64.v x3 + w * (S64.v x4) + w2 * (S64.v x5) + w3 * (S64.v x6) + w4 * (S64.v x7) + w5 * (S64.v x8) + S64.v l0 + w * (S64.v l1) + w2 * (S64.v l2) + w3 * (S64.v l3) + w4 * (S64.v h3)));
  let d4 = K.addc z0 a4 h0 r;
  let b4 = !r;
  let d5 = K.addc d4 a5 h1 r;
  let b5 = !r;
  let d6 = K.addc d5 a6 h2 r;
  let b6 = !r;
  let d7 = K.addc d6 a7 z0 r;
  let b7 = !r;
  let d8 = K.addc d7 a8 z0 r;
  let b8 = !r;
  assert (pure (S64.v b4 + w * (S64.v b5) + w2 * (S64.v b6) + w3 * (S64.v b7) + w4 * (S64.v b8) + w5 * (S64.v d8) ==
                S64.v a4 + w * (S64.v a5) + w2 * (S64.v a6) + w3 * (S64.v a7) + w4 * (S64.v a8) + S64.v h0 + w * (S64.v h1) + w2 * (S64.v h2)));
  assert (pure (w * (S64.v b4 + w * (S64.v b5) + w2 * (S64.v b6) + w3 * (S64.v b7) + w4 * (S64.v b8)) + w6 * (S64.v c8 + S64.v d8) == wv vt 3 + S64.v q * m));
  no_carry (S64.v b4 + w * (S64.v b5) + w2 * (S64.v b6) + w3 * (S64.v b7) + w4 * (S64.v b8)) (S64.v c8) (S64.v d8) (wv vt 3 + S64.v q * m) w6;
  assert (pure (S64.v c8 == 0 /\ S64.v d8 == 0));
  A.((t.(4sz) <- b4));
  A.((t.(5sz) <- b5));
  A.((t.(6sz) <- b6));
  A.((t.(7sz) <- b7));
  A.((t.(8sz) <- b8));
  q
}

#restart-solver

(** [W_4 < 2 m]: one conditional subtraction of [m], by a borrow chain
    through the fifth word and a masked select. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn csub (o t: A.array S64.t) (n0 n1 n2 n3 mu: S64.t) (m: erased nat)
        (#vo: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to t vt **
  pure (Seq.length vo == 4 /\ Seq.length vt == 9 /\ mok n0 n1 n2 n3 mu m /\ wv vt 4 < 2 * m)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to t vt **
  pure (Seq.length vo' == 4 /\ F64.ev vo' < m /\ F64.ev vo' == wv vt 4 % m)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let r4 = A.(t.(4sz));
  let r5 = A.(t.(5sz));
  let r6 = A.(t.(6sz));
  let r7 = A.(t.(7sz));
  let r8 = A.(t.(8sz));
  let mut r = z0;
  let b = K.subb z0 r4 n0 r;
  let s0 = !r;
  let b = K.subb b r5 n1 r;
  let s1 = !r;
  let b = K.subb b r6 n2 r;
  let s2 = !r;
  let b = K.subb b r7 n3 r;
  let s3 = !r;
  let b = K.subb b r8 z0 r;
  let s4 = !r;
  assert (pure (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) + w4 * S64.v s4 - w5 * S64.v b ==
                wv vt 4 - m));
  mask_ok (S64.v b);
  let mk = S64.sub_mod z0 b;
  let o0 = S64.select mk r4 s0;
  let o1 = S64.select mk r5 s1;
  let o2 = S64.select mk r6 s2;
  let o3 = S64.select mk r7 s3;
  assert (pure (S64.v b == 1 ==> ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == wv vt 4));
  assert (pure (S64.v b == 0 ==> ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == wv vt 4 - m));
  modm_ok (wv vt 4) (ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3)) m;
  put4 o o0 o1 o2 o3;
}

(** {2 The product}

    [n] is the modulus as four words and [mu] is [-n^-1 mod 2^64]; both
    are read once.  On numbers below the modulus, [mmul] is Montgomery's
    product, [R z = a b mod m] with [R = 2^256]. *)

#push-options "--z3rlimit 200"

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn mmul (out a b n: A.array S64.t) (mu: S64.t) (m: erased nat)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
        (#pn: perm) (#vn: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to n #pn vn **
  pure (Seq.length vo == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4 /\
        Seq.length vn == 4 /\ m == F64.ev vn /\ 0 < m /\
        (F64.ix vn 0 * S64.v mu + 1) % w == 0 /\
        F64.ev va < m /\ F64.ev vb < m)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to n #pn vn **
  pure (Seq.length vo' == 4 /\ F64.ev vo' < m /\
        w4 * F64.ev vo' % m == F64.ev va * F64.ev vb % m)
{
  A.pts_to_len n;
  let n0 = A.(n.(0sz));
  let n1 = A.(n.(1sz));
  let n2 = A.(n.(2sz));
  let n3 = A.(n.(3sz));
  assert (pure (mok n0 n1 n2 n3 mu m));
  mok_lt n0 n1 n2 n3 mu m;
  let z = S64.classify 0uL;
  let mut t = [| z; 8sz |];
  Mem.track t;
  A.pts_to_len t;
  F64.mul8 t a b;
  with y. assert (A.pts_to t y);
  prod_lt (F64.ev va) (F64.ev vb) m m;
  sq_lt m;
  let mut s = [| z; 9sz |];
  Mem.track s;
  A.pts_to_len s;
  A.((s.(0sz) <- t.(0sz)));
  A.((s.(1sz) <- t.(1sz)));
  A.((s.(2sz) <- t.(2sz)));
  A.((s.(3sz) <- t.(3sz)));
  A.((s.(4sz) <- t.(4sz)));
  A.((s.(5sz) <- t.(5sz)));
  A.((s.(6sz) <- t.(6sz)));
  A.((s.(7sz) <- t.(7sz)));
  with s0. assert (A.pts_to s s0);
  assert (pure (wv s0 0 == F64.ev va * F64.ev vb));
  let q0 = rstep0 s n0 n1 n2 n3 mu m;
  with s1. assert (A.pts_to s s1);
  let q1 = rstep1 s n0 n1 n2 n3 mu m;
  with s2. assert (A.pts_to s s2);
  let q2 = rstep2 s n0 n1 n2 n3 mu m;
  with s3. assert (A.pts_to s s3);
  let q3 = rstep3 s n0 n1 n2 n3 mu m;
  with s4. assert (A.pts_to s s4);
  qsum (S64.v q0) (S64.v q1) (S64.v q2) (S64.v q3) m;
  let qq : erased nat = hide (ev4 (S64.v q0) (S64.v q1) (S64.v q2) (S64.v q3));
  assert (pure (w4 * wv s4 4 == F64.ev va * F64.ev vb + reveal qq * m));
  final_lt (F64.ev va * F64.ev vb) qq m (wv s4 4);
  csub out s n0 n1 n2 n3 mu m;
  with o. assert (A.pts_to out o);
  glue (F64.ev o) (wv s4 4) (F64.ev va * F64.ev vb) qq m;
  assert (pure (F64.ev o < m /\ w4 * F64.ev o % m == F64.ev va * F64.ev vb % m));
  Mem.wipe s 9sz;
  Mem.wipe t 8sz;
}

#pop-options

#pop-options
