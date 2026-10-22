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

(** The arithmetic behind a four-lane Poly1305.

    {2 Four Horner chains}

    The specification absorbs one block at a time, [a <- (a + m_i) r].  Over
    four blocks that is

      [a <- (a + m_0) r^4 + m_1 r^3 + m_2 r^2 + m_3 r],

    so if four accumulators [x_0 .. x_3] are each multiplied by [r^4] and
    given the next block of their own residue class modulo four, the number
    [x_0 r^4 + x_1 r^3 + x_2 r^2 + x_3 r] advances exactly as the
    specification's accumulator does.  [horner4] is that number,
    [four_steps] is the specification's side, [horner_step] the
    implementation's, and the invariant of the vector loop is that the two
    agree modulo [prime].  At the end each lane is multiplied by its own
    power and the four are added.

    {2 Wider multipliers}

    [Spec.Poly1305.Field.mul_reduce_ok] asks for [r]'s limbs under [2^26],
    which a clamped key satisfies.  The powers [r^2, r^3, r^4] come out of
    the carry chain, which only promises [2^27].  One more bit on one side
    makes the five-term column sums [21 * 2^55 < 2^60] rather than [2^59];
    the carry chain still lands every limb under [2^27].  The three lemmas
    below are the old ones with that bit added. *)
module Spec.Poly1305.Vec

open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring
open Hacl.Spec.Loops
open Spec.Poly1305.Field

module Math = FStar.Math.Lemmas
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Spec = Spec.Poly1305

#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

(** {2 One more bit on the multiplier} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let prod_bound27 (a b: nat)
  : Lemma (requires a < pow2 28 /\ b < pow2 27) (ensures a * b < pow2 55)
  = Math.pow2_plus 28 27;
    Math.lemma_mult_le_right b a (pow2 28 - 1);
    Math.lemma_mult_le_left (pow2 28 - 1) b (pow2 27 - 1)

let mul_no_overflow27 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat)
  : Lemma (requires bounded5 h0 h1 h2 h3 h4 28 /\ bounded5 r0 r1 r2 r3 r4 27)
          (ensures bounded5 (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4) 60)
  = let bound (h r: nat) : Lemma (requires h < pow2 28 /\ r < pow2 27)
                                 (ensures h * r < pow2 55) = prod_bound27 h r in
    bound h0 r0; bound h0 r1; bound h0 r2; bound h0 r3; bound h0 r4;
    bound h1 r0; bound h1 r1; bound h1 r2; bound h1 r3; bound h1 r4;
    bound h2 r0; bound h2 r1; bound h2 r2; bound h2 r3; bound h2 r4;
    bound h3 r0; bound h3 r1; bound h3 r2; bound h3 r3; bound h3 r4;
    bound h4 r0; bound h4 r1; bound h4 r2; bound h4 r3; bound h4 r4;
    Math.pow2_plus 5 55;
    assert_norm (pow2 5 == 32)

let carry_chain_bounds60 (e0 e1 e2 e3 e4 t0 t1 t2 t3 t4: nat)
  : Lemma (requires bounded5 e0 e1 e2 e3 e4 60 /\ chain e0 e1 e2 e3 e4 t0 t1 t2 t3 t4)
          (ensures bounded5 t0 t1 t2 t3 t4 27)
  = let x1 = e1 + e0 / radix in
    let x3 = e3 % radix in
    let x4 = e4 + e3 / radix in
    let x01 = e0 % radix + 5 * (x4 / radix) in
    let x2 = e2 + x1 / radix in
    let x31 = x3 + x2 / radix in
    div_bound e0 60 26;
    div_bound e3 60 26;
    add_bound e1 (e0 / radix) 60 34;
    add_bound e4 (e3 / radix) 60 34;
    div_bound x4 61 26;
    assert_norm (5 * pow2 35 < pow2 38);
    add_bound (5 * (x4 / radix)) (e0 % radix) 38 26;
    div_bound x1 61 26;
    add_bound e2 (x1 / radix) 60 35;
    div_bound x2 61 26;
    add_bound (x2 / radix) x3 35 26;
    div_bound x31 36 26;
    div_bound x01 39 26;
    Math.pow2_lt_compat 27 26;
    Math.pow2_lt_compat 26 13;
    Math.pow2_lt_compat 26 10;
    Math.pow2_double_sum 26

(** The carry chain's intermediates, for an implementation that must know
    each fits in sixty-four bits before it adds into it. *)
let chain_fits60 (e0 e1 e2 e3 e4: nat)
  : Lemma (requires bounded5 e0 e1 e2 e3 e4 60)
          (ensures (let x1 = e1 + e0 / radix in
                    let x4 = e4 + e3 / radix in
                    let x2 = e2 + x1 / radix in
                    let x31 = e3 % radix + x2 / radix in
                    let x01 = e0 % radix + 5 * (x4 / radix) in
                    x1 < pow2 61 /\ x4 < pow2 61 /\ x2 < pow2 61 /\
                    x4 / radix < pow2 35 /\
                    x01 < pow2 39 /\ x31 < pow2 36 /\
                    x1 % radix + x01 / radix < pow2 27 /\
                    x4 % radix + x31 / radix < pow2 27))
  = let x1 = e1 + e0 / radix in
    let x4 = e4 + e3 / radix in
    let x2 = e2 + x1 / radix in
    let x31 = e3 % radix + x2 / radix in
    let x01 = e0 % radix + 5 * (x4 / radix) in
    div_bound e0 60 26;
    div_bound e3 60 26;
    add_bound e1 (e0 / radix) 60 34;
    add_bound e4 (e3 / radix) 60 34;
    div_bound x4 61 26;
    assert_norm (5 * pow2 35 < pow2 38);
    add_bound (5 * (x4 / radix)) (e0 % radix) 38 26;
    div_bound x1 61 26;
    add_bound e2 (x1 / radix) 60 35;
    div_bound x2 61 26;
    add_bound (x2 / radix) (e3 % radix) 35 26;
    div_bound x31 36 26;
    div_bound x01 39 26;
    Math.pow2_lt_compat 26 13;
    Math.pow2_lt_compat 26 10;
    Math.pow2_double_sum 26

let mul_reduce_ok27 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 t0 t1 t2 t3 t4: nat)
  : Lemma
      (requires
         bounded5 h0 h1 h2 h3 h4 28 /\ bounded5 r0 r1 r2 r3 r4 27 /\
         chain (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               t0 t1 t2 t3 t4)
      (ensures
         bounded5 t0 t1 t2 t3 t4 27 /\
         as_nat5 t0 t1 t2 t3 t4 % prime ==
         (as_nat5 h0 h1 h2 h3 h4 * as_nat5 r0 r1 r2 r3 r4) % prime)
  = let e0 = d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e1 = d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e2 = d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e3 = d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e4 = d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    mul_no_overflow27 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4;
    carry_chain_bounds60 e0 e1 e2 e3 e4 t0 t1 t2 t3 t4;
    carry_chain_cong e0 e1 e2 e3 e4 t0 t1 t2 t3 t4;
    mul_mod h0 h1 h2 h3 h4 r0 r1 r2 r3 r4

#pop-options

(** {2 Congruence} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let cong (x y: int) : prop = x % prime == y % prime

let cong_add (a b c d: int)
  : Lemma (requires cong a b /\ cong c d) (ensures cong (a + c) (b + d))
  = Math.lemma_mod_add_distr a c prime;
    Math.lemma_mod_add_distr (c % prime) a prime;
    Math.lemma_mod_add_distr b d prime;
    Math.lemma_mod_add_distr (d % prime) b prime;
    assert ((a + c) % prime == (c % prime + a % prime) % prime);
    assert ((b + d) % prime == (d % prime + b % prime) % prime)

let cong_mul (a b c d: int)
  : Lemma (requires cong a b /\ cong c d) (ensures cong (a * c) (b * d))
  = Math.lemma_mod_mul_distr_l a c prime;
    Math.lemma_mod_mul_distr_l b d prime;
    Math.lemma_mod_mul_distr_r (a % prime) c prime;
    Math.lemma_mod_mul_distr_r (b % prime) d prime

let cong_trans (a b c: int)
  : Lemma (requires cong a b /\ cong b c) (ensures cong a c) = ()

let cong_mod (a: int) : Lemma (cong (a % prime) a)
  = Math.lemma_mod_twice a prime

#pop-options

(** {2 Four blocks at once} *)

let r2 (r: int) : int = r * r
let r3 (r: int) : int = r * (r * r)
let r4 (r: int) : int = r * (r * (r * r))

let horner4 (r x0 x1 x2 x3: int) : int =
  x0 * r4 r + x1 * r3 r + x2 * r2 r + x3 * r

let bv (msg: Seq.seq S8.t) (i: nat { 16 * i + 16 <= Seq.length msg }) : GTot nat =
  Spec.block_val (Seq.slice msg (16 * i) (16 * i + 16))

let sacc (msg: Seq.seq S8.t) (r acc: nat) (n: nat) : GTot nat =
  Spec.blocks_acc msg 0 n r acc

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let one_step (msg: Seq.seq S8.t) (r acc: nat) (n: nat)
  : Lemma (requires 16 * n + 16 <= Seq.length msg)
          (ensures sacc msg r acc (n + 1) == ((sacc msg r acc n + bv msg n) * r) % prime)
  = unfold_repeati_g n (Spec.bstep msg 0 r) acc;
    assert (Spec.block16 msg (0 + 16 * n) == Seq.slice msg (16 * n) (16 * n + 16))

let step_mod (x y r: int)
  : Lemma (((x % prime + y) * r) % prime == ((x + y) * r) % prime)
  = Math.lemma_mod_add_distr y x prime;
    Math.lemma_mod_mul_distr_l (x + y) r prime;
    Math.lemma_mod_mul_distr_l (x % prime + y) r prime

let horner_ring (s b0 b1 b2 b3 r: int)
  : Lemma (((((s + b0) * r + b1) * r + b2) * r + b3) * r == horner4 r (s + b0) b1 b2 b3)
  = assert (((((s + b0) * r + b1) * r + b2) * r + b3) * r ==
            (s + b0) * (r * (r * (r * r))) + b1 * (r * (r * r)) + b2 * (r * r) + b3 * r)
      by (canon_semiring int_cr)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let four_steps (msg: Seq.seq S8.t) (r acc: nat) (n: nat)
  : Lemma (requires 16 * n + 64 <= Seq.length msg)
          (ensures sacc msg r acc (n + 4) ==
                   horner4 r (sacc msg r acc n + bv msg n)
                           (bv msg (n + 1)) (bv msg (n + 2)) (bv msg (n + 3)) % prime)
  = let s = sacc msg r acc n in
    let b0 = bv msg n in
    let b1 = bv msg (n + 1) in
    let b2 = bv msg (n + 2) in
    let b3 = bv msg (n + 3) in
    one_step msg r acc n;
    assert (sacc msg r acc (n + 1) == ((s + b0) * r) % prime);
    one_step msg r acc (n + 1);
    step_mod ((s + b0) * r) b1 r;
    assert (sacc msg r acc (n + 2) == (((s + b0) * r + b1) * r) % prime);
    one_step msg r acc (n + 2);
    step_mod (((s + b0) * r + b1) * r) b2 r;
    assert (sacc msg r acc (n + 3) == ((((s + b0) * r + b1) * r + b2) * r) % prime);
    one_step msg r acc (n + 3);
    step_mod ((((s + b0) * r + b1) * r + b2) * r) b3 r;
    assert (sacc msg r acc (n + 4) == (((((s + b0) * r + b1) * r + b2) * r + b3) * r) % prime);
    horner_ring s b0 b1 b2 b3 r

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let horner_lin (r x0 x1 x2 x3 m0 m1 m2 m3 q: int)
  : Lemma (horner4 r (x0 * q + m0) (x1 * q + m1) (x2 * q + m2) (x3 * q + m3) ==
           q * horner4 r x0 x1 x2 x3 + horner4 r m0 m1 m2 m3)
  = assert (horner4 r (x0 * q + m0) (x1 * q + m1) (x2 * q + m2) (x3 * q + m3) ==
            q * horner4 r x0 x1 x2 x3 + horner4 r m0 m1 m2 m3)
      by (norm [delta_only [`%horner4; `%r2; `%r3; `%r4]]; canon_semiring int_cr)

let horner_cong (r x0 x1 x2 x3 y0 y1 y2 y3: int)
  : Lemma (requires cong x0 y0 /\ cong x1 y1 /\ cong x2 y2 /\ cong x3 y3)
          (ensures cong (horner4 r x0 x1 x2 x3) (horner4 r y0 y1 y2 y3))
  = cong_mul x0 y0 (r4 r) (r4 r);
    cong_mul x1 y1 (r3 r) (r3 r);
    cong_mul x2 y2 (r2 r) (r2 r);
    cong_mul x3 y3 r r;
    cong_add (x0 * r4 r) (y0 * r4 r) (x1 * r3 r) (y1 * r3 r);
    cong_add (x0 * r4 r + x1 * r3 r) (y0 * r4 r + y1 * r3 r) (x2 * r2 r) (y2 * r2 r);
    cong_add (x0 * r4 r + x1 * r3 r + x2 * r2 r) (y0 * r4 r + y1 * r3 r + y2 * r2 r)
             (x3 * r) (y3 * r)

#pop-options

(** The invariant of the vector loop, with the lanes given in block order. *)
let hinv (msg: Seq.seq S8.t) (r acc: nat) (n: nat) (x0 x1 x2 x3: nat) : prop =
  16 * n <= Seq.length msg /\ cong (horner4 r x0 x1 x2 x3) (sacc msg r acc n)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Before the loop: the first four blocks, and the incoming accumulator
    added to the first. *)
let horner_init (msg: Seq.seq S8.t) (r acc: nat) (h: nat) (x0 x1 x2 x3: nat)
  : Lemma (requires 64 <= Seq.length msg /\ cong h acc /\
                    x0 == h + bv msg 0 /\ x1 == bv msg 1 /\ x2 == bv msg 2 /\ x3 == bv msg 3)
          (ensures hinv msg r acc 4 x0 x1 x2 x3)
  = repeati_g_zero (Spec.bstep msg 0 r) acc;
    four_steps msg r acc 0;
    cong_add h acc (bv msg 0) (bv msg 0);
    horner_cong r x0 x1 x2 x3 (acc + bv msg 0) x1 x2 x3;
    cong_mod (horner4 r (acc + bv msg 0) x1 x2 x3)

(** One trip round the loop: every lane multiplied by (something congruent
    to) [r^4], and the next four blocks added. *)
let horner_step (msg: Seq.seq S8.t) (r acc: nat) (n: nat) (q: nat)
                (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3: nat)
  : Lemma (requires hinv msg r acc n x0 x1 x2 x3 /\ 16 * n + 64 <= Seq.length msg /\
                    cong q (r4 r) /\
                    cong y0 (x0 * q) /\ cong y1 (x1 * q) /\
                    cong y2 (x2 * q) /\ cong y3 (x3 * q) /\
                    z0 == y0 + bv msg n /\ z1 == y1 + bv msg (n + 1) /\
                    z2 == y2 + bv msg (n + 2) /\ z3 == y3 + bv msg (n + 3))
          (ensures hinv msg r acc (n + 4) z0 z1 z2 z3)
  = let s = sacc msg r acc n in
    let b0 = bv msg n in
    let b1 = bv msg (n + 1) in
    let b2 = bv msg (n + 2) in
    let b3 = bv msg (n + 3) in
    let hx = horner4 r x0 x1 x2 x3 in
    four_steps msg r acc n;
    (* the lanes, as products *)
    cong_add y0 (x0 * q) b0 b0;
    cong_add y1 (x1 * q) b1 b1;
    cong_add y2 (x2 * q) b2 b2;
    cong_add y3 (x3 * q) b3 b3;
    horner_cong r z0 z1 z2 z3 (x0 * q + b0) (x1 * q + b1) (x2 * q + b2) (x3 * q + b3);
    horner_lin r x0 x1 x2 x3 b0 b1 b2 b3 q;
    (* q * hx is congruent to r^4 * s *)
    cong_mul q (r4 r) hx s;
    cong_add (q * hx) (r4 r * s) (horner4 r b0 b1 b2 b3) (horner4 r b0 b1 b2 b3);
    (* and that is the specification's next value *)
    horner_lin r 0 0 0 0 (s + b0) b1 b2 b3 1;
    assert (horner4 r (s + b0) b1 b2 b3 == r4 r * s + horner4 r b0 b1 b2 b3)
      by (norm [delta_only [`%horner4; `%r2; `%r3; `%r4]]; canon_semiring int_cr);
    cong_mod (horner4 r (s + b0) b1 b2 b3)

(** After the loop: each lane multiplied by (something congruent to) its
    own power of [r], and the four added. *)
let horner_final (msg: Seq.seq S8.t) (r acc: nat) (n: nat)
                 (x0 x1 x2 x3 p0 p1 p2 p3 y0 y1 y2 y3: nat)
  : Lemma (requires hinv msg r acc n x0 x1 x2 x3 /\
                    cong p0 (r4 r) /\ cong p1 (r3 r) /\ cong p2 (r2 r) /\ cong p3 r /\
                    cong y0 (x0 * p0) /\ cong y1 (x1 * p1) /\
                    cong y2 (x2 * p2) /\ cong y3 (x3 * p3))
          (ensures cong (y0 + y1 + y2 + y3) (sacc msg r acc n))
  = cong_mul x0 x0 p0 (r4 r);
    cong_mul x1 x1 p1 (r3 r);
    cong_mul x2 x2 p2 (r2 r);
    cong_mul x3 x3 p3 r;
    cong_trans y0 (x0 * p0) (x0 * r4 r);
    cong_trans y1 (x1 * p1) (x1 * r3 r);
    cong_trans y2 (x2 * p2) (x2 * r2 r);
    cong_trans y3 (x3 * p3) (x3 * r);
    cong_add y0 (x0 * r4 r) y1 (x1 * r3 r);
    cong_add (y0 + y1) (x0 * r4 r + x1 * r3 r) y2 (x2 * r2 r);
    cong_add (y0 + y1 + y2) (x0 * r4 r + x1 * r3 r + x2 * r2 r) y3 (x3 * r)

#pop-options
