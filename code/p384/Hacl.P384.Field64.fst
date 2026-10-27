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

(** The P-384 field in six sixty-four-bit words, specialised.
    The generic bignum layer multiplies with loops over a runtime length
    and reads the modulus from a table; at six words that is four fifths
    overhead.  Here the multiplication is coarsely interleaved Montgomery
    (one word of [a] at a time): {!step} takes an accumulator below [2 p]
    in seven words to [(acc + x b + u p) / 2^64], again below [2 p], and
    {!mont} calls it six times and subtracts [p] once if it can.
    For [p = 2^384 - 2^128 - 2^96 + 2^32 - 1] the lowest word is
    [2^32 - 1], so the Montgomery quotient is [u = s0 (2^32 + 1) mod 2^64],
    and the top three words of [p] are all ones, so [u p] takes four
    multiplications rather than six.  Every statement in {!step} is linear
    once the products are named; the modular bookkeeping is in lemmas.
    Addition and subtraction are a carry chain and a masked correction.
    Nothing here has a CPU target: [adc] and [mul] are baseline x86-64. *)
module Hacl.P384.Field64

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
module T = FStar.Tactics.V2
module Canon = FStar.Tactics.CanonCommSemiring

(** {2 Numbers} *)

unfold let pp : pos = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

unfold let ev6 (a0 a1 a2 a3 a4 a5: int) : int =
  a0 + w * a1 + w2 * a2 + w3 * a3 + w4 * a4 + w5 * a5

unfold let ev7 (a0 a1 a2 a3 a4 a5 a6: int) : int =
  ev6 a0 a1 a2 a3 a4 a5 + w6 * a6

(** The number six words stand for. *)
let fv (s: Seq.seq S64.t) : GTot nat =
  ev6 (F64.ix s 0) (F64.ix s 1) (F64.ix s 2) (F64.ix s 3) (F64.ix s 4) (F64.ix s 5)

(** The number seven words stand for. *)
let av (s: Seq.seq S64.t) : GTot nat =
  ev7 (F64.ix s 0) (F64.ix s 1) (F64.ix s 2) (F64.ix s 3) (F64.ix s 4) (F64.ix s 5)
      (F64.ix s 6)

(** {2 Arithmetic facts} *)

let dist6 (x b0 b1 b2 b3 b4 b5: int)
  : Lemma (x * ev6 b0 b1 b2 b3 b4 b5 ==
           x * b0 + w * (x * b1) + w2 * (x * b2) + w3 * (x * b3) + w4 * (x * b4) + w5 * (x * b5))
  = ()

let prod_le (x y: nat)
  : Lemma (requires x < w /\ y < pp) (ensures x * y <= (w - 1) * (pp - 1))
  = Math.lemma_mult_le_right y x (w - 1);
    Math.lemma_mult_le_left (w - 1) y (pp - 1)

(** The Montgomery quotient: [-p^-1 mod 2^64 = 2^32 + 1]. *)
let mu_ok (s0 u: nat)
  : Lemma (requires s0 < w /\ u == (s0 * 4294967297) % pow2 64)
          (ensures (s0 + (u * 4294967295) % pow2 64) % pow2 64 == 0)
  = assert_norm (pow2 64 == w);
    Math.lemma_mod_mul_distr_l (s0 * 4294967297) 4294967295 w;
    assert (s0 * 4294967297 * 4294967295 == s0 * w - s0);
    Math.lemma_mod_plus_distr_r s0 (s0 * w - s0) w;
    Math.cancel_mul_mod s0 w

let step_mod (a' a xb u: nat)
  : Lemma (requires w * a' == a + xb + u * pp)
          (ensures (w * a') % pp == (a + xb) % pp)
  = Math.lemma_mod_plus (a + xb) u pp

let inv_step (wi: pos) (acc acc' pre ai b: nat)
  : Lemma (requires (wi * acc) % pp == (pre * b) % pp /\
                    (w * acc') % pp == (acc + ai * b) % pp)
          (ensures (w * wi * acc') % pp == ((pre + wi * ai) * b) % pp)
  = calc (==) {
      (w * wi * acc') % pp;
      == { Math.paren_mul_right wi w acc'; Math.swap_mul w wi }
      (wi * (w * acc')) % pp;
      == { Math.lemma_mod_mul_distr_r wi (w * acc') pp }
      (wi * ((w * acc') % pp)) % pp;
      == { }
      (wi * ((acc + ai * b) % pp)) % pp;
      == { Math.lemma_mod_mul_distr_r wi (acc + ai * b) pp }
      (wi * (acc + ai * b)) % pp;
      == { Math.distributivity_add_right wi acc (ai * b); Math.paren_mul_right wi ai b }
      (wi * acc + wi * ai * b) % pp;
      == { Math.lemma_mod_plus_distr_l (wi * acc) (wi * ai * b) pp }
      ((wi * acc) % pp + wi * ai * b) % pp;
      == { }
      ((pre * b) % pp + wi * ai * b) % pp;
      == { Math.lemma_mod_plus_distr_l (pre * b) (wi * ai * b) pp }
      (pre * b + wi * ai * b) % pp;
      == { Math.distributivity_add_left pre (wi * ai) b }
      ((pre + wi * ai) * b) % pp;
    }

let chain6 (v1 v2 v3 v4 v5 v6 a0 a1 a2 a3 a4 a5 b: nat)
  : Lemma (requires (w * v1) % pp == (0 + a0 * b) % pp /\
                    (w * v2) % pp == (v1 + a1 * b) % pp /\
                    (w * v3) % pp == (v2 + a2 * b) % pp /\
                    (w * v4) % pp == (v3 + a3 * b) % pp /\
                    (w * v5) % pp == (v4 + a4 * b) % pp /\
                    (w * v6) % pp == (v5 + a5 * b) % pp)
          (ensures (w6 * v6) % pp == (ev6 a0 a1 a2 a3 a4 a5 * b) % pp)
  = inv_step 1 0 v1 0 a0 b;
    inv_step w v1 v2 a0 a1 b;
    inv_step w2 v2 v3 (a0 + w * a1) a2 b;
    inv_step w3 v3 v4 (a0 + w * a1 + w2 * a2) a3 b;
    inv_step w4 v4 v5 (a0 + w * a1 + w2 * a2 + w3 * a3) a4 b;
    inv_step w5 v5 v6 (a0 + w * a1 + w2 * a2 + w3 * a3 + w4 * a4) a5 b

let mod_out (o v: nat)
  : Lemma (requires o == v % pp) (ensures (w6 * o) % pp == (w6 * v) % pp)
  = Math.lemma_mod_mul_distr_r w6 v pp

(** {2 Carry chains}

    The chains below are linear in their words and carries, and say so
    here, over plain numbers, where Z3 sees nothing else. *)

let add6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 s0 s1 s2 s3 s4 s5 c0 c1 c2 c3 c4 c5 c6: nat)
  : Lemma (requires s0 + w * c1 == a0 + b0 + c0 /\ s1 + w * c2 == a1 + b1 + c1 /\
                    s2 + w * c3 == a2 + b2 + c2 /\ s3 + w * c4 == a3 + b3 + c3 /\
                    s4 + w * c5 == a4 + b4 + c4 /\ s5 + w * c6 == a5 + b5 + c5)
          (ensures ev6 s0 s1 s2 s3 s4 s5 + w6 * c6 ==
                   ev6 a0 a1 a2 a3 a4 a5 + ev6 b0 b1 b2 b3 b4 b5 + c0)
  = ()

let add7 (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 s0 s1 s2 s3 s4 s5 s6 c0 c1 c2 c3 c4 c5 c6 c7: nat)
  : Lemma (requires s0 + w * c1 == a0 + b0 + c0 /\ s1 + w * c2 == a1 + b1 + c1 /\
                    s2 + w * c3 == a2 + b2 + c2 /\ s3 + w * c4 == a3 + b3 + c3 /\
                    s4 + w * c5 == a4 + b4 + c4 /\ s5 + w * c6 == a5 + b5 + c5 /\
                    s6 + w * c7 == a6 + b6 + c6)
          (ensures ev7 s0 s1 s2 s3 s4 s5 s6 + w7 * c7 ==
                   ev7 a0 a1 a2 a3 a4 a5 a6 + ev7 b0 b1 b2 b3 b4 b5 b6 + c0)
  = ()

let sub6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 s0 s1 s2 s3 s4 s5 c1 c2 c3 c4 c5 c6: nat)
  : Lemma (requires s0 - w * c1 == a0 - b0 /\ s1 - w * c2 == a1 - b1 - c1 /\
                    s2 - w * c3 == a2 - b2 - c2 /\ s3 - w * c4 == a3 - b3 - c3 /\
                    s4 - w * c5 == a4 - b4 - c4 /\ s5 - w * c6 == a5 - b5 - c5)
          (ensures ev6 s0 s1 s2 s3 s4 s5 - w6 * c6 ==
                   ev6 a0 a1 a2 a3 a4 a5 - ev6 b0 b1 b2 b3 b4 b5)
  = ()

let sub7 (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 s0 s1 s2 s3 s4 s5 s6 c1 c2 c3 c4 c5 c6 c7: nat)
  : Lemma (requires s0 - w * c1 == a0 - b0 /\ s1 - w * c2 == a1 - b1 - c1 /\
                    s2 - w * c3 == a2 - b2 - c2 /\ s3 - w * c4 == a3 - b3 - c3 /\
                    s4 - w * c5 == a4 - b4 - c4 /\ s5 - w * c6 == a5 - b5 - c5 /\
                    s6 - w * c7 == a6 - b6 - c6)
          (ensures ev7 s0 s1 s2 s3 s4 s5 s6 - w7 * c7 ==
                   ev7 a0 a1 a2 a3 a4 a5 a6 - ev7 b0 b1 b2 b3 b4 b5 b6)
  = ()

(** Six double words [l + 2^64 h], one word apart. *)
let row7 (l0 l1 l2 l3 l4 l5 h0 h1 h2 h3 h4 h5 p0 p1 p2 p3 p4 p5: nat)
  : Lemma (requires l0 + w * h0 == p0 /\ l1 + w * h1 == p1 /\ l2 + w * h2 == p2 /\
                    l3 + w * h3 == p3 /\ l4 + w * h4 == p4 /\ l5 + w * h5 == p5)
          (ensures ev7 l0 l1 l2 l3 l4 l5 0 + ev7 0 h0 h1 h2 h3 h4 h5 == ev6 p0 p1 p2 p3 p4 p5)
  = ()

(** [u 2^32] split by the two shifts. *)
let shift_val (u lo hi: nat)
  : Lemma (requires u < w /\ lo == (u * pow2 32) % pow2 64 /\ hi == u / pow2 32)
          (ensures u * 4294967296 == lo + w * hi /\ hi < 4294967296)
  = assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 64 == w);
    Math.lemma_div_mod u 4294967296;
    Math.lemma_mod_plus ((u % 4294967296) * 4294967296) hi w;
    Math.small_mod ((u % 4294967296) * 4294967296) w

(** [p = 2^384 - 2^128 - 2^96 + 2^32 - 1], so [2^384 u - u p] is
    [u (2^128 + 2^96 - 2^32 + 1)]: three words and a bit, from [u], its
    shifts and a borrow chain. *)
let kval (u lo hi r0 e1 e2 k2 k3 bb0 bb1 bb2: nat)
  : Lemma (requires u < w /\ lo < w /\ hi < 4294967296 /\ r0 < w /\ e1 < w /\ e2 < w /\
                    k2 < w /\ bb0 <= 1 /\ bb1 <= 1 /\ bb2 <= 1 /\
                    u * 4294967296 == lo + w * hi /\
                    r0 - w * bb0 == u - lo /\ e1 - w * bb1 == lo - hi - bb0 /\
                    e2 - w * bb2 == hi - 0 - bb1 /\ k2 + w * k3 == e2 + u + 0)
          (ensures bb2 == 0 /\ r0 + w * ev7 e1 k2 k3 0 0 0 0 == u * w6 - u * pp)
  = ()

(** The low word of [2^384 u - u p] is [s0]: the reduction clears it. *)
let r0_eq (s0 r0 m n: int)
  : Lemma (requires 0 <= s0 /\ s0 < w /\ 0 <= r0 /\ r0 < w /\ r0 + m == w * n /\
                    (s0 + m % pow2 64) % pow2 64 == 0)
          (ensures r0 == s0)
  = assert_norm (pow2 64 == w);
    Math.lemma_mod_plus_distr_r s0 m w;
    Math.lemma_mod_plus (s0 - r0) n w;
    if s0 >= r0 then Math.small_mod (s0 - r0) w
    else (Math.lemma_mod_plus (s0 - r0) 1 w; Math.small_mod (s0 - r0 + w) w)

(** [(s + u p) / 2^64] where [s = a + x b]: [u] goes in at the top, the
    three words [e1 k2 k3] (with [s0] below them) come off. *)
let step_val (a xb s0 s1 s2 s3 s4 s5 s6 s7 u e1 k2 k3 g v6 s7' t1 t2 t3 t4 t5 t6 t7 d8: nat)
  : Lemma (requires ev7 s0 s1 s2 s3 s4 s5 s6 + w7 * s7 == a + xb /\
                    s0 + w * ev7 e1 k2 k3 0 0 0 0 == u * w6 - u * pp /\
                    v6 + w * g == s6 + u /\ s7' == s7 + g /\
                    ev7 t1 t2 t3 t4 t5 t6 t7 - w7 * d8 ==
                      ev7 s1 s2 s3 s4 s5 v6 s7' - ev7 e1 k2 k3 0 0 0 0 /\
                    t1 < w /\ t2 < w /\ t3 < w /\ t4 < w /\ t5 < w /\ t6 < w /\ t7 < w /\ d8 <= 1 /\
                    a < 2 * pp /\ xb <= (w - 1) * (pp - 1) /\ u < w)
          (ensures d8 == 0 /\ w * ev7 t1 t2 t3 t4 t5 t6 t7 == a + xb + u * pp /\
                   ev7 t1 t2 t3 t4 t5 t6 t7 < 2 * pp)
  = ()

let row_bound (r x: nat) (c: nat)
  : Lemma (requires r + w7 * c == x /\ x < w7) (ensures c == 0) = ()

let add_sel (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 o0 o1 o2 o3 o4 o5: nat) (bb: nat)
  : Lemma (requires bb <= 1 /\
                    (bb == 1 ==> (o0 == a0 /\ o1 == a1 /\ o2 == a2 /\ o3 == a3 /\ o4 == a4 /\ o5 == a5)) /\
                    (bb == 0 ==> (o0 == b0 /\ o1 == b1 /\ o2 == b2 /\ o3 == b3 /\ o4 == b4 /\ o5 == b5)))
          (ensures ev6 o0 o1 o2 o3 o4 o5 ==
                   (if bb = 1 then ev6 a0 a1 a2 a3 a4 a5 else ev6 b0 b1 b2 b3 b4 b5))
  = ()

let mask_ok (b: nat)
  : Lemma (requires b <= 1)
          (ensures (0 - b) % pow2 64 == (if b = 0 then 0 else pow2 64 - 1))
  = assert_norm (pow2 64 == w);
    if b = 0 then () else Math.lemma_mod_plus (-1) 1 w

let modp_ok (x o: int)
  : Lemma (requires 0 <= o /\ o < pp /\ (o == x \/ o == x - pp \/ o == x + pp))
          (ensures o == x % pp)
  = Math.small_mod o pp;
    Math.lemma_mod_plus o 1 pp;
    Math.lemma_mod_plus o (-1) pp

(** One conditional subtraction: [x] in seven words is [x6 2^384 + r];
    [s - 2^448 b = x - p]; the output [o] is [r] if [b] else [s]. *)
let csub_ok (x x6 s6 b r s o: nat)
  : Lemma (requires x < 2 * pp /\ b <= 1 /\ x == r + w6 * x6 /\ r < w6 /\ s < w6 /\
                    (s + w6 * s6) - w7 * b == x - pp /\ s6 < w /\
                    o == (if b = 1 then r else s))
          (ensures o < pp /\ o == x % pp)
  = if b = 1 then modp_ok x o else modp_ok x o

(** [s - 2^384 c = a - b]; [q] is [p] if [c] else zero; [d + 2^384 e = s + q]. *)
let fsub_ok (a b c e s q d: nat)
  : Lemma (requires a < pp /\ b < pp /\ c <= 1 /\ s < w6 /\ d < w6 /\
                    s - w6 * c == a - b /\ q == (if c = 1 then pp else 0) /\
                    d + w6 * e == s + q)
          (ensures d == (a + pp - b) % pp)
  = modp_ok (a + pp - b) d

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

[@@ CInline; CPrologue "__attribute__((always_inline))"]
inline_for_extraction noextract
let mu (s0: S64.t)
  : u:S64.t{(S64.v s0 + (S64.v u * 4294967295) % pow2 64) % pow2 64 == 0}
  = let u = S64.mul_mod s0 (S64.classify 0x100000001uL) in
    mu_ok (S64.v s0) (S64.v u);
    u

fn put6 (o: A.array S64.t) (x0 x1 x2 x3 x4 x5: S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 6)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 6 /\
        fv vo' == ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5))
{
  A.pts_to_len o;
  A.((o.(0sz) <- x0));
  A.((o.(1sz) <- x1));
  A.((o.(2sz) <- x2));
  A.((o.(3sz) <- x3));
  A.((o.(4sz) <- x4));
  A.((o.(5sz) <- x5));
}

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn put7 (o: A.array S64.t) (x0 x1 x2 x3 x4 x5 x6: S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 7)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 7 /\ F64.ix vo' 0 == S64.v x0 /\
        av vo' == ev7 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5) (S64.v x6))
{
  A.pts_to_len o;
  A.((o.(0sz) <- x0));
  A.((o.(1sz) <- x1));
  A.((o.(2sz) <- x2));
  A.((o.(3sz) <- x3));
  A.((o.(4sz) <- x4));
  A.((o.(5sz) <- x5));
  A.((o.(6sz) <- x6));
}

(** {2 Montgomery multiplication} *)

(** [x b] as seven words. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn xrow (q: A.array S64.t) (x b0 b1 b2 b3 b4 b5: S64.t) (#vq: erased (Seq.seq S64.t))
requires A.pts_to q vq **
  pure (Seq.length vq == 7 /\
        ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5) < pp)
ensures exists* (vq': Seq.seq S64.t).
  A.pts_to q vq' **
  pure (Seq.length vq' == 7 /\
        av vq' == S64.v x * ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5))
{
  let z0 = S64.classify 0uL;
  consts ();
  let m0 = S128.mul_wide x b0;
  let l0 = L.lo m0;
  let h0 = L.hi m0;
  L.lo_hi m0;
  let m1 = S128.mul_wide x b1;
  let l1 = L.lo m1;
  let h1 = L.hi m1;
  L.lo_hi m1;
  let m2 = S128.mul_wide x b2;
  let l2 = L.lo m2;
  let h2 = L.hi m2;
  L.lo_hi m2;
  let m3 = S128.mul_wide x b3;
  let l3 = L.lo m3;
  let h3 = L.hi m3;
  L.lo_hi m3;
  let m4 = S128.mul_wide x b4;
  let l4 = L.lo m4;
  let h4 = L.hi m4;
  L.lo_hi m4;
  let m5 = S128.mul_wide x b5;
  let l5 = L.lo m5;
  let h5 = L.hi m5;
  L.lo_hi m5;
  let mut r = z0;
  let c2 = K.addc z0 l1 h0 r;
  let r1 = !r;
  let c3 = K.addc c2 l2 h1 r;
  let r2 = !r;
  let c4 = K.addc c3 l3 h2 r;
  let r3 = !r;
  let c5 = K.addc c4 l4 h3 r;
  let r4 = !r;
  let c6 = K.addc c5 l5 h4 r;
  let r5 = !r;
  let c7 = K.addc c6 z0 h5 r;
  let r6 = !r;
  add7 (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3) (S64.v l4) (S64.v l5) 0
       0 (S64.v h0) (S64.v h1) (S64.v h2) (S64.v h3) (S64.v h4) (S64.v h5)
       (S64.v l0) (S64.v r1) (S64.v r2) (S64.v r3) (S64.v r4) (S64.v r5) (S64.v r6)
       0 0 (S64.v c2) (S64.v c3) (S64.v c4) (S64.v c5) (S64.v c6) (S64.v c7);
  row7 (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3) (S64.v l4) (S64.v l5)
       (S64.v h0) (S64.v h1) (S64.v h2) (S64.v h3) (S64.v h4) (S64.v h5)
       (S64.v x * S64.v b0) (S64.v x * S64.v b1) (S64.v x * S64.v b2)
       (S64.v x * S64.v b3) (S64.v x * S64.v b4) (S64.v x * S64.v b5);
  dist6 (S64.v x) (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5);
  prod_le (S64.v x) (ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5));
  row_bound (ev7 (S64.v l0) (S64.v r1) (S64.v r2) (S64.v r3) (S64.v r4) (S64.v r5) (S64.v r6))
            (S64.v x * ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5))
            (S64.v c7);
  put7 q l0 r1 r2 r3 r4 r5 r6;
}

#restart-solver

(** [acc := (acc + x b + u p) / 2^64], with [u] chosen to make the
    division exact. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn step (acc: A.array S64.t) (x b0 b1 b2 b3 b4 b5: S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to acc va **
  pure (Seq.length va == 7 /\ av va < 2 * pp /\
        ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5) < pp)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to acc va' **
  pure (Seq.length va' == 7 /\ av va' < 2 * pp /\
        (w * av va') % pp ==
          (av va + S64.v x * ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5)) % pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len acc;
  consts ();
  let z = z0;
  let mut q = [| z; 7sz |];
  Mem.track q;
  A.pts_to_len q;
  xrow q x b0 b1 b2 b3 b4 b5;
  with vq. assert (A.pts_to q vq);
  prod_le (S64.v x) (ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5));
  let a0 = A.(acc.(0sz));
  let a1 = A.(acc.(1sz));
  let a2 = A.(acc.(2sz));
  let a3 = A.(acc.(3sz));
  let a4 = A.(acc.(4sz));
  let a5 = A.(acc.(5sz));
  let a6 = A.(acc.(6sz));
  let x0 = A.(q.(0sz));
  let x1 = A.(q.(1sz));
  let x2 = A.(q.(2sz));
  let x3 = A.(q.(3sz));
  let x4 = A.(q.(4sz));
  let x5 = A.(q.(5sz));
  let x6 = A.(q.(6sz));
  let mut r = z0;
  let c1 = K.addc z0 a0 x0 r;
  let s0 = !r;
  let c2 = K.addc c1 a1 x1 r;
  let s1 = !r;
  let c3 = K.addc c2 a2 x2 r;
  let s2 = !r;
  let c4 = K.addc c3 a3 x3 r;
  let s3 = !r;
  let c5 = K.addc c4 a4 x4 r;
  let s4 = !r;
  let c6 = K.addc c5 a5 x5 r;
  let s5 = !r;
  let s7 = K.addc c6 a6 x6 r;
  let s6 = !r;
  add7 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) (S64.v a6)
       (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5) (S64.v x6)
       (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v s6)
       0 (S64.v c1) (S64.v c2) (S64.v c3) (S64.v c4) (S64.v c5) (S64.v c6) (S64.v s7);
  let u = mu s0;
  let lo = S64.shift_left u 32ul;
  let hi = S64.shift_right u 32ul;
  shift_val (S64.v u) (S64.v lo) (S64.v hi);
  let bb0 = K.subb z0 u lo r;
  let r0 = !r;
  let bb1 = K.subb bb0 lo hi r;
  let e1 = !r;
  let bb2 = K.subb bb1 hi z0 r;
  let e2 = !r;
  let k3 = K.addc z0 e2 u r;
  let k2 = !r;
  kval (S64.v u) (S64.v lo) (S64.v hi) (S64.v r0) (S64.v e1) (S64.v e2) (S64.v k2) (S64.v k3)
       (S64.v bb0) (S64.v bb1) (S64.v bb2);
  r0_eq (S64.v s0) (S64.v r0) (S64.v u * 4294967295)
        (S64.v u * 18446744078004518912 - ev7 (S64.v e1) (S64.v k2) (S64.v k3) 0 0 0 0);
  let g = K.addc z0 s6 u r;
  let v6 = !r;
  let g2 = K.addc g s7 z0 r;
  let s7' = !r;
  let d2 = K.subb z0 s1 e1 r;
  let t1 = !r;
  let d3 = K.subb d2 s2 k2 r;
  let t2 = !r;
  let d4 = K.subb d3 s3 k3 r;
  let t3 = !r;
  let d5 = K.subb d4 s4 z0 r;
  let t4 = !r;
  let d6 = K.subb d5 s5 z0 r;
  let t5 = !r;
  let d7 = K.subb d6 v6 z0 r;
  let t6 = !r;
  let d8 = K.subb d7 s7' z0 r;
  let t7 = !r;
  sub7 (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v v6) (S64.v s7')
       (S64.v e1) (S64.v k2) (S64.v k3) 0 0 0 0
       (S64.v t1) (S64.v t2) (S64.v t3) (S64.v t4) (S64.v t5) (S64.v t6) (S64.v t7)
       (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5) (S64.v d6) (S64.v d7) (S64.v d8);
  step_val (av va) (av vq)
           (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v s6) (S64.v s7)
           (S64.v u) (S64.v e1) (S64.v k2) (S64.v k3) (S64.v g) (S64.v v6) (S64.v s7')
           (S64.v t1) (S64.v t2) (S64.v t3) (S64.v t4) (S64.v t5) (S64.v t6) (S64.v t7)
           (S64.v d8);
  put7 acc t1 t2 t3 t4 t5 t6 t7;
  with va'. assert (A.pts_to acc va');
  step_mod (av va') (av va) (av vq) (S64.v u);
  Mem.nowipe q;
}

#restart-solver

(** [acc < 2 p] to [acc mod p]: one conditional subtraction of [p]. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn csub (o t: A.array S64.t) (#vo: erased (Seq.seq S64.t))
        (#pt: perm) (#vt: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to t #pt vt **
  pure (Seq.length vo == 6 /\ Seq.length vt == 7 /\ av vt < 2 * pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to t #pt vt **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ fv vo' == av vt % pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let r0 = A.(t.(0sz));
  let r1 = A.(t.(1sz));
  let r2 = A.(t.(2sz));
  let r3 = A.(t.(3sz));
  let r4 = A.(t.(4sz));
  let r5 = A.(t.(5sz));
  let r6 = A.(t.(6sz));
  let ones = S64.classify 0xffffffffffffffffuL;
  let mut r = z0;
  let b1 = K.subb z0 r0 (S64.classify 0xffffffffuL) r;
  let s0 = !r;
  let b2 = K.subb b1 r1 (S64.classify 0xffffffff00000000uL) r;
  let s1 = !r;
  let b3 = K.subb b2 r2 (S64.classify 0xfffffffffffffffeuL) r;
  let s2 = !r;
  let b4 = K.subb b3 r3 ones r;
  let s3 = !r;
  let b5 = K.subb b4 r4 ones r;
  let s4 = !r;
  let b6 = K.subb b5 r5 ones r;
  let s5 = !r;
  let b = K.subb b6 r6 z0 r;
  let s6 = !r;
  sub7 (S64.v r0) (S64.v r1) (S64.v r2) (S64.v r3) (S64.v r4) (S64.v r5) (S64.v r6)
       4294967295 18446744069414584320 18446744073709551614
       18446744073709551615 18446744073709551615 18446744073709551615 0
       (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v s6)
       (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5) (S64.v b6) (S64.v b);
  mask_ok (S64.v b);
  let m = S64.sub_mod z0 b;
  let o0 = S64.select m r0 s0;
  let o1 = S64.select m r1 s1;
  let o2 = S64.select m r2 s2;
  let o3 = S64.select m r3 s3;
  let o4 = S64.select m r4 s4;
  let o5 = S64.select m r5 s5;
  add_sel (S64.v r0) (S64.v r1) (S64.v r2) (S64.v r3) (S64.v r4) (S64.v r5)
          (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5)
          (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) (S64.v o4) (S64.v o5) (S64.v b);
  csub_ok (av vt) (S64.v r6) (S64.v s6) (S64.v b)
          (ev6 (S64.v r0) (S64.v r1) (S64.v r2) (S64.v r3) (S64.v r4) (S64.v r5))
          (ev6 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5))
          (ev6 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) (S64.v o4) (S64.v o5));
  put6 o o0 o1 o2 o3 o4 o5;
}

#restart-solver

(** Montgomery's product of two numbers below [p], given as words:
    [2^384 z = a b mod p]. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn mont (out: A.array S64.t) (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5: S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo **
  pure (Seq.length vo == 6 /\
        ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) < pp /\
        ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5) < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\
        (w6 * fv vo') % pp ==
          (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) *
           ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5)) % pp)
{
  let z = S64.classify 0uL;
  let mut acc = [| z; 7sz |];
  Mem.track acc;
  A.pts_to_len acc;
  with v0. assert (A.pts_to acc v0);
  assert (pure (av v0 == 0));
  step acc a0 b0 b1 b2 b3 b4 b5;
  with v1. assert (A.pts_to acc v1);
  step acc a1 b0 b1 b2 b3 b4 b5;
  with v2. assert (A.pts_to acc v2);
  step acc a2 b0 b1 b2 b3 b4 b5;
  with v3. assert (A.pts_to acc v3);
  step acc a3 b0 b1 b2 b3 b4 b5;
  with v4. assert (A.pts_to acc v4);
  step acc a4 b0 b1 b2 b3 b4 b5;
  with v5. assert (A.pts_to acc v5);
  step acc a5 b0 b1 b2 b3 b4 b5;
  with v6. assert (A.pts_to acc v6);
  chain6 (av v1) (av v2) (av v3) (av v4) (av v5) (av v6)
         (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)
         (ev6 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) (S64.v b4) (S64.v b5));
  csub out acc;
  with o. assert (A.pts_to out o);
  mod_out (fv o) (av v6);
  Mem.nowipe acc;
}

(** {2 Squaring}

    A square has fifteen distinct cross products, each counted twice, and
    six squares: twenty-one multiplications rather than {!mont}'s thirty-six.
    {!sq_cross} adds the cross products row by row into ten words,
    {!sq_diag} doubles them and adds the squares (both, with their carry
    lemmas, generated by [spec/group-gen/p384/sqr.py]), and {!msqr} reduces the
    twelve words: six reduction-only {!rstep}s take the low half [L] to
    [(L + U p) / 2^384 <= p], which the high half [H < p] joins below [2 p]
    for {!csub}.  Every carry chain is linear once the products are named,
    and bounded because each product is at most [(2^64 - 1)^2]. *)

unfold let w9 : pos = 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136
unfold let w10 : pos = 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776
unfold let w11 : pos = 84162174424773976115855838126082058648805436845170781751972494449099714468753293153818664580441415219631727501698851483408310916002940861810045036330430093599283578738055113571066620126149163476340692027772502016

(** The number twelve words stand for. *)
let tv (s: Seq.seq S64.t) : GTot nat =
  F64.ix s 0 + w * F64.ix s 1 + w2 * F64.ix s 2 + w3 * F64.ix s 3 + w4 * F64.ix s 4 +
  w5 * F64.ix s 5 + w6 * F64.ix s 6 + w7 * F64.ix s 7 + w8 * F64.ix s 8 +
  w9 * F64.ix s 9 + w10 * F64.ix s 10 + w11 * F64.ix s 11

let pbound (x y: nat)
  : Lemma (requires x < w /\ y < w) (ensures x * y <= 340282366920938463426481119284349108225)
  = Math.lemma_mult_le_right y x (w - 1);
    Math.lemma_mult_le_left (w - 1) y (w - 1)

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn put12 (o: A.array S64.t) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11: S64.t)
         (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 12)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 12 /\ F64.ix vo' 0 == S64.v x0 /\ F64.ix vo' 11 == S64.v x11 /\
        tv vo' == S64.v x0 + w * S64.v x1 + w2 * S64.v x2 + w3 * S64.v x3 + w4 * S64.v x4 +
                  w5 * S64.v x5 + w6 * S64.v x6 + w7 * S64.v x7 + w8 * S64.v x8 +
                  w9 * S64.v x9 + w10 * S64.v x10 + w11 * S64.v x11)
{
  A.pts_to_len o;
  A.((o.(0sz) <- x0));
  A.((o.(1sz) <- x1));
  A.((o.(2sz) <- x2));
  A.((o.(3sz) <- x3));
  A.((o.(4sz) <- x4));
  A.((o.(5sz) <- x5));
  A.((o.(6sz) <- x6));
  A.((o.(7sz) <- x7));
  A.((o.(8sz) <- x8));
  A.((o.(9sz) <- x9));
  A.((o.(10sz) <- x10));
  A.((o.(11sz) <- x11));
}

let sqx0 (p01 p02 p03 p04 p05 l1 l2 l3 l4 l5 h1 h2 h3 h4 h5 q2 cq2 q3 cq3 q4 cq4 q5 cq5 q6 cq6: nat)
  : Lemma (requires p01 <= 340282366920938463426481119284349108225 /\
                    p02 <= 340282366920938463426481119284349108225 /\
                    p03 <= 340282366920938463426481119284349108225 /\
                    p04 <= 340282366920938463426481119284349108225 /\
                    p05 <= 340282366920938463426481119284349108225 /\
                    l1 < w /\ h1 < w /\ l1 + w * h1 == p01 /\
                    l2 < w /\ h2 < w /\ l2 + w * h2 == p02 /\
                    l3 < w /\ h3 < w /\ l3 + w * h3 == p03 /\
                    l4 < w /\ h4 < w /\ l4 + w * h4 == p04 /\
                    l5 < w /\ h5 < w /\ l5 + w * h5 == p05 /\
                    q2 < w /\ cq2 <= 1 /\
                    q3 < w /\ cq3 <= 1 /\
                    q4 < w /\ cq4 <= 1 /\
                    q5 < w /\ cq5 <= 1 /\
                    q6 < w /\ cq6 <= 1 /\
                    q2 + w * cq2 == l2 + h1 + 0 /\
                    q3 + w * cq3 == l3 + h2 + cq2 /\
                    q4 + w * cq4 == l4 + h3 + cq3 /\
                    q5 + w * cq5 == l5 + h4 + cq4 /\
                    q6 + w * cq6 == h5 + cq5)
          (ensures w * l1 + w2 * q2 + w3 * q3 + w4 * q4 + w5 * q5 + w6 * q6 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05)
  = ()

let sqx1 (p01 p02 p03 p04 p05 p12 p13 p14 p15 l2 l3 l4 l5 h2 h3 h4 h5 o1 o2 o3 o4 o5 o6 q4 cq4 q5 cq5 q6 cq6 q7 cq7 n3 ca3 n4 ca4 n5 ca5 n6 ca6 n7 ca7: nat)
  : Lemma (requires p01 <= 340282366920938463426481119284349108225 /\
                    p02 <= 340282366920938463426481119284349108225 /\
                    p03 <= 340282366920938463426481119284349108225 /\
                    p04 <= 340282366920938463426481119284349108225 /\
                    p05 <= 340282366920938463426481119284349108225 /\
                    p12 <= 340282366920938463426481119284349108225 /\
                    p13 <= 340282366920938463426481119284349108225 /\
                    p14 <= 340282366920938463426481119284349108225 /\
                    p15 <= 340282366920938463426481119284349108225 /\
                    l2 < w /\ h2 < w /\ l2 + w * h2 == p12 /\
                    l3 < w /\ h3 < w /\ l3 + w * h3 == p13 /\
                    l4 < w /\ h4 < w /\ l4 + w * h4 == p14 /\
                    l5 < w /\ h5 < w /\ l5 + w * h5 == p15 /\
                    o1 < w /\
                    o2 < w /\
                    o3 < w /\
                    o4 < w /\
                    o5 < w /\
                    o6 < w /\
                    w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * o5 + w6 * o6 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 /\
                    q4 < w /\ cq4 <= 1 /\
                    q5 < w /\ cq5 <= 1 /\
                    q6 < w /\ cq6 <= 1 /\
                    q7 < w /\ cq7 <= 1 /\
                    n3 < w /\ ca3 <= 1 /\
                    n4 < w /\ ca4 <= 1 /\
                    n5 < w /\ ca5 <= 1 /\
                    n6 < w /\ ca6 <= 1 /\
                    n7 < w /\ ca7 <= 1 /\
                    q4 + w * cq4 == l3 + h2 + 0 /\
                    q5 + w * cq5 == l4 + h3 + cq4 /\
                    q6 + w * cq6 == l5 + h4 + cq5 /\
                    q7 + w * cq7 == h5 + cq6 /\
                    n3 + w * ca3 == o3 + l2 + 0 /\
                    n4 + w * ca4 == o4 + q4 + ca3 /\
                    n5 + w * ca5 == o5 + q5 + ca4 /\
                    n6 + w * ca6 == o6 + q6 + ca5 /\
                    n7 + w * ca7 == q7 + ca6)
          (ensures w * o1 + w2 * o2 + w3 * n3 + w4 * n4 + w5 * n5 + w6 * n6 + w7 * n7 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15)
  = ()

let sqx2 (p01 p02 p03 p04 p05 p12 p13 p14 p15 p23 p24 p25 l3 l4 l5 h3 h4 h5 o1 o2 o3 o4 o5 o6 o7 q6 cq6 q7 cq7 q8 cq8 n5 ca5 n6 ca6 n7 ca7 n8 ca8: nat)
  : Lemma (requires p01 <= 340282366920938463426481119284349108225 /\
                    p02 <= 340282366920938463426481119284349108225 /\
                    p03 <= 340282366920938463426481119284349108225 /\
                    p04 <= 340282366920938463426481119284349108225 /\
                    p05 <= 340282366920938463426481119284349108225 /\
                    p12 <= 340282366920938463426481119284349108225 /\
                    p13 <= 340282366920938463426481119284349108225 /\
                    p14 <= 340282366920938463426481119284349108225 /\
                    p15 <= 340282366920938463426481119284349108225 /\
                    p23 <= 340282366920938463426481119284349108225 /\
                    p24 <= 340282366920938463426481119284349108225 /\
                    p25 <= 340282366920938463426481119284349108225 /\
                    l3 < w /\ h3 < w /\ l3 + w * h3 == p23 /\
                    l4 < w /\ h4 < w /\ l4 + w * h4 == p24 /\
                    l5 < w /\ h5 < w /\ l5 + w * h5 == p25 /\
                    o1 < w /\
                    o2 < w /\
                    o3 < w /\
                    o4 < w /\
                    o5 < w /\
                    o6 < w /\
                    o7 < w /\
                    w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * o5 + w6 * o6 + w7 * o7 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 /\
                    q6 < w /\ cq6 <= 1 /\
                    q7 < w /\ cq7 <= 1 /\
                    q8 < w /\ cq8 <= 1 /\
                    n5 < w /\ ca5 <= 1 /\
                    n6 < w /\ ca6 <= 1 /\
                    n7 < w /\ ca7 <= 1 /\
                    n8 < w /\ ca8 <= 1 /\
                    q6 + w * cq6 == l4 + h3 + 0 /\
                    q7 + w * cq7 == l5 + h4 + cq6 /\
                    q8 + w * cq8 == h5 + cq7 /\
                    n5 + w * ca5 == o5 + l3 + 0 /\
                    n6 + w * ca6 == o6 + q6 + ca5 /\
                    n7 + w * ca7 == o7 + q7 + ca6 /\
                    n8 + w * ca8 == q8 + ca7)
          (ensures w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * n5 + w6 * n6 + w7 * n7 + w8 * n8 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25)
  = ()

let sqx3 (p01 p02 p03 p04 p05 p12 p13 p14 p15 p23 p24 p25 p34 p35 l4 l5 h4 h5 o1 o2 o3 o4 o5 o6 o7 o8 q8 cq8 q9 cq9 n7 ca7 n8 ca8 n9 ca9: nat)
  : Lemma (requires p01 <= 340282366920938463426481119284349108225 /\
                    p02 <= 340282366920938463426481119284349108225 /\
                    p03 <= 340282366920938463426481119284349108225 /\
                    p04 <= 340282366920938463426481119284349108225 /\
                    p05 <= 340282366920938463426481119284349108225 /\
                    p12 <= 340282366920938463426481119284349108225 /\
                    p13 <= 340282366920938463426481119284349108225 /\
                    p14 <= 340282366920938463426481119284349108225 /\
                    p15 <= 340282366920938463426481119284349108225 /\
                    p23 <= 340282366920938463426481119284349108225 /\
                    p24 <= 340282366920938463426481119284349108225 /\
                    p25 <= 340282366920938463426481119284349108225 /\
                    p34 <= 340282366920938463426481119284349108225 /\
                    p35 <= 340282366920938463426481119284349108225 /\
                    l4 < w /\ h4 < w /\ l4 + w * h4 == p34 /\
                    l5 < w /\ h5 < w /\ l5 + w * h5 == p35 /\
                    o1 < w /\
                    o2 < w /\
                    o3 < w /\
                    o4 < w /\
                    o5 < w /\
                    o6 < w /\
                    o7 < w /\
                    o8 < w /\
                    w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * o5 + w6 * o6 + w7 * o7 + w8 * o8 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25 /\
                    q8 < w /\ cq8 <= 1 /\
                    q9 < w /\ cq9 <= 1 /\
                    n7 < w /\ ca7 <= 1 /\
                    n8 < w /\ ca8 <= 1 /\
                    n9 < w /\ ca9 <= 1 /\
                    q8 + w * cq8 == l5 + h4 + 0 /\
                    q9 + w * cq9 == h5 + cq8 /\
                    n7 + w * ca7 == o7 + l4 + 0 /\
                    n8 + w * ca8 == o8 + q8 + ca7 /\
                    n9 + w * ca9 == q9 + ca8)
          (ensures w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * o5 + w6 * o6 + w7 * n7 + w8 * n8 + w9 * n9 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25 + w7 * p34 + w8 * p35)
  = ()

let sqx4 (p01 p02 p03 p04 p05 p12 p13 p14 p15 p23 p24 p25 p34 p35 p45 l5 h5 o1 o2 o3 o4 o5 o6 o7 o8 o9 q10 cq10 n9 ca9 n10 ca10: nat)
  : Lemma (requires p01 <= 340282366920938463426481119284349108225 /\
                    p02 <= 340282366920938463426481119284349108225 /\
                    p03 <= 340282366920938463426481119284349108225 /\
                    p04 <= 340282366920938463426481119284349108225 /\
                    p05 <= 340282366920938463426481119284349108225 /\
                    p12 <= 340282366920938463426481119284349108225 /\
                    p13 <= 340282366920938463426481119284349108225 /\
                    p14 <= 340282366920938463426481119284349108225 /\
                    p15 <= 340282366920938463426481119284349108225 /\
                    p23 <= 340282366920938463426481119284349108225 /\
                    p24 <= 340282366920938463426481119284349108225 /\
                    p25 <= 340282366920938463426481119284349108225 /\
                    p34 <= 340282366920938463426481119284349108225 /\
                    p35 <= 340282366920938463426481119284349108225 /\
                    p45 <= 340282366920938463426481119284349108225 /\
                    l5 < w /\ h5 < w /\ l5 + w * h5 == p45 /\
                    o1 < w /\
                    o2 < w /\
                    o3 < w /\
                    o4 < w /\
                    o5 < w /\
                    o6 < w /\
                    o7 < w /\
                    o8 < w /\
                    o9 < w /\
                    w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * o5 + w6 * o6 + w7 * o7 + w8 * o8 + w9 * o9 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25 + w7 * p34 + w8 * p35 /\
                    q10 < w /\ cq10 <= 1 /\
                    n9 < w /\ ca9 <= 1 /\
                    n10 < w /\ ca10 <= 1 /\
                    q10 + w * cq10 == h5 + 0 /\
                    n9 + w * ca9 == o9 + l5 + 0 /\
                    n10 + w * ca10 == q10 + ca9)
          (ensures w * o1 + w2 * o2 + w3 * o3 + w4 * o4 + w5 * o5 + w6 * o6 + w7 * o7 + w8 * o8 + w9 * n9 + w10 * n10 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25 + w7 * p34 + w8 * p35 + w9 * p45)
  = ()

let sqd (p00 p01 p02 p03 p04 p05 p11 p12 p13 p14 p15 p22 p23 p24 p25 p33 p34 p35 p44 p45 p55 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 s0 s1 s2 s3 s4 s5 g0 g1 g2 g3 g4 g5 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11: nat)
  : Lemma (requires p00 <= 340282366920938463426481119284349108225 /\
                    p01 <= 340282366920938463426481119284349108225 /\
                    p02 <= 340282366920938463426481119284349108225 /\
                    p03 <= 340282366920938463426481119284349108225 /\
                    p04 <= 340282366920938463426481119284349108225 /\
                    p05 <= 340282366920938463426481119284349108225 /\
                    p11 <= 340282366920938463426481119284349108225 /\
                    p12 <= 340282366920938463426481119284349108225 /\
                    p13 <= 340282366920938463426481119284349108225 /\
                    p14 <= 340282366920938463426481119284349108225 /\
                    p15 <= 340282366920938463426481119284349108225 /\
                    p22 <= 340282366920938463426481119284349108225 /\
                    p23 <= 340282366920938463426481119284349108225 /\
                    p24 <= 340282366920938463426481119284349108225 /\
                    p25 <= 340282366920938463426481119284349108225 /\
                    p33 <= 340282366920938463426481119284349108225 /\
                    p34 <= 340282366920938463426481119284349108225 /\
                    p35 <= 340282366920938463426481119284349108225 /\
                    p44 <= 340282366920938463426481119284349108225 /\
                    p45 <= 340282366920938463426481119284349108225 /\
                    p55 <= 340282366920938463426481119284349108225 /\
                    t1 < w /\
                    t2 < w /\
                    t3 < w /\
                    t4 < w /\
                    t5 < w /\
                    t6 < w /\
                    t7 < w /\
                    t8 < w /\
                    t9 < w /\
                    t10 < w /\
                    w * t1 + w2 * t2 + w3 * t3 + w4 * t4 + w5 * t5 + w6 * t6 + w7 * t7 + w8 * t8 + w9 * t9 + w10 * t10 == w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25 + w7 * p34 + w8 * p35 + w9 * p45 /\
                    d1 < w /\ e1 <= 1 /\
                    d2 < w /\ e2 <= 1 /\
                    d3 < w /\ e3 <= 1 /\
                    d4 < w /\ e4 <= 1 /\
                    d5 < w /\ e5 <= 1 /\
                    d6 < w /\ e6 <= 1 /\
                    d7 < w /\ e7 <= 1 /\
                    d8 < w /\ e8 <= 1 /\
                    d9 < w /\ e9 <= 1 /\
                    d10 < w /\ e10 <= 1 /\
                    s0 < w /\ g0 < w /\ s0 + w * g0 == p00 /\
                    s1 < w /\ g1 < w /\ s1 + w * g1 == p11 /\
                    s2 < w /\ g2 < w /\ s2 + w * g2 == p22 /\
                    s3 < w /\ g3 < w /\ s3 + w * g3 == p33 /\
                    s4 < w /\ g4 < w /\ s4 + w * g4 == p44 /\
                    s5 < w /\ g5 < w /\ s5 + w * g5 == p55 /\
                    u1 < w /\ f1 <= 1 /\
                    u2 < w /\ f2 <= 1 /\
                    u3 < w /\ f3 <= 1 /\
                    u4 < w /\ f4 <= 1 /\
                    u5 < w /\ f5 <= 1 /\
                    u6 < w /\ f6 <= 1 /\
                    u7 < w /\ f7 <= 1 /\
                    u8 < w /\ f8 <= 1 /\
                    u9 < w /\ f9 <= 1 /\
                    u10 < w /\ f10 <= 1 /\
                    u11 < w /\ f11 <= 1 /\
                    d1 + w * e1 == t1 + t1 + 0 /\
                    d2 + w * e2 == t2 + t2 + e1 /\
                    d3 + w * e3 == t3 + t3 + e2 /\
                    d4 + w * e4 == t4 + t4 + e3 /\
                    d5 + w * e5 == t5 + t5 + e4 /\
                    d6 + w * e6 == t6 + t6 + e5 /\
                    d7 + w * e7 == t7 + t7 + e6 /\
                    d8 + w * e8 == t8 + t8 + e7 /\
                    d9 + w * e9 == t9 + t9 + e8 /\
                    d10 + w * e10 == t10 + t10 + e9 /\
                    u1 + w * f1 == d1 + g0 + 0 /\
                    u2 + w * f2 == d2 + s1 + f1 /\
                    u3 + w * f3 == d3 + g1 + f2 /\
                    u4 + w * f4 == d4 + s2 + f3 /\
                    u5 + w * f5 == d5 + g2 + f4 /\
                    u6 + w * f6 == d6 + s3 + f5 /\
                    u7 + w * f7 == d7 + g3 + f6 /\
                    u8 + w * f8 == d8 + s4 + f7 /\
                    u9 + w * f9 == d9 + g4 + f8 /\
                    u10 + w * f10 == d10 + s5 + f9 /\
                    u11 + w * f11 == e10 + g5 + f10)
          (ensures s0 + w * u1 + w2 * u2 + w3 * u3 + w4 * u4 + w5 * u5 + w6 * u6 + w7 * u7 + w8 * u8 + w9 * u9 + w10 * u10 + w11 * u11 == p00 + w2 * p11 + w4 * p22 + w6 * p33 + w8 * p44 + w10 * p55 + 2 * (w * p01 + w2 * p02 + w3 * p03 + w4 * p04 + w5 * p05 + w3 * p12 + w4 * p13 + w5 * p14 + w6 * p15 + w5 * p23 + w6 * p24 + w7 * p25 + w7 * p34 + w8 * p35 + w9 * p45))
  = ()

let sq_expand (a0 a1 a2 a3 a4 a5: int)
  : Lemma (ev6 a0 a1 a2 a3 a4 a5 * ev6 a0 a1 a2 a3 a4 a5 ==
           (a0 * a0) + w2 * (a1 * a1) + w4 * (a2 * a2) + w6 * (a3 * a3) + w8 * (a4 * a4) + w10 * (a5 * a5) + 2 * (w * (a0 * a1) + w2 * (a0 * a2) + w3 * (a0 * a3) + w4 * (a0 * a4) + w5 * (a0 * a5) + w3 * (a1 * a2) + w4 * (a1 * a3) + w5 * (a1 * a4) + w6 * (a1 * a5) + w5 * (a2 * a3) + w6 * (a2 * a4) + w7 * (a2 * a5) + w7 * (a3 * a4) + w8 * (a3 * a5) + w9 * (a4 * a5)))
  = assert (ev6 a0 a1 a2 a3 a4 a5 * ev6 a0 a1 a2 a3 a4 a5 ==
           (a0 * a0) + w2 * (a1 * a1) + w4 * (a2 * a2) + w6 * (a3 * a3) + w8 * (a4 * a4) + w10 * (a5 * a5) + 2 * (w * (a0 * a1) + w2 * (a0 * a2) + w3 * (a0 * a3) + w4 * (a0 * a4) + w5 * (a0 * a5) + w3 * (a1 * a2) + w4 * (a1 * a3) + w5 * (a1 * a4) + w6 * (a1 * a5) + w5 * (a2 * a3) + w6 * (a2 * a4) + w7 * (a2 * a5) + w7 * (a3 * a4) + w8 * (a3 * a5) + w9 * (a4 * a5)))
      by (T.norm [delta_only [`%ev6; `%w; `%w2; `%w3; `%w4; `%w5; `%w6; `%w7; `%w8; `%w9; `%w10; `%w11]];
          Canon.int_semiring ())

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn sq_cross (t: A.array S64.t) (a0 a1 a2 a3 a4 a5: S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt ** pure (Seq.length vt == 12)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 12 /\ F64.ix vt' 0 == 0 /\ F64.ix vt' 11 == 0 /\ tv vt' == w * (S64.v a0 * S64.v a1) + w2 * (S64.v a0 * S64.v a2) + w3 * (S64.v a0 * S64.v a3) + w4 * (S64.v a0 * S64.v a4) + w5 * (S64.v a0 * S64.v a5) + w3 * (S64.v a1 * S64.v a2) + w4 * (S64.v a1 * S64.v a3) + w5 * (S64.v a1 * S64.v a4) + w6 * (S64.v a1 * S64.v a5) + w5 * (S64.v a2 * S64.v a3) + w6 * (S64.v a2 * S64.v a4) + w7 * (S64.v a2 * S64.v a5) + w7 * (S64.v a3 * S64.v a4) + w8 * (S64.v a3 * S64.v a5) + w9 * (S64.v a4 * S64.v a5))
{
  let z0 = S64.classify 0uL;
  consts ();
  let mut r = z0;
  let m01 = S128.mul_wide a0 a1;
  let l01 = L.lo m01;
  let h01 = L.hi m01;
  L.lo_hi m01;
  pbound (S64.v a0) (S64.v a1);
  let m02 = S128.mul_wide a0 a2;
  let l02 = L.lo m02;
  let h02 = L.hi m02;
  L.lo_hi m02;
  pbound (S64.v a0) (S64.v a2);
  let m03 = S128.mul_wide a0 a3;
  let l03 = L.lo m03;
  let h03 = L.hi m03;
  L.lo_hi m03;
  pbound (S64.v a0) (S64.v a3);
  let m04 = S128.mul_wide a0 a4;
  let l04 = L.lo m04;
  let h04 = L.hi m04;
  L.lo_hi m04;
  pbound (S64.v a0) (S64.v a4);
  let m05 = S128.mul_wide a0 a5;
  let l05 = L.lo m05;
  let h05 = L.hi m05;
  L.lo_hi m05;
  pbound (S64.v a0) (S64.v a5);
  let cq0_2 = K.addc z0 l02 h01 r;
  let q0_2 = !r;
  let cq0_3 = K.addc cq0_2 l03 h02 r;
  let q0_3 = !r;
  let cq0_4 = K.addc cq0_3 l04 h03 r;
  let q0_4 = !r;
  let cq0_5 = K.addc cq0_4 l05 h04 r;
  let q0_5 = !r;
  let cq0_6 = K.addc cq0_5 z0 h05 r;
  let q0_6 = !r;
  sqx0 (S64.v a0 * S64.v a1) (S64.v a0 * S64.v a2) (S64.v a0 * S64.v a3) (S64.v a0 * S64.v a4) (S64.v a0 * S64.v a5) (S64.v l01) (S64.v l02) (S64.v l03) (S64.v l04) (S64.v l05) (S64.v h01) (S64.v h02) (S64.v h03) (S64.v h04) (S64.v h05) (S64.v q0_2) (S64.v cq0_2) (S64.v q0_3) (S64.v cq0_3) (S64.v q0_4) (S64.v cq0_4) (S64.v q0_5) (S64.v cq0_5) (S64.v q0_6) (S64.v cq0_6);
  let m12 = S128.mul_wide a1 a2;
  let l12 = L.lo m12;
  let h12 = L.hi m12;
  L.lo_hi m12;
  pbound (S64.v a1) (S64.v a2);
  let m13 = S128.mul_wide a1 a3;
  let l13 = L.lo m13;
  let h13 = L.hi m13;
  L.lo_hi m13;
  pbound (S64.v a1) (S64.v a3);
  let m14 = S128.mul_wide a1 a4;
  let l14 = L.lo m14;
  let h14 = L.hi m14;
  L.lo_hi m14;
  pbound (S64.v a1) (S64.v a4);
  let m15 = S128.mul_wide a1 a5;
  let l15 = L.lo m15;
  let h15 = L.hi m15;
  L.lo_hi m15;
  pbound (S64.v a1) (S64.v a5);
  let cq1_4 = K.addc z0 l13 h12 r;
  let q1_4 = !r;
  let cq1_5 = K.addc cq1_4 l14 h13 r;
  let q1_5 = !r;
  let cq1_6 = K.addc cq1_5 l15 h14 r;
  let q1_6 = !r;
  let cq1_7 = K.addc cq1_6 z0 h15 r;
  let q1_7 = !r;
  let ca1_3 = K.addc z0 q0_3 l12 r;
  let n1_3 = !r;
  let ca1_4 = K.addc ca1_3 q0_4 q1_4 r;
  let n1_4 = !r;
  let ca1_5 = K.addc ca1_4 q0_5 q1_5 r;
  let n1_5 = !r;
  let ca1_6 = K.addc ca1_5 q0_6 q1_6 r;
  let n1_6 = !r;
  let ca1_7 = K.addc ca1_6 z0 q1_7 r;
  let n1_7 = !r;
  sqx1 (S64.v a0 * S64.v a1) (S64.v a0 * S64.v a2) (S64.v a0 * S64.v a3) (S64.v a0 * S64.v a4) (S64.v a0 * S64.v a5) (S64.v a1 * S64.v a2) (S64.v a1 * S64.v a3) (S64.v a1 * S64.v a4) (S64.v a1 * S64.v a5) (S64.v l12) (S64.v l13) (S64.v l14) (S64.v l15) (S64.v h12) (S64.v h13) (S64.v h14) (S64.v h15) (S64.v l01) (S64.v q0_2) (S64.v q0_3) (S64.v q0_4) (S64.v q0_5) (S64.v q0_6) (S64.v q1_4) (S64.v cq1_4) (S64.v q1_5) (S64.v cq1_5) (S64.v q1_6) (S64.v cq1_6) (S64.v q1_7) (S64.v cq1_7) (S64.v n1_3) (S64.v ca1_3) (S64.v n1_4) (S64.v ca1_4) (S64.v n1_5) (S64.v ca1_5) (S64.v n1_6) (S64.v ca1_6) (S64.v n1_7) (S64.v ca1_7);
  let m23 = S128.mul_wide a2 a3;
  let l23 = L.lo m23;
  let h23 = L.hi m23;
  L.lo_hi m23;
  pbound (S64.v a2) (S64.v a3);
  let m24 = S128.mul_wide a2 a4;
  let l24 = L.lo m24;
  let h24 = L.hi m24;
  L.lo_hi m24;
  pbound (S64.v a2) (S64.v a4);
  let m25 = S128.mul_wide a2 a5;
  let l25 = L.lo m25;
  let h25 = L.hi m25;
  L.lo_hi m25;
  pbound (S64.v a2) (S64.v a5);
  let cq2_6 = K.addc z0 l24 h23 r;
  let q2_6 = !r;
  let cq2_7 = K.addc cq2_6 l25 h24 r;
  let q2_7 = !r;
  let cq2_8 = K.addc cq2_7 z0 h25 r;
  let q2_8 = !r;
  let ca2_5 = K.addc z0 n1_5 l23 r;
  let n2_5 = !r;
  let ca2_6 = K.addc ca2_5 n1_6 q2_6 r;
  let n2_6 = !r;
  let ca2_7 = K.addc ca2_6 n1_7 q2_7 r;
  let n2_7 = !r;
  let ca2_8 = K.addc ca2_7 z0 q2_8 r;
  let n2_8 = !r;
  sqx2 (S64.v a0 * S64.v a1) (S64.v a0 * S64.v a2) (S64.v a0 * S64.v a3) (S64.v a0 * S64.v a4) (S64.v a0 * S64.v a5) (S64.v a1 * S64.v a2) (S64.v a1 * S64.v a3) (S64.v a1 * S64.v a4) (S64.v a1 * S64.v a5) (S64.v a2 * S64.v a3) (S64.v a2 * S64.v a4) (S64.v a2 * S64.v a5) (S64.v l23) (S64.v l24) (S64.v l25) (S64.v h23) (S64.v h24) (S64.v h25) (S64.v l01) (S64.v q0_2) (S64.v n1_3) (S64.v n1_4) (S64.v n1_5) (S64.v n1_6) (S64.v n1_7) (S64.v q2_6) (S64.v cq2_6) (S64.v q2_7) (S64.v cq2_7) (S64.v q2_8) (S64.v cq2_8) (S64.v n2_5) (S64.v ca2_5) (S64.v n2_6) (S64.v ca2_6) (S64.v n2_7) (S64.v ca2_7) (S64.v n2_8) (S64.v ca2_8);
  let m34 = S128.mul_wide a3 a4;
  let l34 = L.lo m34;
  let h34 = L.hi m34;
  L.lo_hi m34;
  pbound (S64.v a3) (S64.v a4);
  let m35 = S128.mul_wide a3 a5;
  let l35 = L.lo m35;
  let h35 = L.hi m35;
  L.lo_hi m35;
  pbound (S64.v a3) (S64.v a5);
  let cq3_8 = K.addc z0 l35 h34 r;
  let q3_8 = !r;
  let cq3_9 = K.addc cq3_8 z0 h35 r;
  let q3_9 = !r;
  let ca3_7 = K.addc z0 n2_7 l34 r;
  let n3_7 = !r;
  let ca3_8 = K.addc ca3_7 n2_8 q3_8 r;
  let n3_8 = !r;
  let ca3_9 = K.addc ca3_8 z0 q3_9 r;
  let n3_9 = !r;
  sqx3 (S64.v a0 * S64.v a1) (S64.v a0 * S64.v a2) (S64.v a0 * S64.v a3) (S64.v a0 * S64.v a4) (S64.v a0 * S64.v a5) (S64.v a1 * S64.v a2) (S64.v a1 * S64.v a3) (S64.v a1 * S64.v a4) (S64.v a1 * S64.v a5) (S64.v a2 * S64.v a3) (S64.v a2 * S64.v a4) (S64.v a2 * S64.v a5) (S64.v a3 * S64.v a4) (S64.v a3 * S64.v a5) (S64.v l34) (S64.v l35) (S64.v h34) (S64.v h35) (S64.v l01) (S64.v q0_2) (S64.v n1_3) (S64.v n1_4) (S64.v n2_5) (S64.v n2_6) (S64.v n2_7) (S64.v n2_8) (S64.v q3_8) (S64.v cq3_8) (S64.v q3_9) (S64.v cq3_9) (S64.v n3_7) (S64.v ca3_7) (S64.v n3_8) (S64.v ca3_8) (S64.v n3_9) (S64.v ca3_9);
  let m45 = S128.mul_wide a4 a5;
  let l45 = L.lo m45;
  let h45 = L.hi m45;
  L.lo_hi m45;
  pbound (S64.v a4) (S64.v a5);
  let cq4_10 = K.addc z0 z0 h45 r;
  let q4_10 = !r;
  let ca4_9 = K.addc z0 n3_9 l45 r;
  let n4_9 = !r;
  let ca4_10 = K.addc ca4_9 z0 q4_10 r;
  let n4_10 = !r;
  sqx4 (S64.v a0 * S64.v a1) (S64.v a0 * S64.v a2) (S64.v a0 * S64.v a3) (S64.v a0 * S64.v a4) (S64.v a0 * S64.v a5) (S64.v a1 * S64.v a2) (S64.v a1 * S64.v a3) (S64.v a1 * S64.v a4) (S64.v a1 * S64.v a5) (S64.v a2 * S64.v a3) (S64.v a2 * S64.v a4) (S64.v a2 * S64.v a5) (S64.v a3 * S64.v a4) (S64.v a3 * S64.v a5) (S64.v a4 * S64.v a5) (S64.v l45) (S64.v h45) (S64.v l01) (S64.v q0_2) (S64.v n1_3) (S64.v n1_4) (S64.v n2_5) (S64.v n2_6) (S64.v n3_7) (S64.v n3_8) (S64.v n3_9) (S64.v q4_10) (S64.v cq4_10) (S64.v n4_9) (S64.v ca4_9) (S64.v n4_10) (S64.v ca4_10);
  put12 t z0 l01 q0_2 n1_3 n1_4 n2_5 n2_6 n3_7 n3_8 n4_9 n4_10 z0;
}

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn sq_diag (t: A.array S64.t) (a0 a1 a2 a3 a4 a5: S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 12 /\ F64.ix vt 0 == 0 /\ F64.ix vt 11 == 0 /\ tv vt == w * (S64.v a0 * S64.v a1) + w2 * (S64.v a0 * S64.v a2) + w3 * (S64.v a0 * S64.v a3) + w4 * (S64.v a0 * S64.v a4) + w5 * (S64.v a0 * S64.v a5) + w3 * (S64.v a1 * S64.v a2) + w4 * (S64.v a1 * S64.v a3) + w5 * (S64.v a1 * S64.v a4) + w6 * (S64.v a1 * S64.v a5) + w5 * (S64.v a2 * S64.v a3) + w6 * (S64.v a2 * S64.v a4) + w7 * (S64.v a2 * S64.v a5) + w7 * (S64.v a3 * S64.v a4) + w8 * (S64.v a3 * S64.v a5) + w9 * (S64.v a4 * S64.v a5))
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 12 /\ tv vt' == (S64.v a0 * S64.v a0) + w2 * (S64.v a1 * S64.v a1) + w4 * (S64.v a2 * S64.v a2) + w6 * (S64.v a3 * S64.v a3) + w8 * (S64.v a4 * S64.v a4) + w10 * (S64.v a5 * S64.v a5) + 2 * (w * (S64.v a0 * S64.v a1) + w2 * (S64.v a0 * S64.v a2) + w3 * (S64.v a0 * S64.v a3) + w4 * (S64.v a0 * S64.v a4) + w5 * (S64.v a0 * S64.v a5) + w3 * (S64.v a1 * S64.v a2) + w4 * (S64.v a1 * S64.v a3) + w5 * (S64.v a1 * S64.v a4) + w6 * (S64.v a1 * S64.v a5) + w5 * (S64.v a2 * S64.v a3) + w6 * (S64.v a2 * S64.v a4) + w7 * (S64.v a2 * S64.v a5) + w7 * (S64.v a3 * S64.v a4) + w8 * (S64.v a3 * S64.v a5) + w9 * (S64.v a4 * S64.v a5)))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let t1 = A.(t.(1sz));
  let t2 = A.(t.(2sz));
  let t3 = A.(t.(3sz));
  let t4 = A.(t.(4sz));
  let t5 = A.(t.(5sz));
  let t6 = A.(t.(6sz));
  let t7 = A.(t.(7sz));
  let t8 = A.(t.(8sz));
  let t9 = A.(t.(9sz));
  let t10 = A.(t.(10sz));
  let mut r = z0;
  let e1 = K.addc z0 t1 t1 r;
  let d1 = !r;
  let e2 = K.addc e1 t2 t2 r;
  let d2 = !r;
  let e3 = K.addc e2 t3 t3 r;
  let d3 = !r;
  let e4 = K.addc e3 t4 t4 r;
  let d4 = !r;
  let e5 = K.addc e4 t5 t5 r;
  let d5 = !r;
  let e6 = K.addc e5 t6 t6 r;
  let d6 = !r;
  let e7 = K.addc e6 t7 t7 r;
  let d7 = !r;
  let e8 = K.addc e7 t8 t8 r;
  let d8 = !r;
  let e9 = K.addc e8 t9 t9 r;
  let d9 = !r;
  let e10 = K.addc e9 t10 t10 r;
  let d10 = !r;
  let m00 = S128.mul_wide a0 a0;
  let l00 = L.lo m00;
  let h00 = L.hi m00;
  L.lo_hi m00;
  pbound (S64.v a0) (S64.v a0);
  let m11 = S128.mul_wide a1 a1;
  let l11 = L.lo m11;
  let h11 = L.hi m11;
  L.lo_hi m11;
  pbound (S64.v a1) (S64.v a1);
  let m22 = S128.mul_wide a2 a2;
  let l22 = L.lo m22;
  let h22 = L.hi m22;
  L.lo_hi m22;
  pbound (S64.v a2) (S64.v a2);
  let m33 = S128.mul_wide a3 a3;
  let l33 = L.lo m33;
  let h33 = L.hi m33;
  L.lo_hi m33;
  pbound (S64.v a3) (S64.v a3);
  let m44 = S128.mul_wide a4 a4;
  let l44 = L.lo m44;
  let h44 = L.hi m44;
  L.lo_hi m44;
  pbound (S64.v a4) (S64.v a4);
  let m55 = S128.mul_wide a5 a5;
  let l55 = L.lo m55;
  let h55 = L.hi m55;
  L.lo_hi m55;
  pbound (S64.v a5) (S64.v a5);
  let f1 = K.addc z0 d1 h00 r;
  let u1 = !r;
  let f2 = K.addc f1 d2 l11 r;
  let u2 = !r;
  let f3 = K.addc f2 d3 h11 r;
  let u3 = !r;
  let f4 = K.addc f3 d4 l22 r;
  let u4 = !r;
  let f5 = K.addc f4 d5 h22 r;
  let u5 = !r;
  let f6 = K.addc f5 d6 l33 r;
  let u6 = !r;
  let f7 = K.addc f6 d7 h33 r;
  let u7 = !r;
  let f8 = K.addc f7 d8 l44 r;
  let u8 = !r;
  let f9 = K.addc f8 d9 h44 r;
  let u9 = !r;
  let f10 = K.addc f9 d10 l55 r;
  let u10 = !r;
  let f11 = K.addc f10 e10 h55 r;
  let u11 = !r;
  sqd (S64.v a0 * S64.v a0) (S64.v a0 * S64.v a1) (S64.v a0 * S64.v a2) (S64.v a0 * S64.v a3) (S64.v a0 * S64.v a4) (S64.v a0 * S64.v a5) (S64.v a1 * S64.v a1) (S64.v a1 * S64.v a2) (S64.v a1 * S64.v a3) (S64.v a1 * S64.v a4) (S64.v a1 * S64.v a5) (S64.v a2 * S64.v a2) (S64.v a2 * S64.v a3) (S64.v a2 * S64.v a4) (S64.v a2 * S64.v a5) (S64.v a3 * S64.v a3) (S64.v a3 * S64.v a4) (S64.v a3 * S64.v a5) (S64.v a4 * S64.v a4) (S64.v a4 * S64.v a5) (S64.v a5 * S64.v a5) (S64.v t1) (S64.v t2) (S64.v t3) (S64.v t4) (S64.v t5) (S64.v t6) (S64.v t7) (S64.v t8) (S64.v t9) (S64.v t10) (S64.v d1) (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5) (S64.v d6) (S64.v d7) (S64.v d8) (S64.v d9) (S64.v d10) (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4) (S64.v e5) (S64.v e6) (S64.v e7) (S64.v e8) (S64.v e9) (S64.v e10) (S64.v l00) (S64.v l11) (S64.v l22) (S64.v l33) (S64.v l44) (S64.v l55) (S64.v h00) (S64.v h11) (S64.v h22) (S64.v h33) (S64.v h44) (S64.v h55) (S64.v u1) (S64.v u2) (S64.v u3) (S64.v u4) (S64.v u5) (S64.v u6) (S64.v u7) (S64.v u8) (S64.v u9) (S64.v u10) (S64.v u11) (S64.v f1) (S64.v f2) (S64.v f3) (S64.v f4) (S64.v f5) (S64.v f6) (S64.v f7) (S64.v f8) (S64.v f9) (S64.v f10) (S64.v f11);
  put12 t l00 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11;
}



#restart-solver

(** [acc := (acc + u p) / 2^64]: {!step} without a product row.  The
    quotient [u] is returned so that six steps compose exactly. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep (acc: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to acc va ** pure (Seq.length va == 7 /\ av va < 2 * pp)
returns u: S64.t
ensures exists* (va': Seq.seq S64.t).
  A.pts_to acc va' **
  pure (Seq.length va' == 7 /\ av va' < 2 * pp /\ w * av va' == av va + S64.v u * pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len acc;
  consts ();
  let s0 = A.(acc.(0sz));
  let s1 = A.(acc.(1sz));
  let s2 = A.(acc.(2sz));
  let s3 = A.(acc.(3sz));
  let s4 = A.(acc.(4sz));
  let s5 = A.(acc.(5sz));
  let s6 = A.(acc.(6sz));
  let mut r = z0;
  let u = mu s0;
  let lo = S64.shift_left u 32ul;
  let hi = S64.shift_right u 32ul;
  shift_val (S64.v u) (S64.v lo) (S64.v hi);
  let bb0 = K.subb z0 u lo r;
  let r0 = !r;
  let bb1 = K.subb bb0 lo hi r;
  let e1 = !r;
  let bb2 = K.subb bb1 hi z0 r;
  let e2 = !r;
  let k3 = K.addc z0 e2 u r;
  let k2 = !r;
  kval (S64.v u) (S64.v lo) (S64.v hi) (S64.v r0) (S64.v e1) (S64.v e2) (S64.v k2) (S64.v k3)
       (S64.v bb0) (S64.v bb1) (S64.v bb2);
  r0_eq (S64.v s0) (S64.v r0) (S64.v u * 4294967295)
        (S64.v u * 18446744078004518912 - ev7 (S64.v e1) (S64.v k2) (S64.v k3) 0 0 0 0);
  let g = K.addc z0 s6 u r;
  let v6 = !r;
  let d2 = K.subb z0 s1 e1 r;
  let t1 = !r;
  let d3 = K.subb d2 s2 k2 r;
  let t2 = !r;
  let d4 = K.subb d3 s3 k3 r;
  let t3 = !r;
  let d5 = K.subb d4 s4 z0 r;
  let t4 = !r;
  let d6 = K.subb d5 s5 z0 r;
  let t5 = !r;
  let d7 = K.subb d6 v6 z0 r;
  let t6 = !r;
  let d8 = K.subb d7 g z0 r;
  let t7 = !r;
  sub7 (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v v6) (S64.v g)
       (S64.v e1) (S64.v k2) (S64.v k3) 0 0 0 0
       (S64.v t1) (S64.v t2) (S64.v t3) (S64.v t4) (S64.v t5) (S64.v t6) (S64.v t7)
       (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5) (S64.v d6) (S64.v d7) (S64.v d8);
  step_val (av va) 0
           (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v s6) 0
           (S64.v u) (S64.v e1) (S64.v k2) (S64.v k3) (S64.v g) (S64.v v6) (S64.v g)
           (S64.v t1) (S64.v t2) (S64.v t3) (S64.v t4) (S64.v t5) (S64.v t6) (S64.v t7)
           (S64.v d8);
  put7 acc t1 t2 t3 t4 t5 t6 t7;
  u
}

(** Six reduction steps: [2^384 R = L + U p] with [U < 2^384], so [R <= p]. *)
let redc6 (l v1 v2 v3 v4 v5 v6 u0 u1 u2 u3 u4 u5: nat)
  : Lemma (requires l < w6 /\ u0 < w /\ u1 < w /\ u2 < w /\ u3 < w /\ u4 < w /\ u5 < w /\
                    w * v1 == l + u0 * pp /\ w * v2 == v1 + u1 * pp /\ w * v3 == v2 + u2 * pp /\
                    w * v4 == v3 + u3 * pp /\ w * v5 == v4 + u4 * pp /\ w * v6 == v5 + u5 * pp)
          (ensures w6 * v6 == l + ev6 u0 u1 u2 u3 u4 u5 * pp /\ v6 <= pp)
  = ()

(** A square below [p^2] has its high half below [p]. *)
let hi_lt (h l: nat)
  : Lemma (requires h * w6 + l < pp * pp) (ensures h < pp)
  = Math.lemma_mult_lt_left pp pp w6;
    if h >= pp then Math.lemma_mult_le_right w6 pp h

let sq_lt (a: nat)
  : Lemma (requires a < pp) (ensures a * a < pp * pp)
  = if a > 0 then (Math.lemma_mult_lt_right a a pp; Math.lemma_mult_lt_left pp a pp)

let tv_split (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11: nat)
  : Lemma (x0 + w * x1 + w2 * x2 + w3 * x3 + w4 * x4 + w5 * x5 + w6 * x6 + w7 * x7 +
           w8 * x8 + w9 * x9 + w10 * x10 + w11 * x11 ==
           ev6 x6 x7 x8 x9 x10 x11 * w6 + ev6 x0 x1 x2 x3 x4 x5)
  = ()

(** [R + H] for [2^384 R = L + U p] and [H 2^384 + L = T]: below [2 p],
    and [2^384 (R + H) = T (mod p)]. *)
let msq_fin (t h l r u s c: nat)
  : Lemma (requires h * w6 + l == t /\ w6 * r == l + u * pp /\ r <= pp /\ h < pp /\
                    s + w7 * c == r + h)
          (ensures c == 0 /\ s < 2 * pp /\ (w6 * s) % pp == t % pp)
  = assert (c == 0);
    assert (w6 * s == t + u * pp);
    Math.lemma_mod_plus t u pp

#restart-solver

(** Montgomery's reduction of twelve words below [p^2]. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn mred (out t: A.array S64.t) (#vo: erased (Seq.seq S64.t))
        (#vt: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt **
  pure (Seq.length vo == 6 /\ Seq.length vt == 12 /\ tv vt < pp * pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t vt **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ (w6 * fv vo') % pp == tv vt % pp)
{
  let z = S64.classify 0uL;
  consts ();
  A.pts_to_len t;
  let x0 = A.(t.(0sz));
  let x1 = A.(t.(1sz));
  let x2 = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let x9 = A.(t.(9sz));
  let x10 = A.(t.(10sz));
  let x11 = A.(t.(11sz));
  tv_split (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5)
           (S64.v x6) (S64.v x7) (S64.v x8) (S64.v x9) (S64.v x10) (S64.v x11);
  hi_lt (ev6 (S64.v x6) (S64.v x7) (S64.v x8) (S64.v x9) (S64.v x10) (S64.v x11))
        (ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5));
  let mut acc = [| z; 7sz |];
  Mem.track acc;
  A.pts_to_len acc;
  put7 acc x0 x1 x2 x3 x4 x5 z;
  with v0. assert (A.pts_to acc v0);
  let u0 = rstep acc;
  with v1. assert (A.pts_to acc v1);
  let u1 = rstep acc;
  with v2. assert (A.pts_to acc v2);
  let u2 = rstep acc;
  with v3. assert (A.pts_to acc v3);
  let u3 = rstep acc;
  with v4. assert (A.pts_to acc v4);
  let u4 = rstep acc;
  with v5. assert (A.pts_to acc v5);
  let u5 = rstep acc;
  with v6. assert (A.pts_to acc v6);
  redc6 (av v0) (av v1) (av v2) (av v3) (av v4) (av v5) (av v6)
        (S64.v u0) (S64.v u1) (S64.v u2) (S64.v u3) (S64.v u4) (S64.v u5);
  let r0 = A.(acc.(0sz));
  let r1 = A.(acc.(1sz));
  let r2 = A.(acc.(2sz));
  let r3 = A.(acc.(3sz));
  let r4 = A.(acc.(4sz));
  let r5 = A.(acc.(5sz));
  let r6 = A.(acc.(6sz));
  let mut r = z;
  let c1 = K.addc z r0 x6 r;
  let s0 = !r;
  let c2 = K.addc c1 r1 x7 r;
  let s1 = !r;
  let c3 = K.addc c2 r2 x8 r;
  let s2 = !r;
  let c4 = K.addc c3 r3 x9 r;
  let s3 = !r;
  let c5 = K.addc c4 r4 x10 r;
  let s4 = !r;
  let c6 = K.addc c5 r5 x11 r;
  let s5 = !r;
  let c7 = K.addc c6 r6 z r;
  let s6 = !r;
  add7 (S64.v r0) (S64.v r1) (S64.v r2) (S64.v r3) (S64.v r4) (S64.v r5) (S64.v r6)
       (S64.v x6) (S64.v x7) (S64.v x8) (S64.v x9) (S64.v x10) (S64.v x11) 0
       (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v s6)
       0 (S64.v c1) (S64.v c2) (S64.v c3) (S64.v c4) (S64.v c5) (S64.v c6) (S64.v c7);
  put7 acc s0 s1 s2 s3 s4 s5 s6;
  with vs. assert (A.pts_to acc vs);
  msq_fin (tv vt)
          (ev6 (S64.v x6) (S64.v x7) (S64.v x8) (S64.v x9) (S64.v x10) (S64.v x11))
          (ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5))
          (av v6)
          (ev6 (S64.v u0) (S64.v u1) (S64.v u2) (S64.v u3) (S64.v u4) (S64.v u5))
          (av vs) (S64.v c7);
  csub out acc;
  with o. assert (A.pts_to out o);
  mod_out (fv o) (av vs);
  Mem.nowipe acc;
}

#restart-solver

(** The twelve-word square. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn msq12 (t: A.array S64.t) (a0 a1 a2 a3 a4 a5: S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt ** pure (Seq.length vt == 12)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' ** pure (Seq.length vt' == 12 /\ tv vt' == (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)) * (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)))
{
  sq_cross t a0 a1 a2 a3 a4 a5;
  sq_diag t a0 a1 a2 a3 a4 a5;
  sq_expand (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5);
}

(** Montgomery's square of a number below [p], given as words. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn msqr (out: A.array S64.t) (a0 a1 a2 a3 a4 a5: S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo **
  pure (Seq.length vo == 6 /\ ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ (w6 * fv vo') % pp == ((ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)) * (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5))) % pp)
{
  let z = S64.classify 0uL;
  let mut t = [| z; 12sz |];
  Mem.track t;
  A.pts_to_len t;
  msq12 t a0 a1 a2 a3 a4 a5;
  sq_lt (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5));
  mred out t;
  Mem.nowipe t;
}

#restart-solver

(** {2 The ring operations}

    On numbers below [p]: [fmul] and [fsqr] are Montgomery's product,
    [R z = a b mod p] with [R = 2^384], and [fadd] and [fsub] are the plain
    sum and difference mod [p]. *)

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn fmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ Seq.length vb == 6 /\
        fv va < pp /\ fv vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ (w6 * fv vo') % pp == (fv va * fv vb) % pp)
{
  A.pts_to_len a;
  A.pts_to_len b;
  mont out A.(a.(0sz)) A.(a.(1sz)) A.(a.(2sz)) A.(a.(3sz)) A.(a.(4sz)) A.(a.(5sz))
           A.(b.(0sz)) A.(b.(1sz)) A.(b.(2sz)) A.(b.(3sz)) A.(b.(4sz)) A.(b.(5sz));
}

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn fsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ fv va < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ (w6 * fv vo') % pp == (fv va * fv va) % pp)
{
  A.pts_to_len a;
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let a4 = A.(a.(4sz));
  let a5 = A.(a.(5sz));
  msqr out a0 a1 a2 a3 a4 a5;
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn addw (out: A.array S64.t) (a0 a1 a2 a3 a4 a5 x0 x1 x2 x3 x4 x5: S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo **
  pure (Seq.length vo == 6 /\ ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) < pp /\ ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5) < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' **
  pure (Seq.length vo' == 6 /\ fv vo' == (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) + ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5)) % pp)
{
  let z0 = S64.classify 0uL;
  consts ();
  let ones = S64.classify 0xffffffffffffffffuL;
  let mut r = z0;
  let c1 = K.addc z0 a0 x0 r;
  let s0 = !r;
  let c2 = K.addc c1 a1 x1 r;
  let s1 = !r;
  let c3 = K.addc c2 a2 x2 r;
  let s2 = !r;
  let c4 = K.addc c3 a3 x3 r;
  let s3 = !r;
  let c5 = K.addc c4 a4 x4 r;
  let s4 = !r;
  let c = K.addc c5 a5 x5 r;
  let s5 = !r;
  add6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)
       (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5)
       (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5)
       0 (S64.v c1) (S64.v c2) (S64.v c3) (S64.v c4) (S64.v c5) (S64.v c);
  let e1 = K.subb z0 s0 (S64.classify 0xffffffffuL) r;
  let d0 = !r;
  let e2 = K.subb e1 s1 (S64.classify 0xffffffff00000000uL) r;
  let d1 = !r;
  let e3 = K.subb e2 s2 (S64.classify 0xfffffffffffffffeuL) r;
  let d2 = !r;
  let e4 = K.subb e3 s3 ones r;
  let d3 = !r;
  let e5 = K.subb e4 s4 ones r;
  let d4 = !r;
  let e6 = K.subb e5 s5 ones r;
  let d5 = !r;
  let d = K.subb e6 c z0 r;
  let d6 = !r;
  sub7 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5) (S64.v c)
       4294967295 18446744069414584320 18446744073709551614
       18446744073709551615 18446744073709551615 18446744073709551615 0
       (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5) (S64.v d6)
       (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4) (S64.v e5) (S64.v e6) (S64.v d);
  mask_ok (S64.v d);
  let m = S64.sub_mod z0 d;
  let o0 = S64.select m s0 d0;
  let o1 = S64.select m s1 d1;
  let o2 = S64.select m s2 d2;
  let o3 = S64.select m s3 d3;
  let o4 = S64.select m s4 d4;
  let o5 = S64.select m s5 d5;
  add_sel (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5)
          (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5)
          (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) (S64.v o4) (S64.v o5) (S64.v d);
  csub_ok ((ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)) + (ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5))) (S64.v c) (S64.v d6) (S64.v d)
          (ev6 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5))
          (ev6 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5))
          (ev6 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) (S64.v o4) (S64.v o5));
  put6 out o0 o1 o2 o3 o4 o5;
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn subw (out: A.array S64.t) (a0 a1 a2 a3 a4 a5 x0 x1 x2 x3 x4 x5: S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo **
  pure (Seq.length vo == 6 /\ ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) < pp /\ ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5) < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' **
  pure (Seq.length vo' == 6 /\ fv vo' == (ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5) + pp - ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5)) % pp)
{
  let z0 = S64.classify 0uL;
  consts ();
  let mut r = z0;
  let c1 = K.subb z0 a0 x0 r;
  let s0 = !r;
  let c2 = K.subb c1 a1 x1 r;
  let s1 = !r;
  let c3 = K.subb c2 a2 x2 r;
  let s2 = !r;
  let c4 = K.subb c3 a3 x3 r;
  let s3 = !r;
  let c5 = K.subb c4 a4 x4 r;
  let s4 = !r;
  let c = K.subb c5 a5 x5 r;
  let s5 = !r;
  sub6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5)
       (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5)
       (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5)
       (S64.v c1) (S64.v c2) (S64.v c3) (S64.v c4) (S64.v c5) (S64.v c);
  mask_ok (S64.v c);
  let m = S64.sub_mod z0 c;
  let ones = S64.classify 0xffffffffffffffffuL;
  let q0 = S64.select m (S64.classify 0xffffffffuL) z0;
  let q1 = S64.select m (S64.classify 0xffffffff00000000uL) z0;
  let q2 = S64.select m (S64.classify 0xfffffffffffffffeuL) z0;
  let q3 = S64.select m ones z0;
  let e1 = K.addc z0 s0 q0 r;
  let d0 = !r;
  let e2 = K.addc e1 s1 q1 r;
  let d1 = !r;
  let e3 = K.addc e2 s2 q2 r;
  let d2 = !r;
  let e4 = K.addc e3 s3 q3 r;
  let d3 = !r;
  let e5 = K.addc e4 s4 q3 r;
  let d4 = !r;
  let d = K.addc e5 s5 q3 r;
  let d5 = !r;
  add6 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5)
       (S64.v q0) (S64.v q1) (S64.v q2) (S64.v q3) (S64.v q3) (S64.v q3)
       (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5)
       0 (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4) (S64.v e5) (S64.v d);
  fsub_ok ((ev6 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) (S64.v a5))) ((ev6 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) (S64.v x4) (S64.v x5))) (S64.v c) (S64.v d)
          (ev6 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) (S64.v s4) (S64.v s5))
          (ev6 (S64.v q0) (S64.v q1) (S64.v q2) (S64.v q3) (S64.v q3) (S64.v q3))
          (ev6 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) (S64.v d4) (S64.v d5));
  put6 out d0 d1 d2 d3 d4 d5;
}

fn fadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ fv va < pp /\ Seq.length vb == 6 /\ fv vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv va + fv vb) % pp)
{
  A.pts_to_len a;
  A.pts_to_len b;
  addw out A.(a.(0sz)) A.(a.(1sz)) A.(a.(2sz)) A.(a.(3sz)) A.(a.(4sz)) A.(a.(5sz)) A.(b.(0sz)) A.(b.(1sz)) A.(b.(2sz)) A.(b.(3sz)) A.(b.(4sz)) A.(b.(5sz));
}

fn fsub (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ fv va < pp /\ Seq.length vb == 6 /\ fv vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv va + pp - fv vb) % pp)
{
  A.pts_to_len a;
  A.pts_to_len b;
  subw out A.(a.(0sz)) A.(a.(1sz)) A.(a.(2sz)) A.(a.(3sz)) A.(a.(4sz)) A.(a.(5sz)) A.(b.(0sz)) A.(b.(1sz)) A.(b.(2sz)) A.(b.(3sz)) A.(b.(4sz)) A.(b.(5sz));
}

fn fdbl (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ fv va < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv va + fv va) % pp)
{
  A.pts_to_len a;
  addw out A.(a.(0sz)) A.(a.(1sz)) A.(a.(2sz)) A.(a.(3sz)) A.(a.(4sz)) A.(a.(5sz)) A.(a.(0sz)) A.(a.(1sz)) A.(a.(2sz)) A.(a.(3sz)) A.(a.(4sz)) A.(a.(5sz));
}

fn fadd1 (o b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ fv vo < pp /\ Seq.length vb == 6 /\ fv vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv vo + fv vb) % pp)
{
  A.pts_to_len o;
  A.pts_to_len b;
  addw o A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz)) A.(b.(0sz)) A.(b.(1sz)) A.(b.(2sz)) A.(b.(3sz)) A.(b.(4sz)) A.(b.(5sz));
}

fn fdbl1 (o: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo **
  pure (Seq.length vo == 6 /\ fv vo < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv vo + fv vo) % pp)
{
  A.pts_to_len o;
  addw o A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz)) A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz));
}

fn fsub1 (o b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ fv vo < pp /\ Seq.length vb == 6 /\ fv vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv vo + pp - fv vb) % pp)
{
  A.pts_to_len o;
  A.pts_to_len b;
  subw o A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz)) A.(b.(0sz)) A.(b.(1sz)) A.(b.(2sz)) A.(b.(3sz)) A.(b.(4sz)) A.(b.(5sz));
}

fn fsub2 (o a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ fv vo < pp /\ Seq.length va == 6 /\ fv va < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == 6 /\ fv vo' == (fv va + pp - fv vo) % pp)
{
  A.pts_to_len o;
  A.pts_to_len a;
  subw o A.(a.(0sz)) A.(a.(1sz)) A.(a.(2sz)) A.(a.(3sz)) A.(a.(4sz)) A.(a.(5sz)) A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz));
}

fn fmul1 (o b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ fv vo < pp /\ Seq.length vb == 6 /\ fv vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ (w6 * fv vo') % pp == (fv vo * fv vb) % pp)
{
  A.pts_to_len o;
  A.pts_to_len b;
  mont o A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz)) A.(b.(0sz)) A.(b.(1sz)) A.(b.(2sz)) A.(b.(3sz)) A.(b.(4sz)) A.(b.(5sz));
}

fn fsqr1 (o: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo **
  pure (Seq.length vo == 6 /\ fv vo < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 6 /\ fv vo' < pp /\ (w6 * fv vo') % pp == (fv vo * fv vo) % pp)
{
  A.pts_to_len o;
  msqr o A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz));
}

#pop-options
