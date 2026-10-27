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
  mont out a0 a1 a2 a3 a4 a5 a0 a1 a2 a3 a4 a5;
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
  mont o A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz)) A.(o.(0sz)) A.(o.(1sz)) A.(o.(2sz)) A.(o.(3sz)) A.(o.(4sz)) A.(o.(5sz));
}

#pop-options
