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

(** The P-256 field in four sixty-four-bit words, specialised.

    {!Hacl.Impl.Mont4} is a generic Montgomery multiplier: the modulus is
    table data and a product is summed in columns of [__int128].  For
    [p = 2^256 - 2^224 + 2^192 + 2^96 - 1] almost all of that is wasted.
    Its lowest word is [2^64 - 1], so [-p^-1 mod 2^64 = 1] and the
    Montgomery quotient of a step is just the bottom word [u]; and
    [p + 1 = 2^96 + 2^192 * P3] with [P3 = 0xffffffff00000001], so adding
    [u p] and dropping the zero bottom word is adding [u 2^32] one word up
    and [u P3] three words up -- two shifts and one multiplication, where
    the generic step has four multiplications.

    The product itself is {!Hacl.Curve25519.Field64.mul8}, sixteen
    multiplications chained with [adc]; four reduction steps
    ({!rstep0} .. {!rstep3}) leave a number below [2 p], and {!csub}
    subtracts [p] once if it can.  Every step's statement is linear --
    [w * W_(k+1) == W_k + u p], with the powers of the radix written as
    numerals -- so Z3 checks each one without help.

    Addition and subtraction are a carry chain and a masked correction.
    Nothing here has a CPU target: [adc] and [mul] are baseline x86-64. *)
module Hacl.P256.Field64

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

(** {2 Numbers} *)

unfold let pp : pos = 115792089210356248762697446949407573530086143415290314195533631308867097853951

unfold let w9 : pos = 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136

(** Nine words from [k] up; past the end they read as zero. *)
let wv (s: Seq.seq S64.t) (k: nat) : GTot nat =
  F64.ix s k + w * F64.ix s (k + 1) + w2 * F64.ix s (k + 2) + w3 * F64.ix s (k + 3) +
  w4 * F64.ix s (k + 4) + w5 * F64.ix s (k + 5) + w6 * F64.ix s (k + 6) +
  w7 * F64.ix s (k + 7) + w8 * F64.ix s (k + 8)

let split32 (u: nat)
  : Lemma (requires u < w)
          (ensures (u * pow2 32) % pow2 64 + w * (u / pow2 32) == 4294967296 * u)
  = assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 64 == w);
    Math.euclidean_division_definition u 4294967296;
    Math.lemma_mod_plus ((u % 4294967296) * 4294967296) (u / 4294967296) w;
    Math.small_mod ((u % 4294967296) * 4294967296) w

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

let glue (o x t u: nat)
  : Lemma (requires o % pp == x % pp /\ w4 * x == t + u * pp)
          (ensures w4 * o % pp == t % pp)
  = Math.lemma_mod_mul_distr_r w4 o pp;
    Math.lemma_mod_mul_distr_r w4 x pp;
    Math.lemma_mod_plus t u pp

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

(** {!Hacl.Curve25519.Field64.put4} without its [bmi2] target. *)
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

    Step [k] takes the window [W_k] (words [k] to [8]) with [u] its bottom
    word, and leaves [W_(k+1) = (W_k + u p) / 2^64] in words [k+1] to [8].
    The bound in the precondition is what says the carry out of the top
    word is zero. *)

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep0 (t: A.array S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ wv vt 0 + F64.ix vt 0 * pp < w9)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ w * wv vt' 1 == wv vt 0 + F64.ix vt 0 * pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let u = A.(t.(0sz));
  let x1 = A.(t.(1sz));
  let x2 = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let sl = S64.shift_left u 32ul;
  let sr = S64.shift_right u 32ul;
  split32 (S64.v u);
  let m = S128.mul_wide u (S64.classify 0xffffffff00000001uL);
  let lo = L.lo m;
  let hi = L.hi m;
  L.lo_hi m;
  let mut r = z0;
  let c1 = K.addc z0 x1 sl r;
  let y1 = !r;
  let c2 = K.addc c1 x2 sr r;
  let y2 = !r;
  let c3 = K.addc c2 x3 lo r;
  let y3 = !r;
  let c4 = K.addc c3 x4 hi r;
  let y4 = !r;
  let c5 = K.addc c4 x5 z0 r;
  let y5 = !r;
  let c6 = K.addc c5 x6 z0 r;
  let y6 = !r;
  let c7 = K.addc c6 x7 z0 r;
  let y7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let y8 = !r;
  assert (pure (S64.v y1 + w * S64.v y2 + w2 * S64.v y3 + w3 * S64.v y4 + w4 * S64.v y5 + w5 * S64.v y6 + w6 * S64.v y7 + w7 * S64.v y8 + w8 * S64.v c8 ==
                S64.v x1 + w * S64.v x2 + w2 * S64.v x3 + w3 * S64.v x4 + w4 * S64.v x5 + w5 * S64.v x6 + w6 * S64.v x7 + w7 * S64.v x8 +
                S64.v sl + w * S64.v sr + w2 * S64.v lo + w3 * S64.v hi));
  assert (pure (w * (S64.v y1 + w * S64.v y2 + w2 * S64.v y3 + w3 * S64.v y4 + w4 * S64.v y5 + w5 * S64.v y6 + w6 * S64.v y7 + w7 * S64.v y8 + w8 * S64.v c8) == wv vt 0 + S64.v u * pp));
  assert (pure (S64.v c8 == 0));
  A.((t.(1sz) <- y1));
  A.((t.(2sz) <- y2));
  A.((t.(3sz) <- y3));
  A.((t.(4sz) <- y4));
  A.((t.(5sz) <- y5));
  A.((t.(6sz) <- y6));
  A.((t.(7sz) <- y7));
  A.((t.(8sz) <- y8));
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep1 (t: A.array S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ wv vt 1 + F64.ix vt 1 * pp < w8)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ w * wv vt' 2 == wv vt 1 + F64.ix vt 1 * pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let u = A.(t.(1sz));
  let x2 = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let sl = S64.shift_left u 32ul;
  let sr = S64.shift_right u 32ul;
  split32 (S64.v u);
  let m = S128.mul_wide u (S64.classify 0xffffffff00000001uL);
  let lo = L.lo m;
  let hi = L.hi m;
  L.lo_hi m;
  let mut r = z0;
  let c2 = K.addc z0 x2 sl r;
  let y2 = !r;
  let c3 = K.addc c2 x3 sr r;
  let y3 = !r;
  let c4 = K.addc c3 x4 lo r;
  let y4 = !r;
  let c5 = K.addc c4 x5 hi r;
  let y5 = !r;
  let c6 = K.addc c5 x6 z0 r;
  let y6 = !r;
  let c7 = K.addc c6 x7 z0 r;
  let y7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let y8 = !r;
  assert (pure (S64.v y2 + w * S64.v y3 + w2 * S64.v y4 + w3 * S64.v y5 + w4 * S64.v y6 + w5 * S64.v y7 + w6 * S64.v y8 + w7 * S64.v c8 ==
                S64.v x2 + w * S64.v x3 + w2 * S64.v x4 + w3 * S64.v x5 + w4 * S64.v x6 + w5 * S64.v x7 + w6 * S64.v x8 +
                S64.v sl + w * S64.v sr + w2 * S64.v lo + w3 * S64.v hi));
  assert (pure (w * (S64.v y2 + w * S64.v y3 + w2 * S64.v y4 + w3 * S64.v y5 + w4 * S64.v y6 + w5 * S64.v y7 + w6 * S64.v y8 + w7 * S64.v c8) == wv vt 1 + S64.v u * pp));
  assert (pure (S64.v c8 == 0));
  A.((t.(2sz) <- y2));
  A.((t.(3sz) <- y3));
  A.((t.(4sz) <- y4));
  A.((t.(5sz) <- y5));
  A.((t.(6sz) <- y6));
  A.((t.(7sz) <- y7));
  A.((t.(8sz) <- y8));
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep2 (t: A.array S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ wv vt 2 + F64.ix vt 2 * pp < w7)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ w * wv vt' 3 == wv vt 2 + F64.ix vt 2 * pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let u = A.(t.(2sz));
  let x3 = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let sl = S64.shift_left u 32ul;
  let sr = S64.shift_right u 32ul;
  split32 (S64.v u);
  let m = S128.mul_wide u (S64.classify 0xffffffff00000001uL);
  let lo = L.lo m;
  let hi = L.hi m;
  L.lo_hi m;
  let mut r = z0;
  let c3 = K.addc z0 x3 sl r;
  let y3 = !r;
  let c4 = K.addc c3 x4 sr r;
  let y4 = !r;
  let c5 = K.addc c4 x5 lo r;
  let y5 = !r;
  let c6 = K.addc c5 x6 hi r;
  let y6 = !r;
  let c7 = K.addc c6 x7 z0 r;
  let y7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let y8 = !r;
  assert (pure (S64.v y3 + w * S64.v y4 + w2 * S64.v y5 + w3 * S64.v y6 + w4 * S64.v y7 + w5 * S64.v y8 + w6 * S64.v c8 ==
                S64.v x3 + w * S64.v x4 + w2 * S64.v x5 + w3 * S64.v x6 + w4 * S64.v x7 + w5 * S64.v x8 +
                S64.v sl + w * S64.v sr + w2 * S64.v lo + w3 * S64.v hi));
  assert (pure (w * (S64.v y3 + w * S64.v y4 + w2 * S64.v y5 + w3 * S64.v y6 + w4 * S64.v y7 + w5 * S64.v y8 + w6 * S64.v c8) == wv vt 2 + S64.v u * pp));
  assert (pure (S64.v c8 == 0));
  A.((t.(3sz) <- y3));
  A.((t.(4sz) <- y4));
  A.((t.(5sz) <- y5));
  A.((t.(6sz) <- y6));
  A.((t.(7sz) <- y7));
  A.((t.(8sz) <- y8));
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn rstep3 (t: A.array S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
  pure (Seq.length vt == 9 /\ wv vt 3 + F64.ix vt 3 * pp < w6)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 9 /\ w * wv vt' 4 == wv vt 3 + F64.ix vt 3 * pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let u = A.(t.(3sz));
  let x4 = A.(t.(4sz));
  let x5 = A.(t.(5sz));
  let x6 = A.(t.(6sz));
  let x7 = A.(t.(7sz));
  let x8 = A.(t.(8sz));
  let sl = S64.shift_left u 32ul;
  let sr = S64.shift_right u 32ul;
  split32 (S64.v u);
  let m = S128.mul_wide u (S64.classify 0xffffffff00000001uL);
  let lo = L.lo m;
  let hi = L.hi m;
  L.lo_hi m;
  let mut r = z0;
  let c4 = K.addc z0 x4 sl r;
  let y4 = !r;
  let c5 = K.addc c4 x5 sr r;
  let y5 = !r;
  let c6 = K.addc c5 x6 lo r;
  let y6 = !r;
  let c7 = K.addc c6 x7 hi r;
  let y7 = !r;
  let c8 = K.addc c7 x8 z0 r;
  let y8 = !r;
  assert (pure (S64.v y4 + w * S64.v y5 + w2 * S64.v y6 + w3 * S64.v y7 + w4 * S64.v y8 + w5 * S64.v c8 ==
                S64.v x4 + w * S64.v x5 + w2 * S64.v x6 + w3 * S64.v x7 + w4 * S64.v x8 +
                S64.v sl + w * S64.v sr + w2 * S64.v lo + w3 * S64.v hi));
  assert (pure (w * (S64.v y4 + w * S64.v y5 + w2 * S64.v y6 + w3 * S64.v y7 + w4 * S64.v y8 + w5 * S64.v c8) == wv vt 3 + S64.v u * pp));
  assert (pure (S64.v c8 == 0));
  A.((t.(4sz) <- y4));
  A.((t.(5sz) <- y5));
  A.((t.(6sz) <- y6));
  A.((t.(7sz) <- y7));
  A.((t.(8sz) <- y8));
}


#restart-solver

(** [W_4 < 2 p]: one conditional subtraction of [p], by a borrow chain
    through the fifth word and a masked select. *)
[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn csub (o t: A.array S64.t) (#vo: erased (Seq.seq S64.t))
        (#pt: perm) (#vt: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to t #pt vt **
  pure (Seq.length vo == 4 /\ Seq.length vt == 9 /\ wv vt 4 < 2 * pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to t #pt vt **
  pure (Seq.length vo' == 4 /\ F64.ev vo' < pp /\ F64.ev vo' == wv vt 4 % pp)
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
  let b = K.subb z0 r4 (S64.classify 0xffffffffffffffffuL) r;
  let s0 = !r;
  let b = K.subb b r5 (S64.classify 0xffffffffuL) r;
  let s1 = !r;
  let b = K.subb b r6 z0 r;
  let s2 = !r;
  let b = K.subb b r7 (S64.classify 0xffffffff00000001uL) r;
  let s3 = !r;
  let b = K.subb b r8 z0 r;
  let s4 = !r;
  assert (pure (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) + w4 * S64.v s4 - w5 * S64.v b ==
                wv vt 4 - pp));
  mask_ok (S64.v b);
  let m = S64.sub_mod z0 b;
  let o0 = S64.select m r4 s0;
  let o1 = S64.select m r5 s1;
  let o2 = S64.select m r6 s2;
  let o3 = S64.select m r7 s3;
  assert (pure (S64.v b == 1 ==> ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == wv vt 4));
  assert (pure (S64.v b == 0 ==> ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == wv vt 4 - pp));
  modp_ok (wv vt 4) (ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3));
  put4 o o0 o1 o2 o3;
}

(** {2 The ring operations}

    On numbers below [p]: [fmul] is Montgomery's product, [R z = a b mod p]
    with [R = 2^256], and the other two are the plain sum and difference
    mod [p]. *)

#push-options "--z3rlimit 200"

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn fmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4 /\
        F64.ev va < pp /\ F64.ev vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 4 /\ F64.ev vo' < pp /\
        w4 * F64.ev vo' % pp == F64.ev va * F64.ev vb % pp)
{
  let z = S64.classify 0uL;
  let mut t = [| z; 8sz |];
  A.pts_to_len t;
  F64.mul8 t a b;
  with y. assert (A.pts_to t y);
  prod_lt (F64.ev va) (F64.ev vb) pp pp;
  let mut s = [| z; 9sz |];
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
  rstep0 s;
  with s1. assert (A.pts_to s s1);
  rstep1 s;
  with s2. assert (A.pts_to s s2);
  rstep2 s;
  with s3. assert (A.pts_to s s3);
  rstep3 s;
  with s4. assert (A.pts_to s s4);
  assert (pure (w4 * wv s4 4 == F64.ev va * F64.ev vb + (F64.ix s0 0 + w * F64.ix s1 1 + w2 * F64.ix s2 2 + w3 * F64.ix s3 3) * pp));
  csub out s;
  with o. assert (A.pts_to out o);
  glue (F64.ev o) (wv s4 4) (F64.ev va * F64.ev vb)
       (F64.ix s0 0 + w * F64.ix s1 1 + w2 * F64.ix s2 2 + w3 * F64.ix s3 3);
}

#pop-options

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn fadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4 /\
        F64.ev va < pp /\ F64.ev vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 4 /\ F64.ev vo' == (F64.ev va + F64.ev vb) % pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  A.pts_to_len b;
  consts ();
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let mut r = z0;
  let c = K.addc z0 a0 b0 r;
  let s0 = !r;
  let c = K.addc c a1 b1 r;
  let s1 = !r;
  let c = K.addc c a2 b2 r;
  let s2 = !r;
  let c = K.addc c a3 b3 r;
  let s3 = !r;
  assert (pure (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) + w4 * S64.v c ==
                F64.ev va + F64.ev vb));
  let d = K.subb z0 s0 (S64.classify 0xffffffffffffffffuL) r;
  let d0 = !r;
  let d = K.subb d s1 (S64.classify 0xffffffffuL) r;
  let d1 = !r;
  let d = K.subb d s2 z0 r;
  let d2 = !r;
  let d = K.subb d s3 (S64.classify 0xffffffff00000001uL) r;
  let d3 = !r;
  let d = K.subb d c z0 r;
  let d4 = !r;
  assert (pure (ev4 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) + w4 * S64.v d4 - w5 * S64.v d ==
                F64.ev va + F64.ev vb - pp));
  mask_ok (S64.v d);
  let m = S64.sub_mod z0 d;
  let o0 = S64.select m s0 d0;
  let o1 = S64.select m s1 d1;
  let o2 = S64.select m s2 d2;
  let o3 = S64.select m s3 d3;
  assert (pure (S64.v d == 1 ==> ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == F64.ev va + F64.ev vb));
  assert (pure (S64.v d == 0 ==> ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == F64.ev va + F64.ev vb - pp));
  modp_ok (F64.ev va + F64.ev vb) (ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3));
  put4 out o0 o1 o2 o3;
}

#restart-solver

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn fsub (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4 /\
        F64.ev va < pp /\ F64.ev vb < pp)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == 4 /\ F64.ev vo' == (F64.ev va + pp - F64.ev vb) % pp)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  A.pts_to_len b;
  consts ();
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let mut r = z0;
  let c = K.subb z0 a0 b0 r;
  let s0 = !r;
  let c = K.subb c a1 b1 r;
  let s1 = !r;
  let c = K.subb c a2 b2 r;
  let s2 = !r;
  let c = K.subb c a3 b3 r;
  let s3 = !r;
  assert (pure (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) - w4 * S64.v c ==
                F64.ev va - F64.ev vb));
  mask_ok (S64.v c);
  let m = S64.sub_mod z0 c;
  let q0 = S64.select m (S64.classify 0xffffffffffffffffuL) z0;
  let q1 = S64.select m (S64.classify 0xffffffffuL) z0;
  let q3 = S64.select m (S64.classify 0xffffffff00000001uL) z0;
  let d = K.addc z0 s0 q0 r;
  let d0 = !r;
  let d = K.addc d s1 q1 r;
  let d1 = !r;
  let d = K.addc d s2 z0 r;
  let d2 = !r;
  let d = K.addc d s3 q3 r;
  let d3 = !r;
  assert (pure (ev4 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) + w4 * S64.v d ==
                ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) +
                ev4 (S64.v q0) (S64.v q1) 0 (S64.v q3)));
  assert (pure (S64.v c == 0 ==> ev4 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) == F64.ev va - F64.ev vb));
  assert (pure (S64.v c == 1 ==> ev4 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3) == F64.ev va - F64.ev vb + pp));
  modp_ok (F64.ev va + pp - F64.ev vb) (ev4 (S64.v d0) (S64.v d1) (S64.v d2) (S64.v d3));
  put4 out d0 d1 d2 d3;
}

#pop-options
