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

(** Poly1305's field, on five sixty-four-bit secret integers.

    A field element is a five-element slice; limb [i] carries bits [26i] to
    [26i+26].  Twenty-six is the size that makes the widest intermediate of
    the multiplication -- twenty-one products of a twenty-eight-bit limb by a
    twenty-six-bit one -- land under [2^59], so the whole of Poly1305 fits in
    [uint64] and the extracted C needs no compiler-specific
    hundred-and-twenty-eight-bit type.

    All the arithmetic is in [Spec.Poly1305.Field].  The job here is only to
    compute the numbers that lemma names: [fmul] exhibits its five results as
    the [chain] expressions and [mul_reduce_ok] does the rest.  That is
    deliberate.  Applying a congruence lemma from inside a Pulse [fn] drags
    the whole separation-logic context into the query, and the arithmetic
    here is heavy enough without it.

    The limbs are secret integers throughout: every operation below is a
    64-bit add, multiply, shift or mask, all of them constant time, and there
    is no branch anywhere in the module. *)
module Hacl.Poly1305.Field

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Poly1305.Field

module S = Pulse.Lib.Slice
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module G = FStar.Ghost

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Viewing a slice as a number} *)

let vv (v: Seq.seq S64.t) (i: nat) : GTot nat =
  if i < Seq.length v then S64.v (Seq.index v i) else 0

let feval (v: Seq.seq S64.t) : GTot nat = as_nat5 (vv v 0) (vv v 1) (vv v 2) (vv v 3) (vv v 4)

let bounded (v: Seq.seq S64.t) (n: nat) : GTot prop =
  bounded5 (vv v 0) (vv v 1) (vv v 2) (vv v 3) (vv v 4) n

(** The five wide limbs of the schoolbook product, as a single named
    predicate.  Naming it matters: written out, the five equations are in
    scope for every query in [fmul], and [fmul]'s queries already carry a
    separation-logic context. *)
let is_product (vd vh vr: Seq.seq S64.t) : GTot prop =
  vv vd 0 == d0 (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
                (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4) /\
  vv vd 1 == d1 (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
                (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4) /\
  vv vd 2 == d2 (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
                (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4) /\
  vv vd 3 == d3 (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
                (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4) /\
  vv vd 4 == d4 (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
                (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4)

(** What [fmul] leaves behind.  Named for the same reason [is_product] is:
    left written out, [fmul]'s postcondition makes the solver unfold [feval]
    -- five [as_nat5] limbs, and [prime] -- in a query that also carries the
    heap.  Named, the match between the lemma's conclusion and the function's
    contract is syntactic. *)
let fmul_post (vh vr vh': Seq.seq S64.t) : GTot prop =
  bounded vh' 27 /\ feval vh' % prime == (feval vh * feval vr) % prime

(** [mul_reduce_ok] at the sequences, so that the Pulse code applies one
    lemma to one hypothesis and never sees the arithmetic. *)
let fmul_ok (vh vr vd vh': Seq.seq S64.t)
  : Lemma (requires bounded vh 28 /\ bounded vr 26 /\ is_product vd vh vr /\
                    chain (vv vd 0) (vv vd 1) (vv vd 2) (vv vd 3) (vv vd 4)
                          (vv vh' 0) (vv vh' 1) (vv vh' 2) (vv vh' 3) (vv vh' 4))
          (ensures fmul_post vh vr vh')
  = mul_reduce_ok (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
                  (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4)
                  (vv vh' 0) (vv vh' 1) (vv vh' 2) (vv vh' 3) (vv vh' 4)

(** {2 The four machine operations}

    Each is the obvious [uint64] instruction plus the argument that its
    result did not wrap.  Keeping them separate from the code that uses them
    means the modular-arithmetic side condition is discharged once each,
    against a two-line context, rather than twenty-five times inside [fmul]. *)

inline_for_extraction
let mask26 : m: S64.t { S64.v m == pow2 26 - 1 } =
  assert_norm (pow2 26 - 1 == 0x3ffffff);
  S64.classify 0x3ffffffuL

inline_for_extraction
let lo26 (x: S64.t) : r: S64.t { S64.v r == S64.v x % pow2 26 } =
  UInt.logand_mask #64 (S64.v x) 26;
  S64.logand x mask26

inline_for_extraction
let hi26 (x: S64.t) : r: S64.t { S64.v r == S64.v x / pow2 26 } =
  S64.shift_right x 26ul

inline_for_extraction
let add2 (x y: S64.t)
  : Pure S64.t (requires S64.v x + S64.v y < pow2 64)
               (ensures fun z -> S64.v z == S64.v x + S64.v y)
  = Math.small_mod (S64.v x + S64.v y) (pow2 64);
    S64.add_mod x y

inline_for_extraction
let mul26 (x y: S64.t)
  : Pure S64.t (requires S64.v x < pow2 28 /\ S64.v y < pow2 26)
               (ensures fun z -> S64.v z == S64.v x * S64.v y /\ S64.v z < pow2 54)
  = prod_bound (S64.v x) (S64.v y);
    Math.pow2_lt_compat 64 54;
    Math.small_mod (S64.v x * S64.v y) (pow2 64);
    S64.mul_mod x y

inline_for_extraction
let times5 (x: S64.t)
  : Pure S64.t (requires 5 * S64.v x < pow2 64)
               (ensures fun z -> S64.v z == 5 * S64.v x)
  = Math.small_mod (5 * S64.v x) (pow2 64);
    S64.mul_mod (S64.classify 5uL) x

let five_fits (x: nat) : Lemma (requires x < pow2 54) (ensures 5 * x < pow2 64)
  = assert_norm (5 * pow2 54 < pow2 64)

(** Twenty-one products of at most [2^54] fit under [2^59]; the solver needs
    telling that [2^59] is thirty-two times [2^54] to see it. *)
let sum21 (_: unit) : Lemma (32 * pow2 54 == pow2 59)
  = Math.pow2_plus 5 54;
    assert_norm (pow2 5 == 32)

inline_for_extraction
let add5w (a b c d e: S64.t)
  : Pure S64.t
      (requires S64.v a + S64.v b + S64.v c + S64.v d + S64.v e < pow2 59)
      (ensures fun z -> S64.v z == S64.v a + S64.v b + S64.v c + S64.v d + S64.v e /\
                     S64.v z < pow2 59)
  = Math.pow2_lt_compat 64 59;
    let s1 = add2 a b in
    let s2 = add2 s1 c in
    let s3 = add2 s2 d in
    add2 s3 e

#pop-options

(** {2 Multiplication}

    [h <- h * r mod (2^130 - 5)], in two halves.

    The halves exist for the proof, not for the C: the schoolbook products and
    the carry chain in one [fn] made a query that ran for half an hour without
    an answer, and split in two -- with a five-word scratch slice carrying the
    wide limbs between them -- each half goes through in a couple of minutes.
    It is the same lesson as in the specification, one level up: what the
    solver cannot do is not any individual step but every step with all the
    others in scope. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** The twenty-five products, summed into five limbs under [2^58].  The four
    terms of each limb that would land at or above [2^130] have already been
    brought down five places and multiplied by five. *)
fn mul_limbs (d: S.slice S64.t) (h: S.slice S64.t) (r: S.slice S64.t)
             (#vd: erased (Seq.seq S64.t))
             (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
requires S.pts_to d vd ** S.pts_to h vh ** S.pts_to r vr **
         pure (Seq.length vd == 5 /\ Seq.length vh == 5 /\ Seq.length vr == 5 /\
               bounded vh 28 /\ bounded vr 26)
ensures exists* (vd': Seq.seq S64.t).
  S.pts_to d vd' ** S.pts_to h vh ** S.pts_to r vr **
  pure (Seq.length vh == 5 /\ Seq.length vr == 5 /\
        bounded vh 28 /\ bounded vr 26 /\
        Seq.length vd' == 5 /\ bounded vd' 59 /\ is_product vd' vh vr)
{
  S.pts_to_len d;
  S.pts_to_len h;
  S.pts_to_len r;
  sum21 ();
  let h0 = S.(h.(0sz));
  let h1 = S.(h.(1sz));
  let h2 = S.(h.(2sz));
  let h3 = S.(h.(3sz));
  let h4 = S.(h.(4sz));
  let r0 = S.(r.(0sz));
  let r1 = S.(r.(1sz));
  let r2 = S.(r.(2sz));
  let r3 = S.(r.(3sz));
  let r4 = S.(r.(4sz));

  let p00 = mul26 h0 r0;
  let p01 = mul26 h0 r1;
  let p02 = mul26 h0 r2;
  let p03 = mul26 h0 r3;
  let p04 = mul26 h0 r4;
  let p10 = mul26 h1 r0;
  let p11 = mul26 h1 r1;
  let p12 = mul26 h1 r2;
  let p13 = mul26 h1 r3;
  let p14 = mul26 h1 r4;
  let p20 = mul26 h2 r0;
  let p21 = mul26 h2 r1;
  let p22 = mul26 h2 r2;
  let p23 = mul26 h2 r3;
  let p24 = mul26 h2 r4;
  let p30 = mul26 h3 r0;
  let p31 = mul26 h3 r1;
  let p32 = mul26 h3 r2;
  let p33 = mul26 h3 r3;
  let p34 = mul26 h3 r4;
  let p40 = mul26 h4 r0;
  let p41 = mul26 h4 r1;
  let p42 = mul26 h4 r2;
  let p43 = mul26 h4 r3;
  let p44 = mul26 h4 r4;

  five_fits (S64.v p14);
  five_fits (S64.v p23);
  five_fits (S64.v p32);
  five_fits (S64.v p41);
  five_fits (S64.v p24);
  five_fits (S64.v p33);
  five_fits (S64.v p42);
  five_fits (S64.v p34);
  five_fits (S64.v p43);
  five_fits (S64.v p44);

  let e0 = add5w p00 (times5 p14) (times5 p23) (times5 p32) (times5 p41);
  let e1 = add5w p01 p10 (times5 p24) (times5 p33) (times5 p42);
  let e2 = add5w p02 p11 p20 (times5 p34) (times5 p43);
  let e3 = add5w p03 p12 p21 p30 (times5 p44);
  let e4 = add5w p04 p13 p22 p31 p40;

  S.((d.(0sz) <- e0));
  S.((d.(1sz) <- e1));
  S.((d.(2sz) <- e2));
  S.((d.(3sz) <- e3));
  S.((d.(4sz) <- e4));
}

(** The six carries: five up, and one wrapping the top round to the bottom
    multiplied by five, then one more up.  This computes exactly
    [Spec.Poly1305.Field.chain] and claims nothing else; what that chain is
    worth is [carry_chain_cong]'s business. *)
fn carry_chain_impl (h: S.slice S64.t) (d: S.slice S64.t)
                    (#vh: erased (Seq.seq S64.t)) (#vd: erased (Seq.seq S64.t))
requires S.pts_to h vh ** S.pts_to d vd **
         pure (Seq.length vh == 5 /\ Seq.length vd == 5 /\ bounded vd 59)
ensures exists* (vh': Seq.seq S64.t). S.pts_to h vh' ** S.pts_to d vd **
  pure (Seq.length vd == 5 /\ bounded vd 59 /\ Seq.length vh' == 5 /\
        chain (vv vd 0) (vv vd 1) (vv vd 2) (vv vd 3) (vv vd 4)
              (vv vh' 0) (vv vh' 1) (vv vh' 2) (vv vh' 3) (vv vh' 4))
{
  S.pts_to_len h;
  S.pts_to_len d;
  let e0 = S.(d.(0sz));
  let e1 = S.(d.(1sz));
  let e2 = S.(d.(2sz));
  let e3 = S.(d.(3sz));
  let e4 = S.(d.(4sz));

  chain_fits (S64.v e0) (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4);
  Math.pow2_lt_compat 64 60;
  Math.pow2_lt_compat 64 38;

  let f1 = add2 e1 (hi26 e0);
  let f2 = add2 e2 (hi26 f1);
  let f3 = add2 e3 (hi26 f2);
  let f4 = add2 e4 (hi26 f3);
  div_bound (S64.v f4) 60 26;
  Math.pow2_le_compat 54 34;
  five_fits (S64.v (hi26 f4));
  let g0 = add2 (lo26 e0) (times5 (hi26 f4));

  S.((h.(0sz) <- lo26 g0));
  S.((h.(1sz) <- add2 (lo26 f1) (hi26 g0)));
  S.((h.(2sz) <- lo26 f2));
  S.((h.(3sz) <- lo26 f3));
  S.((h.(4sz) <- lo26 f4));
}

fn fmul (h: S.slice S64.t) (r: S.slice S64.t) (d: S.slice S64.t)
        (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
        (#vd: erased (Seq.seq S64.t))
requires S.pts_to h vh ** S.pts_to r vr ** S.pts_to d vd **
         pure (Seq.length vh == 5 /\ Seq.length vr == 5 /\ Seq.length vd == 5 /\
               bounded vh 28 /\ bounded vr 26)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t).
  S.pts_to h vh' ** S.pts_to r vr ** S.pts_to d vd' **
  pure (Seq.length vh == 5 /\ Seq.length vr == 5 /\
        bounded vh 28 /\ bounded vr 26 /\
        Seq.length vd' == 5 /\
        Seq.length vh' == 5 /\ fmul_post vh vr vh')
{
  mul_limbs d h r;
  with vd'. assert (S.pts_to d vd');
  carry_chain_impl h d;
  with vh'. assert (S.pts_to h vh');
  fmul_ok vh vr vd' vh';
  (* A Pulse [fn] must not end with a lemma call: the function's [ensures] is
     checked at the last statement, and a trailing lemma's conclusion is not
     yet in scope there.  Any statement after it will do. *)
  S.pts_to_len h;
}

#pop-options

(** {2 Addition}

    Limbwise, with no carrying at all: the accumulator comes out of [fmul]
    under [2^27] and a block's limbs are under [2^26], so the sum is under
    [2^28], which is exactly what [fmul] accepts.  That is the whole reason
    the multiplication was given two bits of slack rather than one -- it
    means the block loop is a multiply and five adds, with no carry chain
    between them. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

fn fadd (h: S.slice S64.t) (b: S.slice S64.t)
        (#vh: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S64.t))
requires S.pts_to h vh ** S.pts_to b vb **
         pure (Seq.length vh == 5 /\ Seq.length vb == 5 /\
               bounded vh 27 /\ bounded vb 26)
ensures exists* (vh': Seq.seq S64.t). S.pts_to h vh' ** S.pts_to b vb **
  pure (Seq.length vh == 5 /\ Seq.length vb == 5 /\
        Seq.length vh' == 5 /\ bounded vh' 28 /\
        feval vh' == feval vh + feval vb)
{
  S.pts_to_len h;
  S.pts_to_len b;
  Math.pow2_lt_compat 27 26;
  Math.pow2_double_sum 27;
  Math.pow2_lt_compat 64 28;
  add5_eval (vv vh 0) (vv vh 1) (vv vh 2) (vv vh 3) (vv vh 4)
            (vv vb 0) (vv vb 1) (vv vb 2) (vv vb 3) (vv vb 4);
  let a0 = S.(h.(0sz));
  let a1 = S.(h.(1sz));
  let a2 = S.(h.(2sz));
  let a3 = S.(h.(3sz));
  let a4 = S.(h.(4sz));
  let b0 = S.(b.(0sz));
  let b1 = S.(b.(1sz));
  let b2 = S.(b.(2sz));
  let b3 = S.(b.(3sz));
  let b4 = S.(b.(4sz));
  S.((h.(0sz) <- add2 a0 b0));
  S.((h.(1sz) <- add2 a1 b1));
  S.((h.(2sz) <- add2 a2 b2));
  S.((h.(3sz) <- add2 a3 b3));
  S.((h.(4sz) <- add2 a4 b4));
}

(** The accumulator starts at zero. *)
fn set_zero (h: S.slice S64.t) (#vh: erased (Seq.seq S64.t))
requires S.pts_to h vh ** pure (Seq.length vh == 5)
ensures exists* (vh': Seq.seq S64.t). S.pts_to h vh' **
  pure (Seq.length vh' == 5 /\ bounded vh' 26 /\ feval vh' == 0)
{
  S.pts_to_len h;
  S.((h.(0sz) <- S64.zero));
  S.((h.(1sz) <- S64.zero));
  S.((h.(2sz) <- S64.zero));
  S.((h.(3sz) <- S64.zero));
  S.((h.(4sz) <- S64.zero));
}

#pop-options
