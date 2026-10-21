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

(** Keccak-f[1600].

    The state is a twenty-five element slice of sixty-four bit lanes, indexed
    [x + 5 * y] exactly as [Spec.SHA3] indexes its sequences, so every step
    below has a postcondition of the form [vst == Spec.SHA3.theta vst0] and
    there is no representation change to reason about.

    {b A round is one pass, not three.}  theta, rho-pi, chi and iota are
    fused, in the style of the Keccak team's reference code: the round reads
    all twenty-five lanes of its input once, computes the five column
    parities and the five theta values in registers, and then, one output
    row at a time, forms the five rho-pi lanes of that row as
    [rotl (a[src] ^ d[col]) rho] and writes chi of them straight to the
    output.  Nothing is stored between the steps.  The earlier version did
    theta in place, rho-pi into a scratch buffer and chi back, which is three
    full read-write sweeps of the state per round; fusing them is 1.15-1.3x
    on SHA3-256.

    The input and output of a round must be different buffers, so the
    twenty-five lane scratch buffer [b] that the interface already threads
    through is used as the other half of a ping-pong: rounds alternate
    [st -> b] and [b -> st], and twenty-four is even, so the result ends up
    back in [st].

    {b Everything inside a round is unrolled.}  A round is twenty-five lanes,
    and writing it as a [while] loop over a runtime index costs far more than
    the loop overhead: the lane index has to be decomposed with a runtime [% 5]
    and [/ 5], the rho offsets have to be read from a table instead of being
    immediate, and -- worst -- the rotate becomes a variable-count rotate,
    which on x86 is three instructions with a flag dependency instead of one
    [rol].  Neither gcc nor clang unrolls these loops at [-O3] by default (the
    trip count is twenty-five and the bodies are not tiny), so the cost is
    paid at run time, twenty-four times per permutation.

    Each step is therefore written as an [inline_for_extraction] lane function
    -- verified once, against a symbolic index -- and then applied twenty-five
    times to literal indices.  The extracted C is straight-line code with
    immediate offsets and immediate rotation counts, and the proof cost is one
    lane, not twenty-five.

    {b The permutation itself is [inline_for_extraction] too}, so that it
    lands inside each of the six sponges rather than being called from them.
    That is worth 2.2x on a short SHA3-256 and 1.14x on bulk, on top of what
    specialising the rate already buys: the round counter and the state
    pointers become local, the twenty-four iterations lose their call
    boundary, and the two twenty-five word scratch buffers stop having to be
    re-established.  gcc will do some of this on its own -- it was cloning
    the round function already -- but only while its interprocedural budget lasts,
    and clang does none of it.

    The output-lane functions carry a prefix invariant saying that everything
    below the current index already agrees with [round n a]; the rho-pi lanes
    in between live only in registers, each with a postcondition naming its
    entry of [rho_pi (theta a)].  That is exactly the invariant the
    [while] loops used to carry, so each call site discharges the same
    obligation a loop iteration used to, and the twenty-five calls chain
    without the solver ever seeing a nested [Seq.upd]. *)
module Hacl.Hash.SHA3.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module G = FStar.Ghost
module Loops = Hacl.Spec.Loops

(** {2 Rotation by a literal offset}

    [Hacl.Secret.UInt64.rotate_left] wants a nonzero offset, and [rotc 0] is
    zero, so the zero case is a branch.  Every caller below passes a literal,
    so the branch folds at compile time and what reaches the back end is a
    single [rol] with an immediate. *)

let rotl_u32 (x: S64.t) (k: U32.t { U32.v k < 64 }) : (y: S64.t { y == rotl x (U32.v k) }) =
  if k = 0ul then x else (U32.uv_inv k; S64.rotate_left x k)

(** {2 The pieces of a fused round} *)

(** [theta_d] from the two neighbouring column parities, with the column
    indices already reduced mod 5 (proof-only helper). *)
let theta_d_from (s: state) (x: nat { x < 5 }) (xm xp: nat) (cm cp: S64.t)
  : Lemma (requires xm == (x + 4) % 5 /\ xp == (x + 1) % 5 /\
                    cm == theta_c s xm /\ cp == theta_c s xp)
          (ensures S64.logxor cm (rotl cp 1) == theta_d s x)
  = ()

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** One lane of [rho_pi (theta a)], computed from registers: [s] is the
    source lane of [a], [d] is its column's theta value, [k] is its rho
    offset.  Nothing is stored; the result goes straight into chi. *)
inline_for_extraction
fn bval (va: erased (Seq.seq S64.t)) (i: SZ.t) (s: S64.t) (d: S64.t) (k: U32.t)
requires pure (Seq.length va == 25 /\ SZ.v i < 25 /\ U32.v k < 64 /\
               s == Seq.index va (rho_pi_src (SZ.v i)) /\
               d == theta_d va (rho_pi_src (SZ.v i) % 5) /\
               U32.v k == rotc (rho_pi_src (SZ.v i)))
returns b: S64.t
ensures pure (Seq.length va == 25 /\ SZ.v i < 25 /\
              b == Seq.index (rho_pi (theta va)) (SZ.v i))
{
  theta_index (reveal va) (rho_pi_src (SZ.v i));
  rho_pi_index (theta (reveal va)) (SZ.v i);
  rotl_u32 (S64.logxor s d) k
}

(** One output lane of a round, other than lane 0: chi of three lanes of the
    same row of [rho_pi (theta a)], all three already in registers. *)
inline_for_extraction
fn chi_out (e: A.array S64.t) (va: erased (Seq.seq S64.t)) (n: erased nat)
           (i: SZ.t) (b0: S64.t) (b1: S64.t) (b2: S64.t)
           (#ve: erased (Seq.seq S64.t))
requires A.pts_to e ve **
         pure (Seq.length va == 25 /\ Seq.length ve == 25 /\ n < 24 /\
               0 < SZ.v i /\ SZ.v i < 25 /\
               b0 == Seq.index (rho_pi (theta va)) (SZ.v i) /\
               b1 == Seq.index (rho_pi (theta va)) (idx ((SZ.v i % 5 + 1) % 5) (SZ.v i / 5)) /\
               b2 == Seq.index (rho_pi (theta va)) (idx ((SZ.v i % 5 + 2) % 5) (SZ.v i / 5)) /\
               (forall (m: nat). m < SZ.v i ==> Seq.index ve m == Seq.index (round n va) m))
ensures exists* (ve': Seq.seq S64.t).
  A.pts_to e ve' **
  pure (Seq.length va == 25 /\ Seq.length ve' == 25 /\ n < 24 /\ SZ.v i < 25 /\
        (forall (m: nat). m < SZ.v i + 1 ==> Seq.index ve' m == Seq.index (round n va) m))
{
  A.pts_to_len e;
  chi_index (rho_pi (theta (reveal va))) (SZ.v i);
  round_index (reveal va) n (SZ.v i);
  A.((e.(i) <- S64.logxor b0 (S64.logand (S64.lognot b1) b2)));
}

(** Lane 0, with iota folded in. *)
inline_for_extraction
fn chi_out0 (e: A.array S64.t) (va: erased (Seq.seq S64.t)) (n: erased nat)
            (r: S64.t) (b0: S64.t) (b1: S64.t) (b2: S64.t)
            (#ve: erased (Seq.seq S64.t))
requires A.pts_to e ve **
         pure (Seq.length va == 25 /\ Seq.length ve == 25 /\ n < 24 /\
               r == Seq.index rc n /\
               b0 == Seq.index (rho_pi (theta va)) 0 /\
               b1 == Seq.index (rho_pi (theta va)) 1 /\
               b2 == Seq.index (rho_pi (theta va)) 2)
ensures exists* (ve': Seq.seq S64.t).
  A.pts_to e ve' **
  pure (Seq.length va == 25 /\ Seq.length ve' == 25 /\ n < 24 /\
        (forall (m: nat). m < 1 ==> Seq.index ve' m == Seq.index (round n va) m))
{
  A.pts_to_len e;
  chi_index (rho_pi (theta (reveal va))) 0;
  round_index0 (reveal va) n;
  A.((e.(0sz) <- S64.logxor (S64.logxor b0 (S64.logand (S64.lognot b1) b2)) r));
}

#pop-options

(** {2 One round, and the permutation} *)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [e] becomes [round n a].  [a] is only read, and it is read once: the
    twenty-five loads at the top feed both the column parities and, through
    [bval], the rho-pi lanes. *)
inline_for_extraction
fn fround (a: A.array S64.t) (e: A.array S64.t)
          (rc_tbl: A.array S64.t) (n: SZ.t)
          (#pa: perm) (#va: erased (Seq.seq S64.t)) (#ve0: erased (Seq.seq S64.t))
          (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to e ve0 ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length va == 25 /\ Seq.length ve0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ SZ.v n < 24)
ensures exists* (ve: Seq.seq S64.t).
  A.pts_to a #pa va ** A.pts_to e ve ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length va == 25 /\ Seq.length ve == 25 /\ SZ.v n < 24 /\
        ve == round (SZ.v n) (reveal va))
{
  A.pts_to_len a;
  A.pts_to_len e;
  A.pts_to_len rc_tbl;
  rotc_lit ();
  rho_pi_src_lit ();
  chi_nbr_lit ();
  let s00 = A.(a.(0sz));
  let s01 = A.(a.(1sz));
  let s02 = A.(a.(2sz));
  let s03 = A.(a.(3sz));
  let s04 = A.(a.(4sz));
  let s05 = A.(a.(5sz));
  let s06 = A.(a.(6sz));
  let s07 = A.(a.(7sz));
  let s08 = A.(a.(8sz));
  let s09 = A.(a.(9sz));
  let s10 = A.(a.(10sz));
  let s11 = A.(a.(11sz));
  let s12 = A.(a.(12sz));
  let s13 = A.(a.(13sz));
  let s14 = A.(a.(14sz));
  let s15 = A.(a.(15sz));
  let s16 = A.(a.(16sz));
  let s17 = A.(a.(17sz));
  let s18 = A.(a.(18sz));
  let s19 = A.(a.(19sz));
  let s20 = A.(a.(20sz));
  let s21 = A.(a.(21sz));
  let s22 = A.(a.(22sz));
  let s23 = A.(a.(23sz));
  let s24 = A.(a.(24sz));
  let c0 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s00 s05) s10) s15) s20;
  let c1 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s01 s06) s11) s16) s21;
  let c2 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s02 s07) s12) s17) s22;
  let c3 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s03 s08) s13) s18) s23;
  let c4 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s04 s09) s14) s19) s24;
  theta_c_eq (reveal va) 0;
  theta_c_eq (reveal va) 1;
  theta_c_eq (reveal va) 2;
  theta_c_eq (reveal va) 3;
  theta_c_eq (reveal va) 4;
  let d0 = S64.logxor c4 (rotl_u32 c1 1ul);
  theta_d_from (reveal va) 0 4 1 c4 c1;
  assert (pure (d0 == theta_d (reveal va) 0));
  let d1 = S64.logxor c0 (rotl_u32 c2 1ul);
  theta_d_from (reveal va) 1 0 2 c0 c2;
  assert (pure (d1 == theta_d (reveal va) 1));
  let d2 = S64.logxor c1 (rotl_u32 c3 1ul);
  theta_d_from (reveal va) 2 1 3 c1 c3;
  assert (pure (d2 == theta_d (reveal va) 2));
  let d3 = S64.logxor c2 (rotl_u32 c4 1ul);
  theta_d_from (reveal va) 3 2 4 c2 c4;
  assert (pure (d3 == theta_d (reveal va) 3));
  let d4 = S64.logxor c3 (rotl_u32 c0 1ul);
  theta_d_from (reveal va) 4 3 0 c3 c0;
  assert (pure (d4 == theta_d (reveal va) 4));
  let b00 = bval va 0sz s00 d0 0ul;
  let b01 = bval va 1sz s06 d1 44ul;
  let b02 = bval va 2sz s12 d2 43ul;
  let b03 = bval va 3sz s18 d3 21ul;
  let b04 = bval va 4sz s24 d4 14ul;
  let r = A.(rc_tbl.(n));
  chi_out0 e va (SZ.v n) r b00 b01 b02;
  chi_out e va (SZ.v n) 1sz b01 b02 b03;
  chi_out e va (SZ.v n) 2sz b02 b03 b04;
  chi_out e va (SZ.v n) 3sz b03 b04 b00;
  chi_out e va (SZ.v n) 4sz b04 b00 b01;
  let b05 = bval va 5sz s03 d3 28ul;
  let b06 = bval va 6sz s09 d4 20ul;
  let b07 = bval va 7sz s10 d0 3ul;
  let b08 = bval va 8sz s16 d1 45ul;
  let b09 = bval va 9sz s22 d2 61ul;
  chi_out e va (SZ.v n) 5sz b05 b06 b07;
  chi_out e va (SZ.v n) 6sz b06 b07 b08;
  chi_out e va (SZ.v n) 7sz b07 b08 b09;
  chi_out e va (SZ.v n) 8sz b08 b09 b05;
  chi_out e va (SZ.v n) 9sz b09 b05 b06;
  let b10 = bval va 10sz s01 d1 1ul;
  let b11 = bval va 11sz s07 d2 6ul;
  let b12 = bval va 12sz s13 d3 25ul;
  let b13 = bval va 13sz s19 d4 8ul;
  let b14 = bval va 14sz s20 d0 18ul;
  chi_out e va (SZ.v n) 10sz b10 b11 b12;
  chi_out e va (SZ.v n) 11sz b11 b12 b13;
  chi_out e va (SZ.v n) 12sz b12 b13 b14;
  chi_out e va (SZ.v n) 13sz b13 b14 b10;
  chi_out e va (SZ.v n) 14sz b14 b10 b11;
  let b15 = bval va 15sz s04 d4 27ul;
  let b16 = bval va 16sz s05 d0 36ul;
  let b17 = bval va 17sz s11 d1 10ul;
  let b18 = bval va 18sz s17 d2 15ul;
  let b19 = bval va 19sz s23 d3 56ul;
  chi_out e va (SZ.v n) 15sz b15 b16 b17;
  chi_out e va (SZ.v n) 16sz b16 b17 b18;
  chi_out e va (SZ.v n) 17sz b17 b18 b19;
  chi_out e va (SZ.v n) 18sz b18 b19 b15;
  chi_out e va (SZ.v n) 19sz b19 b15 b16;
  let b20 = bval va 20sz s02 d2 62ul;
  let b21 = bval va 21sz s08 d3 55ul;
  let b22 = bval va 22sz s14 d4 39ul;
  let b23 = bval va 23sz s15 d0 41ul;
  let b24 = bval va 24sz s21 d1 2ul;
  chi_out e va (SZ.v n) 20sz b20 b21 b22;
  chi_out e va (SZ.v n) 21sz b21 b22 b23;
  chi_out e va (SZ.v n) 22sz b22 b23 b24;
  chi_out e va (SZ.v n) 23sz b23 b24 b20;
  chi_out e va (SZ.v n) 24sz b24 b20 b21;
  with ve. assert (A.pts_to e ve);
  assert (pure (Seq.length (round (SZ.v n) (reveal va)) == 25));
  assert (pure (reveal ve `Seq.equal` (round (SZ.v n) (reveal va))));
}

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** Twenty-four rounds, as twelve trips round a loop whose body is two
    rounds: [st] to [b], then [b] back to [st].  The double round is what
    lets each round read one buffer and write the other without a copy.
    The loop itself is {i not} unrolled further: twenty-four copies of a
    fully unrolled round is about twenty kilobytes of code, which costs more
    in instruction cache than it saves in loop overhead. *)
inline_for_extraction
fn permute_impl (st: A.array S64.t) (b: A.array S64.t)
                (rc_tbl: A.array S64.t)
                (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
                (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\ Seq.length vb == 25 /\
        vst == permute (reveal vst0))
{
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 24sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst ** A.pts_to b vb **
    A.pts_to rc_tbl #prc vrc **
    pure (Seq.length vst0 == 25 /\ SZ.v vi <= 24 /\ SZ.v vi % 2 == 0 /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\
          vst == Loops.repeati (SZ.v vi) round (reveal vst0))
  decreases (24 - SZ.v (!i))
  {
    let vi = !i;
    Loops.unfold_repeati (SZ.v vi) round (reveal vst0);
    fround st b rc_tbl vi;
    let vj = SZ.add vi 1sz;
    Loops.unfold_repeati (SZ.v vj) round (reveal vst0);
    fround b st rc_tbl vj;
    i := SZ.add vi 2sz;
  };
}

#pop-options
