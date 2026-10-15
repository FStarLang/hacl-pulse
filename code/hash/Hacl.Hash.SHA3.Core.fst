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

    One scratch buffer is threaded through: [b], twenty-five lanes, holds the
    state between rho-pi and chi.  rho-pi is a permutation of the lanes
    combined with a rotation, so it cannot be done in place; chi reads three
    lanes to write one, so it cannot either.  theta needs no buffer: its five
    column parities are held in local variables.

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
    [round_impl] already -- but only while its interprocedural budget lasts,
    and clang does none of it.

    The lane functions all carry the same shape of specification: a prefix
    invariant saying that everything below the current index already agrees
    with the specification's sequence.  That is exactly the invariant the
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

(** {2 theta}

    The five column parities and the five values folded back into the columns
    are ordinary local variables; the twenty-five lanes are read before any is
    written, so the whole step reads the state once and writes it once. *)

(** [theta_d] from the two neighbouring column parities, with the column
    indices already reduced mod 5 (proof-only helper). *)
let theta_d_from (s: state) (x: nat { x < 5 }) (xm xp: nat) (cm cp: S64.t)
  : Lemma (requires xm == (x + 4) % 5 /\ xp == (x + 1) % 5 /\
                    cm == theta_c s xm /\ cp == theta_c s xp)
          (ensures S64.logxor cm (rotl cp 1) == theta_d s x)
  = ()

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** One lane of theta.  [a] is the lane's old value and [d] is the value its
    column contributes, both already in registers, so the lane function is a
    single xor and a single store. *)
inline_for_extraction
fn theta_lane (st: A.array S64.t) (vst0: erased (Seq.seq S64.t))
              (i: SZ.t) (a: S64.t) (d: S64.t)
              (#vst: erased (Seq.seq S64.t))
requires A.pts_to st vst **
         pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\ SZ.v i < 25 /\
               a == Seq.index vst0 (SZ.v i) /\ d == theta_d vst0 (SZ.v i % 5) /\
               (forall (k: nat). k < SZ.v i ==> Seq.index vst k == Seq.index (theta vst0) k))
ensures exists* (vst': Seq.seq S64.t).
  A.pts_to st vst' **
  pure (Seq.length vst0 == 25 /\ Seq.length vst' == 25 /\ SZ.v i < 25 /\
        (forall (k: nat). k < SZ.v i + 1 ==> Seq.index vst' k == Seq.index (theta vst0) k))
{
  A.pts_to_len st;
  theta_index (reveal vst0) (SZ.v i);
  A.((st.(i) <- S64.logxor a d));
}

(** [st] becomes [theta st]. *)
inline_for_extraction
fn theta_impl (st: A.array S64.t) (#vst0: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** pure (Seq.length vst0 == 25)
ensures exists* (vst: Seq.seq S64.t).
  A.pts_to st vst **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\ vst == theta (reveal vst0))
{
  A.pts_to_len st;
  let s00 = A.(st.(0sz));
  let s01 = A.(st.(1sz));
  let s02 = A.(st.(2sz));
  let s03 = A.(st.(3sz));
  let s04 = A.(st.(4sz));
  let s05 = A.(st.(5sz));
  let s06 = A.(st.(6sz));
  let s07 = A.(st.(7sz));
  let s08 = A.(st.(8sz));
  let s09 = A.(st.(9sz));
  let s10 = A.(st.(10sz));
  let s11 = A.(st.(11sz));
  let s12 = A.(st.(12sz));
  let s13 = A.(st.(13sz));
  let s14 = A.(st.(14sz));
  let s15 = A.(st.(15sz));
  let s16 = A.(st.(16sz));
  let s17 = A.(st.(17sz));
  let s18 = A.(st.(18sz));
  let s19 = A.(st.(19sz));
  let s20 = A.(st.(20sz));
  let s21 = A.(st.(21sz));
  let s22 = A.(st.(22sz));
  let s23 = A.(st.(23sz));
  let s24 = A.(st.(24sz));
  let c0 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s00 s05) s10) s15) s20;
  let c1 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s01 s06) s11) s16) s21;
  let c2 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s02 s07) s12) s17) s22;
  let c3 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s03 s08) s13) s18) s23;
  let c4 = S64.logxor (S64.logxor (S64.logxor (S64.logxor s04 s09) s14) s19) s24;
  theta_c_eq (reveal vst0) 0;
  theta_c_eq (reveal vst0) 1;
  theta_c_eq (reveal vst0) 2;
  theta_c_eq (reveal vst0) 3;
  theta_c_eq (reveal vst0) 4;
  let d0 = S64.logxor c4 (rotl_u32 c1 1ul);
  theta_d_from (reveal vst0) 0 4 1 c4 c1;
  assert (pure (d0 == theta_d (reveal vst0) 0));
  let d1 = S64.logxor c0 (rotl_u32 c2 1ul);
  theta_d_from (reveal vst0) 1 0 2 c0 c2;
  assert (pure (d1 == theta_d (reveal vst0) 1));
  let d2 = S64.logxor c1 (rotl_u32 c3 1ul);
  theta_d_from (reveal vst0) 2 1 3 c1 c3;
  assert (pure (d2 == theta_d (reveal vst0) 2));
  let d3 = S64.logxor c2 (rotl_u32 c4 1ul);
  theta_d_from (reveal vst0) 3 2 4 c2 c4;
  assert (pure (d3 == theta_d (reveal vst0) 3));
  let d4 = S64.logxor c3 (rotl_u32 c0 1ul);
  theta_d_from (reveal vst0) 4 3 0 c3 c0;
  assert (pure (d4 == theta_d (reveal vst0) 4));
  theta_lane st vst0 0sz s00 d0;
  theta_lane st vst0 1sz s01 d1;
  theta_lane st vst0 2sz s02 d2;
  theta_lane st vst0 3sz s03 d3;
  theta_lane st vst0 4sz s04 d4;
  theta_lane st vst0 5sz s05 d0;
  theta_lane st vst0 6sz s06 d1;
  theta_lane st vst0 7sz s07 d2;
  theta_lane st vst0 8sz s08 d3;
  theta_lane st vst0 9sz s09 d4;
  theta_lane st vst0 10sz s10 d0;
  theta_lane st vst0 11sz s11 d1;
  theta_lane st vst0 12sz s12 d2;
  theta_lane st vst0 13sz s13 d3;
  theta_lane st vst0 14sz s14 d4;
  theta_lane st vst0 15sz s15 d0;
  theta_lane st vst0 16sz s16 d1;
  theta_lane st vst0 17sz s17 d2;
  theta_lane st vst0 18sz s18 d3;
  theta_lane st vst0 19sz s19 d4;
  theta_lane st vst0 20sz s20 d0;
  theta_lane st vst0 21sz s21 d1;
  theta_lane st vst0 22sz s22 d2;
  theta_lane st vst0 23sz s23 d3;
  theta_lane st vst0 24sz s24 d4;
  with vst. assert (A.pts_to st vst);
  assert (pure (Seq.length (theta (reveal vst0)) == 25));
  assert (pure (reveal vst `Seq.equal` (theta (reveal vst0))));
}

#pop-options

(** {2 rho and pi} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** One lane of rho-pi: read lane [j], rotate by the literal [k], store at
    lane [i]. *)
inline_for_extraction
fn rho_pi_lane (st: A.array S64.t) (b: A.array S64.t) (i: SZ.t) (j: SZ.t) (k: U32.t)
               (#pst: perm) (#vst: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S64.t))
requires A.pts_to st #pst vst ** A.pts_to b vb **
         pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\
               SZ.v i < 25 /\ SZ.v j < 25 /\ U32.v k < 64 /\
               SZ.v j == rho_pi_src (SZ.v i) /\ U32.v k == rotc (SZ.v j) /\
               (forall (m: nat). m < SZ.v i ==> Seq.index vb m == Seq.index (rho_pi vst) m))
ensures exists* (vb': Seq.seq S64.t).
  A.pts_to st #pst vst ** A.pts_to b vb' **
  pure (Seq.length vst == 25 /\ Seq.length vb' == 25 /\ SZ.v i < 25 /\
        (forall (m: nat). m < SZ.v i + 1 ==> Seq.index vb' m == Seq.index (rho_pi vst) m))
{
  A.pts_to_len st;
  A.pts_to_len b;
  let a = A.(st.(j));
  rho_pi_index (reveal vst) (SZ.v i);
  A.((b.(i) <- rotl_u32 a k));
}

(** [b] becomes [rho_pi st]. *)
inline_for_extraction
fn rho_pi_impl (st: A.array S64.t) (b: A.array S64.t)
               (#pst: perm) (#vst: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
requires A.pts_to st #pst vst ** A.pts_to b vb0 **
         pure (Seq.length vst == 25 /\ Seq.length vb0 == 25)
ensures exists* (vb: Seq.seq S64.t).
  A.pts_to st #pst vst ** A.pts_to b vb **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\ vb == rho_pi (reveal vst))
{
  A.pts_to_len st;
  A.pts_to_len b;
  rotc_lit ();
  rho_pi_lane st b 0sz 0sz 0ul;
  rho_pi_lane st b 1sz 6sz 44ul;
  rho_pi_lane st b 2sz 12sz 43ul;
  rho_pi_lane st b 3sz 18sz 21ul;
  rho_pi_lane st b 4sz 24sz 14ul;
  rho_pi_lane st b 5sz 3sz 28ul;
  rho_pi_lane st b 6sz 9sz 20ul;
  rho_pi_lane st b 7sz 10sz 3ul;
  rho_pi_lane st b 8sz 16sz 45ul;
  rho_pi_lane st b 9sz 22sz 61ul;
  rho_pi_lane st b 10sz 1sz 1ul;
  rho_pi_lane st b 11sz 7sz 6ul;
  rho_pi_lane st b 12sz 13sz 25ul;
  rho_pi_lane st b 13sz 19sz 8ul;
  rho_pi_lane st b 14sz 20sz 18ul;
  rho_pi_lane st b 15sz 4sz 27ul;
  rho_pi_lane st b 16sz 5sz 36ul;
  rho_pi_lane st b 17sz 11sz 10ul;
  rho_pi_lane st b 18sz 17sz 15ul;
  rho_pi_lane st b 19sz 23sz 56ul;
  rho_pi_lane st b 20sz 2sz 62ul;
  rho_pi_lane st b 21sz 8sz 55ul;
  rho_pi_lane st b 22sz 14sz 39ul;
  rho_pi_lane st b 23sz 15sz 41ul;
  rho_pi_lane st b 24sz 21sz 2ul;
  with vb. assert (A.pts_to b vb);
  assert (pure (Seq.length (rho_pi (reveal vst)) == 25));
  assert (pure (reveal vb `Seq.equal` (rho_pi (reveal vst))));
}

#pop-options

(** {2 chi} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** One lane of chi.  [j1] and [j2] are the two other lanes of the same row,
    one and two columns along. *)
inline_for_extraction
fn chi_lane (b: A.array S64.t) (st: A.array S64.t) (i: SZ.t) (j1: SZ.t) (j2: SZ.t)
            (#pb: perm) (#vb: erased (Seq.seq S64.t)) (#vst: erased (Seq.seq S64.t))
requires A.pts_to b #pb vb ** A.pts_to st vst **
         pure (Seq.length vb == 25 /\ Seq.length vst == 25 /\
               SZ.v i < 25 /\ SZ.v j1 < 25 /\ SZ.v j2 < 25 /\
               SZ.v j1 == idx ((SZ.v i % 5 + 1) % 5) (SZ.v i / 5) /\
               SZ.v j2 == idx ((SZ.v i % 5 + 2) % 5) (SZ.v i / 5) /\
               (forall (m: nat). m < SZ.v i ==> Seq.index vst m == Seq.index (chi vb) m))
ensures exists* (vst': Seq.seq S64.t).
  A.pts_to b #pb vb ** A.pts_to st vst' **
  pure (Seq.length vb == 25 /\ Seq.length vst' == 25 /\ SZ.v i < 25 /\
        (forall (m: nat). m < SZ.v i + 1 ==> Seq.index vst' m == Seq.index (chi vb) m))
{
  A.pts_to_len b;
  A.pts_to_len st;
  let a0 = A.(b.(i));
  let a1 = A.(b.(j1));
  let a2 = A.(b.(j2));
  chi_index (reveal vb) (SZ.v i);
  A.((st.(i) <- S64.logxor a0 (S64.logand (S64.lognot a1) a2)));
}

(** [st] becomes [chi b]. *)
inline_for_extraction
fn chi_impl (b: A.array S64.t) (st: A.array S64.t)
            (#pb: perm) (#vb: erased (Seq.seq S64.t)) (#vst0: erased (Seq.seq S64.t))
requires A.pts_to b #pb vb ** A.pts_to st vst0 **
         pure (Seq.length vb == 25 /\ Seq.length vst0 == 25)
ensures exists* (vst: Seq.seq S64.t).
  A.pts_to b #pb vb ** A.pts_to st vst **
  pure (Seq.length vb == 25 /\ Seq.length vst == 25 /\ vst == chi (reveal vb))
{
  A.pts_to_len b;
  A.pts_to_len st;
  chi_lane b st 0sz 1sz 2sz;
  chi_lane b st 1sz 2sz 3sz;
  chi_lane b st 2sz 3sz 4sz;
  chi_lane b st 3sz 4sz 0sz;
  chi_lane b st 4sz 0sz 1sz;
  chi_lane b st 5sz 6sz 7sz;
  chi_lane b st 6sz 7sz 8sz;
  chi_lane b st 7sz 8sz 9sz;
  chi_lane b st 8sz 9sz 5sz;
  chi_lane b st 9sz 5sz 6sz;
  chi_lane b st 10sz 11sz 12sz;
  chi_lane b st 11sz 12sz 13sz;
  chi_lane b st 12sz 13sz 14sz;
  chi_lane b st 13sz 14sz 10sz;
  chi_lane b st 14sz 10sz 11sz;
  chi_lane b st 15sz 16sz 17sz;
  chi_lane b st 16sz 17sz 18sz;
  chi_lane b st 17sz 18sz 19sz;
  chi_lane b st 18sz 19sz 15sz;
  chi_lane b st 19sz 15sz 16sz;
  chi_lane b st 20sz 21sz 22sz;
  chi_lane b st 21sz 22sz 23sz;
  chi_lane b st 22sz 23sz 24sz;
  chi_lane b st 23sz 24sz 20sz;
  chi_lane b st 24sz 20sz 21sz;
  with vst. assert (A.pts_to st vst);
  assert (pure (Seq.length (chi (reveal vb)) == 25));
  assert (pure (reveal vst `Seq.equal` (chi (reveal vb))));
}

#pop-options

(** {2 One round, and the permutation} *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

inline_for_extraction
fn round_impl (st: A.array S64.t) (b: A.array S64.t)
              (rc_tbl: A.array S64.t) (n: SZ.t)
              (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
              (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ SZ.v n < 24)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
        Seq.length vb == 25 /\ SZ.v n < 24 /\
        vst == round (SZ.v n) (reveal vst0))
{
  A.pts_to_len st;
  A.pts_to_len rc_tbl;
  theta_impl st;
  rho_pi_impl st b;
  chi_impl b st;
  with v1. assert (A.pts_to st v1);
  let x0 = A.(st.(0sz));
  let r = A.(rc_tbl.(n));
  A.((st.(0sz) <- S64.logxor x0 r));
}

(** Twenty-four rounds.  This loop is {i not} unrolled: twenty-four copies of a
    fully unrolled round is about twenty kilobytes of code, which costs more in
    instruction cache than it saves in loop overhead. *)
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
    pure (Seq.length vst0 == 25 /\ SZ.v vi <= 24 /\ Seq.length vst == 25 /\
          Seq.length vb == 25 /\
          vst == Loops.repeati (SZ.v vi) round (reveal vst0))
  decreases (24 - SZ.v (!i))
  {
    let vi = !i;
    Loops.unfold_repeati (SZ.v vi) round (reveal vst0);
    round_impl st b rc_tbl vi;
    i := SZ.add vi 1sz;
  };
}

#pop-options
