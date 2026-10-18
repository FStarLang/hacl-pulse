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

(** The final reduction: from a small five-limb number to the canonical one.

    Everything in [Hacl.Poly1305.Field] works modulo the prime and leaves the
    limbs merely small.  The tag needs the representative below [prime], and
    it needs it without a branch.

    Three ripple carries and a mask, as [Spec.Poly1305.Field] lays out: the
    first makes the accumulator canonical plus a carry out of the top, which
    folds back into limb zero multiplied by five; the second and third ripple
    that number and that number plus five, and the carry out of the third is
    the answer to "is it at least [prime]", because [prime + 5] is [2^130].

    Each of these runs once per message, so nothing here is on a hot path;
    what matters is that it is constant time, which it is -- five shifts,
    five masks and five adds apiece, and a [select] at the end. *)
module Hacl.Poly1305.Reduce

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Poly1305.Field
open Hacl.Poly1305.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 One ripple carry}

    Five limbs in, five canonical limbs and the carry out.  Nothing wraps:
    this is the plain positional carry, and what falls off the top is
    returned rather than folded back in. *)

inline_for_extraction
fn ripple_impl (t: A.array S64.t) (e0 e1 e2 e3 e4: S64.t)
               (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt **
         pure (Seq.length vt == 5 /\
               bounded5 (S64.v e0) (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4) 27)
returns c: S64.t
ensures exists* (vt': Seq.seq S64.t). A.pts_to t vt' **
  pure (Seq.length vt' == 5 /\
        ripple (S64.v e0) (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4)
               (vv vt' 0) (vv vt' 1) (vv vt' 2) (vv vt' 3) (vv vt' 4) (S64.v c))
{
  A.pts_to_len t;
  Math.pow2_lt_compat 64 28;
  Math.lemma_div_lt (S64.v e0) 27 26;
  assert_norm (pow2 1 == 2);
  assert_norm (pow2 2 == 4);
  assert_norm (pow2 27 + 4 < pow2 28);
  let f1 = add2 e1 (hi26 e0);
  Math.lemma_div_lt (S64.v f1) 28 26;
  let f2 = add2 e2 (hi26 f1);
  Math.lemma_div_lt (S64.v f2) 28 26;
  let f3 = add2 e3 (hi26 f2);
  Math.lemma_div_lt (S64.v f3) 28 26;
  let f4 = add2 e4 (hi26 f3);
  A.((t.(0sz) <- lo26 e0));
  A.((t.(1sz) <- lo26 f1));
  A.((t.(2sz) <- lo26 f2));
  A.((t.(3sz) <- lo26 f3));
  A.((t.(4sz) <- lo26 f4));
  hi26 f4
}

#pop-options

(** {2 The reduction} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn reduce (h: A.array S64.t) (#vh: erased (Seq.seq S64.t))
requires A.pts_to h vh ** pure (Seq.length vh == 5 /\ bounded vh 27)
ensures exists* (vh': Seq.seq S64.t). A.pts_to h vh' **
  pure (Seq.length vh' == 5 /\ bounded vh' 26 /\
        feval vh' == feval vh % prime)
{
  A.pts_to_len h;
  let z = S64.zero;
  let mut aarr = [| z; 5sz |];
  Mem.track aarr;
  A.pts_to_len aarr;
  A.pts_to_len aarr;
  let mut rarr = [| z; 5sz |];
  Mem.track rarr;
  A.pts_to_len rarr;
  A.pts_to_len rarr;
  let mut qarr = [| z; 5sz |];
  Mem.track qarr;
  A.pts_to_len qarr;
  A.pts_to_len qarr;

  let e0 = A.(h.(0sz));
  let e1 = A.(h.(1sz));
  let e2 = A.(h.(2sz));
  let e3 = A.(h.(3sz));
  let e4 = A.(h.(4sz));
  let ca = ripple_impl aarr e0 e1 e2 e3 e4;
  with va. assert (A.pts_to aarr va);
  ripple_eval (S64.v e0) (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4)
              (vv va 0) (vv va 1) (vv va 2) (vv va 3) (vv va 4) (S64.v ca);
  ripple_carry_bound (S64.v e0) (S64.v e1) (S64.v e2) (S64.v e3) (S64.v e4)
                     (vv va 0) (vv va 1) (vv va 2) (vv va 3) (vv va 4) (S64.v ca);
  fold_carry (vv va 0) (vv va 1) (vv va 2) (vv va 3) (vv va 4) (S64.v ca);

  (* [p], congruent to the accumulator and below [2 * prime]. *)
  let a0 = A.(aarr.(0sz));
  let a1 = A.(aarr.(1sz));
  let a2 = A.(aarr.(2sz));
  let a3 = A.(aarr.(3sz));
  let a4 = A.(aarr.(4sz));
  assert_norm (pow2 26 + 20 < pow2 27);
  Math.pow2_lt_compat 64 27;
  let p0 = add2 a0 (times5 ca);
  let p0five = add2 p0 (S64.classify 5uL);

  let cr = ripple_impl rarr p0 a1 a2 a3 a4;
  with vr. assert (A.pts_to rarr vr);
  ripple_eval (S64.v p0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4)
              (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4) (S64.v cr);
  let cq = ripple_impl qarr p0five a1 a2 a3 a4;
  with vq. assert (A.pts_to qarr vq);
  ripple_eval (S64.v p0five) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4)
              (vv vq 0) (vv vq 1) (vv vq 2) (vv vq 3) (vv vq 4) (S64.v cq);

  (* Both carries are zero or one because the number is below [2^131]. *)
  as_nat5_bound (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4);
  as_nat5_bound (vv vq 0) (vv vq 1) (vv vq 2) (vv vq 3) (vv vq 4);
  add5_eval (vv va 0) (vv va 1) (vv va 2) (vv va 3) (vv va 4) (5 * S64.v ca) 0 0 0 0;
  as_nat5_bound (vv va 0) (vv va 1) (vv va 2) (vv va 3) (vv va 4);
  as_nat5_bottom (5 * S64.v ca);
  Math.pow2_le_compat 130 5;
  assert_norm (pow2 5 == 32);
  ripple_small (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4) (S64.v cr)
               (as_nat5 (S64.v p0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4));
  ripple_small (vv vq 0) (vv vq 1) (vv vq 2) (vv vq 3) (vv vq 4) (S64.v cq)
               (as_nat5 (S64.v p0five) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4));
  add5_eval (S64.v p0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4) 5 0 0 0 0;
  as_nat5_bottom 5;
  select_ok (as_nat5 (S64.v p0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4))
            (as_nat5 (vv vr 0) (vv vr 1) (vv vr 2) (vv vr 3) (vv vr 4))
            (as_nat5 (vv vq 0) (vv vq 1) (vv vq 2) (vv vq 3) (vv vq 4))
            (S64.v cr) (S64.v cq);

  let m = S64.eq_mask cq (S64.classify 1uL);
  let r0 = A.(rarr.(0sz));
  let r1 = A.(rarr.(1sz));
  let r2 = A.(rarr.(2sz));
  let r3 = A.(rarr.(3sz));
  let r4 = A.(rarr.(4sz));
  let q0 = A.(qarr.(0sz));
  let q1 = A.(qarr.(1sz));
  let q2 = A.(qarr.(2sz));
  let q3 = A.(qarr.(3sz));
  let q4 = A.(qarr.(4sz));
  A.((h.(0sz) <- S64.select m q0 r0));
  A.((h.(1sz) <- S64.select m q1 r1));
  A.((h.(2sz) <- S64.select m q2 r2));
  A.((h.(3sz) <- S64.select m q3 r3));
  A.((h.(4sz) <- S64.select m q4 r4));
  Mem.wipe qarr 5sz;
  Mem.wipe rarr 5sz;
  Mem.wipe aarr 5sz;
  ()
}

#pop-options
