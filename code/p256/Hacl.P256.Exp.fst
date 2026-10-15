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

(** Exponentiation in P-256's field by a public exponent.

    {!Hacl.K256.Exp52}'s loop over {!Hacl.P256.Field}.  [Hacl.Impl.Exp4]
    raises a Montgomery residue with the generic four-limb multiply, which
    since {!Hacl.P256.Field64} is half the speed of the field's own; this
    is the same square-and-multiply on the field's [fsqr] and [fmul].  The
    representation is still Montgomery, but [fev] hides it: the
    accumulator starts at [fone] and every step is stated over [fev].

    The exponent is four public sixty-four-bit limbs from
    {!Hacl.P256.Tables}, read with [Spec.Mont4]'s [ebit], [edigit] and
    [exp_step], exactly as in {!Hacl.K256.Exp52}.

    {b Why the branch is safe}, as in [Hacl.Impl.Exp4]: the exponent is a
    constant from the standard and is not secret, which is exactly what its
    [uint64] type records. *)
module Hacl.P256.Exp

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Hacl.Impl.Limb4
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module MA = Spec.ModArith
module B4 = Spec.Bignum4
module F4 = Spec.Field4
module M4 = Spec.Mont4
module L4 = Hacl.Impl.Lit4
module E4 = Hacl.Impl.Exp4

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The conditional multiply of the loop body, as its own function: a Pulse
    [if] whose branches disagree on the value of two slices is easier to
    join through a postcondition written by hand than one inferred. *)
inline_for_extraction
fn cmul (bb: bool) (out t1 a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t)) (#w1: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t1 w1 ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ Seq.length w1 == nl /\
        felem va /\ felem vo)
ensures exists* (vo': Seq.seq S64.t) (w1': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t1 w1' ** A.pts_to a #pa va **
  pure (Seq.length vo' == nl /\ Seq.length w1' == nl /\ felem vo' /\
        fev vo' ==
          (if bb then MA.mul #P.prime (fev vo) (fev va)
           else fev vo))
{
  A.pts_to_len out;
  A.pts_to_len t1;
  if bb {
    fcopy t1 out;
    fmul out t1 a;
  } else {
    ()
  }
}

(** One step: square, then multiply if bit [bi] of the exponent is set.  It
    is a function of its own for the reason [Hacl.Impl.Exp4.estep] is --- a
    Pulse [fn] pays for every definition already in scope, and a loop body
    of this size inside [fexp] times out where the same code in isolation
    does not. *)
inline_for_extraction
fn estep (out t1 a: A.array S64.t) (e: A.array U64.t) (bi: SZ.t) (kk: erased nat)
         (#vo: erased (Seq.seq S64.t)) (#w1: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
         (#pe: perm) (#ve: erased (Seq.seq U64.t))
requires A.pts_to out vo ** A.pts_to t1 w1 ** A.pts_to a #pa va **
  A.pts_to e #pe ve **
  pure (Seq.length vo == nl /\ Seq.length w1 == nl /\
        Seq.length ve == B4.nl /\ B4.bnd (L4.pvals ve) B4.base /\ SZ.v bi < 256 /\
        felem va /\ felem vo /\
        fev vo == MA.exp #P.prime (fev va) kk)
ensures exists* (vo': Seq.seq S64.t) (w1': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t1 w1' ** A.pts_to a #pa va **
  A.pts_to e #pe ve **
  pure (Seq.length vo' == nl /\ Seq.length w1' == nl /\ felem vo' /\
        fev vo' ==
          MA.exp #P.prime (fev va)
                 (2 * kk + B4.eval (L4.pvals ve) / pow2 (SZ.v bi) % 2))
{
  A.pts_to_len out;
  A.pts_to_len t1;
  A.pts_to_len e;
  with v. assert (A.pts_to out v);
  fcopy t1 out;
  fsqr out t1;
  let k = SZ.div bi 64sz;
  assert (pure (SZ.v k == SZ.v bi / 64));
  assert (pure (SZ.v k < B4.nl));
  let l = A.(e.(k));
  assert (pure (l == Seq.index ve (SZ.v bi / 64)));
  let r = SZ.rem bi 64sz;
  assert (pure (SZ.v r == SZ.v bi % 64));
  Math.small_mod (SZ.v r) (pow2 32);
  let j = SZ.sizet_to_uint32 r;
  assert (pure (U32.v j == SZ.v bi % 64));
  let b = U64.logand (U64.shift_right l j) 1uL;
  E4.bit_of ve (SZ.v bi) l j;
  M4.exp_step #P.prime (fev va) kk (U64.v b);
  with u. assert (A.pts_to out u);
  assert (pure (fev u ==
                MA.mul #P.prime (MA.exp #P.prime (fev va) kk)
                               (MA.exp #P.prime (fev va) kk)));
  cmul (E4.is_one b) out t1 a;
  ()
}

(** [out := a ^ (eval e)], with [e] four public limbs.  The accumulator
    starts at one, which is now a literal rather than a table.

    [inline_for_extraction] for the reason [Hacl.Impl.Exp4.mexp] gives:
    both call sites have their own exponent, and a copy that knows it is
    worth the duplication. *)
#push-options "--z3rlimit 600"
inline_for_extraction
fn fexp (out a: A.array S64.t) (e: A.array U64.t) (n: erased nat)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pe: perm) (#ve: erased (Seq.seq U64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to e #pe ve **
  pure (Seq.length vo == nl /\ felem va /\
        Seq.length ve == B4.nl /\ reveal n < pow2 256 /\ L4.pvals ve == F4.limbs n)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to e #pe ve **
  pure (felem vo' /\ fev vo' == MA.exp #P.prime (fev va) n)
{
  A.pts_to_len out;
  A.pts_to_len e;
  assert_norm (1 < P.prime);
  F4.limbs_ok (reveal n);
  let z = S64.zero;
  let mut a1 = [| z; 4sz |]; A.pts_to_len a1; A.pts_to_len a1;
  fone out;
  Math.small_div (reveal n) (pow2 256);
  MA.exp_zero #P.prime (fev va);
  assert (pure (reveal n / pow2 256 == 0));
  let mut i = 256sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (w1: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a1 w1 **
    A.pts_to a #pa va ** A.pts_to e #pe ve **
    pure (SZ.v vi <= 256 /\ Seq.length v == nl /\ Seq.length w1 == nl /\
          felem v /\
          fev v == MA.exp #P.prime (fev va) (reveal n / pow2 (SZ.v vi)))
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let ni = SZ.sub vi 1sz;
    estep out a1 a e ni (hide (reveal n / pow2 (SZ.v vi)));
    M4.edigit (reveal n) (SZ.v vi);
    i := ni;
  };
  assert_norm (pow2 0 == 1);
  ()
}
#pop-options

#pop-options
