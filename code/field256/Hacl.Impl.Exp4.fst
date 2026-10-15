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

(** Exponentiation by a public exponent.

    Inversion, square roots and scalar inversion are all [x^e] for a fixed
    [e] that appears in the standard.  HACL* writes an addition chain for
    each: a page of straight-line code per exponent, and a page of exponent
    bookkeeping to verify it.  A left-to-right binary loop is one function
    and one invariant, serves all three, and is about a hundred and thirty
    multiplications dearer than the chains -- against the two thousand five
    hundred that the scalar multiplication it accompanies already costs.

    {b Why the branch is safe.}  The exponent is a constant from the
    standard and is not secret, so the loop may skip the multiplication
    when the bit is clear.  That is the whole reason the exponent tables
    are [uint64] rather than the library's secret [S64]: the type is the
    declassification. *)
module Hacl.Impl.Exp4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.Field4
open Spec.Mont4
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Impl.Lit4

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module MA = Spec.ModArith

(** Comparing against a literal is a nuisance under [--fuel 0]: the machine
    integer [1uL] is [uint_to_t 1], whose typing needs [pow2 64].  Doing it
    once, outside the options block, keeps it out of every proof below. *)
let is_one (b: U64.t) : (r: bool { r <==> U64.v b == 1 }) = b = 1uL

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The bit the loop body tests, in one lemma so that the machine-integer
    reasoning never meets the loop's context.  It is stated on the very term
    the loop builds, so the caller has nothing left to rewrite. *)
let bit_of (ve: Seq.seq U64.t) (i: nat { i < 256 }) (l: U64.t) (j: U32.t)
  : Lemma (requires Seq.length ve == nl /\ bnd (pvals ve) base /\
                    l == Seq.index ve (i / 64) /\ U32.v j == i % 64)
          (ensures (let b = U64.v (U64.logand (U64.shift_right l j) 1uL) in
                    b < 2 /\ b == eval (pvals ve) / pow2 i % 2))
  = assert_norm (pow2 1 - 1 == 1);
    assert_norm (pow2 1 == 2);
    assert_norm (rad == 64);
    UInt.logand_mask #64 (U64.v (U64.shift_right l j)) 1;
    ebit (pvals ve) i

(** Index arithmetic of the loop body, at top level. *)
let idx_of (bi: SZ.t)
  : Lemma (SZ.v (SZ.div bi 64sz) == SZ.v bi / 64 /\
           SZ.v (SZ.rem bi 64sz) == SZ.v bi % 64)
  = ()

(** The loop exits at [vi = 0], where the exponent prefix is all of [en]. *)
let exp_final (en: nat) (vi: SZ.t)
  : Lemma (requires not (SZ.v vi > 0))
          (ensures en / pow2 (SZ.v vi) == en)
  = assert_norm (pow2 0 == 1)

(** The conditional multiply of the loop body, as its own function: a Pulse
    [if] whose branches disagree on the value of two slices is easier to
    join through a postcondition written by hand than one inferred. *)
inline_for_extraction
fn cmul (bb: bool) (out t1 a ms nm: A.array S64.t) (mu: S64.t) (d: erased modulus)
        (#vo: erased (Seq.seq S64.t)) (#w1: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pm: perm) (#vms: erased (Seq.seq S64.t))
        (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t1 w1 ** A.pts_to a #pa va **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length w1 == nl /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
        res d (vals va) /\ res d (vals vo))
ensures exists* (vo': Seq.seq S64.t) (w1': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t1 w1' ** A.pts_to a #pa va **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ Seq.length w1' == nl /\ res d (vals vo') /\
        mev d (vals vo') ==
          (if bb then MA.mul (mev d (vals vo)) (mev d (vals va))
           else mev d (vals vo)))
{
  A.pts_to_len out;
  A.pts_to_len t1;
  if bb {
    mev_mul d (vals vo) (vals va);
    acopy t1 out;
    amul out t1 a ms nm mu d;
  } else {
    ()
  }
}

(** One step of the loop: square, then multiply if bit [bi] of the exponent
    is set.  It is a function of its own because a Pulse [fn] pays for every
    definition already in scope; a loop body of this size inside [mexp]
    times out where the same code in isolation does not. *)
inline_for_extraction
fn estep (out t1 t2 a: A.array S64.t) (e: A.array U64.t)
         (ms nm: A.array S64.t) (bi: SZ.t)
         (mu: S64.t) (d: erased modulus) (kk: erased nat)
         (#vo: erased (Seq.seq S64.t))
         (#w1: erased (Seq.seq S64.t)) (#w2: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
         (#pe: perm) (#ve: erased (Seq.seq U64.t))
         (#pm: perm) (#vms: erased (Seq.seq S64.t))
         (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t1 w1 ** A.pts_to t2 w2 **
  A.pts_to a #pa va ** A.pts_to e #pe ve **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\
        Seq.length w1 == nl /\ Seq.length w2 == nl /\
        Seq.length ve == nl /\ bnd (pvals ve) base /\ SZ.v bi < 256 /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
        res d (vals va) /\ res d (vals vo) /\
        mev d (vals vo) == mpow d (mev d (vals va)) kk)
ensures exists* (vo': Seq.seq S64.t)
                (w1': Seq.seq S64.t) (w2': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t1 w1' ** A.pts_to t2 w2' **
  A.pts_to a #pa va ** A.pts_to e #pe ve **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\
        Seq.length w1' == nl /\ Seq.length w2' == nl /\ res d (vals vo') /\
        mev d (vals vo') ==
          mpow d (mev d (vals va))
                 (2 * kk + eval (pvals ve) / pow2 (SZ.v bi) % 2))
{
  A.pts_to_len out;
  A.pts_to_len t1;
  A.pts_to_len t2;
  A.pts_to_len e;
  with v. assert (A.pts_to out v);
  acopy t1 out;
  acopy t2 out;
  amul out t1 t2 ms nm mu d;
  mev_mul d (vals v) (vals v);
  idx_of bi;
  let k = SZ.div bi 64sz;
  assert (pure (SZ.v k == SZ.v bi / 64));
  assert (pure (SZ.v k < nl));
  let l = A.(e.(k));
  assert (pure (l == Seq.index ve (SZ.v bi / 64)));
  let r = SZ.rem bi 64sz;
  assert (pure (SZ.v r == SZ.v bi % 64));
  Math.small_mod (SZ.v r) (pow2 32);
  let j = SZ.sizet_to_uint32 r;
  assert (pure (U32.v j == SZ.v bi % 64));
  let b = U64.logand (U64.shift_right l j) 1uL;
  bit_of ve (SZ.v bi) l j;
  exp_step (mev d (vals va)) kk (U64.v b);
  with u. assert (A.pts_to out u);
  assert (pure (mev d (vals u) ==
                MA.mul (MA.exp (mev d (vals va)) kk)
                       (MA.exp (mev d (vals va)) kk)));
  cmul (is_one b) out t1 a ms nm mu d;
  with vv. assert (A.pts_to out vv);
  assert (pure (mev d (vals vv) ==
                MA.exp (mev d (vals va)) (2 * kk + U64.v b)));
}

(** [out := a^(eval e)], with [a] in Montgomery form and [e] sixteen public
    limbs.  [r1] is the Montgomery one, which is where the accumulator
    starts.

    [inline_for_extraction], for the reason given at the top of
    [Hacl.Impl.Mont4]: each of the six call sites has its own modulus, its
    own Montgomery constant and its own exponent, and a copy that knows them
    is worth seven to nine percent on P-256 and secp256k1 inversion.  gcc
    will clone this by itself if its interprocedural budget happens to
    stretch that far, and clang will not clone it at all; neither is a thing
    to depend on. *)
#push-options "--z3rlimit 600"
inline_for_extraction
fn mexp (out a: A.array S64.t) (e: A.array U64.t) (r1 ms nm: A.array S64.t)
        (mu: S64.t) (d: erased modulus)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pe: perm) (#ve: erased (Seq.seq U64.t))
        (#p1: perm) (#v1: erased (Seq.seq S64.t))
        (#pm: perm) (#vms: erased (Seq.seq S64.t))
        (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to e #pe ve **
  A.pts_to r1 #p1 v1 ** A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\
        Seq.length ve == nl /\ bnd (pvals ve) base /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
        vals v1 == d.r1 /\ res d (vals va))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to e #pe ve **
  A.pts_to r1 #p1 v1 ** A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (res d (vals vo') /\
        mev d (vals vo') == mpow d (mev d (vals va)) (eval (pvals ve)))
{
  A.pts_to_len out;
  A.pts_to_len e;
  A.pts_to_len r1;
  mev_one d;
  let en = hide (eval (pvals ve));
  ebnd (pvals ve);
  let z = S64.zero;
  let mut a1 = [| z; 4sz |]; A.pts_to_len a1; let mut a2 = [| z; 4sz |]; A.pts_to_len a2; A.pts_to_len a1; A.pts_to_len a2;
  acopy out r1;
  ebnd (pvals ve);
  Math.small_div (reveal en) (pow2 256);
  MA.exp_zero (mev d (vals va));
  assert (pure (reveal en / pow2 256 == 0));
  let mut i = 256sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t)
                    (w1: Seq.seq S64.t) (w2: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a1 w1 ** A.pts_to a2 w2 **
    A.pts_to a #pa va ** A.pts_to e #pe ve ** A.pts_to r1 #p1 v1 **
    A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
    pure (SZ.v vi <= 256 /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
          res d (vals v) /\
          mev d (vals v) ==
            mpow d (mev d (vals va)) (reveal en / pow2 (SZ.v vi)))
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let ni = SZ.sub vi 1sz;
    estep out a1 a2 a e ms nm ni mu d (hide (reveal en / pow2 (SZ.v vi)));
    edigit (reveal en) (SZ.v vi);
    i := ni;
  };
  with vi v w1 w2. assert (pts_to i vi ** A.pts_to out v ** A.pts_to a1 w1 ** A.pts_to a2 w2);
  exp_final (reveal en) vi;
  ()
}
#pop-options

#pop-options
