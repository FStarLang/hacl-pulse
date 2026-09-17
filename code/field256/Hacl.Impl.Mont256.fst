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

(** The modular operations, with their scratch.

    [Hacl.Impl.Bignum256] allocates nothing: its workspace is forty-one wide
    columns and eight words, and it takes them as arguments, because that is
    the only way to prove anything about a loop that reuses them.  Nobody
    wants to write that at a call site, so each operation gets a wrapper
    here that declares the scratch and drops it on return.  Seven hundred
    bytes of stack per multiply is not a cost worth an interface for.

    These are ordinary functions rather than [inline_for_extraction] ones,
    and they still take the modulus as an argument: the field and the scalar
    field share the code, and the emitted C has one [amul] rather than two.
    Specialising the two moduli would buy the multiplier nothing -- the
    limbs it reads are data either way -- and would double the object. *)
module Hacl.Impl.Mont256

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.Montgomery256
open Spec.Field256
open Hacl.Impl.Limb
open Spec.Mont256
open Hacl.Impl.Bignum256

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast
module Declassify = Hacl.Secret.Declassify
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 Multiplication} *)

fn amul (out a b ms nm: A.array S64.t) (mu: S64.t) (d: erased modulus)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
        (#pm: perm) (#vms: erased (Seq.seq S64.t))
        (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ res d (vals vo') /\
        vals vo' == mmul d (vals va) (vals vb))
{
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut ap = [| z128; 15sz |]; A.pts_to_len ap; let mut at = [| z128; 17sz |]; A.pts_to_len at; let mut ar = [| z128; 9sz |]; A.pts_to_len ar; let mut asv = [| z; 8sz |]; A.pts_to_len asv; A.pts_to_len ap; A.pts_to_len at; A.pts_to_len ar; A.pts_to_len asv;
  assert_norm (nw == 15);
  assert_norm (ncol == 17);
  mmul_op out a b ap at ar asv ms nm mu d;
  ()
}

(** {2 Addition, subtraction and negation} *)

fn aadd (out a b nm: A.array S64.t) (d: erased modulus)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
        (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vnm == nl /\
        vals vnm == d.nm /\ res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ res d (vals vo') /\
        vals vo' == madd d (vals va) (vals vb))
{
  let z = S64.zero;
  let mut asv = [| z; 8sz |]; A.pts_to_len asv; A.pts_to_len asv;
  madd_op out a b asv nm d;
  ()
}

fn asub (out a b ms: A.array S64.t) (d: erased modulus)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
        (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vms == nl /\
        vals vms == d.ms /\ res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ res d (vals vo') /\
        vals vo' == msub d (vals va) (vals vb))
{
  let z = S64.zero;
  let mut asv = [| z; 8sz |]; A.pts_to_len asv; A.pts_to_len asv;
  msub_op out a b asv ms d;
  ()
}

(** Negation is a subtraction from a stack-allocated zero, which the
    allocation already gives. *)
fn aneg (out a ms: A.array S64.t) (d: erased modulus)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vms == nl /\
        vals vms == d.ms /\ res d (vals va))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ res d (vals vo') /\
        vals vo' == mneg d (vals va))
{
  let z = S64.zero;
  let mut az = [| z; 8sz |]; A.pts_to_len az; A.pts_to_len az;
  with vz. assert (A.pts_to az vz);
  Seq.lemma_eq_intro (vals vz) mzero;
  mzero_ok ();
  asub out az a ms d;
  ()
}

(** {2 Copying} *)

fn acopy (dst src: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == nl /\ Seq.length vs == nl)
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs **
  pure (Seq.length vd' == nl /\ vd' == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  assert (pure (Seq.length v == nl /\
                (forall (k: nat). k < nl ==> Seq.index v k == Seq.index vs k)));
  Seq.lemma_eq_intro v vs;
  ()
}

(** {2 Zeroing} *)

fn azero (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == nl)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (Seq.length vo' == nl /\ vals vo' == mzero)
{
  A.pts_to_len out;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index (vals v) k == 0))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    A.((out.(vi) <- S64.zero));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro (vals v) mzero;
  ()
}

(** {2 Comparison}

    The limbs are canonical, so a difference in any of them is a difference
    in the value.  The mask is folded rather than branched on, and only the
    final answer -- which is public in every caller -- is declassified. *)

#push-options "--z3rlimit 200"

fn aeq (a b: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (eval (vals va) = eval (vals vb)))
{
  A.pts_to_len a; A.pts_to_len b;
  let mut m = S64.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (mm: S64.t).
    pts_to i vi ** pts_to m mm ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\
          (if (forall (k: nat). k < SZ.v vi ==>
                 Seq.index (vals va) k == Seq.index (vals vb) k)
           then S64.v mm == pow2 64 - 1 else S64.v mm == 0))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let mm = !m;
    let xa = A.(a.(vi));
    let xb = A.(b.(vi));
    let e = S64.eq_mask xa xb;
    UInt.logand_lemma_1 #64 (S64.v e);
    UInt.logand_lemma_2 #64 (S64.v e);
    UInt.logand_commutative #64 (S64.v mm) (S64.v e);
    m := S64.logand mm e;
    i := SZ.add vi 1sz;
  };
  let mm = !m;
  assert_norm ((pow2 64 - 1) % pow2 8 == pow2 8 - 1);
  let m8 = Cast.u64_to_u8 mm;
  let r = Declassify.bool_of_mask m8;
  Classical.move_requires (Seq.lemma_eq_intro (vals va)) (vals vb);
  Classical.move_requires (res_uniq (vals va)) (vals vb);
  r
}

#pop-options

(** {2 Ordering}

    Equality is enough for every curve operation, but a policy like
    secp256k1's low-S rule needs an ordering.  The subtraction [msub]
    already performs computes one: its carry out is one exactly when the
    difference did not go negative. *)

fn ageq (a b: A.array S64.t) (d: erased modulus)
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (modulus_ok d /\ res d (vals va) /\ res d (vals vb))
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (eval (vals va) >= eval (vals vb)))
{
  A.pts_to_len a; A.pts_to_len b;
  let z = S64.zero;
  let mut at = [| z; 8sz |]; A.pts_to_len at; A.pts_to_len at;
  let co = negsub_op at a b;
  msub_pre d (vals va) (vals vb);
  ebnd (carry_low (addw (vals va) (negw (vals vb))));
  assert_norm ((pow2 64 - 1) % pow2 8 == pow2 8 - 1);
  let m = S64.eq_mask co S64.zero;
  let m8 = Cast.u64_to_u8 m;
  let lo = Declassify.bool_of_mask m8;
  not lo
}

(** {2 Range check}

    A decoder gets thirty-two bytes and has to say whether they are below
    the modulus.  The conditional subtraction already answers that: it
    changes the value exactly when the value was too large. *)

#push-options "--z3rlimit 200"

fn abelow (a s nm: A.array S64.t) (d: erased modulus)
          (#va: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
          (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to s vs ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length va == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        bnd (vals va) base /\ pow2 256 < 2 * d.m)
returns r: bool
ensures exists* (va': Seq.seq S64.t) (vs': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to s vs' ** A.pts_to nm #pn vnm **
  pure (Seq.length va' == nl /\ Seq.length vs' == nl /\
        res d (vals va') /\ r == (eval (vals va) < d.m) /\
        (r ==> vals va' == reveal (vals va)))
{
  A.pts_to_len a;
  let z = S64.zero;
  let mut ac = [| z; 8sz |]; A.pts_to_len ac; A.pts_to_len ac;
  acopy ac a;
  ebnd (vals va);
  csub_op a s nm S64.zero d;
  csub_eq d (vals va);
  with va'. assert (A.pts_to a va');
  let r = aeq a ac;
  Classical.move_requires (res_uniq (vals va')) (vals va);
  r
}

(** The same subtraction used for its arithmetic rather than its answer: a
    value below twice the modulus is brought below it. *)
fn ared (a s nm: A.array S64.t) (d: erased modulus)
        (#va: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
        (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to s vs ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length va == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        bnd (vals va) base /\ pow2 256 < 2 * d.m)
ensures exists* (va': Seq.seq S64.t) (vs': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to s vs' ** A.pts_to nm #pn vnm **
  pure (Seq.length va' == nl /\ Seq.length vs' == nl /\
        res d (vals va') /\ eval (vals va') == eval (vals va) % d.m)
{
  A.pts_to_len a;
  ebnd (vals va);
  csub_ok d (vals va) 0;
  Classical.move_requires (Math.small_mod (eval (vals va))) d.m;
  Math.lemma_mod_sub (eval (vals va)) d.m 1;
  csub_op a s nm S64.zero d;
}

(** {2 Constant-time selection}

    The scalar multiplication chooses between two accumulators on a bit of
    a secret scalar, so the choice cannot be a branch.  The mask carries
    the bit as a ghost boolean, which is what lets the postcondition be an
    ordinary [if]. *)

fn asel (out a b: A.array S64.t) (m: S64.t) (bb: erased bool)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length va == nl /\ Seq.length vb == nl /\
        S64.v m == (if bb then pow2 64 - 1 else 0))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (vo' == (if bb then reveal vb else reveal va))
{
  A.pts_to_len out; A.pts_to_len a; A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k ==
               Seq.index (if bb then reveal vb else reveal va) k))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let xa = A.(a.(vi));
    let xb = A.(b.(vi));
    A.((out.(vi) <- S64.select m xb xa));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro v (if bb then reveal vb else reveal va);
  ()
}

(** {2 Reading a bit of a secret number}

    The index is public -- it is the loop counter -- but the bit is not, so
    the answer comes back as a mask rather than a boolean. *)

fn abit (s: A.array S64.t) (i: SZ.t)
        (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to s #ps vs **
  pure (Seq.length vs == nl /\ bnd (vals vs) base /\ SZ.v i < 256)
returns m: S64.t
ensures A.pts_to s #ps vs **
  pure (S64.v m ==
          (if eval (vals vs) / pow2 (SZ.v i) % 2 = 1 then pow2 64 - 1 else 0))
{
  A.pts_to_len s;
  assert_norm (rad == 32);
  ebit (vals vs) (SZ.v i);
  let k = SZ.div i 32sz;
  let l = A.(s.(k));
  let r = SZ.rem i 32sz;
  Math.small_mod (SZ.v r) (pow2 32);
  let j = SZ.sizet_to_uint32 r;
  assert_norm (pow2 1 - 1 == 1);
  assert_norm (pow2 1 == 2);
  UInt.logand_mask #64 (S64.v (S64.shift_right l j)) 1;
  let b = S64.logand (S64.shift_right l j) (S64.classify 1uL);
  S64.sub_mod S64.zero b
}

#pop-options
#pop-options
