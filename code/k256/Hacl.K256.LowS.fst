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

(** Low-S.

    [(r, s)] and [(r, q - s)] verify against the same key and the same
    message, so an ECDSA signature is malleable as a byte string even
    though it is not forgeable.  Bitcoin forbids the upper half, and HACL*
    exposes that as a predicate and a normaliser rather than as a flag on
    signing; this module is the two of them.

    The boundary is [q / 2] rounded down and belongs to the low half, [q]
    being odd.  Deciding which side of it a scalar falls on needs an
    ordering rather than the equality every other test in this library
    uses, which is what {!Hacl.Impl.Mont256.ageq} is for. *)
module Hacl.K256.LowS

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.K256.Field
open Spec.Mont256
open Hacl.Spec.Bytes
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.Impl.Bignum256
open Hacl.Impl.Mont256
open Hacl.Impl.Lit256
open Hacl.K256.Tables

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let qmod_m (_: unit) : Lemma (qmod.m == K.order) = ()

(** The facts every function here starts from: the modulus is well formed,
    [2^256] is less than twice it, and half of it is a residue. *)
let setup (_: unit)
  : Lemma (modulus_ok qmod /\ qmod.m == K.order /\ pow2 256 < 2 * K.order /\
           res qmod (limbs K.q_half) /\ eval (limbs K.q_half) == K.q_half)
  = qmod_ok (); qmod_m ();
    assert_norm (pow2 256 < 2 * K.order);
    assert_norm (K.q_half < K.order);
    assert_norm (K.q_half < pow2 256);
    limbs_ok K.q_half

(** {2 Reading an [s]}

    Every function below starts the same way: thirty-two big-endian bytes,
    the range check that every decoder does, and a test against zero.  It
    is a function of its own because the cost of an SMT query grows faster
    than the number of definitions it can see. *)

inline_for_extraction
fn load_nz (a0 a1 a2: A.array S64.t) (b: A.array S8.t)
           (#v0 #v1 #v2: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires
  A.pts_to a0 v0 ** A.pts_to a1 v1 ** A.pts_to a2 v2 ** A.pts_to b #pb vb **
  pure (Seq.length v0 == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl /\
        Seq.length vb == 32)
returns r: bool
ensures exists* (w0 w1 w2: Seq.seq S64.t).
  A.pts_to a0 w0 ** A.pts_to a1 w1 ** A.pts_to a2 w2 ** A.pts_to b #pb vb **
  pure (Seq.length w1 == nl /\ Seq.length w2 == nl /\ res qmod (vals w0) /\
        r == (0 < be_nat vb && be_nat vb < K.order) /\
        (r ==> eval (vals w0) == be_nat vb))
{
  setup (); mzero_ok ();
  load_be a0 b;
  let nm = qnm ();
  let lo = abelow a0 a1 nm qmod;
  drop_table nm;
  azero a2;
  let zr = aeq a0 a2;
  lo && not zr
}

(** {2 The predicate}

    [0 < s <= q / 2].  The range check is the one every decoder does; the
    upper bound is the new part. *)

let isn (vb: Seq.seq S8.t) : GTot bool =
  if Seq.length vb = 32 then K.is_normalized vb else false

fn is_normalized (b: A.array S8.t) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #pb vb ** pure (Seq.length vb == 32)
returns r: bool
ensures A.pts_to b #pb vb ** pure (r == isn vb)
{
  setup ();
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let mut a2 = [| z; 16sz |]; A.pts_to_len a2; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2;
  let ok = load_nz a0 a1 a2 b;
  if ok {
    let qh = qhalf ();
    let r = ageq qh a0 qmod;
    drop_table qh;
    r
  } else {
    false
  }
}

let isns (vb: Seq.seq S8.t) : GTot bool =
  if Seq.length vb = 64 then K.is_signature_normalized vb else false

fn is_signature_normalized (sg: A.array S8.t)
                           (#ps: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to sg #ps vb ** pure (Seq.length vb == 64)
returns r: bool
ensures A.pts_to sg #ps vb ** pure (r == isns vb)
{
  A.pts_to_len sg;
  let ss = Sub.sub sg 32sz 64sz;
  with vss. assert (A.pts_to ss #ps vss);
  A.pts_to_len ss;
  assert (pure (Seq.equal vss (Seq.slice vb 32 64)));
  let r = is_normalized ss;
  Sub.unsub sg 32 64 ss;
  with vb1. assert (A.pts_to sg #ps vb1);
  A.pts_to_len sg;
  assert (pure (Seq.equal vb1 vb));
  r
}

(** {2 The smaller of the two}

    [min s (q - s)].  The branch is on the signature, which is public, so
    it is an ordinary [if] and not a masked select. *)

inline_for_extraction
fn norm_s (a3 a0: A.array S64.t)
          (#v3: erased (Seq.seq S64.t))
          (#p0: perm) (#v0: erased (Seq.seq S64.t))
requires A.pts_to a3 v3 ** A.pts_to a0 #p0 v0 **
  pure (Seq.length v3 == nl /\ res qmod (vals v0) /\ 0 < eval (vals v0))
ensures exists* (w3: Seq.seq S64.t).
  A.pts_to a3 w3 ** A.pts_to a0 #p0 v0 **
  pure (Seq.length w3 == nl /\ bnd (vals w3) base /\
        eval (vals w3) == (if eval (vals v0) > K.q_half
                           then K.order - eval (vals v0) else eval (vals v0)))
{
  setup ();
  let qh = qhalf ();
  let le = ageq qh a0 qmod;
  drop_table qh;
  if le {
    acopy a3 a0;
    ()
  } else {
    let ms = qms ();
    aneg a3 a0 ms qmod;
    drop_table ms;
    mneg_ok qmod (vals v0);
    Math.small_mod (K.order - eval (vals v0)) K.order;
    ()
  }
}

(** {2 The normaliser}

    In place, as HACL*'s is: [s] is replaced by [min s (q - s)] and the
    first half is not touched.  [false] means [s] was not a scalar at all,
    and then nothing is written. *)

let sgnorm (vb: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vb = 64 then K.signature_normalize vb else None

fn signature_normalize (sg: A.array S8.t) (#vb: erased (Seq.seq S8.t))
requires A.pts_to sg vb ** pure (Seq.length vb == 64)
returns r: bool
ensures exists* (wb: Seq.seq S8.t).
  A.pts_to sg wb **
  pure (Seq.length wb == 64 /\ r == Some? (sgnorm vb) /\
        (r ==> wb == Some?.v (sgnorm vb)))
{
  setup ();
  A.pts_to_len sg;
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let mut a3 = [| z; 16sz |]; A.pts_to_len a3; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;

  let ss = Sub.sub sg 32sz 64sz;
  with vss. assert (A.pts_to ss vss);
  A.pts_to_len ss;
  assert (pure (Seq.equal vss (Seq.slice vb 32 64)));
  let ok = load_nz a0 a1 a2 ss;
  Sub.unsub sg 32 64 ss;
  with vb1. assert (A.pts_to sg vb1);
  A.pts_to_len sg;
  assert (pure (Seq.equal vb1 vb));

  if ok {
    norm_s a3 a0;
    let ts = Sub.sub sg 32sz 64sz;
    A.pts_to_len ts;
    store_be ts a3;
    with vts. assert (A.pts_to ts vts);
    Sub.unsub sg 32 64 ts;
    with wb. assert (A.pts_to sg wb);
    A.pts_to_len sg;
    assert (pure (Seq.equal wb (Seq.append (Seq.slice vb 0 32) vts)));
    true
  } else {
    false
  }
}

#pop-options
