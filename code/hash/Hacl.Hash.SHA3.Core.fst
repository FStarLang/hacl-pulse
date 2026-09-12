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

    Two scratch buffers are threaded through: [c], five lanes, holds the column
    parities that theta needs, and [b], twenty-five lanes, holds the state
    between rho-pi and chi.  rho-pi is a permutation of the lanes combined with
    a rotation, so it cannot be done in place; chi reads three lanes to write
    one, so it cannot either.  The two together are one buffer's worth of
    traffic per round, which is what every Keccak implementation does.

    The rotation offsets live in a twenty-five element table of [uint32_t]
    rather than in a [match]: the offsets are public, and a table read is a
    load where a match over a runtime index would be a jump table. *)
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

(** {2 Rotation with a runtime offset}

    [Hacl.Secret.UInt64.rotate_left] wants a nonzero offset, and [rotc 0] is
    zero, so the zero case is a branch -- on a public value, so it is free of
    any constant-time concern. *)

let rotl_u32 (x: S64.t) (k: U32.t { U32.v k < 64 }) : (y: S64.t { y == rotl x (U32.v k) }) =
  if k = 0ul then x else (U32.uv_inv k; S64.rotate_left x k)

(** {2 theta} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** The five column parities. *)
fn theta_c_impl (st: A.array S64.t) (c: A.array S64.t)
                (#pst: perm) (#vst: erased (Seq.seq S64.t)) (#vc0: erased (Seq.seq S64.t))
requires A.pts_to st #pst vst ** A.pts_to c vc0 **
         pure (Seq.length vst == 25 /\ Seq.length vc0 == 5)
ensures exists* (vc: Seq.seq S64.t).
  A.pts_to st #pst vst ** A.pts_to c vc **
  pure (Seq.length vst == 25 /\ Seq.length vc == 5 /\
        (forall (x: nat). x < 5 ==> Seq.index vc x == theta_c vst x))
{
  A.pts_to_len st;
  A.pts_to_len c;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (vc: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st #pst vst ** A.pts_to c vc **
    pure (Seq.length vst == 25 /\ SZ.v vi <= 5 /\ Seq.length vc == 5 /\
          (forall (x: nat). x < SZ.v vi ==> Seq.index vc x == theta_c vst x))
  decreases (5 - SZ.v (!i))
  {
    let vi = !i;
    let a0 = A.(st.(vi));
    let a1 = A.(st.(SZ.add vi 5sz));
    let a2 = A.(st.(SZ.add vi 10sz));
    let a3 = A.(st.(SZ.add vi 15sz));
    let a4 = A.(st.(SZ.add vi 20sz));
    let r = S64.logxor (S64.logxor (S64.logxor (S64.logxor a0 a1) a2) a3) a4;
    theta_c_eq (reveal vst) (SZ.v vi);
    A.((c.(vi) <- r));
    i := SZ.add vi 1sz;
  };
}

(** [st] becomes [theta st]. *)
fn theta_apply (st: A.array S64.t) (c: A.array S64.t)
               (#vst0: erased (Seq.seq S64.t)) (#pc: perm) (#vc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to c #pc vc **
         pure (Seq.length vst0 == 25 /\ Seq.length vc == 5 /\
               (forall (x: nat). x < 5 ==> Seq.index vc x == theta_c vst0 x))
ensures exists* (vst: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to c #pc vc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
        vst == theta (reveal vst0))
{
  A.pts_to_len st;
  A.pts_to_len c;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst ** A.pts_to c #pc vc **
    pure (Seq.length vst0 == 25 /\ SZ.v vi <= 25 /\ Seq.length vst == 25 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vst k == Seq.index (theta vst0) k) /\
          (forall (k: nat). SZ.v vi <= k /\ k < 25 ==> Seq.index vst k == Seq.index vst0 k))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    let x = SZ.rem vi 5sz;
    assert (pure (SZ.v x < 5));
    let x4 = SZ.rem (SZ.add x 4sz) 5sz;
    let x1 = SZ.rem (SZ.add x 1sz) 5sz;
    assert (pure (SZ.v x4 < 5 /\ SZ.v x1 < 5));
    let c1 = A.(c.(x4));
    let c2 = A.(c.(x1));
    let d = S64.logxor c1 (rotl_u32 c2 1ul);
    let a = A.(st.(vi));
    A.((st.(vi) <- S64.logxor a d));
    theta_step (reveal vst0) (reveal vc) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with vst. assert (A.pts_to st vst);
  assert (pure (Seq.length (theta (reveal vst0)) == 25));
  assert (pure (reveal vst `Seq.equal` (theta (reveal vst0))));
}

#pop-options

(** {2 rho and pi} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** [b] becomes [rho_pi st].  [rotc_tbl] holds the twenty-five rho offsets. *)
fn rho_pi_impl (st: A.array S64.t) (b: A.array S64.t) (rotc_tbl: A.array U32.t)
               (#pst: perm) (#vst: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
               (#pr: perm) (#vr: erased (Seq.seq U32.t))
requires A.pts_to st #pst vst ** A.pts_to b vb0 ** A.pts_to rotc_tbl #pr vr **
         pure (Seq.length vst == 25 /\ Seq.length vb0 == 25 /\ Seq.length vr == 25 /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j))
ensures exists* (vb: Seq.seq S64.t).
  A.pts_to st #pst vst ** A.pts_to b vb ** A.pts_to rotc_tbl #pr vr **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\
        vb == rho_pi (reveal vst))
{
  A.pts_to_len st;
  A.pts_to_len b;
  A.pts_to_len rotc_tbl;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (vb: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st #pst vst ** A.pts_to b vb ** A.pts_to rotc_tbl #pr vr **
    pure (Seq.length vst == 25 /\ SZ.v vi <= 25 /\ Seq.length vb == 25 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vb k == Seq.index (rho_pi vst) k))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    let x = SZ.rem vi 5sz;
    let y = SZ.div vi 5sz;
    assert (pure (SZ.v x < 5 /\ SZ.v y < 5));
    let j = SZ.add (SZ.rem (SZ.add x (SZ.mul 3sz y)) 5sz) (SZ.mul 5sz x);
    assert (pure (SZ.v j < 25 /\ SZ.v j == rho_pi_src (SZ.v vi)));
    let a = A.(st.(j));
    let k = A.(rotc_tbl.(j));
    A.((b.(vi) <- rotl_u32 a k));
    rho_pi_index (reveal vst) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with vb. assert (A.pts_to b vb);
  assert (pure (Seq.length (rho_pi (reveal vst)) == 25));
  assert (pure (reveal vb `Seq.equal` (rho_pi (reveal vst))));
}

#pop-options

(** {2 chi} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** [st] becomes [chi b]. *)
fn chi_impl (b: A.array S64.t) (st: A.array S64.t)
            (#pb: perm) (#vb: erased (Seq.seq S64.t)) (#vst0: erased (Seq.seq S64.t))
requires A.pts_to b #pb vb ** A.pts_to st vst0 **
         pure (Seq.length vb == 25 /\ Seq.length vst0 == 25)
ensures exists* (vst: Seq.seq S64.t).
  A.pts_to b #pb vb ** A.pts_to st vst **
  pure (Seq.length vb == 25 /\ Seq.length vst == 25 /\
        vst == chi (reveal vb))
{
  A.pts_to_len b;
  A.pts_to_len st;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t).
    pts_to i vi ** A.pts_to b #pb vb ** A.pts_to st vst **
    pure (Seq.length vb == 25 /\ SZ.v vi <= 25 /\ Seq.length vst == 25 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vst k == Seq.index (chi vb) k))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    let x = SZ.rem vi 5sz;
    let y = SZ.div vi 5sz;
    assert (pure (SZ.v x < 5 /\ SZ.v y < 5));
    let y5 = SZ.mul 5sz y;
    let j1 = SZ.add (SZ.rem (SZ.add x 1sz) 5sz) y5;
    let j2 = SZ.add (SZ.rem (SZ.add x 2sz) 5sz) y5;
    assert (pure (SZ.v j1 < 25 /\ SZ.v j2 < 25));
    let a0 = A.(b.(vi));
    let a1 = A.(b.(j1));
    let a2 = A.(b.(j2));
    A.((st.(vi) <- S64.logxor a0 (S64.logand (S64.lognot a1) a2)));
    chi_index (reveal vb) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with vst. assert (A.pts_to st vst);
  assert (pure (Seq.length (chi (reveal vb)) == 25));
  assert (pure (reveal vst `Seq.equal` (chi (reveal vb))));
}

#pop-options

(** {2 One round, and the permutation} *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn round_impl (st: A.array S64.t) (b: A.array S64.t) (c: A.array S64.t)
              (rotc_tbl: A.array U32.t) (rc_tbl: A.array S64.t) (n: SZ.t)
              (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
              (#vc0: erased (Seq.seq S64.t))
              (#pr: perm) (#vr: erased (Seq.seq U32.t))
              (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to c vc0 **
         A.pts_to rotc_tbl #pr vr ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\ Seq.length vc0 == 5 /\
               Seq.length vr == 25 /\ reveal vrc == (rc <: Seq.seq S64.t) /\
               SZ.v n < 24 /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j))
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to c vc **
  A.pts_to rotc_tbl #pr vr ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
        Seq.length vb == 25 /\ Seq.length vc == 5 /\ SZ.v n < 24 /\
        vst == round (SZ.v n) (reveal vst0))
{
  A.pts_to_len st;
  A.pts_to_len rc_tbl;
  theta_c_impl st c;
  theta_apply st c;
  rho_pi_impl st b rotc_tbl;
  chi_impl b st;
  with v1. assert (A.pts_to st v1);
  let x0 = A.(st.(0sz));
  let r = A.(rc_tbl.(n));
  A.((st.(0sz) <- S64.logxor x0 r));
}

(** Twenty-four rounds. *)
fn permute_impl (st: A.array S64.t) (b: A.array S64.t) (c: A.array S64.t)
                (rotc_tbl: A.array U32.t) (rc_tbl: A.array S64.t)
                (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
                (#vc0: erased (Seq.seq S64.t))
                (#pr: perm) (#vr: erased (Seq.seq U32.t))
                (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to c vc0 **
         A.pts_to rotc_tbl #pr vr ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\ Seq.length vc0 == 5 /\
               Seq.length vr == 25 /\ reveal vrc == (rc <: Seq.seq S64.t) /\
               (forall (j: nat). j < 25 ==> U32.v (Seq.index vr j) == rotc j))
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to c vc **
  A.pts_to rotc_tbl #pr vr ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\ Seq.length vb == 25 /\
        Seq.length vc == 5 /\ vst == permute (reveal vst0))
{
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 24sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vc: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst ** A.pts_to b vb ** A.pts_to c vc **
    A.pts_to rotc_tbl #pr vr ** A.pts_to rc_tbl #prc vrc **
    pure (Seq.length vst0 == 25 /\ SZ.v vi <= 24 /\ Seq.length vst == 25 /\
          Seq.length vb == 25 /\ Seq.length vc == 5 /\
          vst == Loops.repeati (SZ.v vi) round (reveal vst0))
  decreases (24 - SZ.v (!i))
  {
    let vi = !i;
    Loops.unfold_repeati (SZ.v vi) round (reveal vst0);
    round_impl st b c rotc_tbl rc_tbl vi;
    i := SZ.add vi 1sz;
  };
}

#pop-options
