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

(** The Ed25519 group law, in extended coordinates.

    A point is four field elements, and a field element is what
    [Hacl.Curve25519.Field] says it is: sixteen sixteen-bit limbs in a
    [A.array S64.t].  Rather than invent a record, a point is simply four
    slices passed side by side; that keeps the separation-logic obligations
    trivial (the caller says which four buffers are distinct) and it is
    what the extracted C looks like anyway.

    Every routine here is out-of-place: the output coordinates must be
    disjoint from the inputs.  In Pulse that is not a convention but a
    consequence of the types -- an argument that is written needs full
    permission, one that is read needs only a fraction, and the two cannot
    be the same buffer.  The scalar multiplication below therefore keeps
    three points in flight, which is the price of the formulas being
    branch-free. *)
module Hacl.Ed25519.Point

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Curve25519.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Cast = Hacl.Secret.Cast
module C = Spec.Curve25519
module E = Spec.Ed25519
module Loops = Hacl.Spec.Loops
module Table = Hacl.Impl.Table
module Tables = Hacl.Ed25519.Tables

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

(** {2 Points as four limb sequences} *)

(** The point four limb sequences denote. *)
let pt (a b c d: Seq.seq S64.t) : GTot E.ext_point =
  (fev (vals a), fev (vals b), fev (vals c), fev (vals d))

(** All four are field elements in the representable range. *)
let pt_ok (a b c d: Seq.seq S64.t) : prop =
  felem (vals a) /\ felem (vals b) /\ felem (vals c) /\ felem (vals d)

(** [fscale] multiplies by an integer and reduces once, which is the same
    thing as adding a field element to itself. *)
let double_ok (x: nat)
  : Lemma ((2 * x) % C.prime == C.fadd (x % C.prime) (x % C.prime))
  = C.prime_gt_one ();
    Math.lemma_mod_plus_distr_l x x C.prime;
    Math.lemma_mod_plus_distr_r (x % C.prime) x C.prime

(** Doubling a factor and multiplying, or multiplying and doubling the
    product: the same element.  That is what lets a doubling square [z1]
    and scale the square by two, rather than scale [z1] and multiply --
    fifteen limb products in place of twenty-five. *)
let dblmul (a b: C.elem)
  : Lemma (C.fmul (C.fadd a a) b == C.fadd (C.fmul a b) (C.fmul a b))
  = C.prime_gt_one ();
    Math.lemma_mod_mul_distr_l (a + a) b C.prime;
    Math.distributivity_add_left a a b;
    Math.lemma_mod_plus_distr_l (a * b) (a * b) C.prime;
    Math.lemma_mod_plus_distr_r ((a * b) % C.prime) (a * b) C.prime

(** {2 Addition}

    "add-2008-hwcd-3".  Six scratch elements and the multiplier's own
    thirty-one word scratch are allocated here rather than passed in: the
    caller already has to name twelve buffers.

    The temporaries are recycled in the obvious way.  After the four
    products [a], [b], [c] and [e = 2 z1 z2] are in hand, [a] and [b] are
    dead as soon as [E = b - a] and [H = b + a] have been formed, so
    [F = e - c] and [G = e + c] go straight back into them. *)

#push-options "--z3rlimit 400"

fn point_add (ox oy oz ot: A.array S64.t)
             (x1 y1 z1 t1: A.array S64.t)
             (x2 y2 z2 t2: A.array S64.t)
             (#vox: erased (Seq.seq S64.t)) (#voy: erased (Seq.seq S64.t)) (#voz: erased (Seq.seq S64.t)) (#vot: erased (Seq.seq S64.t))
             (#p1: perm) (#vx1: erased (Seq.seq S64.t)) (#vy1: erased (Seq.seq S64.t)) (#vz1: erased (Seq.seq S64.t)) (#vt1: erased (Seq.seq S64.t))
             (#p2: perm) (#vx2: erased (Seq.seq S64.t)) (#vy2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t)) (#vt2: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 **
  A.pts_to z1 #p1 vz1 ** A.pts_to t1 #p1 vt1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
  A.pts_to z2 #p2 vz2 ** A.pts_to t2 #p2 vt2 **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl /\
        pt_ok vx1 vy1 vz1 vt1 /\ pt_ok vx2 vy2 vz2 vt2)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 **
  A.pts_to z1 #p1 vz1 ** A.pts_to t1 #p1 vt1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
  A.pts_to z2 #p2 vz2 ** A.pts_to t2 #p2 vt2 **
  pure (pt_ok wx wy wz wt /\
        pt wx wy wz wt ==
          E.point_add (pt vx1 vy1 vz1 vt1) (pt vx2 vy2 vz2 vt2))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len x1; A.pts_to_len y1; A.pts_to_len z1; A.pts_to_len t1;
  A.pts_to_len x2; A.pts_to_len y2; A.pts_to_len z2; A.pts_to_len t2;
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut au = [| z; 5sz |]; A.pts_to_len au; let mut av = [| z; 5sz |]; A.pts_to_len av; let mut aa = [| z; 5sz |]; A.pts_to_len aa; let mut ab = [| z; 5sz |]; A.pts_to_len ab; let mut ac = [| z; 5sz |]; A.pts_to_len ac; let mut ae = [| z; 5sz |]; A.pts_to_len ae; let mut aw = [| z128; 9sz |]; A.pts_to_len aw; A.pts_to_len au; A.pts_to_len av; A.pts_to_len aa;
  A.pts_to_len ab; A.pts_to_len ac; A.pts_to_len ae; A.pts_to_len aw;

  (* aa = (y1 - x1) (y2 - x2) *)
  fsub au y1 x1;
  fsub av y2 x2;
  fmul aa au av;

  (* ab = (y1 + x1) (y2 + x2) *)
  fadd au y1 x1;
  fadd av y2 x2;
  fmul ab au av;

  (* ac = 2d t1 t2 *)
  let dt = Table.table Tables.d2_arr 5sz;
  Tables.d2_ok ();
  fmul au dt t1;
  Table.drop_table dt;
  fmul ac au t2;

  (* ae = 2 z1 z2 *)
  fscale au z1 2uL aw;
  with vu. assert (A.pts_to au vu);
  double_ok (eval (vals vz1));
  assert (pure (fev (vals vu) == C.fadd (fev (vals vz1)) (fev (vals vz1))));
  fmul ae au z2;

  (* E = ab - aa, H = ab + aa, then F = ae - ac and G = ae + ac on top of aa and ab *)
  fsub au ab aa;
  fadd av ab aa;
  fsub aa ae ac;
  fadd ab ae ac;

  fmul ox au aa;
  fmul oy ab av;
  fmul oz aa ab;
  fmul ot au av;

  with wx. assert (A.pts_to ox wx);
  with wy. assert (A.pts_to oy wy);
  with wz. assert (A.pts_to oz wz);
  with wt. assert (A.pts_to ot wt);
  assert (pure (pt wx wy wz wt ==
                E.point_add (pt vx1 vy1 vz1 vt1) (pt vx2 vy2 vz2 vt2)));

  ()
}

#pop-options

(** {2 Doubling}

    "dbl-2008-hwcd", which never looks at [t1]: the fourth coordinate of
    the result is rebuilt from [E] and [H] like any other. *)

#push-options "--z3rlimit 400"

fn point_double (ox oy oz ot: A.array S64.t)
                (x1 y1 z1 t1: A.array S64.t)
                (#vox: erased (Seq.seq S64.t)) (#voy: erased (Seq.seq S64.t)) (#voz: erased (Seq.seq S64.t)) (#vot: erased (Seq.seq S64.t))
                (#p1: perm) (#vx1: erased (Seq.seq S64.t)) (#vy1: erased (Seq.seq S64.t)) (#vz1: erased (Seq.seq S64.t))
                (#vt1: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 ** A.pts_to t1 #p1 vt1 **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl /\
        felem (vals vx1) /\ felem (vals vy1) /\ felem (vals vz1))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 ** A.pts_to t1 #p1 vt1 **
  pure (pt_ok wx wy wz wt /\
        pt wx wy wz wt == E.point_double (pt vx1 vy1 vz1 vt1))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len x1; A.pts_to_len y1; A.pts_to_len z1; A.pts_to_len t1;
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut au = [| z; 5sz |]; A.pts_to_len au; let mut av = [| z; 5sz |]; A.pts_to_len av; let mut ar = [| z; 5sz |]; A.pts_to_len ar; let mut aa = [| z; 5sz |]; A.pts_to_len aa; let mut ab = [| z; 5sz |]; A.pts_to_len ab; let mut ac = [| z; 5sz |]; A.pts_to_len ac; let mut aw = [| z128; 9sz |]; A.pts_to_len aw; A.pts_to_len au; A.pts_to_len av; A.pts_to_len ar;
  A.pts_to_len aa; A.pts_to_len ab; A.pts_to_len ac; A.pts_to_len aw;

  (* aa = x1^2, ab = y1^2, ac = 2 z1^2 *)
  fsqr aa x1;
  fsqr ab y1;
  fsqr au z1;
  with vq. assert (A.pts_to au vq);
  assert (pure (fev (vals vq) == C.fmul (fev (vals vz1)) (fev (vals vz1))));
  fscale ac au 2uL aw;
  with vu. assert (A.pts_to ac vu);
  double_ok (eval (vals vq));
  dblmul (fev (vals vz1)) (fev (vals vz1));
  assert (pure (fev (vals vu) ==
                C.fmul (C.fadd (fev (vals vz1)) (fev (vals vz1))) (fev (vals vz1))));

  (* ar = (x1 + y1)^2 *)
  fadd au x1 y1;
  fsqr ar au;

  (* H = aa + ab, E = H - ar, G = aa - ab, F = ac + G *)
  fadd av aa ab;
  fsub au av ar;
  fsub ar aa ab;
  fadd aa ac ar;

  fmul ox au aa;
  fmul oy ar av;
  fmul oz aa ar;
  fmul ot au av;

  with wx. assert (A.pts_to ox wx);
  with wy. assert (A.pts_to oy wy);
  with wz. assert (A.pts_to oz wz);
  with wt. assert (A.pts_to ot wt);
  assert (pure (pt wx wy wz wt == E.point_double (pt vx1 vy1 vz1 vt1)));

  ()
}

#pop-options

(** {2 The neutral element}

    [point_at_infinity] is [(0, 1, 1, 0)], so all four coordinates are set
    by the same routine: zero every limb, then write a small constant into
    the least significant one. *)

#push-options "--z3rlimit 120"

fn set_small (a: A.array S64.t) (m: U64.t { U64.v m < base })
             (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == nl)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** pure (felem (vals va') /\ fev (vals va') == U64.v m)
{
  A.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v **
    pure (SZ.v vi <= 5 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index (vals v) k == 0))
  decreases (5 - SZ.v (!i))
  {
    let vi = !i;
    A.((a.(vi) <- S64.zero));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  A.((a.(0sz) <- S64.classify m));
  with v'. assert (A.pts_to a v');
  vals_upd v 0 (S64.classify m);
  eval_zeros (vals v);
  eval_upd (vals v) 0 (U64.v m);
  assert_norm (pow2 (rad * 0) == 1);
  assert_norm (base <= lim);
  C.prime_gt_one ();
  assert_norm (base < C.prime);
  Math.small_mod (U64.v m) C.prime;
  assert (pure (felem (vals v') /\ fev (vals v') == U64.v m));
}

#pop-options

(** Set a point to the neutral element.  This is where the windowed
    scalar multiplication starts both its accumulator and its table. *)
fn set_infinity (x y z t: A.array S64.t)
                (#vx: erased (Seq.seq S64.t)) (#vy: erased (Seq.seq S64.t))
                (#vz: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz ** A.pts_to t vt **
  pure (Seq.length vx == nl /\ Seq.length vy == nl /\
        Seq.length vz == nl /\ Seq.length vt == nl)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt **
  pure (pt_ok wx wy wz wt /\ pt wx wy wz wt == E.point_at_infinity)
{
  assert_norm (1 < base);
  set_small x 0uL;
  set_small y 1uL;
  set_small z 1uL;
  set_small t 0uL;
  C.prime_gt_one ();
}

#pop-options
