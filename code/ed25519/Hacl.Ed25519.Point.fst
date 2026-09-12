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
  let mut au = [| z; 16sz |]; A.pts_to_len au; let mut av = [| z; 16sz |]; A.pts_to_len av; let mut aa = [| z; 16sz |]; A.pts_to_len aa; let mut ab = [| z; 16sz |]; A.pts_to_len ab; let mut ac = [| z; 16sz |]; A.pts_to_len ac; let mut ae = [| z; 16sz |]; A.pts_to_len ae; let mut aw = [| z; 31sz |]; A.pts_to_len aw; A.pts_to_len au; A.pts_to_len av; A.pts_to_len aa;
  A.pts_to_len ab; A.pts_to_len ac; A.pts_to_len ae; A.pts_to_len aw;

  (* aa = (y1 - x1) (y2 - x2) *)
  fsub au y1 x1;
  fsub av y2 x2;
  fmul aa au av aw;

  (* ab = (y1 + x1) (y2 + x2) *)
  fadd au y1 x1;
  fadd av y2 x2;
  fmul ab au av aw;

  (* ac = 2d t1 t2 *)
  let dt = Table.table Tables.d2_arr 16sz;
  Tables.d2_ok ();
  fmul au dt t1 aw;
  Table.drop_table dt;
  fmul ac au t2 aw;

  (* ae = 2 z1 z2 *)
  fscale au z1 2uL;
  with vu. assert (A.pts_to au vu);
  double_ok (eval (vals vz1));
  assert (pure (fev (vals vu) == C.fadd (fev (vals vz1)) (fev (vals vz1))));
  fmul ae au z2 aw;

  (* E = ab - aa, H = ab + aa, then F = ae - ac and G = ae + ac on top of aa and ab *)
  fsub au ab aa;
  fadd av ab aa;
  fsub aa ae ac;
  fadd ab ae ac;

  fmul ox au aa aw;
  fmul oy ab av aw;
  fmul oz aa ab aw;
  fmul ot au av aw;

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
  let mut au = [| z; 16sz |]; A.pts_to_len au; let mut av = [| z; 16sz |]; A.pts_to_len av; let mut ar = [| z; 16sz |]; A.pts_to_len ar; let mut aa = [| z; 16sz |]; A.pts_to_len aa; let mut ab = [| z; 16sz |]; A.pts_to_len ab; let mut ac = [| z; 16sz |]; A.pts_to_len ac; let mut aw = [| z; 31sz |]; A.pts_to_len aw; A.pts_to_len au; A.pts_to_len av; A.pts_to_len ar;
  A.pts_to_len aa; A.pts_to_len ab; A.pts_to_len ac; A.pts_to_len aw;

  (* aa = x1^2, ab = y1^2, ac = 2 z1^2 *)
  copy au x1;
  fmul aa au x1 aw;
  copy au y1;
  fmul ab au y1 aw;
  fscale au z1 2uL;
  with vu. assert (A.pts_to au vu);
  double_ok (eval (vals vz1));
  assert (pure (fev (vals vu) == C.fadd (fev (vals vz1)) (fev (vals vz1))));
  fmul ac au z1 aw;

  (* ar = (x1 + y1)^2 *)
  fadd au x1 y1;
  copy av au;
  fmul ar av au aw;

  (* H = aa + ab, E = H - ar, G = aa - ab, F = ac + G *)
  fadd av aa ab;
  fsub au av ar;
  fsub ar aa ab;
  fadd aa ac ar;

  fmul ox au aa aw;
  fmul oy ar av aw;
  fmul oz aa ar aw;
  fmul ot au av aw;

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
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index (vals v) k == 0))
  decreases (16 - SZ.v (!i))
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

(** Set a point to the neutral element. *)
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
  set_small x 0uL;
  set_small y 1uL;
  set_small z 1uL;
  set_small t 0uL;
  C.prime_gt_one ();
}

(** {2 Scalar multiplication}

    Double-and-add over all two hundred and fifty-six bits, most
    significant first, with the conditional addition done as a swap on a
    mask.  Three points are in flight: the accumulator [a], the doubling
    [b], and the sum [c]; the formulas cannot write their output over an
    input, so there is no way to do it with two. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

fn point_mul_step (ax ay az at ux uy uz ut sx sy sz st: A.array S64.t)
                  (qx qy qz qt: A.array S64.t) (ks: A.array S8.t)
                  (n: SZ.t { SZ.v n < 256 })
                  (#vax: erased (Seq.seq S64.t)) (#vay: erased (Seq.seq S64.t))
                  (#vaz: erased (Seq.seq S64.t)) (#vat: erased (Seq.seq S64.t))
                  (#vux: erased (Seq.seq S64.t)) (#vuy: erased (Seq.seq S64.t))
                  (#vuz: erased (Seq.seq S64.t)) (#vut: erased (Seq.seq S64.t))
                  (#vsx: erased (Seq.seq S64.t)) (#vsy: erased (Seq.seq S64.t))
                  (#vsz: erased (Seq.seq S64.t)) (#vst: erased (Seq.seq S64.t))
                  (#pp: perm)
                  (#vpx: erased (Seq.seq S64.t)) (#vpy: erased (Seq.seq S64.t))
                  (#vpz: erased (Seq.seq S64.t)) (#vpt: erased (Seq.seq S64.t))
                  (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to ax vax ** A.pts_to ay vay ** A.pts_to az vaz ** A.pts_to at vat **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz ** A.pts_to st vst **
  A.pts_to qx #pp vpx ** A.pts_to qy #pp vpy **
  A.pts_to qz #pp vpz ** A.pts_to qt #pp vpt ** A.pts_to ks #pk vk **
  pure (pt_ok vax vay vaz vat /\ pt_ok vpx vpy vpz vpt /\
        Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length vsz == nl /\ Seq.length vst == nl)
ensures exists* (wax way waz wat wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
  A.pts_to ax wax ** A.pts_to ay way ** A.pts_to az waz ** A.pts_to at wat **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
  A.pts_to qx #pp vpx ** A.pts_to qy #pp vpy **
  A.pts_to qz #pp vpz ** A.pts_to qt #pp vpt ** A.pts_to ks #pk vk **
  pure (pt_ok wax way waz wat /\
        Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\
        Seq.length wsz == nl /\ Seq.length wst == nl /\
        pt wax way waz wat ==
          E.point_mul_step vk (pt vpx vpy vpz vpt) (SZ.v n)
                           (pt vax vay vaz vat))
{
  A.pts_to_len ks;
  let bi = SZ.sub 255sz n;
  let bj = SZ.div bi 8sz;
  let sh = SZ.sizet_to_uint32 (SZ.rem bi 8sz);
  assert_norm (pow2 32 > 8);
  Math.small_mod (SZ.v (SZ.rem bi 8sz)) (pow2 32);
  assert (pure (SZ.v bi == 255 - SZ.v n /\ SZ.v bj == SZ.v bi / 8 /\
                U32.v sh == SZ.v bi % 8));
  let byte = A.(ks.(bj));
  let w = Cast.u8_to_u64 byte;
  let sr = S64.shift_right w sh;
  assert (pure (S64.v sr == S64.v w / pow2 (SZ.v bi % 8)));
  UInt.logand_mask #64 (S64.v sr) 1;
  let bit = S64.logand sr (S64.classify 1uL);
  assert (pure (S64.v bit == C.ith_bit vk (SZ.v bi) /\ S64.v bit < 2));
  let sel = S64.eq_mask bit (S64.classify 1uL);
  assert (pure ((S64.v sel == 0) == (S64.v bit <> 1)));

  point_double ux uy uz ut ax ay az at;
  point_add sx sy sz st ux uy uz ut qx qy qz qt;

  cswap sel ux sx;
  cswap sel uy sy;
  cswap sel uz sz;
  cswap sel ut st;

  copy ax ux;
  copy ay uy;
  copy az uz;
  copy at ut;

  with wax. assert (A.pts_to ax wax);
  with way. assert (A.pts_to ay way);
  with waz. assert (A.pts_to az waz);
  with wat. assert (A.pts_to at wat);
  assert (pure (pt wax way waz wat ==
                E.point_mul_step vk (pt vpx vpy vpz vpt) (SZ.v n)
                                 (pt vax vay vaz vat)));
}

#pop-options

(** [out := [k] p].  The accumulator lives in the output, and the two
    working points are allocated here. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

fn point_mul (ox oy oz ot: A.array S64.t) (qx qy qz qt: A.array S64.t)
             (ks: A.array S8.t)
             (#vox: erased (Seq.seq S64.t)) (#voy: erased (Seq.seq S64.t))
             (#voz: erased (Seq.seq S64.t)) (#vot: erased (Seq.seq S64.t))
             (#pp: perm)
             (#vqx: erased (Seq.seq S64.t)) (#vqy: erased (Seq.seq S64.t))
             (#vqz: erased (Seq.seq S64.t)) (#vqt: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy **
  A.pts_to qz #pp vqz ** A.pts_to qt #pp vqt ** A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl /\
        pt_ok vqx vqy vqz vqt)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy **
  A.pts_to qz #pp vqz ** A.pts_to qt #pp vqt ** A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz wt /\
        pt wx wy wz wt == E.point_mul vk (pt vqx vqy vqz vqt))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  let z = S64.zero;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let mut a4 = [| z; 16sz |]; A.pts_to_len a4; let mut a5 = [| z; 16sz |]; A.pts_to_len a5; let mut a6 = [| z; 16sz |]; A.pts_to_len a6; let mut a7 = [| z; 16sz |]; A.pts_to_len a7; let mut a8 = [| z; 16sz |]; A.pts_to_len a8; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3; A.pts_to_len a4;
  A.pts_to_len a5; A.pts_to_len a6; A.pts_to_len a7; A.pts_to_len a8;

  set_infinity ox oy oz ot;
  Loops.repeati_g_zero (E.point_mul_at vk (pt vqx vqy vqz vqt)) E.point_at_infinity;

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
    A.pts_to a1 wux ** A.pts_to a2 wuy ** A.pts_to a3 wuz ** A.pts_to a4 wut **
    A.pts_to a5 wsx ** A.pts_to a6 wsy ** A.pts_to a7 wsz ** A.pts_to a8 wst **
    A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy **
    A.pts_to qz #pp vqz ** A.pts_to qt #pp vqt ** A.pts_to ks #pk vk **
    pure (SZ.v vi <= 256 /\ pt_ok wx wy wz wt /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\
          Seq.length wuz == nl /\ Seq.length wut == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          Seq.length wsz == nl /\ Seq.length wst == nl /\
          pt wx wy wz wt ==
            Loops.repeati_g (SZ.v vi) (E.point_mul_at vk (pt vqx vqy vqz vqt))
                            E.point_at_infinity)
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    with wx. assert (A.pts_to ox wx);
    with wy. assert (A.pts_to oy wy);
    with wz. assert (A.pts_to oz wz);
    with wt. assert (A.pts_to ot wt);
    point_mul_step ox oy oz ot a1 a2 a3 a4 a5 a6 a7 a8 qx qy qz qt ks vi;
    with rx. assert (A.pts_to ox rx);
    with ry. assert (A.pts_to oy ry);
    with rz. assert (A.pts_to oz rz);
    with rt. assert (A.pts_to ot rt);
    Loops.unfold_repeati_g (SZ.v vi) (E.point_mul_at vk (pt vqx vqy vqz vqt))
                           E.point_at_infinity;
    assert (pure (pt rx ry rz rt ==
                  Loops.repeati_g (SZ.v vi + 1)
                    (E.point_mul_at vk (pt vqx vqy vqz vqt))
                    E.point_at_infinity));
    i := SZ.add vi 1sz;
  };

  ()
}

#pop-options

#pop-options
