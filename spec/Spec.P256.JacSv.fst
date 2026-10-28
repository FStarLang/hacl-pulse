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

(** Jacobian coordinates for P-256, as field functions and as polynomial
    computations ({!Spec.Group.Poly}).

    A Jacobian triple [(X, Y, Z)] stands for the homogeneous point
    [(X Z, Y, Z^3)] ({!to_h}); its equation is [Y^2 = X^3 - 3 X Z^4 + b Z^6],
    which is the homogeneous right-hand side at [(X, Y, Z^2)] ({!jeq}).
    Doubling in these coordinates costs eight multiplications to the
    complete formula's eleven, and a run of doublings pays for the two
    conversions.  The functions are written in exactly the order
    {!Hacl.P256.PointWin} computes them, so that the implementation's
    proof is a chain of equalities and the algebra is all here. *)
module Spec.P256.JacSv

open Spec.Group.Poly
open Spec.Group.Check
open Spec.P256.GroupSv
module P = Spec.P256

(** {2 Field functions} *)

let fdbl (a: P.felem) : P.felem = P.fadd a a

(** [dbl-2001-b] for [a = -3], in the order of the implementation. *)
[@@"opaque_to_smt"]
let jdouble (p: P.proj_point) : P.proj_point =
  let (x, y, z) = p in
  let d = P.fmul z z in
  let g = P.fmul y y in
  let z3 = fdbl (P.fmul z y) in
  let t2 = P.fsub x d in
  let t0 = P.fmul (P.fadd d x) t2 in
  let a = P.fadd t0 (fdbl t0) in
  let b4 = fdbl (fdbl (P.fmul x g)) in
  let g8 = fdbl (fdbl (fdbl (P.fmul g g))) in
  let x3 = P.fsub (P.fmul a a) (fdbl b4) in
  let y3 = P.fsub (P.fmul (P.fsub b4 x3) a) g8 in
  (x3, y3, z3)

(** Jacobian to homogeneous. *)
[@@"opaque_to_smt"]
let to_h (p: P.proj_point) : P.proj_point =
  let (x, y, z) = p in (P.fmul x z, y, P.fmul z (P.fmul z z))

(** Homogeneous to Jacobian, away from infinity: [(x z, y z^2, z)]. *)
[@@"opaque_to_smt"]
let tj (p: P.proj_point) : P.proj_point =
  let (x, y, z) = p in (P.fmul x z, P.fmul y (P.fmul z z), z)

(** The Jacobian equation. *)
[@@"opaque_to_smt"]
let jeq (p: P.proj_point) : prop =
  let (x, y, z) = p in P.fmul y y == eqn_r (x, y, P.fmul z z)

(** Mixed addition: the second point is affine, [(x2, y2, 1)].  This is
    Renes--Costello--Batina 2016, Algorithm 5, for [a = -3]: Algorithm 4
    with [Z2 = 1] substituted and simplified, one multiplication cheaper.
    {!Spec.P256.JacChecks.j6} proves it is {!P.point_add} at [Z2 = 1]. *)
[@@"opaque_to_smt"]
let madd (p: P.proj_point) (x2 y2: P.felem) : P.proj_point =
  let (x1, y1, z1) = p in
  let t0 = P.fmul x1 x2 in
  let t1 = P.fmul y1 y2 in
  let t3 = P.fadd x2 y2 in
  let t4 = P.fadd x1 y1 in
  let t3 = P.fmul t3 t4 in
  let t4 = P.fadd t0 t1 in
  let t3 = P.fsub t3 t4 in
  let t4 = P.fmul y2 z1 in
  let t4 = P.fadd t4 y1 in
  let y3 = P.fmul x2 z1 in
  let y3 = P.fadd y3 x1 in
  let z3 = P.fmul P.b_coeff z1 in
  let x3 = P.fsub y3 z3 in
  let z3 = P.fadd x3 x3 in
  let x3 = P.fadd x3 z3 in
  let z3 = P.fsub t1 x3 in
  let x3 = P.fadd t1 x3 in
  let y3 = P.fmul P.b_coeff y3 in
  let t1 = P.fadd z1 z1 in
  let t2 = P.fadd t1 z1 in
  let y3 = P.fsub y3 t2 in
  let y3 = P.fsub y3 t0 in
  let t1 = P.fadd y3 y3 in
  let y3 = P.fadd t1 y3 in
  let t1 = P.fadd t0 t0 in
  let t0 = P.fadd t1 t0 in
  let t0 = P.fsub t0 t2 in
  let t1 = P.fmul t4 y3 in
  let t2 = P.fmul t0 y3 in
  let y3 = P.fmul x3 z3 in
  let y3 = P.fadd y3 t2 in
  let x3 = P.fmul t3 x3 in
  let x3 = P.fsub x3 t1 in
  let z3 = P.fmul t4 z3 in
  let t1 = P.fmul t3 t0 in
  let z3 = P.fadd z3 t1 in
  (x3, y3, z3)

(** {2 The same as polynomial computations} *)

let sdbl (#c: ctx) (a: sv c) : sv c = sadd a a

[@@"opaque_to_smt"]
let jdouble_sv (#c: ctx) (p: sp c) : sp c =
  let (x, y, z) = p in
  let d = smul z z in
  let g = smul y y in
  let z3 = sdbl (smul z y) in
  let t2 = ssub x d in
  let t0 = smul (sadd d x) t2 in
  let a = sadd t0 (sdbl t0) in
  let b4 = sdbl (sdbl (smul x g)) in
  let g8 = sdbl (sdbl (sdbl (smul g g))) in
  let x3 = ssub (smul a a) (sdbl b4) in
  let y3 = ssub (smul (ssub b4 x3) a) g8 in
  (x3, y3, z3)

[@@"opaque_to_smt"]
let to_h_sv (#c: ctx) (p: sp c) : sp c =
  let (x, y, z) = p in (smul x z, y, smul z (smul z z))

[@@"opaque_to_smt"]
let tj_sv (#c: ctx) (p: sp c) : sp c =
  let (x, y, z) = p in (smul x z, smul y (smul z z), z)

[@@"opaque_to_smt"]
let madd_sv (#c: ctx) (b: sv c) (p: sp c) (x2 y2: sv c) : sp c =
  let (x1, y1, z1) = p in
  let t0 = smul x1 x2 in
  let t1 = smul y1 y2 in
  let t3 = sadd x2 y2 in
  let t4 = sadd x1 y1 in
  let t3 = smul t3 t4 in
  let t4 = sadd t0 t1 in
  let t3 = ssub t3 t4 in
  let t4 = smul y2 z1 in
  let t4 = sadd t4 y1 in
  let y3 = smul x2 z1 in
  let y3 = sadd y3 x1 in
  let z3 = smul b z1 in
  let x3 = ssub y3 z3 in
  let z3 = sadd x3 x3 in
  let x3 = sadd x3 z3 in
  let z3 = ssub t1 x3 in
  let x3 = sadd t1 x3 in
  let y3 = smul b y3 in
  let t1 = sadd z1 z1 in
  let t2 = sadd t1 z1 in
  let y3 = ssub y3 t2 in
  let y3 = ssub y3 t0 in
  let t1 = sadd y3 y3 in
  let y3 = sadd t1 y3 in
  let t1 = sadd t0 t0 in
  let t0 = sadd t1 t0 in
  let t0 = ssub t0 t2 in
  let t1 = smul t4 y3 in
  let t2 = smul t0 y3 in
  let y3 = smul x3 z3 in
  let y3 = sadd y3 t2 in
  let x3 = smul t3 x3 in
  let x3 = ssub x3 t1 in
  let z3 = smul t4 z3 in
  let t1 = smul t3 t0 in
  let z3 = sadd z3 t1 in
  (x3, y3, z3)

(** [Y^2 -> X^3 - 3 X Z^4 + b Z^6]: the Jacobian equation as a rewrite. *)
[@@"opaque_to_smt"]
let jac_hyp (c: ctx) (i j k: (k: nat { k < c.nv })) : hyp c =
  let x = svar c i in let y = svar c j in let z = svar c k in
  (smul y y, eqn_rsv (x, y, smul z z))

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let jdouble_val (c: ctx { c.m == m0 }) (p: sp c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures tof3 (jdouble_sv p) == jdouble (tof3 p))
  = m0_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%jdouble) jdouble;
    FStar.Pervasives.reveal_opaque (`%jdouble_sv) (jdouble_sv #c)

let madd_val (c: ctx { c.m == m0 }) (b: sv c) (p: sp c) (x2 y2: sv c)
  : Lemma (requires ok c /\ c.o == o /\ vl b == bl)
          (ensures tof3 (madd_sv b p x2 y2) == madd (tof3 p) (tof (vl x2)) (tof (vl y2)))
  = m0_lem (); bl_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%madd) madd;
    FStar.Pervasives.reveal_opaque (`%madd_sv) (madd_sv #c)

let to_h_val (c: ctx { c.m == m0 }) (p: sp c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures tof3 (to_h_sv p) == to_h (tof3 p))
  = m0_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%to_h) to_h;
    FStar.Pervasives.reveal_opaque (`%to_h_sv) (to_h_sv #c)

let tj_val (c: ctx { c.m == m0 }) (p: sp c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures tof3 (tj_sv p) == tj (tof3 p))
  = m0_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%tj) tj;
    FStar.Pervasives.reveal_opaque (`%tj_sv) (tj_sv #c)

(** [jeq] at a polynomial triple is an equation between two of them. *)
let jeq_val (c: ctx { c.m == m0 }) (p: sp c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures (let (x, y, z) = p in
                    jeq (tof3 p) <==>
                    tof (vl (smul y y)) == tof (vl (eqn_rsv (x, y, smul z z)))))
  = m0_lem (); o_eqs ();
    let (x, y, z) = p in
    eqn_val c (x, y, smul z z);
    FStar.Pervasives.reveal_opaque (`%jeq) jeq

let jac_hyp_ok (c: ctx) (i j k: (k: nat { k < c.nv }))
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o /\
                    jeq (tof (nth0 0 c.env i), tof (nth0 0 c.env j), tof (nth0 0 c.env k)))
          (ensures vl (fst (jac_hyp c i j k)) == vl (snd (jac_hyp c i j k)))
  = o_eqs ();
    FStar.Pervasives.reveal_opaque (`%jac_hyp) jac_hyp;
    jeq_val c (svar c i, svar c j, svar c k)
#pop-options
