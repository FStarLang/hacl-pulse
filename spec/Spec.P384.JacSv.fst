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

(** Jacobian coordinates for P-384, as field functions and as polynomial
    computations ({!Spec.Group.Poly}).

    A Jacobian triple [(X, Y, Z)] stands for the homogeneous point
    [(X Z, Y, Z^3)] ({!to_h}); its equation is [Y^2 = X^3 - 3 X Z^4 + b Z^6],
    which is the homogeneous right-hand side at [(X, Y, Z^2)] ({!jeq}).
    Doubling in these coordinates costs eight multiplications to the
    complete formula's eleven, and a run of doublings pays for the two
    conversions.  The functions are written in exactly the order
    {!Hacl.P384.PointWin} computes them, so that the implementation's
    proof is a chain of equalities and the algebra is all here. *)
module Spec.P384.JacSv

open Spec.Group.Poly
open Spec.Group.Check
open Spec.P384.GroupSv
module P = Spec.P384

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
