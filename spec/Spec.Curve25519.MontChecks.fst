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

(** Polynomial identities behind the X25519 ladder.

    The ladder of {!Spec.Curve25519} works on the Montgomery [u]
    coordinate, and Curve25519 is birationally equivalent to Edwards25519
    by [u = (1 + y) / (1 - y)].  This module does not define the Montgomery
    curve at all: it states the ladder's two formulas as identities about
    Edwards points, whose group law {!Spec.Ed25519.Group} already proves.
    For an affine Edwards point [(u, v)] -- [u] the Edwards [x], [v] the
    Edwards [y] -- the Montgomery projective coordinate is
    [(1 + v : 1 - v)], and

    - the doubling half of [add_and_double], applied to [(1 + v : 1 - v)],
      gives a pair proportional to that of the Edwards double
      ({!dbl_aff});
    - the differential addition, applied to the coordinates of [N] and [M]
      and to [x1 = u(N - M)], gives a pair proportional to that of [N + M]
      ({!add_aff}), after clearing the denominator of [x1].

    Both are cross-multiplied identities modulo the affine curve equations
    and are checked by the normaliser exactly as the Edwards group law is
    ({!Spec.Group.Poly}, {!Spec.Ed25519.GroupSv}).  The rest are exact
    identities -- homogeneity and symmetry of the formulas -- and three
    small facts about the exceptional points [v = 0] and [v = +-1], which
    are where a projective pair could degenerate.

    Each [_chk] is a boolean computed by the normaliser (in [_ok]); the
    lemma of the same name reads it back as a statement about the field. *)
module Spec.Curve25519.MontChecks

open Spec.Group.Poly
open Spec.Group.Check
open Spec.Ed25519.GroupSv

module E = Spec.Curve25519
module Ed = Spec.Ed25519

(** {2 The ladder's formulas}

    Transcribed from [Spec.Curve25519.add_and_double]: [mdbl] is its
    doubling half, [mdiff] its differential addition, and [mcore] the two
    quantities [DA + CB] and [DA - CB] that the latter squares. *)

let mdbl (q: E.proj) : E.proj =
  let (x2, z2) = q in
  let a = E.fadd x2 z2 in
  let b = E.fsub x2 z2 in
  let aa = E.fmul a a in
  let bb = E.fmul b b in
  let e = E.fsub aa bb in
  (E.fmul aa bb, E.fmul e (E.fadd aa (E.fmul E.a24 e)))

let mcore (p q: E.proj) : E.elem & E.elem =
  let (x2, z2) = p in
  let (x3, z3) = q in
  let a = E.fadd x2 z2 in
  let b = E.fsub x2 z2 in
  let c = E.fadd x3 z3 in
  let d = E.fsub x3 z3 in
  let da = E.fmul d a in
  let cb = E.fmul c b in
  (E.fadd da cb, E.fsub da cb)

let mdiff (x1: E.elem) (p q: E.proj) : E.proj =
  let (s, t) = mcore p q in
  (E.fmul s s, E.fmul x1 (E.fmul t t))

let add_and_double_eq (x1: E.elem) (p q: E.proj)
  : Lemma (E.add_and_double x1 p q == (mdbl p, mdiff x1 p q))
  = ()

(** The same, over [sv]. *)

let a24l : nat = 121665

[@@"opaque_to_smt"]
let mdbl_sv (#c: ctx) (x2 z2: sv c) : sv c & sv c =
  let a = sadd x2 z2 in
  let b = ssub x2 z2 in
  let aa = smul a a in
  let bb = smul b b in
  let e = ssub aa bb in
  (smul aa bb, smul e (sadd aa (smul (kc c a24l) e)))

[@@"opaque_to_smt"]
let mcore_sv (#c: ctx) (x2 z2 x3 z3: sv c) : sv c & sv c =
  let a = sadd x2 z2 in
  let b = ssub x2 z2 in
  let cc = sadd x3 z3 in
  let dd = ssub x3 z3 in
  let da = smul dd a in
  let cb = smul cc b in
  (sadd da cb, ssub da cb)

[@@"opaque_to_smt"]
let mdiff_sv (#c: ctx) (x1 x2 z2 x3 z3: sv c) : sv c & sv c =
  let (s, t) = mcore_sv x2 z2 x3 z3 in
  (smul s s, smul x1 (smul t t))

let tv (#c: ctx { c.m == m0 }) (x: sv c) : E.elem = tof (vl x)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
let mdbl_val (c: ctx { c.m == m0 }) (x z: sv c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures (let (r0, r1) = mdbl_sv x z in (tv r0, tv r1) == mdbl (tv x, tv z)))
  = m0_lem (); o_eqs ();
    assert_norm (a24l % m0 == a24l);
    assert (cst a24l == E.a24);
    FStar.Pervasives.reveal_opaque (`%mdbl_sv) (mdbl_sv #c)

let mcore_val (c: ctx { c.m == m0 }) (x2 z2 x3 z3: sv c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures (let (r0, r1) = mcore_sv x2 z2 x3 z3 in
                    (tv r0, tv r1) == mcore (tv x2, tv z2) (tv x3, tv z3)))
  = m0_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%mcore_sv) (mcore_sv #c)

let mdiff_val (c: ctx { c.m == m0 }) (x1 x2 z2 x3 z3: sv c)
  : Lemma (requires ok c /\ c.o == o)
          (ensures (let (r0, r1) = mdiff_sv x1 x2 z2 x3 z3 in
                    (tv r0, tv r1) == mdiff (tv x1) (tv x2, tv z2) (tv x3, tv z3)))
  = m0_lem (); o_eqs ();
    mcore_val c x2 z2 x3 z3;
    FStar.Pervasives.reveal_opaque (`%mdiff_sv) (mdiff_sv #c)
#pop-options

#push-options "--fuel 5 --ifuel 1"
let holds4 (#c: ctx) (h1 h2 h3 h4: hyp c)
  : Lemma (requires vl (fst h1) == vl (snd h1) /\ vl (fst h2) == vl (snd h2) /\
                    vl (fst h3) == vl (snd h3) /\ vl (fst h4) == vl (snd h4))
          (ensures holds [h1; h2; h3; h4]) = ()
#pop-options

(** {2 Exact identities} *)

(** Distributivity, and [(1 + a) + (1 - a) = 2], which the rest of the
    proof uses to move between affine and projective coordinates. *)
let ring_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c = base m0 fl o' 3 env in
  let a = svar c 0 in
  let b = svar c 1 in
  let x = svar c 2 in
  Nil? (fst (ssub (smul (ssub a b) x) (ssub (smul a x) (smul b x)))) &&
  Nil? (fst (ssub (smul (sadd a b) x) (sadd (smul a x) (smul b x)))) &&
  Nil? (fst (ssub (sadd (sadd (kc c 1) a) (ssub (kc c 1) a)) (kc c 2)))

let ring_ok (o': fops m0) (env: list (elem m0)) : Lemma (ring_chk o' env == true) =
  assert (ring_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let ring (a b x: E.elem)
  : Lemma (E.fmul (E.fsub a b) x == E.fsub (E.fmul a x) (E.fmul b x) /\
           E.fmul (E.fadd a b) x == E.fadd (E.fmul a x) (E.fmul b x) /\
           E.fadd (E.fadd E.one a) (E.fsub E.one a) == 2)
  = let env = [fromf a; fromf b; fromf x] in
    ring_ok o env;
    let c = base m0 fl o 3 env in
    o_ok (); base_ok m0 fl o 3 env;
    envf3 c a b x;
    o_eqs (); m0_lem (); cst_lem ();
    let av = svar c 0 in
    let bv = svar c 1 in
    let xv = svar c 2 in
    kc_val c 1; kc_val c 2;
    sv_eq (smul (ssub av bv) xv) (ssub (smul av xv) (smul bv xv));
    sv_eq (smul (sadd av bv) xv) (sadd (smul av xv) (smul bv xv));
    sv_eq (sadd (sadd (kc c 1) av) (ssub (kc c 1) av)) (kc c 2)
#pop-options

(** Doubling is homogeneous of degree four. *)
let dbl_scale_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c = base m0 fl o' 3 env in
  let s = svar c 0 in
  let k = smul (smul s s) (smul s s) in
  let (a0, a1) = mdbl_sv (smul s (svar c 1)) (smul s (svar c 2)) in
  let (b0, b1) = mdbl_sv (svar c 1) (svar c 2) in
  Nil? (fst (ssub a0 (smul k b0))) &&
  Nil? (fst (ssub a1 (smul k b1)))

let dbl_scale_ok (o': fops m0) (env: list (elem m0)) : Lemma (dbl_scale_chk o' env == true) =
  assert (dbl_scale_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let dbl_scale (s x z: E.elem)
  : Lemma (let k = E.fmul (E.fmul s s) (E.fmul s s) in
           let (b0, b1) = mdbl (x, z) in
           mdbl (E.fmul s x, E.fmul s z) == (E.fmul k b0, E.fmul k b1))
  = let env = [fromf s; fromf x; fromf z] in
    dbl_scale_ok o env;
    let c = base m0 fl o 3 env in
    o_ok (); base_ok m0 fl o 3 env;
    envf3 c s x z;
    o_eqs (); m0_lem ();
    let sv0 = svar c 0 in
    let k = smul (smul sv0 sv0) (smul sv0 sv0) in
    let (a0, a1) = mdbl_sv (smul sv0 (svar c 1)) (smul sv0 (svar c 2)) in
    let (b0, b1) = mdbl_sv (svar c 1) (svar c 2) in
    mdbl_val c (smul sv0 (svar c 1)) (smul sv0 (svar c 2));
    mdbl_val c (svar c 1) (svar c 2);
    sv_eq a0 (smul k b0);
    sv_eq a1 (smul k b1)
#pop-options

(** [mcore] is bilinear: scaling the two inputs scales both outputs by
    the product. *)
let core_scale_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c = base m0 fl o' 6 env in
  let s = svar c 0 in
  let w = svar c 1 in
  let k = smul s w in
  let (a0, a1) = mcore_sv (smul s (svar c 2)) (smul s (svar c 3))
                          (smul w (svar c 4)) (smul w (svar c 5)) in
  let (b0, b1) = mcore_sv (svar c 2) (svar c 3) (svar c 4) (svar c 5) in
  Nil? (fst (ssub a0 (smul k b0))) &&
  Nil? (fst (ssub a1 (smul k b1)))

let core_scale_ok (o': fops m0) (env: list (elem m0)) : Lemma (core_scale_chk o' env == true) =
  assert (core_scale_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let core_scale (s w x2 z2 x3 z3: E.elem)
  : Lemma (let k = E.fmul s w in
           let (b0, b1) = mcore (x2, z2) (x3, z3) in
           mcore (E.fmul s x2, E.fmul s z2) (E.fmul w x3, E.fmul w z3) ==
           (E.fmul k b0, E.fmul k b1))
  = let env = [fromf s; fromf w; fromf x2; fromf z2; fromf x3; fromf z3] in
    core_scale_ok o env;
    let c = base m0 fl o 6 env in
    o_ok (); base_ok m0 fl o 6 env;
    envf6 c s w x2 z2 x3 z3;
    o_eqs (); m0_lem ();
    let sv0 = svar c 0 in
    let wv = svar c 1 in
    let k = smul sv0 wv in
    let (a0, a1) = mcore_sv (smul sv0 (svar c 2)) (smul sv0 (svar c 3))
                            (smul wv (svar c 4)) (smul wv (svar c 5)) in
    let (b0, b1) = mcore_sv (svar c 2) (svar c 3) (svar c 4) (svar c 5) in
    mcore_val c (smul sv0 (svar c 2)) (smul sv0 (svar c 3))
                (smul wv (svar c 4)) (smul wv (svar c 5));
    mcore_val c (svar c 2) (svar c 3) (svar c 4) (svar c 5);
    sv_eq a0 (smul k b0);
    sv_eq a1 (smul k b1)
#pop-options

(** The differential addition does not care which input is which: the
    difference changes sign and is squared. *)
let diff_sym_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c = base m0 fl o' 5 env in
  let (a0, a1) = mdiff_sv (svar c 0) (svar c 1) (svar c 2) (svar c 3) (svar c 4) in
  let (b0, b1) = mdiff_sv (svar c 0) (svar c 3) (svar c 4) (svar c 1) (svar c 2) in
  Nil? (fst (ssub a0 b0)) &&
  Nil? (fst (ssub a1 b1))

let diff_sym_ok (o': fops m0) (env: list (elem m0)) : Lemma (diff_sym_chk o' env == true) =
  assert (diff_sym_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let diff_sym (x1: E.elem) (p q: E.proj)
  : Lemma (mdiff x1 p q == mdiff x1 q p)
  = let (x2, z2) = p in
    let (x3, z3) = q in
    let env = [fromf x1; fromf x2; fromf z2; fromf x3; fromf z3] in
    diff_sym_ok o env;
    let c = base m0 fl o 5 env in
    o_ok (); base_ok m0 fl o 5 env;
    envf5 c x1 x2 z2 x3 z3;
    o_eqs (); m0_lem ();
    let (a0, a1) = mdiff_sv (svar c 0) (svar c 1) (svar c 2) (svar c 3) (svar c 4) in
    let (b0, b1) = mdiff_sv (svar c 0) (svar c 3) (svar c 4) (svar c 1) (svar c 2) in
    mdiff_val c (svar c 0) (svar c 1) (svar c 2) (svar c 3) (svar c 4);
    mdiff_val c (svar c 0) (svar c 3) (svar c 4) (svar c 1) (svar c 2);
    sv_eq a0 b0;
    sv_eq a1 b1
#pop-options

(** If [x z = 0] the doubling's [Z] is zero: its factor [E] is [4 x z]. *)
let dbl_zero_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c0 = base m0 fl o' 2 env in
  let hs = [(smul (svar c0 0) (svar c0 1), kc c0 0)] in
  let c = with_hyps c0 hs in
  let (_, a1) = mdbl_sv (svar c 0) (svar c 1) in
  shapes hs && Nil? (fst (ssub a1 (kc c 0)))

let dbl_zero_ok (o': fops m0) (env: list (elem m0)) : Lemma (dbl_zero_chk o' env == true) =
  assert (dbl_zero_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let dbl_zero (x z: E.elem)
  : Lemma (requires E.fmul x z == 0) (ensures snd (mdbl (x, z)) == 0)
  = let env = [fromf x; fromf z] in
    dbl_zero_ok o env;
    let c0 = base m0 fl o 2 env in
    o_ok (); o_eqs (); m0_lem (); cst_lem ();
    base_ok m0 fl o 2 env;
    envf2 c0 x z;
    let hs = [(smul (svar c0 0) (svar c0 1), kc c0 0)] in
    kc_val c0 0;
    holds1 (smul (svar c0 0) (svar c0 1), kc c0 0);
    hyps_ok c0 hs;
    let c = with_hyps c0 hs in
    envf2 c x z;
    let (_, a1) = mdbl_sv (svar c 0) (svar c 1) in
    mdbl_val c (svar c 0) (svar c 1);
    kc_val c 0;
    sv_eq a1 (kc c 0)
#pop-options

(** {2 The ladder's formulas on the curve} *)

(** Doubling.  The Edwards double of [(u, v)] has Montgomery coordinate
    proportional to [mdbl (1 + v, 1 - v)], and the first component of the
    latter is [16 v^2], which is what rules out the pair [(0, 0)]. *)
let dbl_aff_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c0 = base m0 fl o' 2 env in
  let hs = [aff_hyp c0 0 1] in
  let c = with_hyps c0 hs in
  let v = svar c 1 in
  let (x', z') = mdbl_sv (sadd (kc c 1) v) (ssub (kc c 1) v) in
  let (_, d1, d2, _) = point_double_sv (aff #c 0 1) in
  shapes hs &&
  Nil? (fst (ssub (smul x' (ssub d2 d1)) (smul z' (sadd d2 d1)))) &&
  Nil? (fst (ssub x' (smul (kc c 16) (smul v v))))

let dbl_aff_ok (o': fops m0) (env: list (elem m0)) : Lemma (dbl_aff_chk o' env == true) =
  assert (dbl_aff_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let dbl_aff_ctx (u v: E.elem)
  : Lemma (requires on u v)
          (ensures (let env = [fromf u; fromf v] in
                    let c0 = base m0 fl o 2 env in
                    let c = with_hyps c0 [aff_hyp c0 0 1] in
                    ok c /\ c.m == m0 /\ c.o == o /\ c.nv == 2 /\ c.env == env))
  = o_ok (); o_eqs ();
    let env = [fromf u; fromf v] in
    let c0 = base m0 fl o 2 env in
    base_ok m0 fl o 2 env;
    envf2 c0 u v;
    aff_hyp_ok c0 0 1;
    holds1 (aff_hyp c0 0 1);
    hyps_ok c0 [aff_hyp c0 0 1]

let dbl_aff (u v: E.elem)
  : Lemma (requires on u v)
          (ensures (let (x', z') = mdbl (E.fadd E.one v, E.fsub E.one v) in
                    let (_, d1, d2, _) = pdbl (cpt u v) in
                    E.fmul x' (E.fsub d2 d1) == E.fmul z' (E.fadd d2 d1) /\
                    x' == E.fmul (cst 16) (E.fmul v v)))
  = let env = [fromf u; fromf v] in
    dbl_aff_ok o env;
    let c0 = base m0 fl o 2 env in
    dbl_aff_ctx u v;
    let c = with_hyps c0 [aff_hyp c0 0 1] in
    envf2 c u v;
    o_eqs (); m0_lem (); cst_lem ();
    let vv = svar c 1 in
    let (x', z') = mdbl_sv (sadd (kc c 1) vv) (ssub (kc c 1) vv) in
    let (_, d1, d2, _) = point_double_sv (aff #c 0 1) in
    mdbl_val c (sadd (kc c 1) vv) (ssub (kc c 1) vv);
    aff_val c 0 1;
    point_double_val c (aff #c 0 1);
    kc_val c 1; kc_val c 16;
    sv_eq (smul x' (ssub d2 d1)) (smul z' (sadd d2 d1));
    sv_eq x' (smul (kc c 16) (smul vv vv))
#pop-options

(** Differential addition.  With [M = (um, vm)], [N = (un, vn)], [S = N + M]
    and [D = N - M], the ladder's [mcore (1 + vm, 1 - vm) (1 + vn, 1 - vn)]
    is [(P, Q)] with

      [(e2 - e1) P^2 (s2 - s1) = (e2 + e1) Q^2 (s2 + s1)]

    where [(e1 : e2)] and [(s1 : s2)] are the [Y : Z] of [D] and [S]: since
    [x1 = (e2 + e1)/(e2 - e1)], this is the ladder's output being
    proportional to [S]'s coordinate.  [P - Q = 8 vm] and [P + Q = 8 vn]
    locate the only place both can vanish. *)
let add_aff_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c0 = base m0 fl o' 4 env in
  let hs = [aff_hyp c0 0 1; aff_hyp c0 2 3] in
  let c = with_hyps c0 hs in
  let b = kc c d2l in
  let m = aff #c 0 1 in
  let n = aff #c 2 3 in
  let vm = svar c 1 in
  let vn = svar c 3 in
  let (p0, q0) = mcore_sv (sadd (kc c 1) vm) (ssub (kc c 1) vm)
                          (sadd (kc c 1) vn) (ssub (kc c 1) vn) in
  let (_, s1, s2, _) = point_add_sv b n m in
  let (_, e1, e2, _) = point_add_sv b n (sneg m) in
  shapes hs &&
  Nil? (fst (ssub (smul (smul (ssub e2 e1) (smul p0 p0)) (ssub s2 s1))
                  (smul (smul (sadd e2 e1) (smul q0 q0)) (sadd s2 s1)))) &&
  Nil? (fst (ssub (ssub p0 q0) (smul (kc c 8) vm))) &&
  Nil? (fst (ssub (sadd p0 q0) (smul (kc c 8) vn)))

let add_aff_ok (o': fops m0) (env: list (elem m0)) : Lemma (add_aff_chk o' env == true) =
  assert (add_aff_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let add_aff_ctx (u1 v1 u2 v2: E.elem)
  : Lemma (requires on u1 v1 /\ on u2 v2)
          (ensures (let env = [fromf u1; fromf v1; fromf u2; fromf v2] in
                    let c0 = base m0 fl o 4 env in
                    let c = with_hyps c0 [aff_hyp c0 0 1; aff_hyp c0 2 3] in
                    ok c /\ c.m == m0 /\ c.o == o /\ c.nv == 4 /\ c.env == env))
  = o_ok (); o_eqs ();
    let env = [fromf u1; fromf v1; fromf u2; fromf v2] in
    let c0 = base m0 fl o 4 env in
    base_ok m0 fl o 4 env;
    envf4 c0 u1 v1 u2 v2;
    aff_hyp_ok c0 0 1;
    aff_hyp_ok c0 2 3;
    holds2 (aff_hyp c0 0 1) (aff_hyp c0 2 3);
    hyps_ok c0 [aff_hyp c0 0 1; aff_hyp c0 2 3]

let add_aff (um vm un vn: E.elem)
  : Lemma (requires on um vm /\ on un vn)
          (ensures (let (p0, q0) = mcore (E.fadd E.one vm, E.fsub E.one vm)
                                         (E.fadd E.one vn, E.fsub E.one vn) in
                    let (_, s1, s2, _) = padd (cpt un vn) (cpt um vm) in
                    let (_, e1, e2, _) = padd (cpt un vn) (pneg (cpt um vm)) in
                    E.fmul (E.fmul (E.fsub e2 e1) (E.fmul p0 p0)) (E.fsub s2 s1) ==
                    E.fmul (E.fmul (E.fadd e2 e1) (E.fmul q0 q0)) (E.fadd s2 s1) /\
                    E.fsub p0 q0 == E.fmul (cst 8) vm /\
                    E.fadd p0 q0 == E.fmul (cst 8) vn))
  = let env = [fromf um; fromf vm; fromf un; fromf vn] in
    add_aff_ok o env;
    let c0 = base m0 fl o 4 env in
    add_aff_ctx um vm un vn;
    let c = with_hyps c0 [aff_hyp c0 0 1; aff_hyp c0 2 3] in
    envf4 c um vm un vn;
    o_eqs (); m0_lem (); d_lem (); cst_lem ();
    let b = kc c d2l in
    assert_norm (d2l % m0 == d2l);
    let m = aff #c 0 1 in
    let n = aff #c 2 3 in
    let vmv = svar c 1 in
    let vnv = svar c 3 in
    let (p0, q0) = mcore_sv (sadd (kc c 1) vmv) (ssub (kc c 1) vmv)
                            (sadd (kc c 1) vnv) (ssub (kc c 1) vnv) in
    let (_, s1, s2, _) = point_add_sv b n m in
    let (_, e1, e2, _) = point_add_sv b n (sneg m) in
    mcore_val c (sadd (kc c 1) vmv) (ssub (kc c 1) vmv)
                (sadd (kc c 1) vnv) (ssub (kc c 1) vnv);
    aff_val c 0 1;
    aff_val c 2 3;
    sneg_val c m;
    point_add_val c b n m;
    point_add_val c b n (sneg m);
    kc_val c 1; kc_val c 8;
    sv_eq (smul (smul (ssub e2 e1) (smul p0 p0)) (ssub s2 s1))
          (smul (smul (sadd e2 e1) (smul q0 q0)) (sadd s2 s1));
    sv_eq (ssub p0 q0) (smul (kc c 8) vmv);
    sv_eq (sadd p0 q0) (smul (kc c 8) vnv)
#pop-options

(** The degenerate case: if [vm = vn = 0] then [u^2 = -1] for both points,
    and the difference [D] has [e2^2 = e1^2], so [D] is the identity or the
    point of order two -- never an honest input to the ladder. *)
let degen_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c0 = base m0 fl o' 4 env in
  let hs = [(svar c0 1, kc c0 0); (smul (svar c0 0) (svar c0 0), kc c0 (m0 - 1));
            (svar c0 3, kc c0 0); (smul (svar c0 2) (svar c0 2), kc c0 (m0 - 1))] in
  let c = with_hyps c0 hs in
  let b = kc c d2l in
  let m = aff #c 0 1 in
  let n = aff #c 2 3 in
  let (_, e1, e2, _) = point_add_sv b n (sneg m) in
  shapes hs &&
  Nil? (fst (ssub (smul (ssub e2 e1) (sadd e2 e1)) (kc c 0)))

let degen_ok (o': fops m0) (env: list (elem m0)) : Lemma (degen_chk o' env == true) =
  assert (degen_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let degen (um un: E.elem)
  : Lemma (requires E.fmul um um == E.prime - 1 /\ E.fmul un un == E.prime - 1)
          (ensures (let (_, e1, e2, _) = padd (cpt un 0) (pneg (cpt um 0)) in
                    E.fmul (E.fsub e2 e1) (E.fadd e2 e1) == 0))
  = let env = [fromf um; fromf 0; fromf un; fromf 0] in
    degen_ok o env;
    let c0 = base m0 fl o 4 env in
    o_ok (); o_eqs (); m0_lem (); d_lem (); cst_lem ();
    base_ok m0 fl o 4 env;
    envf4 c0 um 0 un 0;
    let h1 = (svar c0 1, kc c0 0) in
    let h2 = (smul (svar c0 0) (svar c0 0), kc c0 (m0 - 1)) in
    let h3 = (svar c0 3, kc c0 0) in
    let h4 = (smul (svar c0 2) (svar c0 2), kc c0 (m0 - 1)) in
    kc_val c0 0; kc_val c0 (m0 - 1);
    assert_norm ((m0 - 1) % m0 == m0 - 1);
    holds4 h1 h2 h3 h4;
    hyps_ok c0 [h1; h2; h3; h4];
    let c = with_hyps c0 [h1; h2; h3; h4] in
    envf4 c um 0 un 0;
    let b = kc c d2l in
    assert_norm (d2l % m0 == d2l);
    let m = aff #c 0 1 in
    let n = aff #c 2 3 in
    let (_, e1, e2, _) = point_add_sv b n (sneg m) in
    aff_val c 0 1;
    aff_val c 2 3;
    sneg_val c m;
    point_add_val c b n (sneg m);
    kc_val c 0;
    sv_eq (smul (ssub e2 e1) (sadd e2 e1)) (kc c 0)
#pop-options

(** {2 The points with [y = +-z]}

    These are the identity and the point of order two, and the ladder
    encodes both as zero.  On the curve, [y^2 = z^2] forces [x = 0]: the
    equation becomes [-(1 + d) x^2 z^2 = 0]. *)
let tors_x_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c0 = base m0 fl o' 4 env in
  let hs = [(smul (svar c0 1) (svar c0 1), smul (svar c0 2) (svar c0 2))] in
  let c = with_hyps c0 hs in
  let p = var4 #c 0 1 2 3 in
  let x = svar c 0 in
  let z = svar c 2 in
  shapes hs &&
  Nil? (fst (ssub (ssub (hl_sv p) (hr_sv p))
                  (smul (kc c (m0 - 1 - dl)) (smul (smul x x) (smul z z)))))

let tors_x_ok (o': fops m0) (env: list (elem m0)) : Lemma (tors_x_chk o' env == true) =
  assert (tors_x_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let tors_x (x y z t: E.elem)
  : Lemma (requires E.fmul y y == E.fmul z z)
          (ensures E.fsub (hl (x, y, z, t)) (hr (x, y, z, t)) ==
                   E.fmul (cst (m0 - 1 - dl)) (E.fmul (E.fmul x x) (E.fmul z z)))
  = let env = [fromf x; fromf y; fromf z; fromf t] in
    tors_x_ok o env;
    let c0 = base m0 fl o 4 env in
    o_ok (); o_eqs (); m0_lem (); d_lem (); cst_lem ();
    base_ok m0 fl o 4 env;
    envf4 c0 x y z t;
    let h = (smul (svar c0 1) (svar c0 1), smul (svar c0 2) (svar c0 2)) in
    holds1 h;
    hyps_ok c0 [h];
    let c = with_hyps c0 [h] in
    envf4 c x y z t;
    let p = var4 #c 0 1 2 3 in
    var4_val c 0 1 2 3;
    eqn_val c p;
    kc_val c (m0 - 1 - dl);
    let xv = svar c 0 in
    let zv = svar c 2 in
    sv_eq (ssub (hl_sv p) (hr_sv p))
          (smul (kc c (m0 - 1 - dl)) (smul (smul xv xv) (smul zv zv)))
#pop-options

(** And then the double of [(0, y, z, _)] has [x = 0] and [y = z]: it is the
    identity. *)
let tors_dbl_chk (o': fops m0) (env: list (elem m0)) : bool =
  let c0 = base m0 fl o' 4 env in
  let hs = [(svar c0 0, kc c0 0); (smul (svar c0 1) (svar c0 1), smul (svar c0 2) (svar c0 2))] in
  let c = with_hyps c0 hs in
  let (d0, d1, d2, _) = point_double_sv (var4 #c 0 1 2 3) in
  shapes hs &&
  Nil? (fst (ssub d0 (kc c 0))) &&
  Nil? (fst (ssub d1 d2))

let tors_dbl_ok (o': fops m0) (env: list (elem m0)) : Lemma (tors_dbl_chk o' env == true) =
  assert (tors_dbl_chk o' env == true) by (poly_tac ())

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let tors_dbl (y z t: E.elem)
  : Lemma (requires E.fmul y y == E.fmul z z)
          (ensures (let (d0, d1, d2, _) = pdbl (0, y, z, t) in d0 == 0 /\ d1 == d2))
  = let env = [fromf 0; fromf y; fromf z; fromf t] in
    tors_dbl_ok o env;
    let c0 = base m0 fl o 4 env in
    o_ok (); o_eqs (); m0_lem (); cst_lem ();
    base_ok m0 fl o 4 env;
    envf4 c0 0 y z t;
    let h1 = (svar c0 0, kc c0 0) in
    let h2 = (smul (svar c0 1) (svar c0 1), smul (svar c0 2) (svar c0 2)) in
    kc_val c0 0;
    holds2 h1 h2;
    hyps_ok c0 [h1; h2];
    let c = with_hyps c0 [h1; h2] in
    envf4 c 0 y z t;
    let (d0, d1, d2, _) = point_double_sv (var4 #c 0 1 2 3) in
    var4_val c 0 1 2 3;
    point_double_val c (var4 #c 0 1 2 3);
    kc_val c 0;
    sv_eq d0 (kc c 0);
    sv_eq d1 d2
#pop-options
