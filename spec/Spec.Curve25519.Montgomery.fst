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

(** The X25519 ladder computes a scalar multiple.

    Curve25519 and Edwards25519 are birationally equivalent by
    [u = (1 + y) / (1 - y)], and the X25519 base point [9] is the image of
    the Ed25519 base point [g].  So rather than build the Montgomery group
    this module reads the ladder of {!Spec.Curve25519} against the Edwards
    group of {!Spec.Ed25519.Group}, whose laws are already proved: for an
    Edwards point [P] with affine [y]-coordinate [v = yv P], a ladder pair
    [(X, Z)] {e represents} [P] ([mrep]) when it is a nonzero multiple of
    [(1 + v, 1 - v)].  Its encoding [X / Z] is then [ucoord P], the [u]
    coordinate of the image of [P] -- including the identity and the point
    of order two, where [1 - v = 0] and the encoding is [X * 0^(p-2) = 0].

    {2 Proof outline}

    - The two halves of a ladder step preserve representation
      ({!dbl_step}, {!diff_step}).  Both reduce, by homogeneity, to the
      affine identities of {!Spec.Curve25519.MontChecks}; the work here is
      clearing denominators and ruling out the pair [(0, 0)].  The
      differential addition needs the [u] coordinate of the difference to
      be nonzero, which excludes exactly the two points with [v = +-1].
    - After [i] rungs the ladder holds representatives of [n P] and
      [(n + 1) P], [n] the top [i] bits of the scalar ({!ladder_inv}), so
      the encoded result is [ucoord (k P)] ({!ladder_ucoord}).
    - If [ucoord P = 0] the ladder degenerates: every pair has [X Z = 0]
      and the output is [0].  Such a [P] has [2 P = 0], so for an even
      scalar -- every clamped one -- [ucoord (k P) = 0] too.  The headline
      lemma {!ladder_smul} therefore holds for every point on the curve and
      every even scalar, with no case split left for the caller. *)
module Spec.Curve25519.Montgomery

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

module M = FStar.Math.Lemmas
module MA = Spec.ModArith
module F = Spec.Group.Field
module S = Spec.Ed25519.GroupSv
module K = Spec.Ed25519.GroupChecks
module MC = Spec.Curve25519.MontChecks
module Gr = Spec.Ed25519.Group
module Sm = Spec.Ed25519.Smul
module G = Spec.Group.Smul
module B = Hacl.Spec.Bytes
module Loops = Hacl.Spec.Loops
module S8 = Hacl.Secret.UInt8
module Seq = FStar.Seq

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40 --smtencoding.nl_arith_repr wrapped"

(** {2 Field facts}

    Restated from {!Spec.Ed25519.Group}, whose interface does not export
    them. *)

let prime_lem () : Lemma (FStar.Math.Euclid.is_prime prime) = S.m0_lem (); S.prime_m0 ()

let pm : (m: pos { 1 < m }) = prime_gt_one (); prime

#push-options "--fuel 1"
let rec fexp_exp (x: elem) (n: nat)
  : Lemma (ensures fexp x n == MA.exp #pm x n) (decreases n)
  = if n = 0 then () else fexp_exp x (n - 1)

let fexp_zero_pos (n: pos) : Lemma (fexp 0 n == 0) = ()
#pop-options

let finv_zero () : Lemma (finv 0 == 0) =
  prime_gt_one ();
  assert_norm (prime > 2);
  fexp_zero_pos (prime - 2)

let finv_inv (x: elem) : Lemma (finv x == MA.inv #pm x) = prime_gt_one (); fexp_exp x (pm - 2)

let mul_finv (z: elem) : Lemma (requires z <> 0) (ensures fmul z (finv z) == one) =
  prime_lem (); finv_inv z; F.mul_inv #prime z

let div_mul (x z: elem) : Lemma (requires z <> 0) (ensures fmul (fmul x (finv z)) z == x) =
  prime_lem (); finv_inv z; F.div_mul #prime x z

let mul_nz (x y: elem) : Lemma (requires x <> 0 /\ y <> 0) (ensures fmul x y <> 0) =
  prime_lem (); F.mul_nonzero #prime x y

let no_zero_div (x y: elem) : Lemma (requires fmul x y == 0) (ensures x == 0 \/ y == 0) =
  prime_lem (); F.no_zero_div #prime x y

let cancel (a b c: elem) : Lemma (requires c <> 0 /\ fmul a c == fmul b c) (ensures a == b) =
  prime_lem (); F.cancel #prime a b c

let mul4 (a b c d: elem) : Lemma (fmul (fmul a b) (fmul c d) == fmul (fmul a c) (fmul b d)) =
  F.mul4 #prime a b c d

let mul_one (x: elem) : Lemma (fmul x one == x /\ fmul one x == x) =
  fmul_one x; fmul_comm one x

let fmul_zero (x: elem) : Lemma (fmul x 0 == 0 /\ fmul 0 x == 0) =
  M.mul_zero_right_is_zero x; M.mul_zero_left_is_zero x; M.small_mod 0 prime

let fadd_sub_zero (x: elem) : Lemma (fadd x 0 == x /\ fsub x 0 == x) =
  M.small_mod x prime; M.lemma_mod_plus x 1 prime

let finv_one () : Lemma (finv one == one) = mul_finv one; mul_one (finv one)

let div_eq (a b c d: elem)
  : Lemma (requires b <> 0 /\ d <> 0 /\ fmul a d == fmul c b)
          (ensures fmul a (finv b) == fmul c (finv d))
  = prime_lem (); finv_inv b; finv_inv d; Spec.Group.Proj.div_eq #prime a b c d

let add_zero (a: elem) : Lemma (requires fadd one a == 0) (ensures a == prime - 1) =
  if a + 1 < prime then M.small_mod (a + 1) prime

(** [x (y z) = (x y) z = (x z) y], the two rearrangements used below. *)
let mul3 (x y z: elem)
  : Lemma (fmul x (fmul y z) == fmul (fmul x y) z /\ fmul (fmul x y) z == fmul (fmul x z) y)
  = fmul_assoc x y z; fmul_comm y z; fmul_assoc x z y

(** {2 Edwards points, restated} *)

let oc (p: ext_point) : Lemma (on_curve p <==> S.onc p) =
  FStar.Pervasives.reveal_opaque (`%S.onc) S.onc;
  FStar.Pervasives.reveal_opaque (`%S.hl) S.hl;
  FStar.Pervasives.reveal_opaque (`%S.hr) S.hr

let onc_parts (p: ext_point)
  : Lemma (S.onc p <==> (let (x, y, z, t) = p in z <> 0 /\ fmul x y == fmul z t /\ S.hl p == S.hr p))
  = FStar.Pervasives.reveal_opaque (`%S.onc) S.onc

let sc_parts (k: elem) (p: ext_point)
  : Lemma (let (x, y, z, t) = p in S.sc k p == (fmul k x, fmul k y, fmul k z, fmul k t))
  = FStar.Pervasives.reveal_opaque (`%S.sc) S.sc

let cpt_parts (u v: elem) : Lemma (S.cpt u v == (u, v, one, fmul u v)) =
  FStar.Pervasives.reveal_opaque (`%S.cpt) S.cpt

let pneg_eq (p: ext_point) : Lemma (S.pneg p == point_negate p) =
  FStar.Pervasives.reveal_opaque (`%S.pneg) S.pneg

let padd_eq (p q: ext_point) : Lemma (S.padd p q == point_add p q) =
  FStar.Pervasives.reveal_opaque (`%S.padd) S.padd

let pdbl_eq (p: ext_point) : Lemma (S.pdbl p == point_double p) =
  FStar.Pervasives.reveal_opaque (`%S.pdbl) S.pdbl

let z_nz (p: ext_point) : Lemma (requires on_curve p) (ensures (let (_, _, z, _) = p in z <> 0)) =
  oc p; onc_parts p

let ak (p: ext_point) : elem & elem =
  let (x, y, z, _) = p in (fmul x (finv z), fmul y (finv z))

let onc_cpt (u v: elem) : Lemma (requires S.on u v) (ensures on_curve (S.cpt u v)) =
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  onc_parts (S.cpt u v); cpt_parts u v; mul_one (fmul u v); oc (S.cpt u v)

(** Every point is [Z] times its canonical point. *)
let decomp (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures (let (u, v) = ak p in let (_, _, z, _) = p in
                    z <> 0 /\ p == S.sc z (S.cpt u v) /\ S.on u v))
  = let (x, y, z, t) = p in
    oc p; onc_parts p;
    let zi = finv z in
    let u = fmul x zi in
    let v = fmul y zi in
    div_mul x z; fmul_comm u z;
    div_mul y z; fmul_comm v z;
    mul_one z;
    mul_finv z;
    calc (==) {
      fmul z (fmul u v);
      == { mul4 x zi y zi }
      fmul z (fmul (fmul x y) (fmul zi zi));
      == { fmul_comm z t }
      fmul z (fmul (fmul t z) (fmul zi zi));
      == { mul4 t z zi zi }
      fmul z (fmul (fmul t zi) (fmul z zi));
      == { mul_one (fmul t zi) }
      fmul z (fmul t zi);
      == { fmul_comm z (fmul t zi); div_mul t z }
      t;
    };
    cpt_parts u v; sc_parts z (S.cpt u v);
    let c = S.cpt u v in
    assert (p == S.sc z c);
    K.scale_eqs z u v one (fmul u v);
    let z2 = fmul z z in
    mul_nz z z; mul_nz z2 z2;
    cancel (S.hl c) (S.hr c) (fmul z2 z2);
    FStar.Pervasives.reveal_opaque (`%S.on) S.on

(** {2 The [u] coordinate} *)

(** The affine Edwards [y]. *)
let yv (p: ext_point) : elem = let (_, y, z, _) = p in fmul y (finv z)

(** [u = (1 + v) / (1 - v)], with [u = 0] when [v = 1]. *)
let uenc (v: elem) : elem = fmul (fadd one v) (finv (fsub one v))

[@@"opaque_to_smt"]
let ucoord (p: ext_point) : elem = uenc (yv p)

(** A ladder pair stands for [v] when it is a nonzero multiple of
    [(1 + v, 1 - v)]: cross-multiplied, and not [(0, 0)]. *)
let mrepv (q: proj) (v: elem) : prop =
  let (x, z) = q in ~(x == 0 /\ z == 0) /\ fmul x (fsub one v) == fmul z (fadd one v)

(** Both are kept from the solver, whose arithmetic otherwise drowns in
    the field's nonlinear definitions whenever one is in context. *)
[@@"opaque_to_smt"]
let mrep (q: proj) (p: ext_point) : prop = mrepv q (yv p)

let ucoord_def (p: ext_point) : Lemma (ucoord p == uenc (yv p)) =
  FStar.Pervasives.reveal_opaque (`%ucoord) ucoord

let mrep_def (q: proj) (p: ext_point) : Lemma (mrep q p <==> mrepv q (yv p)) =
  FStar.Pervasives.reveal_opaque (`%mrep) mrep

let yv_ak (p: ext_point) : Lemma (snd (ak p) == yv p) = ()

let yv_eq (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal p q) (ensures yv p == yv q)
  = z_nz p; z_nz q;
    let (_, y1, z1, _) = p in
    let (_, y2, z2, _) = q in
    div_eq y1 z1 y2 z2

let yv_scale (k: elem) (p: ext_point)
  : Lemma (requires (let (_, _, z, _) = p in k <> 0 /\ z <> 0)) (ensures yv (S.sc k p) == yv p)
  = let (_, y, z, _) = p in
    sc_parts k p;
    mul_nz k z;
    fmul_assoc k y z; fmul_comm y z; fmul_assoc k z y; fmul_comm (fmul k z) y;
    div_eq (fmul k y) (fmul k z) y z

let two_nz (v: elem) : Lemma (fadd one v <> 0 \/ fsub one v <> 0) =
  MC.ring v v v

(** The encoding of a representative is the [u] coordinate. *)
let enc_rep (x z v: elem)
  : Lemma (requires mrepv (x, z) v) (ensures fmul x (finv z) == uenc v)
  = finv_zero ();
    two_nz v;
    if z = 0 then no_zero_div x (fsub one v)
    else begin
      if fsub one v = 0 then no_zero_div z (fadd one v)
      else (fmul_comm (fadd one v) z; div_eq x z (fadd one v) (fsub one v))
    end

let mk (mu v: elem) : proj = (fmul mu (fadd one v), fmul mu (fsub one v))

let mu_of (q: proj) (v: elem) : elem =
  let (x, z) = q in
  if fsub one v <> 0 then fmul z (finv (fsub one v)) else fmul x (finv (fadd one v))

let extract (q: proj) (v: elem)
  : Lemma (requires mrepv q v) (ensures mu_of q v <> 0 /\ q == mk (mu_of q v) v)
  = let (x, z) = q in
    let a = fadd one v in
    let b = fsub one v in
    let mu = mu_of q v in
    two_nz v;
    if b <> 0 then begin
      div_mul z b;
      mul3 mu a b;
      fmul_comm (fmul mu b) a;
      fmul_comm z a;
      cancel x (fmul mu a) b
    end else begin
      div_mul x a;
      no_zero_div z a
    end

let mk_rep (mu v: elem) : Lemma (requires mu <> 0) (ensures mrepv (mk mu v) v) =
  two_nz v;
  mul3 mu (fadd one v) (fsub one v);
  mul3 mu (fsub one v) (fadd one v);
  fmul_comm (fadd one v) (fsub one v);
  if fadd one v <> 0 then mul_nz mu (fadd one v) else mul_nz mu (fsub one v)

let rep_scale (a b v k: elem)
  : Lemma (requires mrepv (a, b) v /\ k <> 0) (ensures mrepv (fmul k a, fmul k b) v)
  = mul3 k a (fsub one v); mul3 k b (fadd one v);
    fmul_assoc k a (fsub one v); fmul_assoc k b (fadd one v);
    if a <> 0 then mul_nz k a else mul_nz k b

(** The projective pair of [y / z] is [(z + y, z - y)]. *)
let frac_rep (a b d1 d2: elem)
  : Lemma (requires d2 <> 0 /\ ~(a == 0 /\ b == 0) /\
                    fmul a (fsub d2 d1) == fmul b (fadd d2 d1))
          (ensures mrepv (a, b) (fmul d1 (finv d2)))
  = let w = fmul d1 (finv d2) in
    div_mul d1 d2;
    MC.ring one w d2;
    mul_one d2;
    fmul_assoc a (fsub one w) d2;
    fmul_assoc b (fadd one w) d2;
    cancel (fmul a (fsub one w)) (fmul b (fadd one w)) d2

(** {2 Doubling} *)

let dbl_aff_rep (u v: elem)
  : Lemma (requires S.on u v)
          (ensures on_curve (S.pdbl (S.cpt u v)) /\
                   mrepv (MC.mdbl (fadd one v, fsub one v)) (yv (S.pdbl (S.cpt u v))))
  = let c = S.cpt u v in
    onc_cpt u v;
    Gr.point_double_on_curve c; pdbl_eq c;
    z_nz (S.pdbl c);
    let (_, d1, d2, _) = S.pdbl c in
    MC.dbl_aff u v;
    let (x', z') = MC.mdbl (fadd one v, fsub one v) in
    if v = 0 then begin
      fadd_sub_zero one;
      assert (fadd one v == 1 /\ fsub one v == 1);
      assert_norm (snd (MC.mdbl (1, 1)) <> 0)
    end else begin
      S.m0_lem ();
      S.cst_small 16;
      assert_norm (16 < prime);
      mul_nz v v;
      mul_nz 16 (fmul v v)
    end;
    frac_rep x' z' d1 d2

let dbl_step (p: ext_point) (q: proj)
  : Lemma (requires on_curve p /\ mrep q p)
          (ensures mrep (MC.mdbl q) (point_double p))
  = mrep_def q p; mrep_def (MC.mdbl q) (point_double p);
    decomp p;
    let (u, v) = ak p in
    let (_, _, z, _) = p in
    let c = S.cpt u v in
    let mu = mu_of q v in
    extract q v;
    MC.dbl_scale mu (fadd one v) (fsub one v);
    let k = fmul (fmul mu mu) (fmul mu mu) in
    mul_nz mu mu; mul_nz (fmul mu mu) (fmul mu mu);
    dbl_aff_rep u v;
    let (x', z') = MC.mdbl (fadd one v, fsub one v) in
    rep_scale x' z' (yv (S.pdbl c)) k;
    cpt_parts u v;
    K.dbl_scale z u v one (fmul u v);
    pdbl_eq p;
    let z4 = fmul (fmul z z) (fmul z z) in
    mul_nz z z; mul_nz (fmul z z) (fmul z z);
    z_nz (S.pdbl c);
    yv_scale z4 (S.pdbl c)

(** {2 Differential addition} *)

(** [x1 = u(D)] for [D] with affine [y = e1 / e2]: then [x1 (e2 - e1) =
    e2 + e1], and [x1 <> 0] keeps [e2 - e1] away from zero. *)
let x1_rel (e1 e2 x1: elem)
  : Lemma (requires e2 <> 0 /\ x1 == uenc (fmul e1 (finv e2)) /\ x1 <> 0)
          (ensures fsub e2 e1 <> 0 /\ fmul x1 (fsub e2 e1) == fadd e2 e1)
  = let w = fmul e1 (finv e2) in
    finv_zero ();
    div_mul e1 e2;
    MC.ring one w e2;
    mul_one e2;
    assert (fsub one w <> 0);
    mul_nz (fsub one w) e2;
    div_mul (fadd one w) (fsub one w);
    fmul_assoc x1 (fsub one w) e2

(** On the curve, [v = 0] forces [u^2 = -1]. *)
let on_v0 (u: elem) : Lemma (requires S.on u 0) (ensures fmul u u == prime - 1) =
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  FStar.Pervasives.reveal_opaque (`%S.hl) S.hl;
  FStar.Pervasives.reveal_opaque (`%S.hr) S.hr;
  cpt_parts u 0;
  mul_one one; mul_one (fmul u u);
  let uu = fmul u u in
  fmul_zero 0; fmul_zero uu; fmul_zero d;
  mul_one (fsub 0 uu);
  fadd_sub_zero one;
  assert (fadd one 0 == one);
  assert (S.hr (S.cpt u 0) == one);
  assert (S.hl (S.cpt u 0) == fsub 0 uu);
  assert (fsub 0 uu == one);
  if uu = 0 then assert (fsub 0 uu == 0)
  else M.small_mod (prime - uu) prime

let cst8 () : Lemma (S.cst 8 == 8 /\ 8 <> 0) =
  S.m0_lem (); assert_norm (8 < prime); S.cst_small 8

(** The differential addition never produces [(0, 0)]: that would need
    [vm = vn = 0], and then the difference is the identity or the point of
    order two, whose [u] coordinate is zero. *)
let diff_nz_v0 (um un x1: elem)
  : Lemma (requires S.on um 0 /\ S.on un 0 /\ x1 <> 0 /\
                    (let (_, e1, e2, _) = S.padd (S.cpt un 0) (S.pneg (S.cpt um 0)) in
                     fmul x1 (fsub e2 e1) == fadd e2 e1 /\ fsub e2 e1 <> 0))
          (ensures False)
  = let (_, e1, e2, _) = S.padd (S.cpt un 0) (S.pneg (S.cpt um 0)) in
    on_v0 um; on_v0 un;
    MC.degen um un;
    no_zero_div (fsub e2 e1) (fadd e2 e1);
    no_zero_div x1 (fsub e2 e1)

let diff_nz (um vm un vn x1: elem)
  : Lemma (requires S.on um vm /\ S.on un vn /\ x1 <> 0 /\
                    (let (_, e1, e2, _) = S.padd (S.cpt un vn) (S.pneg (S.cpt um vm)) in
                     fmul x1 (fsub e2 e1) == fadd e2 e1 /\ fsub e2 e1 <> 0))
          (ensures (let (p0, q0) = MC.mcore (fadd one vm, fsub one vm) (fadd one vn, fsub one vn) in
                    ~(fmul p0 p0 == 0 /\ fmul x1 (fmul q0 q0) == 0)))
  = let (p0, q0) = MC.mcore (fadd one vm, fsub one vm) (fadd one vn, fsub one vn) in
    if fmul p0 p0 = 0 && fmul x1 (fmul q0 q0) = 0 then begin
      no_zero_div p0 p0;
      no_zero_div x1 (fmul q0 q0);
      no_zero_div q0 q0;
      MC.add_aff um vm un vn;
      cst8 ();
      assert (fsub p0 q0 == 0 /\ fadd p0 q0 == 0);
      no_zero_div 8 vm;
      no_zero_div 8 vn;
      diff_nz_v0 um un x1
    end

let diff_aff_rep (um vm un vn x1: elem)
  : Lemma (requires S.on um vm /\ S.on un vn /\ x1 <> 0 /\
                    x1 == uenc (yv (S.padd (S.cpt un vn) (S.pneg (S.cpt um vm)))))
          (ensures mrepv (MC.mdiff x1 (fadd one vm, fsub one vm) (fadd one vn, fsub one vn))
                         (yv (S.padd (S.cpt un vn) (S.cpt um vm))))
  = let cm = S.cpt um vm in
    let cn = S.cpt un vn in
    onc_cpt um vm; onc_cpt un vn;
    point_negate_on_curve cm; pneg_eq cm;
    point_add_on_curve cn cm; padd_eq cn cm;
    point_add_on_curve cn (S.pneg cm); padd_eq cn (S.pneg cm);
    z_nz (S.padd cn cm); z_nz (S.padd cn (S.pneg cm));
    let (_, s1, s2, _) = S.padd cn cm in
    let (_, e1, e2, _) = S.padd cn (S.pneg cm) in
    x1_rel e1 e2 x1;
    MC.add_aff um vm un vn;
    let (p0, q0) = MC.mcore (fadd one vm, fsub one vm) (fadd one vn, fsub one vn) in
    let a = fmul p0 p0 in
    let b = fmul x1 (fmul q0 q0) in
    let de = fsub e2 e1 in
    (* (e2 - e1) a (s2 - s1) = (e2 + e1) q0^2 (s2 + s1) = (e2 - e1) b (s2 + s1) *)
    fmul_assoc de a (fsub s2 s1);
    mul3 x1 de (fmul q0 q0);
    fmul_comm x1 de;
    fmul_assoc de b (fadd s2 s1);
    fmul_comm de (fmul a (fsub s2 s1));
    fmul_comm de (fmul b (fadd s2 s1));
    cancel (fmul a (fsub s2 s1)) (fmul b (fadd s2 s1)) de;
    diff_nz um vm un vn x1;
    frac_rep a b s1 s2

(** [mdiff] is homogeneous of degree two in each input. *)
let mdiff_scale (x1 s w x2 z2 x3 z3: elem)
  : Lemma (let k = fmul (fmul s w) (fmul s w) in
           let (b0, b1) = MC.mdiff x1 (x2, z2) (x3, z3) in
           MC.mdiff x1 (fmul s x2, fmul s z2) (fmul w x3, fmul w z3) == (fmul k b0, fmul k b1))
  = MC.core_scale s w x2 z2 x3 z3;
    let sw = fmul s w in
    let (p0, q0) = MC.mcore (x2, z2) (x3, z3) in
    mul4 sw p0 sw p0;
    mul4 sw q0 sw q0;
    mul3 x1 (fmul sw sw) (fmul q0 q0);
    fmul_comm x1 (fmul sw sw);
    fmul_assoc (fmul sw sw) x1 (fmul q0 q0)

let diff_step (pm pn pp: ext_point) (x1: elem) (qm qn: proj)
  : Lemma (requires on_curve pm /\ on_curve pn /\ on_curve pp /\
                    mrep qm pm /\ mrep qn pn /\
                    point_equal (point_add pn (point_negate pm)) pp /\
                    x1 == ucoord pp /\ x1 <> 0)
          (ensures mrep (MC.mdiff x1 qm qn) (point_add pn pm))
  = mrep_def qm pm; mrep_def qn pn; mrep_def (MC.mdiff x1 qm qn) (point_add pn pm);
    ucoord_def pp;
    decomp pm; decomp pn;
    let (um, vm) = ak pm in
    let (un, vn) = ak pn in
    let (_, _, zm, _) = pm in
    let (_, _, zn, _) = pn in
    let cm = S.cpt um vm in
    let cn = S.cpt un vn in
    let mum = mu_of qm vm in
    let mun = mu_of qn vn in
    extract qm vm; extract qn vn;
    mdiff_scale x1 mum mun (fadd one vm) (fsub one vm) (fadd one vn) (fsub one vn);
    let k = fmul (fmul mum mun) (fmul mum mun) in
    mul_nz mum mun; mul_nz (fmul mum mun) (fmul mum mun);
    (* The Edwards side, scaled out. *)
    cpt_parts um vm; cpt_parts un vn;
    K.add_scale zn zm un vn one (fmul un vn) um vm one (fmul um vm);
    padd_eq pn pm;
    K.neg_scale zm um vm one (fmul um vm);
    pneg_eq pm; pneg_eq cm;
    let ncm = S.pneg cm in
    let (nx, ny, nz, nt) = ncm in
    sc_parts zm ncm;
    K.add_scale zn zm un vn one (fmul un vn) nx ny nz nt;
    padd_eq pn (point_negate pm);
    let kz = fmul (fmul zn zm) (fmul zn zm) in
    mul_nz zn zm; mul_nz (fmul zn zm) (fmul zn zm);
    onc_cpt um vm; onc_cpt un vn;
    point_negate_on_curve cm;
    point_add_on_curve cn cm; padd_eq cn cm;
    point_add_on_curve cn ncm; padd_eq cn ncm;
    z_nz (S.padd cn cm); z_nz (S.padd cn ncm);
    yv_scale kz (S.padd cn cm);
    yv_scale kz (S.padd cn ncm);
    point_negate_on_curve pm;
    point_add_on_curve pn (point_negate pm);
    yv_eq (point_add pn (point_negate pm)) pp;
    diff_aff_rep um vm un vn x1;
    let (b0, b1) = MC.mdiff x1 (fadd one vm, fsub one vm) (fadd one vn, fsub one vn) in
    rep_scale b0 b1 (yv (S.padd cn cm)) k

(** {2 Group facts} *)

let mrep_congr (q: proj) (p p': ext_point)
  : Lemma (requires on_curve p /\ on_curve p' /\ point_equal p p' /\ mrep q p)
          (ensures mrep q p')
  = mrep_def q p; mrep_def q p'; yv_eq p p'

let trans4 (p q r s: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r /\ on_curve s /\
                    point_equal p q /\ point_equal q r /\ point_equal r s)
          (ensures point_equal p s)
  = point_equal_trans p q r; point_equal_trans p r s

(** [P + Q - Q = P]. *)
let add_sub (p a: ext_point)
  : Lemma (requires on_curve p /\ on_curve a)
          (ensures on_curve (point_add (point_add p a) (point_negate a)) /\
                   point_equal (point_add (point_add p a) (point_negate a)) p)
  = let na = point_negate a in
    let o = point_at_infinity in
    point_negate_on_curve a;
    point_at_infinity_on_curve ();
    point_add_on_curve p a;
    point_add_on_curve (point_add p a) na;
    point_add_on_curve a na;
    point_add_on_curve na a;
    point_add_on_curve p (point_add a na);
    point_add_on_curve p o;
    point_add_on_curve o p;
    point_add_assoc_law p a na;
    point_add_comm_law a na;
    point_add_negate a;
    point_equal_trans (point_add a na) (point_add na a) o;
    point_equal_refl p;
    point_add_congr p p (point_add a na) o;
    point_add_comm_law p o;
    point_add_identity p;
    trans4 (point_add (point_add p a) na) (point_add p (point_add a na)) (point_add p o)
           (point_add o p);
    point_equal_trans (point_add (point_add p a) na) (point_add o p) p

(** [(n + 1) P - n P = P]: the invariant difference of the ladder. *)
let sub_succ (n: nat) (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures on_curve (point_add (Sm.smul (n + 1) p) (point_negate (Sm.smul n p))) /\
                   point_equal (point_add (Sm.smul (n + 1) p) (point_negate (Sm.smul n p))) p)
  = let a = Sm.smul n p in
    let b = Sm.smul (n + 1) p in
    let na = point_negate a in
    Sm.smul_ok n p; Sm.smul_ok (n + 1) p;
    point_negate_on_curve a;
    point_equal_refl a;
    Sm.smul_succ_congr n p a;
    point_add_on_curve a p;
    point_add_on_curve p a;
    point_equal_sym (point_add a p) b;
    point_add_comm_law a p;
    point_equal_trans b (point_add a p) (point_add p a);
    point_equal_refl na;
    point_add_congr b (point_add p a) na na;
    point_add_on_curve b na;
    add_sub p a;
    point_equal_trans (point_add b na) (point_add (point_add p a) na) p

(** {2 The ladder} *)

(** The ladder state for the multiple [n]. *)
[@@"opaque_to_smt"]
let inv_n (p: ext_point) (n: nat) (st: proj & proj) : prop =
  mrep (fst st) (Sm.smul n p) /\ mrep (snd st) (Sm.smul (n + 1) p)

let inv_n_def (p: ext_point) (n: nat) (st: proj & proj)
  : Lemma (inv_n p n st <==> mrep (fst st) (Sm.smul n p) /\ mrep (snd st) (Sm.smul (n + 1) p)) =
  FStar.Pervasives.reveal_opaque (`%inv_n) inv_n

let inv_at (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat { i <= 256 }) (st: proj & proj) : prop =
  inv_n p (B.le_nat k / pow2 (256 - i)) st

(** The two multiples a rung produces. *)
let rung_dbl (p: ext_point) (n: nat) (a: proj)
  : Lemma (requires on_curve p /\ mrep a (Sm.smul n p))
          (ensures mrep (MC.mdbl a) (Sm.smul (2 * n) p))
  = let pa = Sm.smul n p in
    Sm.smul_ok n p; Sm.smul_ok (2 * n) p;
    point_equal_refl pa;
    dbl_step pa a;
    Sm.smul_dbl_congr n p pa;
    mrep_congr (MC.mdbl a) (point_double pa) (Sm.smul (2 * n) p)

let rung_diff (p: ext_point) (n: nat) (a b: proj)
  : Lemma (requires on_curve p /\ ucoord p <> 0 /\
                    mrep a (Sm.smul n p) /\ mrep b (Sm.smul (n + 1) p))
          (ensures mrep (MC.mdiff (ucoord p) a b) (Sm.smul (n + 1 + n) p))
  = let pa = Sm.smul n p in
    let pb = Sm.smul (n + 1) p in
    Sm.smul_ok n p; Sm.smul_ok (n + 1) p; Sm.smul_ok (n + 1 + n) p;
    point_equal_refl pa; point_equal_refl pb;
    sub_succ n p;
    diff_step pa pb p (ucoord p) a b;
    Sm.smul_add_congr (n + 1) n p pb pa;
    mrep_congr (MC.mdiff (ucoord p) a b) (point_add pb pa) (Sm.smul (n + 1 + n) p)

let rung_arith (n: nat)
  : Lemma (n + 1 + n == 2 * n + 1 /\ 2 * (n + 1) == 2 * n + 1 + 1) = ()

let rung (p: ext_point) (n: nat) (a b: proj)
  : Lemma (requires on_curve p /\ ucoord p <> 0 /\ inv_n p n (a, b))
          (ensures inv_n p (2 * n) (MC.mdbl a, MC.mdiff (ucoord p) a b) /\
                   inv_n p (2 * n + 1) (MC.mdiff (ucoord p) a b, MC.mdbl b))
  = rung_arith n;
    inv_n_def p n (a, b);
    inv_n_def p (2 * n) (MC.mdbl a, MC.mdiff (ucoord p) a b);
    inv_n_def p (2 * n + 1) (MC.mdiff (ucoord p) a b, MC.mdbl b);
    rung_dbl p n a;
    rung_dbl p (n + 1) b;
    rung_diff p n a b

let le_bound (k: Seq.lseq S8.t 32) : Lemma (B.le_nat k < pow2 256) =
  B.le_nat_bound k

(** One rung consumes one bit of the scalar. *)
let next_n (k: Seq.lseq S8.t 32) (i: nat { i < 256 })
  : Lemma (let n = B.le_nat k / pow2 (256 - i) in
           let n' = B.le_nat k / pow2 (256 - (i + 1)) in
           (ith_bit k (255 - i) == 0 ==> n' == 2 * n) /\
           (ith_bit k (255 - i) <> 0 ==> n' == 2 * n + 1))
  = Sm.ith_bit_gbit k (255 - i);
    G.shift_bit (B.le_nat k) (255 - i)

(** The rung, read off the specification's [cswap]s. *)
[@@"opaque_to_smt"]
let rung_of (x1: elem) (bit: nat { bit < 2 }) (a b: proj) : GTot (proj & proj) =
  let (p, q) = cswap bit a b in
  let (p, q) = add_and_double x1 p q in
  cswap bit p q

let ladder_at_rung (x1: elem) (k: Seq.lseq S8.t 32) (i: nat { i < 256 }) (a b: proj)
  : Lemma (ladder_at x1 k i (a, b) == rung_of x1 (ith_bit k (255 - i)) a b) =
  FStar.Pervasives.reveal_opaque (`%rung_of) rung_of

let shape0 (x1: elem) (a b: proj) : Lemma (rung_of x1 0 a b == (MC.mdbl a, MC.mdiff x1 a b)) =
  FStar.Pervasives.reveal_opaque (`%rung_of) rung_of;
  MC.add_and_double_eq x1 a b

let shape1 (x1: elem) (a b: proj) : Lemma (rung_of x1 1 a b == (MC.mdiff x1 a b, MC.mdbl b)) =
  FStar.Pervasives.reveal_opaque (`%rung_of) rung_of;
  MC.add_and_double_eq x1 b a;
  MC.diff_sym x1 a b

let bit_one (bit: nat { bit < 2 }) : Lemma (requires bit <> 0) (ensures bit == 1) = ()

let step_any (p: ext_point) (n n': nat) (bit: nat { bit < 2 }) (a b: proj) (st': proj & proj)
  : Lemma (requires inv_n p (2 * n) (MC.mdbl a, MC.mdiff (ucoord p) a b) /\
                    inv_n p (2 * n + 1) (MC.mdiff (ucoord p) a b, MC.mdbl b) /\
                    st' == rung_of (ucoord p) bit a b /\
                    (bit == 0 ==> n' == 2 * n) /\ (bit <> 0 ==> n' == 2 * n + 1))
          (ensures inv_n p n' st')
  = if bit = 0 then shape0 (ucoord p) a b
    else (bit_one bit; shape1 (ucoord p) a b)

let step_inv (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat { i < 256 }) (st: proj & proj)
  : Lemma (requires on_curve p /\ ucoord p <> 0 /\ inv_at k p i st)
          (ensures inv_at k p (i + 1) (ladder_at (ucoord p) k i st))
  = let (a, b) = st in
    next_n k i;
    ladder_at_rung (ucoord p) k i a b;
    rung p (B.le_nat k / pow2 (256 - i)) a b;
    step_any p (B.le_nat k / pow2 (256 - i)) (B.le_nat k / pow2 (256 - (i + 1)))
      (ith_bit k (255 - i)) a b (ladder_at (ucoord p) k i st)

let uenc_nz (v: elem) : Lemma (requires uenc v <> 0) (ensures fsub one v <> 0) =
  if fsub one v = 0 then (finv_zero (); assert (fmul (fadd one v) 0 == 0))

let init_lo (p: ext_point) : Lemma (mrep (one, 0) (Sm.smul 0 p)) =
  Sm.smul_zero p;
  finv_one (); mul_one one;
  assert (yv point_at_infinity == one);
  mrep_def (one, 0) (Sm.smul 0 p)

let init_hi (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p <> 0) (ensures mrep (ucoord p, one) (Sm.smul 1 p))
  = Sm.smul_one p; Sm.smul_ok 1 p;
    yv_eq (Sm.smul 1 p) p;
    ucoord_def p;
    uenc_nz (yv p);
    mrep_def (ucoord p, one) (Sm.smul 1 p);
    div_mul (fadd one (yv p)) (fsub one (yv p));
    mul_one (fadd one (yv p))

let ladder_init_inv (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p <> 0)
          (ensures inv_n p 0 (ladder_init (ucoord p)))
  = inv_n_def p 0 (ladder_init (ucoord p));
    init_lo p;
    init_hi p

[@@"opaque_to_smt"]
let run (x1: elem) (k: Seq.lseq S8.t 32) (i: nat) : GTot (proj & proj) =
  Loops.repeati_g i (ladder_at x1 k) (ladder_init x1)

let run_zero (x1: elem) (k: Seq.lseq S8.t 32) : Lemma (run x1 k 0 == ladder_init x1) =
  FStar.Pervasives.reveal_opaque (`%run) run;
  Loops.repeati_g_zero (ladder_at x1 k) (ladder_init x1)

let run_succ (x1: elem) (k: Seq.lseq S8.t 32) (i: nat)
  : Lemma (run x1 k (i + 1) == ladder_at x1 k i (run x1 k i)) =
  FStar.Pervasives.reveal_opaque (`%run) run;
  Loops.unfold_repeati_g i (ladder_at x1 k) (ladder_init x1)

let run_full (x1: elem) (k: Seq.lseq S8.t 32) : Lemma (montgomery_ladder x1 k == run x1 k 256) =
  FStar.Pervasives.reveal_opaque (`%run) run

let inv_top (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p <> 0) (ensures inv_at k p 0 (run (ucoord p) k 0))
  = le_bound k;
    M.small_div (B.le_nat k) (pow2 256);
    run_zero (ucoord p) k;
    ladder_init_inv p

let inv_succ (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat { i < 256 })
  : Lemma (requires on_curve p /\ ucoord p <> 0 /\ inv_at k p i (run (ucoord p) k i))
          (ensures inv_at k p (i + 1) (run (ucoord p) k (i + 1)))
  = run_succ (ucoord p) k i;
    step_inv k p i (run (ucoord p) k i)

let rec ladder_inv (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat { i <= 256 })
  : Lemma (requires i >= 0 /\ on_curve p /\ ucoord p <> 0)
          (ensures inv_at k p i (run (ucoord p) k i))
          (decreases i)
  = if i <= 0 then inv_top k p
    else (ladder_inv k p (i - 1); inv_succ k p (i - 1))

(** {2 The degenerate input} *)

[@@"opaque_to_smt"]
let zinv (st: proj & proj) : prop =
  let ((x2, z2), (x3, z3)) = st in fmul x2 z2 == 0 /\ fmul x3 z3 == 0

let zinv_def (a b: proj)
  : Lemma (zinv (a, b) <==> fmul (fst a) (snd a) == 0 /\ fmul (fst b) (snd b) == 0) =
  FStar.Pervasives.reveal_opaque (`%zinv) zinv

let mdiff_z (a b: proj) : Lemma (fmul (fst (MC.mdiff 0 a b)) (snd (MC.mdiff 0 a b)) == 0) = ()

let dbl_z (a: proj)
  : Lemma (requires fmul (fst a) (snd a) == 0) (ensures fmul (fst (MC.mdbl a)) (snd (MC.mdbl a)) == 0)
  = let (x, z) = a in
    MC.dbl_zero x z;
    fmul_zero (fst (MC.mdbl a));
    assert (fmul (fst (MC.mdbl a)) 0 == 0)

let zrung0 (a b: proj) : Lemma (requires zinv (a, b)) (ensures zinv (MC.mdbl a, MC.mdiff 0 a b)) =
  zinv_def a b; zinv_def (MC.mdbl a) (MC.mdiff 0 a b);
  dbl_z a; mdiff_z a b

let zrung1 (a b: proj) : Lemma (requires zinv (a, b)) (ensures zinv (MC.mdiff 0 a b, MC.mdbl b)) =
  zinv_def a b; zinv_def (MC.mdiff 0 a b) (MC.mdbl b);
  dbl_z b; mdiff_z a b

let zrung (bit: nat { bit < 2 }) (a b: proj)
  : Lemma (requires zinv (a, b)) (ensures zinv (rung_of 0 bit a b))
  = if bit = 0 then (shape0 0 a b; zrung0 a b) else (bit_one bit; shape1 0 a b; zrung1 a b)

let zstep (k: Seq.lseq S8.t 32) (i: nat { i < 256 }) (a b: proj)
  : Lemma (requires zinv (a, b)) (ensures zinv (ladder_at 0 k i (a, b)))
  = ladder_at_rung 0 k i a b;
    zrung (ith_bit k (255 - i)) a b

let rec ladder_zero (k: Seq.lseq S8.t 32) (i: nat { i <= 256 })
  : Lemma (requires i >= 0) (ensures zinv (run 0 k i)) (decreases i) =
  if i <= 0 then (run_zero 0 k; zinv_def (one, 0) (0, one))
  else begin
    ladder_zero k (i - 1);
    run_succ 0 k (i - 1);
    let (a, b) = run 0 k (i - 1) in
    zstep k (i - 1) a b
  end

let enc_zero (x z: elem) : Lemma (requires fmul x z == 0) (ensures fmul x (finv z) == 0) =
  finv_zero (); no_zero_div x z

(** A point with [u = 0] has [v = +-1], hence [x = 0], hence order at most
    two. *)
let tors_v (v: elem) : Lemma (requires uenc v == 0) (ensures fmul v v == fmul one one) =
  finv_zero ();
  if fsub one v <> 0 then begin
    mul_finv (fsub one v);
    no_zero_div (fadd one v) (finv (fsub one v));
    add_zero v;
    assert_norm (((prime - 1) * (prime - 1)) % prime == 1);
    mul_one one
  end else S.fsub_zero one v

let tors_u (u v: elem) : Lemma (requires S.on u v /\ fmul v v == fmul one one) (ensures u == 0) =
  MC.tors_x u v one (fmul u v);
  cpt_parts u v;
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  S.fsub_self (S.hl (S.cpt u v));
  S.m0_lem (); S.d_lem ();
  assert_norm (S.m0 - 1 - S.dl > 0 /\ S.m0 - 1 - S.dl < S.m0);
  S.cst_small (S.m0 - 1 - S.dl);
  mul_one one;
  mul_one (fmul u u);
  no_zero_div (S.cst (S.m0 - 1 - S.dl)) (fmul (fmul u u) (fmul one one));
  no_zero_div u u

let tors_c (v: elem)
  : Lemma (requires fmul v v == fmul one one)
          (ensures (let (d0, d1, d2, _) = point_double (S.cpt 0 v) in d0 == 0 /\ d1 == d2))
  = MC.tors_dbl v one (fmul 0 v);
    cpt_parts 0 v;
    pdbl_eq (S.cpt 0 v)

let sc_o (s: elem) (d: ext_point)
  : Lemma (requires (let (d0, d1, d2, _) = d in d0 == 0 /\ d1 == d2))
          (ensures point_equal (S.sc s d) point_at_infinity)
  = sc_parts s d;
    let (_, d1, _, _) = d in
    mul_one (fmul s d1)

let tors (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p == 0)
          (ensures on_curve (point_double p) /\ point_equal (point_double p) point_at_infinity)
  = ucoord_def p;
    decomp p;
    yv_ak p;
    let (u, v) = ak p in
    let (_, _, z, _) = p in
    tors_v v;
    tors_u u v;
    tors_c v;
    K.dbl_scale z u v one (fmul u v);
    cpt_parts u v;
    pdbl_eq p; pdbl_eq (S.cpt u v);
    point_double_on_curve p;
    sc_o (fmul (fmul z z) (fmul z z)) (point_double (S.cpt u v))

let dbl_o (p: ext_point)
  : Lemma (requires on_curve p /\ point_equal (point_double p) point_at_infinity)
          (ensures on_curve (Sm.smul 2 p) /\ point_equal (Sm.smul 2 p) point_at_infinity)
  = point_at_infinity_on_curve ();
    Sm.smul_one p; Sm.smul_ok 1 p; Sm.smul_ok 2 p;
    point_equal_sym (Sm.smul 1 p) p;
    Sm.smul_dbl_congr 1 p p;
    point_equal_sym (point_double p) (Sm.smul 2 p);
    point_equal_trans (Sm.smul 2 p) (point_double p) point_at_infinity

let add_o (n: nat) (p: ext_point)
  : Lemma (requires on_curve p /\ point_equal (Sm.smul 2 p) point_at_infinity /\
                    point_equal (Sm.smul n p) point_at_infinity)
          (ensures point_equal (Sm.smul (2 + n) p) point_at_infinity)
  = let o = point_at_infinity in
    let q = Sm.smul 2 p in
    let r = Sm.smul n p in
    point_at_infinity_on_curve ();
    Sm.smul_ok 2 p; Sm.smul_ok n p; Sm.smul_ok (2 + n) p;
    point_equal_refl q; point_equal_refl r;
    Sm.smul_add_congr 2 n p q r;
    point_add_congr q o r o;
    point_add_identity o;
    point_add_on_curve o o;
    point_equal_sym (point_add q r) (Sm.smul (2 + n) p);
    trans4 (Sm.smul (2 + n) p) (point_add q r) (point_add o o) o

#push-options "--smtencoding.nl_arith_repr boxwrap"
let twice (m: nat) : Lemma (2 * m == m + m) = ()
#pop-options

[@@"opaque_to_smt"]
let is_o (n: nat) (p: ext_point) : prop = point_equal (Sm.smul n p) point_at_infinity

let is_o_def (n: nat) (p: ext_point)
  : Lemma (is_o n p <==> point_equal (Sm.smul n p) point_at_infinity) =
  FStar.Pervasives.reveal_opaque (`%is_o) is_o

let is_o_zero (p: ext_point) : Lemma (is_o 0 p) =
  is_o_def 0 p;
  Sm.smul_zero p;
  point_at_infinity_on_curve ();
  point_equal_refl point_at_infinity

let is_o_step (n: nat) (p: ext_point)
  : Lemma (requires on_curve p /\ point_equal (point_double p) point_at_infinity /\ is_o n p)
          (ensures is_o (2 + n) p)
  = is_o_def n p; is_o_def (2 + n) p;
    dbl_o p;
    add_o n p

let zz (m: int) : Lemma (requires m <= 0 /\ m >= 0) (ensures m + m == 0) = ()

let ss (m: int) : Lemma (2 + ((m - 1) + (m - 1)) == m + m) = ()

let rec smul_even_o (m: nat) (p: ext_point)
  : Lemma (requires m >= 0 /\ on_curve p /\ point_equal (point_double p) point_at_infinity)
          (ensures is_o (m + m) p)
          (decreases m)
  = if m <= 0 then (zz m; is_o_zero p)
    else (smul_even_o (m - 1) p; is_o_step ((m - 1) + (m - 1)) p;
          ss m)

let smul_even_tors (m: nat) (p: ext_point)
  : Lemma (requires on_curve p /\ point_equal (point_double p) point_at_infinity)
          (ensures point_equal (Sm.smul (2 * m) p) point_at_infinity)
  = smul_even_o m p; twice m; is_o_def (2 * m) p

let ucoord_o () : Lemma (ucoord point_at_infinity == 0) =
  ucoord_def point_at_infinity; finv_one (); mul_one one; finv_zero ()

(** {2 The ladder computes a multiple} *)

let div_one (n: nat) : Lemma (n / pow2 0 == n) = assert_norm (pow2 0 == 1)

let ladder_rep (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p <> 0)
          (ensures mrep (fst (montgomery_ladder (ucoord p) k)) (Sm.smul (B.le_nat k) p))
  = ladder_inv k p 256;
    run_full (ucoord p) k;
    div_one (B.le_nat k);
    inv_n_def p (B.le_nat k) (run (ucoord p) k 256)

let ladder_ucoord (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p <> 0)
          (ensures (let ((x, z), _) = montgomery_ladder (ucoord p) k in
                    fmul x (finv z) == ucoord (Sm.smul (B.le_nat k) p)))
  = ladder_rep k p;
    let ((x, z), _) = montgomery_ladder (ucoord p) k in
    mrep_def (x, z) (Sm.smul (B.le_nat k) p);
    ucoord_def (Sm.smul (B.le_nat k) p);
    enc_rep x z (yv (Sm.smul (B.le_nat k) p))

let ladder_out_zero (k: Seq.lseq S8.t 32)
  : Lemma (let ((x, z), _) = montgomery_ladder 0 k in fmul x (finv z) == 0)
  = ladder_zero k 256;
    run_full 0 k;
    let (a, b) = run 0 k 256 in
    zinv_def a b;
    enc_zero (fst a) (snd a)

let even_half (n: nat) : Lemma (requires n % 2 == 0) (ensures 2 * (n / 2) == n) =
  M.euclidean_division_definition n 2

let smul_tors_ucoord (n: nat) (p: ext_point)
  : Lemma (requires on_curve p /\ ucoord p == 0 /\ n % 2 == 0)
          (ensures ucoord (Sm.smul n p) == 0)
  = even_half n;
    tors p;
    smul_even_tors (n / 2) p;
    Sm.smul_ok n p;
    point_at_infinity_on_curve ();
    yv_eq (Sm.smul n p) point_at_infinity;
    ucoord_def (Sm.smul n p);
    ucoord_def point_at_infinity;
    ucoord_o ()

(** The ladder's result is the [u] coordinate of [k P], for every point
    [P] on the curve and every even [k] -- in particular every clamped
    scalar. *)
let ladder_smul (k: Seq.lseq S8.t 32) (p: ext_point)
  : Lemma (requires on_curve p /\ B.le_nat k % 2 == 0)
          (ensures (let ((x, z), _) = montgomery_ladder (ucoord p) k in
                    fmul x (finv z) == ucoord (Sm.smul (B.le_nat k) p)))
  = if ucoord p <> 0 then ladder_ucoord k p
    else (ladder_out_zero k; smul_tors_ucoord (B.le_nat k) p)

#pop-options
