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

(** The Ed25519 group law.

    A point [(X, Y, Z, T)] on the curve is [Z] times the canonical point
    [(u, v, 1, uv)] with [(u, v) = (X/Z, Y/Z)], and the formulas are
    homogeneous ({!Spec.Ed25519.GroupChecks.add_scale},
    {!Spec.Ed25519.GroupChecks.dbl_scale}).  [point_equal] is equality of
    [(X/Z, Y/Z)] ({!peq_ak}), so every statement reduces to canonical
    points, where it is a polynomial identity modulo the affine curve
    equations, checked by the normaliser in [Spec.Ed25519.GroupChecks] and
    [Spec.Ed25519.GroupAssoc{1,2}].  Completeness is the one place [d]
    being a non-square is used ({!add_z_nz}). *)
module Spec.Ed25519.Group

open Spec.Curve25519
open Spec.Ed25519

module MA = Spec.ModArith
module M = FStar.Math.Lemmas
module F = Spec.Group.Field
module Pr = Spec.Group.Prime
module S = Spec.Ed25519.GroupSv
module K = Spec.Ed25519.GroupChecks
module A1 = Spec.Ed25519.GroupAssoc1
module A2 = Spec.Ed25519.GroupAssoc2
module B = Hacl.Spec.Bytes

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"

let prime_lem () : Lemma (FStar.Math.Euclid.is_prime prime) = S.m0_lem (); S.prime_m0 ()

(** {2 Field facts} *)

let one_lem () : Lemma (one == 1) = ()

let pm : (m: pos { 1 < m }) = prime_gt_one (); prime

#push-options "--fuel 1"
let rec fexp_exp (x: elem) (n: nat)
  : Lemma (ensures fexp x n == MA.exp #pm x n) (decreases n)
  = if n = 0 then () else fexp_exp x (n - 1)
#pop-options

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

let mul_zero (x: elem) : Lemma (fmul x 0 == 0 /\ fmul 0 x == 0) = ()

let finv_one () : Lemma (finv one == one) = mul_finv one; mul_one (finv one)

let div_eq (a b c d: elem)
  : Lemma (requires b <> 0 /\ d <> 0 /\ fmul a d == fmul c b)
          (ensures fmul a (finv b) == fmul c (finv d))
  = prime_lem (); finv_inv b; finv_inv d; Spec.Group.Proj.div_eq #prime a b c d

let add_zero (a: elem) : Lemma (requires fadd one a == 0) (ensures a == prime - 1) =
  if a + 1 < prime then M.small_mod (a + 1) prime

(** [d] is not a square, by Euler's criterion. *)
let d_euler () : Lemma (MA.exp #pm d ((pm - 1) / 2) == pm - 1) =
  let k : nat = (S.m0 - 1) / 2 in
  assert_norm (Pr.pow_mod S.dl ((S.m0 - 1) / 2) S.m0 == S.m0 - 1);
  Pr.pow_mod_lemma S.dl k S.m0;
  S.m0_lem (); S.d_lem (); F.exp_pow #pm d k

let not_sq (dd s: elem)
  : Lemma (requires FStar.Math.Euclid.is_prime prime /\ MA.exp #pm dd ((pm - 1) / 2) == pm - 1)
          (ensures fmul s s =!= dd)
  = assert_norm (pm % 2 == 1 /\ 2 < pm);
    F.not_square #prime dd;
    assert (MA.mul #prime s s == fmul s s)

let d_not_square (s: elem) : Lemma (fmul s s =!= d) = prime_lem (); d_euler (); not_sq d s

let d_ns (w vv: elem) : Lemma (requires fmul d (fmul w w) == fmul vv vv) (ensures w == 0) =
  if w <> 0 then begin
    let wi = finv w in
    let s = fmul vv wi in
    mul_finv w;
    mul4 vv wi vv wi;
    assert (fmul s s == fmul (fmul d (fmul w w)) (fmul wi wi));
    fmul_assoc d (fmul w w) (fmul wi wi);
    mul4 w w wi wi;
    mul_one one; mul_one d;
    assert (fmul s s == d);
    d_not_square s
  end

(** {2 The curve predicates, restated} *)

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

let pneg_parts (p: ext_point)
  : Lemma (let (x, y, z, t) = p in S.pneg p == (fsub 0 x, y, z, fsub 0 t) /\ S.pneg p == point_negate p)
  = FStar.Pervasives.reveal_opaque (`%S.pneg) S.pneg

let padd_eq (p q: ext_point) : Lemma (S.padd p q == point_add p q) =
  FStar.Pervasives.reveal_opaque (`%S.padd) S.padd

let pdbl_eq (p: ext_point) : Lemma (S.pdbl p == point_double p) =
  FStar.Pervasives.reveal_opaque (`%S.pdbl) S.pdbl

(** The affine coordinates. *)
let ak (p: ext_point) : elem & elem =
  let (x, y, z, _) = p in (fmul x (finv z), fmul y (finv z))

let peq_ak (p q: ext_point)
  : Lemma (requires (let (_, _, z1, _) = p in let (_, _, z2, _) = q in z1 <> 0 /\ z2 <> 0))
          (ensures point_equal p q <==> ak p == ak q)
  = let (x1, y1, z1, _) = p in
    let (x2, y2, z2, _) = q in
    let back (a b: elem)
      : Lemma (requires fmul a (finv z1) == fmul b (finv z2)) (ensures fmul a z2 == fmul b z1)
      = let u = fmul a (finv z1) in
        div_mul a z1; div_mul b z2;
        fmul_assoc u z1 z2; fmul_assoc u z2 z1; fmul_comm z1 z2
    in
    let fwd (a b: elem)
      : Lemma (requires fmul a z2 == fmul b z1) (ensures fmul a (finv z1) == fmul b (finv z2))
      = div_eq a z1 b z2
    in
    Classical.move_requires_2 back x1 x2; Classical.move_requires_2 back y1 y2;
    Classical.move_requires_2 fwd x1 x2; Classical.move_requires_2 fwd y1 y2

let ak_cpt (u v: elem) : Lemma (ak (S.cpt u v) == (u, v)) =
  cpt_parts u v; finv_one (); mul_one u; mul_one v

let ak_scale (k: elem) (p: ext_point)
  : Lemma (requires (let (_, _, z, _) = p in k <> 0 /\ z <> 0)) (ensures ak (S.sc k p) == ak p)
  = let (x, y, z, _) = p in
    sc_parts k p;
    mul_nz k z;
    let aux (a: elem) : Lemma (fmul (fmul k a) (finv (fmul k z)) == fmul a (finv z)) =
      fmul_assoc k a z; fmul_comm a z; fmul_assoc k z a; fmul_comm (fmul k z) a;
      div_eq (fmul k a) (fmul k z) a z
    in
    aux x; aux y

let onc_cpt (u v: elem) : Lemma (requires S.on u v) (ensures S.onc (S.cpt u v)) =
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  onc_parts (S.cpt u v); cpt_parts u v; mul_one (fmul u v)

let onc_scale (k: elem) (p: ext_point)
  : Lemma (requires S.onc p /\ k <> 0) (ensures S.onc (S.sc k p))
  = let (x, y, z, t) = p in
    onc_parts p; onc_parts (S.sc k p); sc_parts k p;
    K.scale_eqs k x y z t;
    mul_nz k z

(** Every point is [Z] times its canonical point. *)
let decomp (p: ext_point)
  : Lemma (requires S.onc p)
          (ensures (let (u, v) = ak p in let (_, _, z, _) = p in
                    z <> 0 /\ p == S.sc z (S.cpt u v) /\ S.on u v))
  = let (x, y, z, t) = p in
    onc_parts p;
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

(** {2 Completeness} *)

let delta (u1 v1 u2 v2: elem) : elem = fmul d (fmul (fmul u1 v1) (fmul u2 v2))

let il : nat = 19681161376707505956807079304988542015446066515923890162744021073123829784752
let jl : nat = 38214883241950591754978413199355411911188925816896391856984770930832735035197

let delta_ne (u1 v1 u2 v2: elem) (ep: nat)
  : Lemma (requires S.on u1 v1 /\ S.on u2 v2 /\ (ep == 1 \/ ep == prime - 1) /\
                    delta u1 v1 u2 v2 == S.cst ep /\
                    (let dt = delta u1 v1 u2 v2 in
                     forall (io: nat). (io == il \/ io == jl) ==>
                       (let w = fmul (fmul u1 v1) (fadd (fmul (S.cst io) u2) v2) in
                        let vv = fadd (fmul (S.cst io) u1) (fmul (S.cst ep) v1) in
                        fsub (fmul d (fmul w w)) (fmul vv vv) ==
                        fmul (fadd (fadd dt (fmul (S.cst 2) (fmul (fmul u1 v1) (S.cst io)))) (S.cst ep))
                             (fsub dt (S.cst ep)))))
          (ensures False)
  = S.m0_lem (); S.cst_lem ();
    S.cst_small ep;
    let dt = delta u1 v1 u2 v2 in
    S.fsub_self dt;
    let one_io (io: nat) : Lemma (requires io == il \/ io == jl)
      (ensures fmul (fmul u1 v1) (fadd (fmul (S.cst io) u2) v2) == 0) =
      let w = fmul (fmul u1 v1) (fadd (fmul (S.cst io) u2) v2) in
      let vv = fadd (fmul (S.cst io) u1) (fmul (S.cst ep) v1) in
      S.fsub_zero (fmul d (fmul w w)) (fmul vv vv);
      d_ns w vv
    in
    one_io il; one_io jl;
    let uv = fmul u1 v1 in
    if uv = 0 then assert (dt == 0)
    else begin
      no_zero_div uv (fadd (fmul (S.cst il) u2) v2);
      no_zero_div uv (fadd (fmul (S.cst jl) u2) v2);
      K.iota_sum u2 v2;
      assert_norm (il + jl == S.m0);
      no_zero_div (S.cst 2) v2;
      assert (v2 == 0);
      assert (dt == 0)
    end

let add_z_nz (u1 v1 u2 v2: elem)
  : Lemma (requires S.on u1 v1 /\ S.on u2 v2)
          (ensures (let (_, _, z, _) = S.padd (S.cpt u1 v1) (S.cpt u2 v2) in z <> 0))
  = K.add_z u1 v1 u2 v2;
    S.cst_lem ();
    let dt = delta u1 v1 u2 v2 in
    let (_, _, z, _) = S.padd (S.cpt u1 v1) (S.cpt u2 v2) in
    if z = 0 then begin
      S.m0_lem ();
      assert_norm (il == 19681161376707505956807079304988542015446066515923890162744021073123829784752);
      assert_norm (jl == S.m0 - il);
      K.comp_pp u1 v1 u2 v2; K.comp_mp u1 v1 u2 v2;
      K.comp_pm u1 v1 u2 v2; K.comp_mm u1 v1 u2 v2;
      no_zero_div (S.cst 4) (fmul (fsub one dt) (fadd one dt));
      no_zero_div (fsub one dt) (fadd one dt);
      if fsub one dt = 0 then begin
        S.fsub_zero one dt;
        delta_ne u1 v1 u2 v2 1
      end else begin
        add_zero dt;
        S.cst_small (prime - 1);
        delta_ne u1 v1 u2 v2 (prime - 1)
      end
    end

(** {2 Addition through the affine coordinates} *)

let eadd (a b: elem & elem) : elem & elem =
  let (u1, v1) = a in let (u2, v2) = b in ak (S.padd (S.cpt u1 v1) (S.cpt u2 v2))

let add_scale4 (s w: elem) (p q: ext_point)
  : Lemma (S.padd (S.sc s p) (S.sc w q) == S.sc (fmul (fmul s w) (fmul s w)) (S.padd p q))
  = let (x1, y1, z1, t1) = p in let (x2, y2, z2, t2) = q in
    K.add_scale s w x1 y1 z1 t1 x2 y2 z2 t2

let onc_add_cpt (u1 v1 u2 v2: elem)
  : Lemma (requires S.on u1 v1 /\ S.on u2 v2)
          (ensures S.onc (S.padd (S.cpt u1 v1) (S.cpt u2 v2)))
  = K.add_on u1 v1 u2 v2; add_z_nz u1 v1 u2 v2;
    onc_parts (S.padd (S.cpt u1 v1) (S.cpt u2 v2))

let add_ak (p q: ext_point)
  : Lemma (requires S.onc p /\ S.onc q)
          (ensures S.onc (S.padd p q) /\ ak (S.padd p q) == eadd (ak p) (ak q) /\
                   S.on (fst (ak p)) (snd (ak p)))
  = decomp p; decomp q;
    let (u1, v1) = ak p in
    let (u2, v2) = ak q in
    let (_, _, z1, _) = p in
    let (_, _, z2, _) = q in
    let c1 = S.cpt u1 v1 in
    let c2 = S.cpt u2 v2 in
    add_scale4 z1 z2 c1 c2;
    let k = fmul (fmul z1 z2) (fmul z1 z2) in
    mul_nz z1 z2; mul_nz (fmul z1 z2) (fmul z1 z2);
    let r = S.padd c1 c2 in
    onc_add_cpt u1 v1 u2 v2;
    onc_scale k r;
    onc_parts r;
    ak_scale k r

(** {2 The statements} *)

let point_at_infinity_on_curve () =
  assert_norm (on_curve point_at_infinity)

let g_on_curve () =
  assert_norm (on_curve g)

let point_add_denominators_nonzero p q =
  oc p; oc q; add_ak p q; padd_eq p q; onc_parts (S.padd p q)

let point_add_on_curve p q =
  oc p; oc q; add_ak p q; padd_eq p q; oc (point_add p q)

let point_double_on_curve p =
  oc p; decomp p;
  let (u, v) = ak p in
  let (x, y, z, t) = p in
  let c = S.cpt u v in
  let (cx, cy, cz, ct) = c in
  K.dbl_scale z cx cy cz ct;
  let k = fmul (fmul z z) (fmul z z) in
  mul_nz z z; mul_nz (fmul z z) (fmul z z);
  let dp = S.pdbl c in
  K.dbl_aff u v;
  add_z_nz u v u v;
  S.cst_lem ();
  let (d0, d1, d2, d3) = dp in
  let (s0, s1, s2, s3) = S.padd c c in
  if d2 = 0 then begin mul_zero (S.cst 4); M.small_mod s2 prime end;
  assert (d2 <> 0);
  onc_parts dp;
  onc_scale k dp;
  pdbl_eq p;
  oc (point_double p)

let point_negate_on_curve p =
  oc p;
  let (x, y, z, t) = p in
  K.neg_eqs x y z t;
  pneg_parts p;
  onc_parts p; onc_parts (S.pneg p);
  oc (point_negate p)

let point_equal_refl p = ()

let point_equal_sym p q = ()

let point_equal_trans p q r =
  oc p; oc q; oc r; onc_parts p; onc_parts q; onc_parts r;
  peq_ak p q; peq_ak q r; peq_ak p r

let point_add_congr p p' q q' =
  oc p; oc p'; oc q; oc q';
  onc_parts p; onc_parts p'; onc_parts q; onc_parts q';
  peq_ak p p'; peq_ak q q';
  add_ak p q; add_ak p' q';
  padd_eq p q; padd_eq p' q';
  onc_parts (S.padd p q); onc_parts (S.padd p' q');
  peq_ak (point_add p q) (point_add p' q')

let point_add_assoc_law p q r =
  oc p; oc q; oc r;
  let pq = S.padd p q in
  let qr = S.padd q r in
  add_ak p q; add_ak q r;
  add_ak pq r; add_ak p qr;
  decomp p; decomp q; decomp r;
  let (u1, v1) = ak p in
  let (u2, v2) = ak q in
  let (u3, v3) = ak r in
  let a = S.cpt u1 v1 in
  let b = S.cpt u2 v2 in
  let c = S.cpt u3 v3 in
  onc_cpt u1 v1; onc_cpt u2 v2; onc_cpt u3 v3;
  ak_cpt u1 v1; ak_cpt u2 v2; ak_cpt u3 v3;
  add_ak a b; add_ak b c;
  let ab = S.padd a b in
  let bc = S.padd b c in
  add_ak ab c; add_ak a bc;
  let l = S.padd ab c in
  let rr = S.padd a bc in
  A1.assoc1 u1 v1 u2 v2 u3 v3;
  A2.assoc2 u1 v1 u2 v2 u3 v3;
  onc_parts l; onc_parts rr;
  peq_ak l rr;
  assert (ak (S.padd pq r) == ak (S.padd p qr));
  padd_eq p q; padd_eq q r; padd_eq pq r; padd_eq p qr;
  onc_parts (S.padd pq r); onc_parts (S.padd p qr);
  peq_ak (S.padd pq r) (S.padd p qr)

let point_add_comm_law p q =
  let (x1, y1, z1, t1) = p in
  let (x2, y2, z2, t2) = q in
  K.add_comm x1 y1 z1 t1 x2 y2 z2 t2;
  padd_eq p q; padd_eq q p

let point_add_identity p =
  let (x, y, z, t) = p in
  K.add_id x y z t;
  padd_eq point_at_infinity p

let point_add_negate p =
  oc p; decomp p;
  let (u, v) = ak p in
  let (x, y, z, t) = p in
  let c = S.cpt u v in
  let (cx, cy, cz, ct) = c in
  K.neg_scale z cx cy cz ct;
  add_scale4 z z (S.pneg c) c;
  K.neg_aff u v;
  let k = fmul (fmul z z) (fmul z z) in
  let n = S.padd (S.pneg c) c in
  sc_parts k n;
  let (n0, n1, n2, _) = n in
  mul_zero k;
  pneg_parts p;
  padd_eq (point_negate p) p;
  mul_one (fmul k n0); mul_one (fmul k n1); mul_one (fmul k n2)

let pe_scale (k: elem) (p q: ext_point)
  : Lemma (requires (let (x1, y1, z1, _) = p in let (x2, y2, z2, _) = q in
                     fmul x1 z2 == fmul x2 z1 /\ fmul y1 z2 == fmul y2 z1))
          (ensures point_equal (S.sc k p) (S.sc k q))
  = let (x1, y1, z1, _) = p in
    let (x2, y2, z2, _) = q in
    sc_parts k p; sc_parts k q;
    mul4 k x1 k z2; mul4 k x2 k z1; mul4 k y1 k z2; mul4 k y2 k z1

let point_double_is_add p =
  oc p; decomp p;
  let (u, v) = ak p in
  let (x, y, z, t) = p in
  let c = S.cpt u v in
  let (cx, cy, cz, ct) = c in
  K.dbl_scale z cx cy cz ct;
  add_scale4 z z c c;
  K.dbl_aff u v;
  let k = fmul (fmul z z) (fmul z z) in
  let (d0, d1, d2, _) = S.pdbl c in
  let (s0, s1, s2, _) = S.padd c c in
  fmul_comm d0 s2; fmul_comm d1 s2;
  pe_scale k (S.pdbl c) (S.padd c c);
  pdbl_eq p; padd_eq p p

let point_compress_congr p q =
  oc p; oc q; onc_parts p; onc_parts q;
  peq_ak p q

(** {2 Decompression lands on the curve}

    All the arithmetic below is done modulo an arbitrary positive [n].
    That is not generality for its own sake: with [prime] in scope the
    solver tries to reason about [2^255 - 19] itself, and what takes seven
    seconds abstractly took over twenty minutes concretely.  Only the last
    two lemmas mention the curve. *)

(** Congruence, as a difference, in both directions. *)
let sub_zero (a b: int) (n: pos)
  : Lemma (requires a % n == b % n) (ensures (a - b) % n == 0)
  = M.lemma_mod_sub_distr a b n; M.lemma_mod_sub_distr a a n

let zero_sub (a b: int) (n: pos)
  : Lemma (requires (a - b) % n == 0) (ensures a % n == b % n)
  = M.lemma_mod_sub_distr a b n; M.lemma_mod_plus_distr_l (a - b) b n

let mul_cong (a b c: int) (n: pos)
  : Lemma (requires a % n == b % n) (ensures (c * a) % n == (c * b) % n)
  = M.lemma_mod_mul_distr_r c a n; M.lemma_mod_mul_distr_r c b n

(** The heart of it.  [v] is the denominator [d y^2 + 1] and the
    hypothesis is [x^2 v = y^2 - 1]; the two sides of the curve equation,
    multiplied through by [v], differ by exactly [v] times that
    hypothesis, so both are [d y^4 + 1]. *)
let cross (x2 y2 v dd: int) (n: pos)
  : Lemma (requires v % n == (dd * y2 + 1) % n /\ (x2 * v) % n == (y2 - 1) % n)
          (ensures ((y2 - x2) * v) % n == ((1 + dd * (x2 * y2)) * v) % n)
  = mul_cong v (dd * y2 + 1) x2 n;
    sub_zero (y2 - 1) (x2 * (dd * y2 + 1)) n;
    let k = (y2 - 1) - x2 * (dd * y2 + 1) in
    M.lemma_mod_mul_distr_r v k n;
    assert ((v * k) % n == 0);
    M.paren_mul_right x2 dd y2;
    M.paren_mul_right dd x2 y2;
    assert (x2 * (dd * y2) == dd * (x2 * y2));
    assert (k == y2 - 1 - dd * (x2 * y2) - x2);
    assert ((y2 - x2) * v - (1 + dd * (x2 * y2)) * v ==
            v * (y2 - x2 - 1 - dd * (x2 * y2)));
    zero_sub ((y2 - x2) * v) ((1 + dd * (x2 * y2)) * v) n

(** Squaring is blind to the sign. *)
let neg_sq_int (x: nat) (n: pos { x < n })
  : Lemma (((n - x) * (n - x)) % n == (x * x) % n)
  = assert ((n - x) * (n - x) == x * x + n * (n - 2 * x));
    M.lemma_mod_plus (x * x) (n - 2 * x) n

(** {!cross} with the reductions that [fadd], [fsub] and [fmul] insert
    written out.  Still no [prime]. *)
let curve_eq_gen (x2 y2 v dd: nat) (n: pos)
  : Lemma (requires x2 < n /\ y2 < n /\ v < n /\ dd < n /\
                    v == ((dd * y2) % n + 1) % n /\
                    (x2 * v) % n == (y2 + n - 1) % n)
          (ensures ((y2 + n - x2) % n * v) % n ==
                   ((1 + (dd * (x2 * y2 % n)) % n) % n * v) % n)
  = M.small_mod v n;
    M.lemma_mod_plus_distr_l (dd * y2) 1 n;
    M.lemma_mod_plus (y2 - 1) 1 n;
    cross x2 y2 v dd n;
    M.lemma_mod_mul_distr_l (y2 + n - x2) v n;
    assert ((y2 + n - x2) * v == (y2 - x2) * v + v * n);
    M.lemma_mod_plus ((y2 - x2) * v) v n;
    M.lemma_mod_mul_distr_r dd (x2 * y2) n;
    M.lemma_mod_plus_distr_r 1 (dd * (x2 * y2)) n;
    M.lemma_mod_mul_distr_l (1 + dd * (x2 * y2)) v n

(** {!curve_eq_gen} at [n = prime], with the denominator cancelled. *)
let curve_eq (x2 y2 v: elem)
  : Lemma (requires v == fadd (fmul d y2) one /\ v <> 0 /\ fmul x2 v == fsub y2 one)
          (ensures fsub y2 x2 == fadd one (fmul d (fmul x2 y2)))
  = curve_eq_gen x2 y2 v d prime;
    cancel (fsub y2 x2) (fadd one (fmul d (fmul x2 y2))) v

(** Squaring is blind to the sign, in the field. *)
let neg_sq (x: elem) : Lemma (fmul (fsub 0 x) (fsub 0 x) == fmul x x) =
  if x = 0 then () else begin
    M.small_mod (prime - x) prime;
    M.lemma_mod_mul_distr_l (prime - x) (prime - x) prime;
    neg_sq_int x prime
  end

(** [recover_x] returns an abscissa satisfying the affine equation. *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let recover_on_curve (y: elem) (sign: nat { sign < 2 }) (x: elem)
  : Lemma (requires recover_x y sign == Some x) (ensures on_curve (x, y, one, fmul x y))
  = let y2 = fmul y y in
    let u = fsub y2 one in
    let v = fadd (fmul d y2) one in
    assert (v <> 0);
    let Some x0 = sqrt_of (fmul u (finv v)) in
    assert (fmul x0 x0 == fmul u (finv v));
    if x = x0 then () else neg_sq x0;
    assert (fmul x x == fmul u (finv v));
    div_mul u v;
    assert (fmul (fmul x x) v == u);
    curve_eq (fmul x x) y2 v;
    (* [hl] and [hr] at [z = one] are the two sides just proved equal. *)
    prime_gt_one ();
    mul_one one;
    FStar.Pervasives.reveal_opaque (`%S.on) S.on;
    FStar.Pervasives.reveal_opaque (`%S.hl) S.hl;
    FStar.Pervasives.reveal_opaque (`%S.hr) S.hr;
    cpt_parts (x) (y);
    mul_one (fsub y2 (fmul x x));
    onc_cpt x y;
    oc (x, y, one, fmul x y)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 200"
let decompress_on_curve s p =
  let n = B.le_nat s in
  let sign = n / pow2 255 in
  let y = n % pow2 255 in
  assert_norm (pow2 255 == 2 * pow2 254);
  B.le_nat_bound s;
  assert_norm (pow2 (8 * 32) == 2 * pow2 255);
  M.lemma_div_lt n 256 255;
  M.lemma_mod_lt n (pow2 255);
  let Some x = recover_x y sign in
  recover_on_curve y sign x
#pop-options
#pop-options
