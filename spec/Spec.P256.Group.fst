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

(** The P-256 group law.

    Every point on the curve is a nonzero multiple of a canonical one --
    [(0 : 1 : 0)] or [(x : y : 1)] -- and the addition law is homogeneous
    of degree two in each argument ({!Spec.P256.GroupChecks.k12}).  So each
    statement reduces to canonical points, where it is either a polynomial
    identity modulo the affine curve equations (checked by the normaliser
    in [Spec.P256.GroupChecks] and [Spec.P256.GroupAssoc{1,2,3}]) or, for
    completeness, a polynomial identity plus the fact that two particular
    polynomials have no roots in the field ([Spec.P256.GroupNR]). *)
module Spec.P256.Group

open Spec.P256

module MA = Spec.ModArith
module M = FStar.Math.Lemmas
module F = Spec.Group.Field
module Pj = Spec.Group.Proj
module S = Spec.P256.GroupSv
module K = Spec.P256.GroupChecks
module NR = Spec.P256.GroupNR
module A1 = Spec.P256.GroupAssoc1
module A2 = Spec.P256.GroupAssoc2
module A3 = Spec.P256.GroupAssoc3

let prime_lem () : Lemma (FStar.Math.Euclid.is_prime prime) = S.m0_lem (); S.prime_m0 ()

(** {2 Field facts} *)

let sub_zero (a b: felem) : Lemma (requires fsub a b == 0) (ensures a == b) =
  if a >= b then begin
    M.lemma_mod_plus (a - b) 1 prime; M.small_mod (a - b) prime
  end
  else M.small_mod (a + prime - b) prime

let add_zero (a b: felem) : Lemma (requires fadd a b == 0) (ensures a == fneg b) =
  if b = 0 then M.small_mod a prime
  else begin
    M.small_mod (prime - b) prime;
    if a + b < prime then M.small_mod (a + b) prime
    else M.lemma_mod_sub (a + b) prime 1
  end

let neg_nz (y: felem) : Lemma (requires y <> 0) (ensures fneg y <> 0) =
  M.small_mod (prime - y) prime

let inv_zero () : Lemma (finv 0 == 0) = ()

(** {2 The curve predicates, restated} *)

let oc_heq (p: proj_point) : Lemma (on_curve p <==> (Pj.nz #prime p /\ S.heq p)) =
  FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
  FStar.Pervasives.reveal_opaque (`%S.eqn_l) S.eqn_l;
  FStar.Pervasives.reveal_opaque (`%S.eqn_r) S.eqn_r

let ff_on (x y: felem) : Lemma (requires fmul y y == S.ff x) (ensures S.on x y) =
  S.cst_lem ();
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  FStar.Pervasives.reveal_opaque (`%S.ff) S.ff

let heq_aff (x y: felem) : Lemma (S.heq (x, y, fone) <==> S.on x y) =
  FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
  K.k18 x y;
  Classical.move_requires (S.on_ff x) y;
  Classical.move_requires (ff_on x) y

let heq_inf () : Lemma (S.heq point_at_infinity) =
  FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
  FStar.Pervasives.reveal_opaque (`%S.eqn_l) S.eqn_l;
  FStar.Pervasives.reveal_opaque (`%S.eqn_r) S.eqn_r

let heq_scale (s: felem) (p: proj_point)
  : Lemma (requires S.heq p) (ensures S.heq (Pj.scale #prime s p))
  = FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
    let (x, y, z) = p in K.k17 s x y z

let heq_unscale (s: felem) (p: proj_point)
  : Lemma (requires s <> 0 /\ S.heq (Pj.scale #prime s p)) (ensures S.heq p)
  = FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
    prime_lem ();
    let (x, y, z) = p in
    K.k17 s x y z;
    let s3 = fmul (fmul s s) s in
    F.mul_nonzero s s; F.mul_nonzero (fmul s s) s;
    MA.mul_comm s3 (S.eqn_l p); MA.mul_comm s3 (S.eqn_r p);
    F.cancel (S.eqn_l p) (S.eqn_r p) s3

(** At [z = 0] the equation says [x^3 = 0]. *)
let inf_shape_of (p: proj_point)
  : Lemma (requires on_curve p) (ensures Pj.inf_shape #prime p)
  = let (x, y, z) = p in
    if z = 0 then begin
      prime_lem ();
      let c = fmul (fmul x x) x in
      let zz = fmul z z in
      assert (zz == 0);
      assert (fmul (fmul y y) z == 0);
      assert (fmul (fmul (fadd fone (fadd fone fone)) x) zz == 0);
      assert (fmul zz z == 0);
      assert (fmul b_coeff (fmul zz z) == 0);
      M.small_mod c prime;
      assert (fsub c 0 == c);
      assert (fadd c 0 == c);
      assert (fmul (fmul x x) x == 0);
      F.no_zero_div (fmul x x) x;
      F.no_zero_div x x
    end

let y_nz (x y: felem) : Lemma (requires S.on x y) (ensures y <> 0) =
  S.on_ff x y; NR.no_root_f x

(** {2 Canonical representatives} *)

let cpt (p: proj_point) : prop =
  p == point_at_infinity \/ (let (u, v, w) = p in w == fone /\ S.on u v)

let canon_on (p: proj_point)
  : Lemma (requires on_curve p)
          (ensures (prime_lem ();
                    Pj.ck #prime p <> 0 /\ p == Pj.scale (Pj.ck #prime p) (Pj.canon #prime p) /\
                    cpt (Pj.canon #prime p)))
  = prime_lem ();
    oc_heq p;
    inf_shape_of p;
    Pj.canon_scale #prime p;
    let cp = Pj.canon #prime p in
    heq_unscale (Pj.ck #prime p) cp;
    let (u, v, w) = cp in
    heq_aff u v

(** {2 Identities of the addition law} *)

let add_scale (s t: felem) (p q: proj_point)
  : Lemma (point_add (Pj.scale #prime s p) (Pj.scale #prime t q) ==
           Pj.scale #prime (fmul (fmul s s) (fmul t t)) (point_add p q))
  = let (x1, y1, z1) = p in
    let (x2, y2, z2) = q in
    K.k12 s t x1 y1 z1 x2 y2 z2

let yof (p: proj_point) : felem = let (_, y, _) = p in y

let add_inf_l (p: proj_point)
  : Lemma (point_add point_at_infinity p == Pj.scale #prime (yof p) p)
  = let (x, y, z) = p in K.k8 x y z

let add_comm (p q: proj_point) : Lemma (point_add p q == point_add q p) =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in
  K.k9 x1 y1 z1 x2 y2 z2

let add_inf_r (p: proj_point)
  : Lemma (point_add p point_at_infinity == Pj.scale #prime (yof p) p)
  = add_comm p point_at_infinity; add_inf_l p

let add_one_l (t: felem) (p q: proj_point)
  : Lemma (point_add p (Pj.scale #prime t q) == Pj.scale #prime (fmul (fmul fone fone) (fmul t t)) (point_add p q))
  = Pj.scale_one #prime p; add_scale fone t p q

let add_one_r (s: felem) (p q: proj_point)
  : Lemma (point_add (Pj.scale #prime s p) q == Pj.scale #prime (fmul (fmul s s) (fmul fone fone)) (point_add p q))
  = Pj.scale_one #prime q; add_scale s fone p q

let peq_scales (s t: felem) (u: proj_point)
  : Lemma (Pj.peq #prime (Pj.scale #prime s u) (Pj.scale #prime t u))
  = Pj.peq_refl u; Pj.peq_scale s t u u

(** {2 Completeness on affine points} *)

#push-options "--z3rlimit 40"
let complete_aff (x1 y1 x2 y2: felem)
  : Lemma (requires S.on x1 y1 /\ S.on x2 y2)
          (ensures Pj.nz #prime (point_add (x1, y1, fone) (x2, y2, fone)))
  = let (x3, y3, z3) = point_add (x1, y1, fone) (x2, y2, fone) in
    let aux () : Lemma (requires x3 == 0 /\ y3 == 0 /\ z3 == 0) (ensures False) =
      prime_lem ();
      K.k2 x1 y1 x2 y2;
      let d = fsub x1 x2 in
      if d <> 0 then begin
        let e = fmul d d in
        F.mul_nonzero d d;
        let sa = fadd y1 y2 in
        let a = fsub (fmul sa sa) (fmul (fadd x1 x2) e) in
        assert (S.eqn_r (a, y1, e) == 0);
        let u = fmul a (finv e) in
        F.div_mul a e;
        assert (fmul u e == a);
        K.k6 u e y1;
        NR.no_root_f u;
        F.mul_nonzero e e; F.mul_nonzero (fmul e e) e;
        F.mul_nonzero (fmul (fmul e e) e) (S.ff u)
      end
      else begin
        sub_zero x1 x2;
        K.k7 x1 y1 y2;
        F.no_zero_div (fsub y2 y1) (fadd y2 y1);
        if fsub y2 y1 = 0 then begin
          sub_zero y2 y1;
          K.k4 x1 y1;
          S.cst_small 8;
          y_nz x1 y1;
          F.mul_nonzero y1 y1; F.mul_nonzero (fmul y1 y1) y1;
          F.mul_nonzero 8 (fmul (fmul y1 y1) y1)
        end
        else begin
          add_zero y2 y1;
          K.k5 x1 y1;
          NR.no_root_q x1
        end
      end
    in
    Classical.move_requires aux ()
#pop-options

let add_canon (p q: proj_point)
  : Lemma (requires cpt p /\ cpt q)
          (ensures Pj.nz #prime (point_add p q) /\ S.heq (point_add p q))
  = prime_lem ();
    heq_inf ();
    let one_inf (a: proj_point)
      : Lemma (requires cpt a /\ a =!= point_at_infinity)
              (ensures Pj.nz #prime (Pj.scale #prime (yof a) a) /\ S.heq (Pj.scale #prime (yof a) a))
      = let (u, v, w) = a in
        y_nz u v;
        heq_aff u v;
        MA.mul_one #prime v;
        heq_scale v a
    in
    if p = point_at_infinity then begin
      add_inf_l q;
      if q = point_at_infinity then () else one_inf q
    end
    else if q = point_at_infinity then begin
      add_inf_r p; one_inf p
    end
    else begin
      let (x1, y1, _) = p in
      let (x2, y2, _) = q in
      K.k1 x1 y1 x2 y2;
      complete_aff x1 y1 x2 y2
    end

let add_on (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q) (ensures on_curve (point_add p q))
  = prime_lem ();
    canon_on p; canon_on q;
    let kp = Pj.ck #prime p in
    let kq = Pj.ck #prime q in
    let cp = Pj.canon #prime p in
    let cq = Pj.canon #prime q in
    add_scale kp kq cp cq;
    add_canon cp cq;
    let s = fmul (fmul kp kp) (fmul kq kq) in
    F.mul_nonzero kp kp; F.mul_nonzero kq kq; F.mul_nonzero (fmul kp kp) (fmul kq kq);
    Pj.scale_nz s (point_add cp cq);
    heq_scale s (point_add cp cq);
    oc_heq (point_add p q)

(** {2 The interface} *)

let on_curve_affine x y =
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  heq_aff x y;
  oc_heq (x, y, fone)

let point_at_infinity_on_curve () =
  heq_inf (); oc_heq point_at_infinity

let g_on_curve () =
  assert_norm (is_on_curve g_x g_y);
  on_curve_affine g_x g_y

let peq_refl p = Pj.peq_refl #prime p

let peq_sym p q = ()

let peq_trans p q r =
  prime_lem ();
  oc_heq q;
  Pj.peq_trans #prime p q r

let peq_is_point_at_infinity p q =
  prime_lem ();
  inf_shape_of p; inf_shape_of q;
  Pj.canon_peq #prime p q;
  Pj.canon_inf #prime p; Pj.canon_inf #prime q

let peq_to_aff_point p q =
  prime_lem ();
  inf_shape_of p; inf_shape_of q;
  Pj.canon_peq #prime p q;
  Pj.canon_inf #prime p; Pj.canon_inf #prime q;
  inv_zero ()

let point_add_denominators_nonzero p q =
  add_on p q; oc_heq (point_add p q)

let point_add_on_curve p q = add_on p q

#push-options "--z3rlimit 40"
let point_double_on_curve p =
  prime_lem ();
  oc_heq p;
  let (x, y, z) = p in
  K.k11 x y z;
  inf_shape_of p;
  if z = 0 then begin
    K.k16 y;
    F.mul_nonzero y y; F.mul_nonzero (fmul y y) (fmul y y)
  end
  else begin
    let yz () : Lemma (requires y == 0) (ensures False) =
      FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
      FStar.Pervasives.reveal_opaque (`%S.eqn_l) S.eqn_l;
      assert (S.eqn_l p == 0);
      let u = fmul x (finv z) in
      F.div_mul x z;
      K.k6 u z y;
      NR.no_root_f u;
      F.mul_nonzero z z; F.mul_nonzero (fmul z z) z;
      F.mul_nonzero (fmul (fmul z z) z) (S.ff u)
    in
    Classical.move_requires yz ();
    K.k15 x y z;
    S.cst_small 8;
    F.mul_nonzero y y; F.mul_nonzero (fmul y y) y; F.mul_nonzero (fmul (fmul y y) y) z;
    F.mul_nonzero 8 (fmul (fmul (fmul y y) y) z)
  end;
  oc_heq (point_double p)
#pop-options

let point_negate_on_curve p =
  oc_heq p;
  let (x, y, z) = p in
  K.k19 x y z;
  FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
  if y <> 0 then neg_nz y;
  oc_heq (point_negate p)

let point_add_congr p p' q q' =
  prime_lem ();
  canon_on p; canon_on p'; canon_on q; canon_on q';
  inf_shape_of p; inf_shape_of p'; inf_shape_of q; inf_shape_of q';
  Pj.canon_peq #prime p p'; Pj.canon_peq #prime q q';
  let cp = Pj.canon #prime p in
  let cq = Pj.canon #prime q in
  add_scale (Pj.ck #prime p) (Pj.ck #prime q) cp cq;
  add_scale (Pj.ck #prime p') (Pj.ck #prime q') cp cq;
  peq_scales (fmul (fmul (Pj.ck #prime p) (Pj.ck #prime p)) (fmul (Pj.ck #prime q) (Pj.ck #prime q)))
             (fmul (fmul (Pj.ck #prime p') (Pj.ck #prime p')) (fmul (Pj.ck #prime q') (Pj.ck #prime q')))
             (point_add cp cq)

(** {3 Associativity} *)

let assoc_inf_l (q r: proj_point)
  : Lemma (Pj.peq #prime (point_add (point_add point_at_infinity q) r)
                         (point_add point_at_infinity (point_add q r)))
  = add_inf_l q;
    add_one_r (yof q) q r;
    add_inf_l (point_add q r);
    peq_scales (fmul (fmul (yof q) (yof q)) (fmul fone fone)) (yof (point_add q r)) (point_add q r)

let assoc_inf_m (p r: proj_point)
  : Lemma (Pj.peq #prime (point_add (point_add p point_at_infinity) r)
                         (point_add p (point_add point_at_infinity r)))
  = add_inf_r p;
    add_one_r (yof p) p r;
    add_inf_l r;
    add_one_l (yof r) p r;
    peq_scales (fmul (fmul (yof p) (yof p)) (fmul fone fone))
               (fmul (fmul fone fone) (fmul (yof r) (yof r))) (point_add p r)

let assoc_inf_r (p q: proj_point)
  : Lemma (Pj.peq #prime (point_add (point_add p q) point_at_infinity)
                         (point_add p (point_add q point_at_infinity)))
  = add_inf_r (point_add p q);
    add_inf_r q;
    add_one_l (yof q) p q;
    peq_scales (yof (point_add p q)) (fmul (fmul fone fone) (fmul (yof q) (yof q))) (point_add p q)

let assoc_canon (p q r: proj_point)
  : Lemma (requires cpt p /\ cpt q /\ cpt r)
          (ensures Pj.peq #prime (point_add (point_add p q) r) (point_add p (point_add q r)))
  = if p = point_at_infinity then assoc_inf_l q r
    else if q = point_at_infinity then assoc_inf_m p r
    else if r = point_at_infinity then assoc_inf_r p q
    else begin
      let (x1, y1, _) = p in
      let (x2, y2, _) = q in
      let (x3, y3, _) = r in
      A1.assoc1 x1 y1 x2 y2 x3 y3;
      A2.assoc2 x1 y1 x2 y2 x3 y3;
      A3.assoc3 x1 y1 x2 y2 x3 y3
    end

#push-options "--z3rlimit 40"
let point_add_assoc_law p q r =
  prime_lem ();
  canon_on p; canon_on q; canon_on r;
  let kp = Pj.ck #prime p in
  let kq = Pj.ck #prime q in
  let kr = Pj.ck #prime r in
  let cp = Pj.canon #prime p in
  let cq = Pj.canon #prime q in
  let cr = Pj.canon #prime r in
  add_scale kp kq cp cq;
  let s1 = fmul (fmul kp kp) (fmul kq kq) in
  add_scale s1 kr (point_add cp cq) cr;
  add_scale kq kr cq cr;
  let s2 = fmul (fmul kq kq) (fmul kr kr) in
  add_scale kp s2 cp (point_add cq cr);
  assoc_canon cp cq cr;
  Pj.peq_scale (fmul (fmul s1 s1) (fmul kr kr)) (fmul (fmul kp kp) (fmul s2 s2))
               (point_add (point_add cp cq) cr) (point_add cp (point_add cq cr))
#pop-options

let point_add_comm_law p q =
  add_comm p q; Pj.peq_refl #prime (point_add q p)

let point_add_identity p =
  add_inf_l p; Pj.peq_scale_l #prime (yof p) p

let peq_inf (x y z: felem) : Lemma (requires x == 0 /\ z == 0) (ensures peq (x, y, z) point_at_infinity) = ()

let point_add_negate p =
  oc_heq p;
  let (x, y, z) = p in
  K.k14 x y z;
  let (x3, y3, z3) = point_add (point_negate p) p in
  peq_inf x3 y3 z3

let point_double_is_add p =
  oc_heq p;
  let (x, y, z) = p in
  K.k10 x y z
