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

(** Projective triples over a prime field: equivalence by
    cross-multiplication, scaling, and the canonical representative.  Shared
    by the two short-Weierstrass curves. *)
module Spec.Group.Proj

open Spec.ModArith
open Spec.Group.Field

type pt (m: pos) = elem m & elem m & elem m

let peq (#m: pos) (p q: pt m) : prop =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in
  mul x1 y2 == mul x2 y1 /\ mul x1 z2 == mul x2 z1 /\ mul y1 z2 == mul y2 z1

let nz (#m: pos) (p: pt m) : prop =
  let (x, y, z) = p in x <> 0 \/ y <> 0 \/ z <> 0

let scale (#m: pos) (k: elem m) (p: pt m) : pt m =
  let (x, y, z) = p in (mul k x, mul k y, mul k z)

let peq_refl (#m: pos) (p: pt m) : Lemma (peq p p) =
  let (x, y, z) = p in mul_comm x y; mul_comm x z; mul_comm y z

let peq_sym (#m: pos) (p q: pt m) : Lemma (requires peq p q) (ensures peq q p) = ()

let cross (#m: pos) (a b u v: elem m)
  : Lemma (requires mul u v == mul v u /\ True)
          (ensures mul (mul a u) (mul b v) == mul (mul a b) (mul u v))
  = mul4 a u b v

let peq_scale (#m: pos) (a b: elem m) (u v: pt m)
  : Lemma (requires peq u v) (ensures peq (scale a u) (scale b v))
  = let (x1, y1, z1) = u in
    let (x2, y2, z2) = v in
    let one_pair (s t s' t': elem m)
      : Lemma (requires mul s t' == mul s' t)
              (ensures mul (mul a s) (mul b t') == mul (mul b s') (mul a t))
      = mul4 a s b t'; mul4 b s' a t; mul_comm a b
    in
    one_pair x1 y1 x2 y2; one_pair x1 z1 x2 z2; one_pair y1 z1 y2 z2

let scale_one (#m: pos { 1 < m }) (p: pt m) : Lemma (scale one p == p) =
  let (x, y, z) = p in
  mul_comm one x; mul_one x; mul_comm one y; mul_one y; mul_comm one z; mul_one z

let peq_scale_l (#m: pos { 1 < m }) (a: elem m) (p: pt m)
  : Lemma (peq (scale a p) p)
  = peq_refl p; peq_scale a one p p; scale_one p

let peq_scale_r (#m: pos { 1 < m }) (a: elem m) (p: pt m)
  : Lemma (peq p (scale a p))
  = peq_scale_l a p

let scale_nz (#m: prime_mod) (k: elem m) (p: pt m)
  : Lemma (requires k <> 0 /\ nz p) (ensures nz (scale k p))
  = let (x, y, z) = p in
    if x <> 0 then mul_nonzero k x
    else if y <> 0 then mul_nonzero k y
    else mul_nonzero k z

let scale_scale (#m: pos) (a b: elem m) (p: pt m)
  : Lemma (scale a (scale b p) == scale (mul a b) p)
  = let (x, y, z) = p in mul_assoc a b x; mul_assoc a b y; mul_assoc a b z

(** {2 Transitivity through a nonzero middle} *)

let coord (#m: pos) (p: pt m) (i: nat { i < 3 }) : elem m =
  let (x, y, z) = p in if i = 0 then x else if i = 1 then y else z

let rel (#m: pos) (p q: pt m) : prop =
  forall (i j: (k: nat { k < 3 })). mul (coord p i) (coord q j) == mul (coord q i) (coord p j)

let peq_rel (#m: pos) (p q: pt m) : Lemma (requires peq p q) (ensures rel p q) =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in
  mul_comm x1 x2; mul_comm y1 y2; mul_comm z1 z2

let rel_peq (#m: pos) (p q: pt m) : Lemma (requires rel p q) (ensures peq p q) =
  assert (mul (coord p 0) (coord q 1) == mul (coord q 0) (coord p 1));
  assert (mul (coord p 0) (coord q 2) == mul (coord q 0) (coord p 2));
  assert (mul (coord p 1) (coord q 2) == mul (coord q 1) (coord p 2))

let tri (#m: prime_mod) (pi pj pk qi qj qk ri rj rk: elem m)
  : Lemma (requires qk <> 0 /\
                    mul pi qk == mul qi pk /\ mul pj qk == mul qj pk /\
                    mul qi rk == mul ri qk /\ mul qj rk == mul rj qk)
          (ensures mul pi rj == mul ri pj)
  = let k2 = mul qk qk in
    mul_nonzero qk qk;
    calc (==) {
      mul (mul pi rj) k2;
      == { mul4 pi rj qk qk }
      mul (mul pi qk) (mul rj qk);
      == { }
      mul (mul qi pk) (mul qj rk);
      == { mul4 qi pk qj rk }
      mul (mul qi qj) (mul pk rk);
      == { mul_comm pk rk }
      mul (mul qi qj) (mul rk pk);
      == { mul4 qi rk qj pk }
      mul (mul qi rk) (mul qj pk);
      == { }
      mul (mul ri qk) (mul pj qk);
      == { mul4 ri qk pj qk }
      mul (mul ri pj) k2;
    };
    cancel (mul pi rj) (mul ri pj) k2

let peq_trans (#m: prime_mod) (p q r: pt m)
  : Lemma (requires nz q /\ peq p q /\ peq q r) (ensures peq p r)
  = peq_rel p q; peq_rel q r;
    let k : (k: nat { k < 3 }) =
      if coord q 0 <> 0 then 0 else if coord q 1 <> 0 then 1 else 2 in
    let aux (i j: (k: nat { k < 3 }))
      : Lemma (mul (coord p i) (coord r j) == mul (coord r i) (coord p j))
      = tri (coord p i) (coord p j) (coord p k) (coord q i) (coord q j) (coord q k)
            (coord r i) (coord r j) (coord r k)
    in
    FStar.Classical.forall_intro_2 aux;
    rel_peq p r

(** {2 The canonical representative}

    [(x/z, y/z, 1)], or [(0, 1, 0)] at infinity.  [inf_shape p] is what a
    curve equation gives at [z = 0]. *)

let inf_shape (#m: pos) (p: pt m) : prop =
  let (x, y, z) = p in z == 0 ==> x == 0 /\ y <> 0

let canon (#m: prime_mod) (p: pt m) : pt m =
  let (x, y, z) = p in
  if z = 0 then (0, one, 0) else (mul x (inv z), mul y (inv z), one)

let ck (#m: pos) (p: pt m) : elem m =
  let (_, y, z) = p in if z = 0 then y else z

let canon_scale (#m: prime_mod) (p: pt m)
  : Lemma (requires inf_shape p) (ensures ck p <> 0 /\ p == scale (ck p) (canon p))
  = let (x, y, z) = p in
    if z = 0 then begin mul_one y; mul_zero y end
    else begin
      div_mul x z; mul_comm (mul x (inv z)) z;
      div_mul y z; mul_comm (mul y (inv z)) z;
      mul_one z
    end

let div_eq (#m: prime_mod) (a b c d: elem m)
  : Lemma (requires b <> 0 /\ d <> 0 /\ mul a d == mul c b)
          (ensures mul a (inv b) == mul c (inv d))
  = let bd = mul b d in
    mul_nonzero b d;
    calc (==) {
      mul (mul a (inv b)) bd;
      == { mul_assoc (mul a (inv b)) b d }
      mul (mul (mul a (inv b)) b) d;
      == { div_mul a b }
      mul a d;
      == { }
      mul c b;
      == { div_mul c d }
      mul (mul (mul c (inv d)) d) b;
      == { mul_assoc (mul c (inv d)) d b }
      mul (mul c (inv d)) (mul d b);
      == { mul_comm d b }
      mul (mul c (inv d)) bd;
    };
    cancel (mul a (inv b)) (mul c (inv d)) bd

let canon_peq (#m: prime_mod) (p q: pt m)
  : Lemma (requires inf_shape p /\ inf_shape q /\ peq p q) (ensures canon p == canon q)
  = let (x1, y1, z1) = p in
    let (x2, y2, z2) = q in
    if z1 = 0 then begin
      mul_zero y2;
      if z2 <> 0 then mul_nonzero y1 z2
    end
    else if z2 = 0 then begin
      mul_zero y1;
      mul_nonzero y2 z1
    end
    else begin
      mul_comm x2 z1; div_eq x1 z1 x2 z2;
      mul_comm y2 z1; div_eq y1 z1 y2 z2
    end

let canon_inf (#m: prime_mod) (p: pt m)
  : Lemma (let (_, _, z) = p in let (_, _, z') = canon p in (z' == 0 <==> z == 0))
  = ()
