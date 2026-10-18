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

(** The base point has order [q], and what follows from it.

    A signature's [S] is reduced mod [q], so the verifier's [[S]B] is
    [[r + k a]B] only if multiples of [B] are blind to multiples of [q].
    This module proves [[q]B = O] ({!base_order}) and from it
    [[n]B = [n mod q]B] for every [n] ({!smul_mod_q}).

    {2 [[q]B = O]}

    [q] is a 253-bit constant and [B] a concrete point, so the multiple is
    a closed term: the abstract double-and-add ladder of
    {!Spec.Group.Smul.ladder_at}, run over 253 bits of [q] at the
    Edwards25519 instance, is evaluated by the normaliser -- 253 doublings
    and about as many additions on concrete field elements, a few seconds --
    and {!Spec.Group.Smul.ladder_is_smul} says that what it computed is
    [smul q g].

    {2 Reducing scalars}

    The rest is generic, over any {!Spec.Group.Smul.grp}: multiples of the
    identity are the identity, [[m]([n]P) = [mn]P], and so if [[n]P = O]
    then [[k]P = [k mod n]P], by splitting [k = (k / n) n + k mod n]. *)
module Spec.Ed25519.Order

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module Loops = Hacl.Spec.Loops
module M = FStar.Math.Lemmas

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

(** {2 Over any group} *)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"

let rec smul_of_zero (#a: Type) (g: G.grp a) (n: nat)
  : Lemma (ensures g.ok (G.smul g n g.zero) /\ g.eqv (G.smul g n g.zero) g.zero)
          (decreases n)
  = g.ok_zero ();
    if n = 0 then g.eqv_refl g.zero
    else begin
      let s = G.smul g (n - 1) g.zero in
      smul_of_zero g (n - 1);
      g.add_id s;
      g.ok_add g.zero s;
      g.eqv_trans (g.add g.zero s) s g.zero
    end

let rec smul_mul (#a: Type) (g: G.grp a) (m n: nat) (p: a)
  : Lemma (requires g.ok p)
          (ensures g.ok (G.smul g m (G.smul g n p)) /\
                   g.eqv (G.smul g m (G.smul g n p)) (G.smul g (m * n) p))
          (decreases m)
  = let q = G.smul g n p in
    G.smul_ok g n p;
    G.smul_ok g m q;
    if m = 0 then (g.ok_zero (); g.eqv_refl g.zero)
    else begin
      smul_mul g (m - 1) n p;
      G.smul_ok g (m - 1) q;
      g.eqv_refl q;
      G.smul_add_congr g n ((m - 1) * n) p q (G.smul g (m - 1) q);
      M.distributivity_sub_left m 1 n
    end

let smul_mod (#a: Type) (g: G.grp a) (n: pos) (k: nat) (p: a)
  : Lemma (requires g.ok p /\ g.eqv (G.smul g n p) g.zero)
          (ensures g.eqv (G.smul g k p) (G.smul g (k % n) p))
  = let t = k / n in
    let r = k % n in
    M.euclidean_division_definition k n;
    let st = G.smul g (t * n) p in
    let sr = G.smul g r p in
    let z = g.zero in
    g.ok_zero ();
    G.smul_ok g k p; G.smul_ok g n p; G.smul_ok g (t * n) p; G.smul_ok g r p;
    (* [[tn]P ~ [t]([n]P) ~ [t]O ~ O] *)
    smul_mul g t n p;
    G.smul_congr g t (G.smul g n p) z;
    smul_of_zero g t;
    G.smul_ok g t z;
    g.eqv_sym (G.smul g t (G.smul g n p)) st;
    g.eqv_trans st (G.smul g t (G.smul g n p)) (G.smul g t z);
    g.eqv_trans st (G.smul g t z) z;
    (* [[k]P ~ [tn]P + [r]P ~ O + [r]P ~ [r]P] *)
    G.smul_add g (t * n) r p;
    g.eqv_refl sr;
    g.add_congr st z sr sr;
    g.ok_add st sr; g.ok_add z sr;
    g.add_id sr;
    g.eqv_trans (G.smul g k p) (g.add st sr) (g.add z sr);
    g.eqv_trans (G.smul g k p) (g.add z sr) sr

#pop-options

(** {2 At the base point} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let ladder_q () : GTot ext_point = Loops.repeati_g 253 (G.ladder_at SM.eg 253 q g) SM.eg.G.zero

let base_order (_: unit)
  : Lemma (on_curve g /\ point_equal (SM.smul q g) point_at_infinity)
  = assert_norm (point_equal (ladder_q ()) point_at_infinity);
    assert_norm (q < pow2 253);
    g_on_curve ();
    G.ladder_is_smul SM.eg 253 q g;
    SM.smul_ok q g;
    point_at_infinity_on_curve ();
    point_equal_sym (ladder_q ()) (SM.smul q g);
    point_equal_trans (SM.smul q g) (ladder_q ()) point_at_infinity

let smul_mod_q (k: nat)
  : Lemma (point_equal (SM.smul k g) (SM.smul (k % q) g))
  = base_order ();
    smul_mod SM.eg q k g

#pop-options
