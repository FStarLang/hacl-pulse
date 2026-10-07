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

(** Two polynomials without roots in the secp256k1 field.

    [f = x^3 + 7]: a root would be a point of order two, and the group has
    odd prime order.  [q = x^6 + 140 x^3 - 392] is what the second
    coordinate of [point_add P (-P)] reduces to on an affine point; it is
    irreducible over the field.  Both are certified by
    {!Spec.Group.Check.nr_check}, with cofactors computed by PARI/GP. *)
module Spec.K256.GroupNR

open Spec.Group.Poly
open Spec.Group.Check
open Spec.K256.GroupSv
module P = Spec.K256

let qb (c: ctx) (x: sv c) : sv c =
  let x3 = smul (smul x x) x in
  sadd (sadd (smul x3 x3) (smul (kc c 140) x3)) (kc c 115792089237316195423570985008687907853269984665640564039457584007908834671271)

let fq (x: P.felem) : P.felem =
  let x3 = P.fmul (P.fmul x x) x in
  P.fadd (P.fadd (P.fmul x3 x3) (P.fmul (cst 140) x3)) (cst 115792089237316195423570985008687907853269984665640564039457584007908834671271)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let qb_val (c: ctx) (x: sv c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o) (ensures tof (vl (qb c x)) == fq (tof (vl x)))
  = o_eqs ()
#pop-options

let uf : list nat = [0; 0; 46758632835564736012269203954919337884311706168562511263687580192619680188360]
let uq : list nat = [0; 0; 95759930878925550389862433258728329785182363458630619644079867686454730649882; 0; 0; 111244439360252908099111608111787426390337830471608360441708511948622550931786]

let nr_f_ok (o': fops m0) (x: elem m0) : Lemma (nr_check m0 fl o' x 3 crv uf == true) =
  assert (nr_check m0 fl o' x 3 crv uf == true) by (poly_tac ())

let nr_q_ok (o': fops m0) (x: elem m0) : Lemma (nr_check m0 fl o' x 6 qb uq == true) =
  assert (nr_check m0 fl o' x 6 qb uq == true) by (poly_tac ())

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let no_root_f (x: P.felem) : Lemma (ff x <> 0) =
  prime_m0 (); o_ok (); o_eqs ();
  nr_f_ok o (fromf x);
  nr_sound m0 fl o (fromf x) 3 crv uf;
  let c0 = base m0 fl o 1 [fromf x] in
  base_ok m0 fl o 1 [fromf x];
  crv_val c0 (svar c0 0);
  m0_lem ()

let no_root_q (x: P.felem) : Lemma (fq x <> 0) =
  prime_m0 (); o_ok (); o_eqs ();
  nr_q_ok o (fromf x);
  nr_sound m0 fl o (fromf x) 6 qb uq;
  let c0 = base m0 fl o 1 [fromf x] in
  base_ok m0 fl o 1 [fromf x];
  qb_val c0 (svar c0 0);
  m0_lem ()
#pop-options
