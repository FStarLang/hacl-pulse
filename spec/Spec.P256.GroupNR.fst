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

(** Two polynomials without roots in the P-256 field.

    [f = x^3 - 3x + b]: a root would be a point of order two, and the group
    has odd prime order.  [q], of degree six, is what the second coordinate
    of [point_add P (-P)] is, exactly; it is irreducible over
    the field.  Both are certified by {!Spec.Group.Check.nr_check}, with
    cofactors computed by PARI/GP. *)
module Spec.P256.GroupNR

open Spec.Group.Poly
open Spec.Group.Check
open Spec.P256.GroupSv
module P = Spec.P256

let qb (c: ctx) (x: sv c) : sv c =
  let x2 = smul x x in
  let x3 = smul x2 x in
  let x4 = smul x2 x2 in
  let x6 = smul x3 x3 in
  let a = ssub x6 (smul (kc c 15) x4) in
  let a = sadd a (smul (kc c 10622650030549101247640466955092353471685816412842311727969707118719663048163) x3) in
  let a = ssub a (smul (kc c 45) x2) in
  let a = sadd a (smul (kc c 29532007860400710501123769562936926789028718530763449875888550533005217399688) x) in
  sadd a (kc c 28747437706978602492028166966294636210670171337568925265845792751086019754239)

let fq (x: P.felem) : P.felem =
  let x2 = P.fmul x x in
  let x3 = P.fmul x2 x in
  let x4 = P.fmul x2 x2 in
  let x6 = P.fmul x3 x3 in
  let a = P.fsub x6 (P.fmul (cst 15) x4) in
  let a = P.fadd a (P.fmul (cst 10622650030549101247640466955092353471685816412842311727969707118719663048163) x3) in
  let a = P.fsub a (P.fmul (cst 45) x2) in
  let a = P.fadd a (P.fmul (cst 29532007860400710501123769562936926789028718530763449875888550533005217399688) x) in
  P.fadd a (cst 28747437706978602492028166966294636210670171337568925265845792751086019754239)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let qb_val (c: ctx) (x: sv c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o) (ensures tof (vl (qb c x)) == fq (tof (vl x)))
  = o_eqs ()
#pop-options

let uf : list nat = [76626890310466861426869089647039036757962535851890885406097439786770458211455; 74462945259064871768191128030512052509059297803194871526163573358218695456204; 34768139465301476436978405170953382516735956999154666452188405812258086013549]
let uq : list nat = [34081389460349755637570387489731476564305015019617941761895829315393738938451; 103124018306319470466439401804704059410403956645056551119019170840060565270143; 79259366179838561116925513329592681209010024427845720844126713678907740194971; 42463712000367483156112096693308175070022290971724142032131133861046655991061; 68038687054849555575283879273459980646839732038751103941580990653459302112873; 8153895769741980894488240254102945788750716952050545993435202203031872638599]

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
