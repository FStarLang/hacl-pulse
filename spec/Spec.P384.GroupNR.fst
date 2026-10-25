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

(** Two polynomials without roots in the P-384 field.

    [f = x^3 - 3x + b]: a root would be a point of order two, and the group
    has odd prime order.  [q], of degree six, is what the second coordinate
    of [point_add P (-P)] is, exactly; it is irreducible over
    the field.  Both are certified by {!Spec.Group.Check.nr_check}, with
    cofactors computed by PARI/GP. *)
module Spec.P384.GroupNR

open Spec.Group.Poly
open Spec.Group.Check
open Spec.P384.GroupSv
module P = Spec.P384

let qb (c: ctx) (x: sv c) : sv c =
  let x2 = smul x x in
  let x3 = smul x2 x in
  let x4 = smul x2 x2 in
  let x6 = smul x3 x3 in
  let a = ssub x6 (smul (kc c 15) x4) in
  let a = sadd a (smul (kc c 39377790646065887797352715505913982395101506611180563745246331784579401796737903025110756150308708131107904574151353) x3) in
  let a = ssub a (smul (kc c 45) x2) in
  let a = sadd a (smul (kc c 15746273148360636835955821283519666676044956112615248913558140389898496723743367749257000472533437278292421349868348) x) in
  sadd a (kc c 17491137107057838905042223302548988768914945235434904230308776635682120207286522300929492604501718300740608221931506)

let fq (x: P.felem) : P.felem =
  let x2 = P.fmul x x in
  let x3 = P.fmul x2 x in
  let x4 = P.fmul x2 x2 in
  let x6 = P.fmul x3 x3 in
  let a = P.fsub x6 (P.fmul (cst 15) x4) in
  let a = P.fadd a (P.fmul (cst 39377790646065887797352715505913982395101506611180563745246331784579401796737903025110756150308708131107904574151353) x3) in
  let a = P.fsub a (P.fmul (cst 45) x2) in
  let a = P.fadd a (P.fmul (cst 15746273148360636835955821283519666676044956112615248913558140389898496723743367749257000472533437278292421349868348) x) in
  P.fadd a (cst 17491137107057838905042223302548988768914945235434904230308776635682120207286522300929492604501718300740608221931506)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let qb_val (c: ctx) (x: sv c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o) (ensures tof (vl (qb c x)) == fq (tof (vl x)))
  = o_eqs ()
#pop-options

let uf : list nat = [23037766613497683937702734290281044719364893268180251583910224888989381657771069200037813904257325918671976092329602; 8235438212423615602427778915669574859600037698862346933589434399495169446996583974901273360826717582835190849638831; 12157362177932134139146813183752135342286725243554133716818896354380897714709611791313184492360272402950851405460538]
let uq : list nat = [28511182613371697707862950000401666607008623861251115306508998628949298205466702043860849873776852679804370593234462; 35383445838839751979251758214834134150126009014789867749392164888792186367498623884145101743927205245057061787658898; 12057566752493692731776596830136332143968432865511942644640305893619294582571308479282919116170218808876910955413898; 26407034048701769759078146494476507720579600692432968039758596972313244834255880785223854028876229503295700620890078; 38603878058663335800714983222466482098739517071872238168240192856823298267866757597970222728578498964868358690322363; 14635504023522280956681494488410149646823056560193859248732984383674680386111414756614751676238753595869135119135468]

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
