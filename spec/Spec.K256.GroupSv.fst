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

(** The secp256k1 formulas as polynomial computations ({!Spec.Group.Poly}),
    and the lemmas that say they compute the specification's values. *)
module Spec.K256.GroupSv

open Spec.Group.Poly
open Spec.Group.Check
module P = Spec.K256
module MA = Spec.ModArith

(** The modulus and [b] as plain literals; see {!Spec.Group.Poly.ctx}. *)
let m0 : pos = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

irreducible let m0_lem () : Lemma (m0 == P.prime) = assert_norm (m0 == P.prime)

let bl : nat = 7

let bl_lem () : Lemma (bl < m0 /\ bl == P.b_coeff) = m0_lem (); assert_norm (bl == P.b_coeff)

(** [3 b], the only curve constant the formulas use. *)
let b3l : nat = 21

let b3_lem () : Lemma (b3l < m0 /\ b3l == P.b3) = m0_lem (); assert_norm (b3l == P.b3)

let prime_m0 () : Lemma (FStar.Math.Euclid.is_prime m0) =
  m0_lem (); Spec.Group.Primes.prime_k256 ()

let fl : nat = 40

type sp (c: ctx) = sv c & sv c & sv c

[@@"opaque_to_smt"]
let point_add_sv (#c: ctx) (b: sv c) (p q: sp c) : sp c =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in
  let t0 = smul x1 x2 in
  let t1 = smul y1 y2 in
  let t2 = smul z1 z2 in
  let t3 = sadd x1 y1 in
  let t4 = sadd x2 y2 in
  let t3 = smul t3 t4 in
  let t4 = sadd t0 t1 in
  let t3 = ssub t3 t4 in
  let t4 = sadd y1 z1 in
  let x3 = sadd y2 z2 in
  let t4 = smul t4 x3 in
  let x3 = sadd t1 t2 in
  let t4 = ssub t4 x3 in
  let x3 = sadd x1 z1 in
  let y3 = sadd x2 z2 in
  let x3 = smul x3 y3 in
  let y3 = sadd t0 t2 in
  let y3 = ssub x3 y3 in
  let x3 = sadd t0 t0 in
  let t0 = sadd x3 t0 in
  let t2 = smul b t2 in
  let z3 = sadd t1 t2 in
  let t1 = ssub t1 t2 in
  let y3 = smul b y3 in
  let x3 = smul t4 y3 in
  let t2 = smul t3 t1 in
  let x3 = ssub t2 x3 in
  let y3 = smul y3 t0 in
  let t1 = smul t1 z3 in
  let y3 = sadd t1 y3 in
  let t0 = smul t0 t3 in
  let z3 = smul z3 t4 in
  let z3 = sadd z3 t0 in
  (x3, y3, z3)


[@@"opaque_to_smt"]
let point_double_sv (#c: ctx) (b: sv c) (p: sp c) : sp c =
  let (x, y, z) = p in
  let t0 = smul y y in
  let z3 = sadd t0 t0 in
  let z3 = sadd z3 z3 in
  let z3 = sadd z3 z3 in
  let t1 = smul y z in
  let t2 = smul z z in
  let t2 = smul b t2 in
  let x3 = smul t2 z3 in
  let y3 = sadd t0 t2 in
  let z3 = smul t1 z3 in
  let t1 = sadd t2 t2 in
  let t2 = sadd t1 t2 in
  let t0 = ssub t0 t2 in
  let y3 = smul t0 y3 in
  let y3 = sadd x3 y3 in
  let t1 = smul x y in
  let x3 = smul t0 t1 in
  let x3 = sadd x3 x3 in
  (x3, y3, z3)

let tof (x: elem m0) : P.felem = m0_lem (); x
let fromf (x: P.felem) : elem m0 = m0_lem (); x

let o : fops m0 =
  m0_lem ();
  { add = (fun x y -> P.fadd x y); sub = (fun x y -> P.fsub x y); mul = (fun x y -> P.fmul x y) }

let o_eqs () : Lemma ((forall (x y: elem m0). o.add x y == P.fadd (tof x) (tof y)) /\
                      (forall (x y: elem m0). o.sub x y == P.fsub (tof x) (tof y)) /\
                      (forall (x y: elem m0). o.mul x y == P.fmul (tof x) (tof y)) /\
                      (forall (x: elem m0). fromf (tof x) == x) /\
                      (forall (x: P.felem). tof (fromf x) == x)) = m0_lem ()

let o_ok () : Lemma (fops_ok o) =
  m0_lem ();
  let aux (x y: elem m0) : Lemma (o.sub x y == (x - y) % m0) =
    FStar.Math.Lemmas.lemma_mod_plus (x - y) 1 m0 in
  FStar.Classical.forall_intro_2 aux

let tof3 (#c: ctx { c.m == m0 }) (p: sp c) : P.proj_point =
  let (x, y, z) = p in (tof (vl x), tof (vl y), tof (vl z))

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
let point_add_val (c: ctx { c.m == m0 }) (b: sv c) (p q: sp c)
  : Lemma (requires ok c /\ c.o == o /\ vl b == b3l)
          (ensures tof3 (point_add_sv b p q) == P.point_add (tof3 p) (tof3 q))
  = m0_lem (); b3_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%P.point_add) P.point_add;
    FStar.Pervasives.reveal_opaque (`%point_add_sv) (point_add_sv #c)

let point_double_val (c: ctx { c.m == m0 }) (b: sv c) (p: sp c)
  : Lemma (requires ok c /\ c.o == o /\ vl b == b3l)
          (ensures tof3 (point_double_sv b p) == P.point_double (tof3 p))
  = m0_lem (); b3_lem (); o_eqs ();
    FStar.Pervasives.reveal_opaque (`%P.point_double) P.point_double;
    FStar.Pervasives.reveal_opaque (`%point_double_sv) (point_double_sv #c)
#pop-options

(** Environments: the [i]th variable of a literal list. *)
#push-options "--fuel 9 --ifuel 0"
let env1 (#m: pos) (a: elem m) : Lemma (let l = [a] in nth0 0 l 0 == a) = ()
let env2 (#m: pos) (a b: elem m) : Lemma (let l = [a; b] in nth0 0 l 0 == a /\ nth0 0 l 1 == b) = ()
let env3 (#m: pos) (a b c: elem m) : Lemma (let l = [a; b; c] in nth0 0 l 0 == a /\ nth0 0 l 1 == b /\ nth0 0 l 2 == c) = ()
let env4 (#m: pos) (a b c d: elem m) : Lemma (let l = [a; b; c; d] in nth0 0 l 0 == a /\ nth0 0 l 1 == b /\ nth0 0 l 2 == c /\ nth0 0 l 3 == d) = ()
let env5 (#m: pos) (a b c d e: elem m) : Lemma (let l = [a; b; c; d; e] in nth0 0 l 0 == a /\ nth0 0 l 1 == b /\ nth0 0 l 2 == c /\ nth0 0 l 3 == d /\ nth0 0 l 4 == e) = ()
let env6 (#m: pos) (a b c d e f: elem m) : Lemma (let l = [a; b; c; d; e; f] in nth0 0 l 0 == a /\ nth0 0 l 1 == b /\ nth0 0 l 2 == c /\ nth0 0 l 3 == d /\ nth0 0 l 4 == e /\ nth0 0 l 5 == f) = ()
let env7 (#m: pos) (a b c d e f g: elem m) : Lemma (let l = [a; b; c; d; e; f; g] in nth0 0 l 0 == a /\ nth0 0 l 1 == b /\ nth0 0 l 2 == c /\ nth0 0 l 3 == d /\ nth0 0 l 4 == e /\ nth0 0 l 5 == f /\ nth0 0 l 6 == g) = ()
let env8 (#m: pos) (a b c d e f g h: elem m) : Lemma (let l = [a; b; c; d; e; f; g; h] in nth0 0 l 0 == a /\ nth0 0 l 1 == b /\ nth0 0 l 2 == c /\ nth0 0 l 3 == d /\ nth0 0 l 4 == e /\ nth0 0 l 5 == f /\ nth0 0 l 6 == g /\ nth0 0 l 7 == h) = ()
#pop-options

(** The same facts read through [tof], for an environment built with
    [fromf]. *)
#push-options "--fuel 9 --ifuel 0"
let envf1 (c: ctx) (x0: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0]) (ensures tof (nth0 0 c.env 0) == x0) =
  o_eqs ()
let envf2 (c: ctx) (x0 x1: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1) =
  o_eqs ()
let envf3 (c: ctx) (x0 x1 x2: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1; fromf x2]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1 /\ tof (nth0 0 c.env 2) == x2) =
  o_eqs ()
let envf4 (c: ctx) (x0 x1 x2 x3: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1; fromf x2; fromf x3]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1 /\ tof (nth0 0 c.env 2) == x2 /\ tof (nth0 0 c.env 3) == x3) =
  o_eqs ()
let envf5 (c: ctx) (x0 x1 x2 x3 x4: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1; fromf x2; fromf x3; fromf x4]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1 /\ tof (nth0 0 c.env 2) == x2 /\ tof (nth0 0 c.env 3) == x3 /\ tof (nth0 0 c.env 4) == x4) =
  o_eqs ()
let envf6 (c: ctx) (x0 x1 x2 x3 x4 x5: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1; fromf x2; fromf x3; fromf x4; fromf x5]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1 /\ tof (nth0 0 c.env 2) == x2 /\ tof (nth0 0 c.env 3) == x3 /\ tof (nth0 0 c.env 4) == x4 /\ tof (nth0 0 c.env 5) == x5) =
  o_eqs ()
let envf7 (c: ctx) (x0 x1 x2 x3 x4 x5 x6: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1; fromf x2; fromf x3; fromf x4; fromf x5; fromf x6]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1 /\ tof (nth0 0 c.env 2) == x2 /\ tof (nth0 0 c.env 3) == x3 /\ tof (nth0 0 c.env 4) == x4 /\ tof (nth0 0 c.env 5) == x5 /\ tof (nth0 0 c.env 6) == x6) =
  o_eqs ()
let envf8 (c: ctx) (x0 x1 x2 x3 x4 x5 x6 x7: P.felem)
  : Lemma (requires c.m == m0 /\ c.env == [fromf x0; fromf x1; fromf x2; fromf x3; fromf x4; fromf x5; fromf x6; fromf x7]) (ensures tof (nth0 0 c.env 0) == x0 /\ tof (nth0 0 c.env 1) == x1 /\ tof (nth0 0 c.env 2) == x2 /\ tof (nth0 0 c.env 3) == x3 /\ tof (nth0 0 c.env 4) == x4 /\ tof (nth0 0 c.env 5) == x5 /\ tof (nth0 0 c.env 6) == x6 /\ tof (nth0 0 c.env 7) == x7) =
  o_eqs ()
#pop-options

(** {2 Constants, the curve, and hypotheses} *)

let kc (c: ctx) (v: nat) : sv c = sconst c (v % c.m)

let cst (v: nat) : P.felem = tof (v % m0)

(** [x^3 + 7], the right-hand side of the affine equation. *)
[@@"opaque_to_smt"]
let crv (c: ctx) (x: sv c) : sv c =
  sadd (smul (smul x x) x) (kc c bl)

[@@"opaque_to_smt"]
let ff (x: P.felem) : P.felem =
  P.fadd (P.fmul (P.fmul x x) x) (cst bl)

(** The homogeneous equation, both sides, exactly as in [Spec.K256.Group]. *)
[@@"opaque_to_smt"]
let eqn_l (p: P.proj_point) : P.felem =
  let (x, y, z) = p in P.fmul (P.fmul y y) z

[@@"opaque_to_smt"]
let eqn_r (p: P.proj_point) : P.felem =
  let (x, y, z) = p in
  P.fadd (P.fmul (P.fmul x x) x) (P.fmul P.b_coeff (P.fmul (P.fmul z z) z))

(** Opaque forms of the two curve predicates, so that the solver never sees
    the field arithmetic inside them unless asked to. *)
[@@"opaque_to_smt"]
let on (x y: P.felem) : prop = P.is_on_curve x y

[@@"opaque_to_smt"]
let heq (p: P.proj_point) : prop = eqn_l p == eqn_r p

[@@"opaque_to_smt"]
let eqn_lsv (#c: ctx) (p: sp c) : sv c =
  let (x, y, z) = p in smul (smul y y) z

[@@"opaque_to_smt"]
let eqn_rsv (#c: ctx) (p: sp c) : sv c =
  let (x, y, z) = p in
  sadd (smul (smul x x) x) (smul (kc c bl) (smul (smul z z) z))

[@@"opaque_to_smt"]
let aff_hyp (c: ctx) (i j: (k: nat { k < c.nv })) : hyp c =
  (smul (svar c j) (svar c j), crv c (svar c i))

[@@"opaque_to_smt"]
let hom_hyp (c: ctx) (i j k: (k: nat { k < c.nv })) : hyp c =
  let p = (svar c i, svar c j, svar c k) in (eqn_lsv p, eqn_rsv p)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let crv_val (c: ctx) (x: sv c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o) (ensures tof (vl (crv c x)) == ff (tof (vl x)))
  = o_eqs ();
    FStar.Pervasives.reveal_opaque (`%crv) crv;
    FStar.Pervasives.reveal_opaque (`%ff) ff

let eqn_val (c: ctx) (p: sp c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o)
          (ensures tof (vl (eqn_lsv p)) == eqn_l (tof3 p) /\ tof (vl (eqn_rsv p)) == eqn_r (tof3 p))
  = o_eqs (); bl_lem (); m0_lem ();
    FStar.Pervasives.reveal_opaque (`%eqn_lsv) (eqn_lsv #c);
    FStar.Pervasives.reveal_opaque (`%eqn_rsv) (eqn_rsv #c);
    FStar.Pervasives.reveal_opaque (`%eqn_l) eqn_l;
    FStar.Pervasives.reveal_opaque (`%eqn_r) eqn_r;
    assert_norm (1 % m0 == 1)

let cst_lem () : Lemma (cst 3 == 3 /\ cst bl == P.b_coeff /\ cst 1 == P.fone /\ cst 0 == 0) =
  m0_lem (); bl_lem ();
  assert_norm (3 % m0 == 3); assert_norm (1 % m0 == 1); assert_norm (0 % m0 == 0)

let on_ff (x y: P.felem) : Lemma (requires on x y) (ensures P.fmul y y == ff x) =
  cst_lem ();
  FStar.Pervasives.reveal_opaque (`%on) on;
  FStar.Pervasives.reveal_opaque (`%ff) ff

let aff_hyp_ok (c: ctx) (i j: (k: nat { k < c.nv }))
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o /\
                    on (tof (nth0 0 c.env i)) (tof (nth0 0 c.env j)))
          (ensures vl (fst (aff_hyp c i j)) == vl (snd (aff_hyp c i j)))
  = o_eqs ();
    FStar.Pervasives.reveal_opaque (`%aff_hyp) aff_hyp;
    on_ff (tof (nth0 0 c.env i)) (tof (nth0 0 c.env j));
    crv_val c (svar c i)

let hom_hyp_ok (c: ctx) (i j k: (k: nat { k < c.nv }))
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o /\
                    heq (tof (nth0 0 c.env i), tof (nth0 0 c.env j), tof (nth0 0 c.env k)))
          (ensures vl (fst (hom_hyp c i j k)) == vl (snd (hom_hyp c i j k)))
  = o_eqs ();
    FStar.Pervasives.reveal_opaque (`%hom_hyp) hom_hyp;
    FStar.Pervasives.reveal_opaque (`%heq) heq;
    eqn_val c (svar c i, svar c j, svar c k)
#pop-options

let cst_small (v: nat) : Lemma (requires v < m0) (ensures cst v == v) =
  m0_lem (); FStar.Math.Lemmas.small_mod v m0

let fneg_lem () : Lemma (forall (y: P.felem). P.fneg y == P.fsub P.fzero y) = ()

(** {2 Points built from the environment} *)

let aff (#c: ctx) (i j: (k: nat { k < c.nv })) : sp c = (svar c i, svar c j, kc c 1)

let var3 (#c: ctx) (i j k: (k: nat { k < c.nv })) : sp c = (svar c i, svar c j, svar c k)

let sinf (c: ctx) : sp c = (kc c 0, kc c 1, kc c 0)

let ksc (#c: ctx) (s: sv c) (p: sp c) : sp c =
  let (x, y, z) = p in (smul s x, smul s y, smul s z)

let sneg (#c: ctx) (p: sp c) : sp c =
  let (x, y, z) = p in (x, ssub (kc c 0) y, z)

let env_at (c: ctx { c.m == m0 }) (i: nat) : P.felem = tof (nth0 0 c.env i)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let aff_val (c: ctx) (i j: (k: nat { k < c.nv }))
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o)
          (ensures tof3 (aff #c i j) == (env_at c i, env_at c j, P.fone))
  = cst_lem (); m0_lem (); assert_norm (1 % m0 == 1)

let var3_val (c: ctx) (i j k: (k: nat { k < c.nv }))
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o)
          (ensures tof3 (var3 #c i j k) == (env_at c i, env_at c j, env_at c k))
  = ()

let sinf_val (c: ctx)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o)
          (ensures tof3 (sinf c) == P.point_at_infinity)
  = cst_lem (); m0_lem (); assert_norm (1 % m0 == 1); assert_norm (0 % m0 == 0)

let ksc_val (c: ctx) (s: sv c) (p: sp c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o)
          (ensures tof3 (ksc s p) == Spec.Group.Proj.scale #P.prime (tof (vl s)) (tof3 p))
  = o_eqs ()

let sneg_val (c: ctx) (p: sp c)
  : Lemma (requires ok c /\ c.m == m0 /\ c.o == o)
          (ensures tof3 (sneg p) == P.point_negate (tof3 p))
  = o_eqs (); cst_lem (); m0_lem (); assert_norm (0 % m0 == 0)

let kc_val (c: ctx) (v: nat)
  : Lemma (requires c.m == m0) (ensures tof (vl (kc c v)) == cst v)
  = ()
#pop-options

(** A polynomial given as a list of (coefficient, exponent vector) terms. *)
let rec smon (#c: ctx) (i: nat) (es: list nat) : Tot (sv c) (decreases es) =
  match es with
  | [] -> kc c 1
  | e :: r -> if i < c.nv then smul (spow (svar c i) e) (smon (i + 1) r) else kc c 1

let rec spoly (#c: ctx) (ts: list (nat & list nat)) : Tot (sv c) (decreases ts) =
  match ts with
  | [] -> kc c 0
  | (k, es) :: r -> sadd (smul (kc c k) (smon 0 es)) (spoly r)
