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

(** Plumbing shared by the curve checks: contexts whose rules come from
    hypotheses, powers, and a certificate that a polynomial has no root in
    a prime field.

    A hypothesis is a pair of [sv]s, the first a single monomial, whose
    values are equal.  {!with_hyps} turns a list of them into rewrite rules,
    and {!hyps_ok} shows that the rules hold wherever the hypotheses do.
    The shape of each left-hand side is a property of the polynomial, which
    only the normaliser can see; so every check computes {!shapes} as part
    of its boolean, and a failed shape makes the check false rather than
    the rules wrong. *)
module Spec.Group.Check

open Spec.Group.Poly
module M = FStar.Math.Lemmas
module F = FStar.Math.Fermat
module E = FStar.Math.Euclid
module Pr = Spec.Group.Prime

let base (m: pos) (fl: nat) (o: fops m) (n: nat) (env: list (elem m)) : ctx =
  { m; o; nv = n; env; rules = []; fuel = fl }

let base_ok (m: pos) (fl: nat) (o: fops m) (n: nat) (env: list (elem m))
  : Lemma (requires fops_ok o) (ensures ok (base m fl o n env))
  = rules_hold_nil m (ienv (base m fl o n env))

type hyp (c: ctx) = sv c & sv c

let mono_of (p: poly) : option mono =
  match p with [(mo, 1)] -> Some mo | _ -> None

let rec shapes (#c: ctx) (hs: list (hyp c)) : bool =
  match hs with [] -> true | (l, _) :: t -> Some? (mono_of (fst l)) && shapes t

let rec rules_of (#c: ctx) (hs: list (hyp c)) : list rule =
  match hs with
  | [] -> []
  | (l, r) :: t ->
    (match mono_of (fst l) with
     | Some mo -> (mo, fst r) :: rules_of t
     | None -> rules_of t)

let rec holds (#c: ctx) (hs: list (hyp c)) : prop =
  match hs with [] -> True | (l, r) :: t -> vl l == vl r /\ holds t

let rec rules_of_ok (c: ctx) (hs: list (hyp c))
  : Lemma (requires ok c /\ holds hs) (ensures rules_hold c.m (ienv c) (rules_of hs))
  = match hs with
    | [] -> ()
    | (l, r) :: t ->
      rules_of_ok c t;
      (match mono_of (fst l) with
       | Some mo ->
         let x : poly & (unit -> elem c.m) = l in
         assert (peval (ienv c) (fst x) % c.m == vl0 x);
         assert (peval (ienv c) [(mo, 1)] == meval (ienv c) mo);
         rule_intro c mo r;
         rules_hold_cons c.m (ienv c) mo (fst r) (rules_of t)
       | None -> ())

let with_hyps (c: ctx) (hs: list (hyp c)) : ctx = with_rules c (rules_of hs)

let hyps_ok (c: ctx) (hs: list (hyp c))
  : Lemma (requires ok c /\ holds hs)
          (ensures ok (with_hyps c hs) /\ (with_hyps c hs).m == c.m /\
                   (with_hyps c hs).o == c.o /\ (with_hyps c hs).env == c.env /\
                   (with_hyps c hs).nv == c.nv /\ ienv (with_hyps c hs) == ienv c)
  = rules_of_ok c hs;
    ok_with_rules c (rules_of hs)

(** {2 Powers} *)

let rec spow (#c: ctx) (a: sv c) (n: nat) : Tot (sv c) (decreases n) =
  if n = 0 then sconst c (1 % c.m)
  else
    let h = spow a (n / 2) in
    let h2 = smul h h in
    if n % 2 = 0 then h2 else smul h2 a

let rec spow_val (#c: ctx) (a: sv c) (n: nat)
  : Lemma (requires ok c) (ensures vl (spow a n) == Pr.pow_mod (vl a) n c.m) (decreases n)
  = if n = 0 then () else spow_val a (n / 2)

(** {2 Horner} *)

let rec shorner (#c: ctx) (x: sv c) (u: list nat) : sv c =
  match u with
  | [] -> sconst c 0
  | a :: t -> sadd (sconst c (a % c.m)) (smul x (shorner x t))

(** {2 No roots}

    [h] has no root in the prime field [F_m] if [x^m - x] is invertible
    modulo [h]: at a root [x^m = x] by Fermat, so [u (x^m - x) = 1] would
    make [0 = 1].  The check runs in one variable with the rule
    [x^d -> x^d - h(x)], which a root makes true. *)

let nr_hyps (c: ctx { c.nv == 1 }) (d: nat) (hb: (c: ctx) -> sv c -> sv c) : list (hyp c) =
  let x0 = svar c 0 in
  [(spow x0 d, ssub (spow x0 d) (hb c x0))]

let nr_check (m: pos) (fl: nat) (o: fops m) (x: elem m) (d: nat)
             (hb: (c: ctx) -> sv c -> sv c) (u: list nat) : bool =
  let c0 = base m fl o 1 [x] in
  let hs = nr_hyps c0 d hb in
  let c = with_hyps c0 hs in
  let xv = svar c 0 in
  let g = ssub (spow xv m) xv in
  shapes hs && Nil? (fst (ssub (smul (shorner xv u) g) (sconst c (1 % m))))

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let nr_sound (m: pos) (fl: nat) (o: fops m) (x: elem m) (d: nat)
             (hb: (c: ctx) -> sv c -> sv c) (u: list nat)
  : Lemma (requires E.is_prime m /\ fops_ok o /\ nr_check m fl o x d hb u == true)
          (ensures (let c0 = base m fl o 1 [x] in vl (hb c0 (svar c0 0)) <> 0))
  = let c0 = base m fl o 1 [x] in
    base_ok m fl o 1 [x];
    let x0 = svar c0 0 in
    if vl (hb c0 x0) = 0 then begin
      let hs = nr_hyps c0 d hb in
      let p = spow x0 d in
      let r = ssub p (hb c0 x0) in
      assert (vl r == o.sub (vl p) 0);
      M.small_mod (vl p) m;
      assert (vl r == vl p);
      assert (hs == [(p, r)]);
      assert (holds hs);
      hyps_ok c0 hs;
      let c = with_hyps c0 hs in
      let xv = svar c 0 in
      ienv_nth c 0;
      assert (vl xv == x);
      spow_val xv m;
      Pr.pow_mod_lemma x m m;
      F.fermat m x;
      M.small_mod x m;
      let g = ssub (spow xv m) xv in
      assert (vl g == 0);
      let lhs = smul (shorner xv u) g in
      assert (vl lhs == 0);
      sv_eq lhs (sconst c (1 % m))
    end
#pop-options

#push-options "--fuel 4 --ifuel 1"
let holds1 (#c: ctx) (h1: hyp c)
  : Lemma (requires vl (fst h1) == vl (snd h1)) (ensures holds [h1]) = ()

let holds2 (#c: ctx) (h1 h2: hyp c)
  : Lemma (requires vl (fst h1) == vl (snd h1) /\ vl (fst h2) == vl (snd h2))
          (ensures holds [h1; h2]) = ()

let holds3 (#c: ctx) (h1 h2 h3: hyp c)
  : Lemma (requires vl (fst h1) == vl (snd h1) /\ vl (fst h2) == vl (snd h2) /\
                    vl (fst h3) == vl (snd h3))
          (ensures holds [h1; h2; h3]) = ()
#pop-options
