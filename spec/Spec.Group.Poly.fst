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

(** A checker for polynomial identities over [Z/m], modulo a set of
    rewriting rules, run by normalisation.

    The group-law proofs are polynomial identities of a size no SMT solver
    and no tactic-level ring normaliser will look at: associativity on
    P-256 is a cross-multiplication of two nine-variable formulas forty
    lines deep, some twenty-six thousand monomials before reduction.  What
    does work is to compute: represent a polynomial as a sorted list of
    monomials, multiply out, reduce modulo the curve equations, and look at
    whether what is left is the empty list.  F\*'s NBE normaliser does that
    fast enough, provided the computation is written as a program rather
    than as a term to be rewritten.

    So this module is a small computer algebra system with a soundness
    proof.  A [poly] is a list of [(exponent vector, coefficient)] pairs;
    [padd], [pmul] and [reduce] are ordinary functions on them, and each is
    proved to commute with evaluation modulo [m].  [reduce] rewrites any
    monomial divisible by the left-hand side of a rule with the rule's
    right-hand side, which is sound exactly when every rule holds at the
    point of evaluation -- that is what [rules_hold] says, and it is the
    only hypothesis a curve proof has to supply.  Nothing here needs the
    normal forms to be canonical for soundness: if a true identity fails to
    reduce to zero the check simply fails.

    The interface to the curve proofs is [sv], a polynomial paired with the
    field element it evaluates to.  Every operation on [sv] computes both
    halves, and its type records that the second half is the specification's
    own [fadd]/[fsub]/[fmul] of the arguments' second halves.  A formula
    transcribed over [sv] therefore carries its meaning in its type, and
    running it by normalisation computes its polynomial; when two such
    polynomials agree, so do the field elements. *)
module Spec.Group.Poly


module L = FStar.List.Tot
module M = FStar.Math.Lemmas

(** {2 Polynomials and their values} *)

type mono = list nat
type poly = list (mono & int)

let rec pow (x: int) (n: nat) : Tot int (decreases n) =
  if n = 0 then 1 else x * pow x (n - 1)

let hd0 (env: list int) : int = match env with [] -> 0 | x :: _ -> x
let tl0 (env: list int) : list int = match env with [] -> [] | _ :: r -> r

let rec meval (env: list int) (mo: mono) : Tot int (decreases mo) =
  match mo with
  | [] -> 1
  | e :: mo' -> pow (hd0 env) e * meval (tl0 env) mo'

let rec peval (env: list int) (p: poly) : Tot int (decreases p) =
  match p with
  | [] -> 0
  | (mo, c) :: p' -> c * meval env mo + peval env p'

(** Congruence modulo [m], and the handful of facts about it that every
    proof below is assembled from. *)
let eqm (m: pos) (a b: int) : prop = a % m == b % m

let eqm_refl (m: pos) (a: int) : Lemma (eqm m a a) = ()

let eqm_sym (m: pos) (a b: int) : Lemma (requires eqm m a b) (ensures eqm m b a) = ()

let eqm_trans (m: pos) (a b c: int)
  : Lemma (requires eqm m a b /\ eqm m b c) (ensures eqm m a c) = ()

let eqm_add (m: pos) (a b c d: int)
  : Lemma (requires eqm m a b /\ eqm m c d) (ensures eqm m (a + c) (b + d))
  = calc (==) {
      (a + c) % m;
      == { M.lemma_mod_plus_distr_l a c m }
      (a % m + c) % m;
      == { M.lemma_mod_plus_distr_r (a % m) c m }
      (a % m + c % m) % m;
      == { }
      (b % m + d % m) % m;
      == { M.lemma_mod_plus_distr_r (b % m) d m }
      (b % m + d) % m;
      == { M.lemma_mod_plus_distr_l b d m }
      (b + d) % m;
    }

let eqm_mul (m: pos) (a b c d: int)
  : Lemma (requires eqm m a b /\ eqm m c d) (ensures eqm m (a * c) (b * d))
  = calc (==) {
      (a * c) % m;
      == { M.lemma_mod_mul_distr_l a c m }
      ((a % m) * c) % m;
      == { M.lemma_mod_mul_distr_r (a % m) c m }
      ((a % m) * (c % m)) % m;
      == { }
      ((b % m) * (d % m)) % m;
      == { M.lemma_mod_mul_distr_r (b % m) d m }
      ((b % m) * d) % m;
      == { M.lemma_mod_mul_distr_l b d m }
      (b * d) % m;
    }

let eqm_mod (m: pos) (a: int) : Lemma (eqm m (a % m) a) = M.lemma_mod_twice a m

let mul4 (a b c d: int) : Lemma ((a * b) * (c * d) == (a * c) * (b * d)) =
  M.paren_mul_right a b (c * d);
  M.paren_mul_right b c d;
  M.swap_mul b c;
  M.paren_mul_right c b d;
  M.paren_mul_right a c (b * d)

let rec pow_add (x: int) (a b: nat)
  : Lemma (ensures pow x (a + b) == pow x a * pow x b) (decreases a)
  = if a = 0 then ()
    else begin
      pow_add x (a - 1) b;
      M.paren_mul_right x (pow x (a - 1)) (pow x b)
    end

(** {2 Monomials} *)

let rec mmul (a b: mono) : mono =
  match a, b with
  | x :: a', y :: b' -> (x + y) :: mmul a' b'
  | [], _ -> b
  | _, [] -> a

let rec meval_mmul (env: list int) (a b: mono)
  : Lemma (ensures meval env (mmul a b) == meval env a * meval env b) (decreases a)
  = match a, b with
    | x :: a', y :: b' ->
      meval_mmul (tl0 env) a' b';
      pow_add (hd0 env) x y;
      mul4 (pow (hd0 env) x) (pow (hd0 env) y) (meval (tl0 env) a') (meval (tl0 env) b')
    | [], _ -> ()
    | _, [] -> ()

(** Lexicographic, and zero only on equal lists: [padd] merges two terms
    when this says they are equal, so it had better mean it. *)
let rec mcmp (a b: mono) : int =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: a', y :: b' -> if x < y then -1 else if x > y then 1 else mcmp a' b'

let rec mcmp_eq (a b: mono) : Lemma (requires mcmp a b = 0) (ensures a == b) =
  match a, b with
  | _ :: a', _ :: b' -> mcmp_eq a' b'
  | _ -> ()

let rec mdiv (mo r: mono) : option mono =
  match mo, r with
  | [], [] -> Some []
  | x :: mo', y :: r' ->
    if y <= x then (match mdiv mo' r' with Some d -> Some ((x - y) :: d) | None -> None)
    else None
  | _ -> None

let rec mdiv_ok (env: list int) (mo r: mono)
  : Lemma (requires Some? (mdiv mo r))
          (ensures meval env mo == meval env r * meval env (Some?.v (mdiv mo r)))
          (decreases mo)
  = match mo, r with
    | [], [] -> ()
    | x :: mo', y :: r' ->
      mdiv_ok (tl0 env) mo' r';
      let d' = Some?.v (mdiv mo' r') in
      pow_add (hd0 env) y (x - y);
      mul4 (pow (hd0 env) y) (pow (hd0 env) (x - y)) (meval (tl0 env) r') (meval (tl0 env) d')

let rec zero_mono (n: nat) : mono = if n = 0 then [] else 0 :: zero_mono (n - 1)

let rec unit_mono (n i: nat) : mono =
  if n = 0 then []
  else if i = 0 then 1 :: zero_mono (n - 1)
  else 0 :: unit_mono (n - 1) (i - 1)

let rec meval_zero (env: list int) (n: nat)
  : Lemma (ensures meval env (zero_mono n) == 1) (decreases n)
  = if n = 0 then () else meval_zero (tl0 env) (n - 1)

let rec nth0 (#a: Type) (d: a) (l: list a) (i: nat) : Tot a (decreases l) =
  match l with
  | [] -> d
  | x :: r -> if i = 0 then x else nth0 d r (i - 1)

let rec meval_unit (env: list int) (n i: nat)
  : Lemma (requires i < n) (ensures meval env (unit_mono n i) == nth0 0 env i) (decreases n)
  = if i = 0 then meval_zero (tl0 env) (n - 1)
    else begin
      meval_unit (tl0 env) (n - 1) (i - 1);
      match env with [] -> () | _ :: _ -> ()
    end

(** {2 Polynomial arithmetic}

    Coefficients are kept in [[1, m)] and zero terms are dropped, so that a
    polynomial that is zero modulo [m] really is the empty list; lists are
    kept sorted in decreasing [mcmp] order, which multiplication by a
    monomial preserves, so that addition is a merge. *)

let rec padd (m: pos) (p q: poly) : Tot poly (decreases %[L.length p + L.length q]) =
  match p, q with
  | [], _ -> q
  | _, [] -> p
  | (m1, c1) :: p', (m2, c2) :: q' ->
    let k = mcmp m1 m2 in
    if k = 0 then
      let s = (c1 + c2) % m in
      if s = 0 then padd m p' q' else (m1, s) :: padd m p' q'
    else if k > 0 then (m1, c1) :: padd m p' q
    else (m2, c2) :: padd m p q'

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec padd_ok (env: list int) (m: pos) (p q: poly)
  : Lemma (ensures eqm m (peval env (padd m p q)) (peval env p + peval env q))
          (decreases %[L.length p + L.length q])
  = match p, q with
    | [], _ -> ()
    | _, [] -> ()
    | (m1, c1) :: p', (m2, c2) :: q' ->
      let k = mcmp m1 m2 in
      let v1 = meval env m1 in
      if k = 0 then begin
        mcmp_eq m1 m2;
        padd_ok env m p' q';
        let s = (c1 + c2) % m in
        let r' = peval env (padd m p' q') in
        let a = peval env p' in
        let b = peval env q' in
        eqm_mod m (c1 + c2);
        eqm_mul m s (c1 + c2) v1 v1;
        M.distributivity_add_left c1 c2 v1;
        eqm_add m (s * v1) ((c1 + c2) * v1) r' (a + b);
        if s = 0 then ()
        else ()
      end
      else if k > 0 then begin
        padd_ok env m p' q;
        eqm_add m (c1 * v1) (c1 * v1) (peval env (padd m p' q)) (peval env p' + peval env q)
      end
      else begin
        padd_ok env m p q';
        let v2 = meval env m2 in
        eqm_add m (c2 * v2) (c2 * v2) (peval env (padd m p q')) (peval env p + peval env q')
      end
#pop-options

let rec pscale (m: pos) (mo: mono) (c: int) (q: poly) : Tot poly (decreases q) =
  match q with
  | [] -> []
  | (m2, c2) :: q' ->
    let s = (c * c2) % m in
    if s = 0 then pscale m mo c q' else (mmul mo m2, s) :: pscale m mo c q'

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec pscale_ok (env: list int) (m: pos) (mo: mono) (c: int) (q: poly)
  : Lemma (ensures eqm m (peval env (pscale m mo c q)) (c * meval env mo * peval env q))
          (decreases q)
  = match q with
    | [] -> ()
    | (m2, c2) :: q' ->
      pscale_ok env m mo c q';
      let s = (c * c2) % m in
      let v = meval env mo in
      let v2 = meval env m2 in
      meval_mmul env mo m2;
      eqm_mod m (c * c2);
      eqm_mul m s (c * c2) (v * v2) (v * v2);
      mul4 c c2 v v2;
      M.distributivity_add_right (c * v) (c2 * v2) (peval env q');
      eqm_add m (s * (v * v2)) ((c * v) * (c2 * v2))
                (peval env (pscale m mo c q')) (c * v * peval env q')
#pop-options

(** Balanced merging: pair adjacent polynomials until one is left.  This is
    what keeps a product of two [n]-term polynomials at [n^2 log n]. *)
let rec psum (env: list int) (l: list poly) : int =
  match l with [] -> 0 | p :: r -> peval env p + psum env r

let rec pairs (m: pos) (l: list poly) : list poly =
  match l with
  | a :: b :: r -> padd m a b :: pairs m r
  | _ -> l

let rec pairs_len (m: pos) (l: list poly)
  : Lemma (ensures L.length (pairs m l) <= L.length l /\
                   (L.length l >= 2 ==> L.length (pairs m l) < L.length l))
  = match l with
    | _ :: _ :: r -> pairs_len m r
    | _ -> ()

let rec pairs_ok (env: list int) (m: pos) (l: list poly)
  : Lemma (ensures eqm m (psum env (pairs m l)) (psum env l))
  = match l with
    | a :: b :: r ->
      pairs_ok env m r;
      padd_ok env m a b;
      eqm_add m (peval env (padd m a b)) (peval env a + peval env b)
                (psum env (pairs m r)) (psum env r)
    | _ -> ()

let rec merge_all (m: pos) (l: list poly) : Tot poly (decreases L.length l) =
  match l with
  | [] -> []
  | [a] -> a
  | _ -> pairs_len m l; merge_all m (pairs m l)

let rec merge_all_ok (env: list int) (m: pos) (l: list poly)
  : Lemma (ensures eqm m (peval env (merge_all m l)) (psum env l)) (decreases L.length l)
  = match l with
    | [] -> ()
    | [a] -> ()
    | _ ->
      pairs_len m l;
      merge_all_ok env m (pairs m l);
      pairs_ok env m l

let rec scale_all (m: pos) (q: poly) (p: poly) : list poly =
  match p with
  | [] -> []
  | (mo, c) :: p' -> pscale m mo c q :: scale_all m q p'

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec scale_all_ok (env: list int) (m: pos) (q p: poly)
  : Lemma (ensures eqm m (psum env (scale_all m q p)) (peval env p * peval env q))
  = match p with
    | [] -> ()
    | (mo, c) :: p' ->
      scale_all_ok env m q p';
      pscale_ok env m mo c q;
      M.distributivity_add_left (c * meval env mo) (peval env p') (peval env q);
      eqm_add m (peval env (pscale m mo c q)) (c * meval env mo * peval env q)
                (psum env (scale_all m q p')) (peval env p' * peval env q)
#pop-options

let pmul (m: pos) (p q: poly) : poly = merge_all m (scale_all m q p)

let pmul_ok (env: list int) (m: pos) (p q: poly)
  : Lemma (eqm m (peval env (pmul m p q)) (peval env p * peval env q))
  = merge_all_ok env m (scale_all m q p);
    scale_all_ok env m q p

(** Negation is scaling by [m - 1]; [mmul [] mo == mo]. *)
let pneg (m: pos) (q: poly) : poly = pscale m [] (m - 1) q

let psub (m: pos) (p q: poly) : poly = padd m p (pneg m q)

let psub_ok (env: list int) (m: pos) (p q: poly)
  : Lemma (eqm m (peval env (psub m p q)) (peval env p - peval env q))
  = padd_ok env m p (pneg m q);
    pscale_ok env m [] (m - 1) q;
    let v = peval env q in
    assert ((m - 1) * 1 * v == m * v - v);
    M.lemma_mod_sub (0 - v) m (0 - v);
    M.lemma_mod_plus (0 - v) v m;
    eqm_add m (peval env p) (peval env p) (peval env (pneg m q)) (m * v - v);
    M.lemma_mod_plus (peval env p - v) v m

(** {2 Reduction modulo rules}

    A rule [(r, q)] says the monomial [r] is congruent to [q] at the point
    of evaluation.  Reducing rewrites every term whose monomial [r]
    divides, and repeats on what the rewrite produced, up to [fuel] times. *)

type rule = mono & poly

let rec rules_hold (m: pos) (env: list int) (rs: list rule) : prop =
  match rs with
  | [] -> True
  | (r, q) :: rs' -> eqm m (meval env r) (peval env q) /\ rules_hold m env rs'

let rec find_rule (rs: list rule) (mo: mono) : option (mono & poly) =
  match rs with
  | [] -> None
  | (r, q) :: rs' ->
    (match mdiv mo r with
     | Some d -> Some (d, q)
     | None -> find_rule rs' mo)

let rec find_rule_ok (env: list int) (m: pos) (rs: list rule) (mo: mono)
  : Lemma (requires rules_hold m env rs /\ Some? (find_rule rs mo))
          (ensures (let (d, q) = Some?.v (find_rule rs mo) in
                    eqm m (meval env mo) (peval env q * meval env d)))
  = match rs with
    | (r, q) :: rs' ->
      (match mdiv mo r with
       | Some d ->
         mdiv_ok env mo r;
         eqm_mul m (meval env r) (peval env q) (meval env d) (meval env d)
       | None -> find_rule_ok env m rs' mo)

let rec reduce_split (m: pos) (fuel: nat) (rs: list rule) (p: poly)
  : Tot (poly & list poly) (decreases %[fuel; 0; L.length p])
  = match p with
    | [] -> ([], [])
    | (mo, c) :: p' ->
      let (k, r) = reduce_split m fuel rs p' in
      (match find_rule rs mo with
       | Some (d, q) ->
         if fuel = 0 then ((mo, c) :: k, r)
         else (k, reduce m (fuel - 1) rs (pscale m d c q) :: r)
       | None -> ((mo, c) :: k, r))

and reduce (m: pos) (fuel: nat) (rs: list rule) (p: poly)
  : Tot poly (decreases %[fuel; 1; 0])
  = let (k, r) = reduce_split m fuel rs p in
    merge_all m (k :: r)

let mul3 (c a b: int) : Lemma (c * (a * b) == c * b * a) =
  M.swap_mul a b;
  M.paren_mul_right c b a

let keep_ok (m: pos) (cv k r p': int)
  : Lemma (requires eqm m (k + r) p') (ensures eqm m ((cv + k) + r) (cv + p'))
  = eqm_add m cv cv (k + r) p'

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec reduce_split_ok (env: list int) (m: pos) (fuel: nat) (rs: list rule) (p: poly)
  : Lemma (requires rules_hold m env rs)
          (ensures (let (k, r) = reduce_split m fuel rs p in
                    eqm m (peval env k + psum env r) (peval env p)))
          (decreases %[fuel; 0; L.length p])
  = match p with
    | [] -> ()
    | (mo, c) :: p' ->
      reduce_split_ok env m fuel rs p';
      let (k, r) = reduce_split m fuel rs p' in
      let v = meval env mo in
      (match find_rule rs mo with
       | Some (d, q) ->
         if fuel = 0 then keep_ok m (c * v) (peval env k) (psum env r) (peval env p')
         else begin
           reduce_ok env m (fuel - 1) rs (pscale m d c q);
           pscale_ok env m d c q;
           find_rule_ok env m rs mo;
           (* c * v == c * (q * d) == c * d * q *)
           eqm_mul m c c v (peval env q * meval env d);
           mul3 c (peval env q) (meval env d);
           let t = peval env (reduce m (fuel - 1) rs (pscale m d c q)) in
           eqm_trans m t (peval env (pscale m d c q)) (c * meval env d * peval env q);
           eqm_trans m t (c * meval env d * peval env q) (c * v);
           eqm_add m (peval env k + psum env r) (peval env p') t (c * v)
         end
       | None -> keep_ok m (c * v) (peval env k) (psum env r) (peval env p'))

and reduce_ok (env: list int) (m: pos) (fuel: nat) (rs: list rule) (p: poly)
  : Lemma (requires rules_hold m env rs)
          (ensures eqm m (peval env (reduce m fuel rs p)) (peval env p))
          (decreases %[fuel; 1; 0])
  = reduce_split_ok env m fuel rs p;
    let (k, r) = reduce_split m fuel rs p in
    merge_all_ok env m (k :: r)
#pop-options

(** {2 Field elements with their polynomials} *)

let elem (m: pos) = x: nat { x < m }

(** The specification's own field operations.  They are taken as
    parameters, not defined here, so that the second half of an [sv]
    is literally the specification's term. *)
noeq type fops (m: pos) = {
  add: elem m -> elem m -> elem m;
  sub: elem m -> elem m -> elem m;
  mul: elem m -> elem m -> elem m;
}

let fops_ok (#m: pos) (o: fops m) : prop =
  (forall (x y: elem m). o.add x y == (x + y) % m) /\
  (forall (x y: elem m). o.sub x y == (x - y) % m) /\
  (forall (x y: elem m). o.mul x y == (x * y) % m)

(** Everything a computation needs: the modulus, the operations, the
    number of variables, the point of evaluation and the rules that hold
    there.  The modulus must be a literal, not the specification's
    [pow2 256 - ...]: the normaliser evaluates types as well as terms, and
    [elem c.m] would then recompute [pow2] on every operation.  The same
    goes for every constant a check mentions -- the specifications' own
    constants carry an [assert_norm] each, and the check should be handed a
    literal instead, with the equation between the two proved once. *)
noeq type ctx = {
  m: pos;
  o: fops m;
  nv: nat;
  env: list (elem m);
  rules: list rule;
  fuel: nat;
}

let rec ints (#m: pos) (l: list (elem m)) : list int =
  match l with [] -> [] | x :: r -> (x <: int) :: ints r

let ienv (c: ctx) : list int = ints c.env

let ok (c: ctx) : prop = fops_ok c.o /\ rules_hold c.m (ienv c) c.rules

(** The value half is a thunk.  The checks run with the environment and the
    field operations abstract, so the value half could not compute to
    anything anyway; were it strict, the normaliser would build its
    symbolic term alongside the polynomial, and that costs far more than the
    polynomial itself. *)
let vl0 (#m: pos) (x: poly & (unit -> elem m)) : elem m = snd x ()

let sv (c: ctx) = x: (poly & (unit -> elem c.m)) { ok c ==> peval (ienv c) (fst x) % c.m == vl0 x }

let vl (#c: ctx) (x: sv c) : elem c.m = vl0 x

let rec nth0_map (c: ctx) (l: list (elem c.m)) (i: nat)
  : Lemma (ensures nth0 0 (ints l) i == nth0 0 l i)
          (decreases l)
  = match l with [] -> () | _ :: r -> if i = 0 then () else nth0_map c r (i - 1)

(** The proofs behind each operation are separate and [irreducible]: the
    operations are run by the normaliser, which must not unfold a proof and
    walk the polynomials a second time. *)
irreducible let svar_lem (c: ctx) (i: nat { i < c.nv })
  : Lemma (peval (ienv c) [(unit_mono c.nv i, 1)] % c.m == nth0 0 c.env i)
  = nth0_map c c.env i;
    meval_unit (ienv c) c.nv i

let svar (c: ctx) (i: nat { i < c.nv }) : r: sv c { vl r == nth0 0 c.env i } =
  svar_lem c i;
  ([(unit_mono c.nv i, 1)], (fun () -> nth0 0 c.env i))

irreducible let sconst_lem (c: ctx) (v: elem c.m)
  : Lemma (peval (ienv c) (if v = 0 then [] else [(zero_mono c.nv, v)]) % c.m == v)
  = meval_zero (ienv c) c.nv

let sconst (c: ctx) (v: elem c.m) : r: sv c { vl r == v } =
  sconst_lem c v;
  ((if v = 0 then [] else [(zero_mono c.nv, v)]), (fun () -> v))

let sv_eqm (#c: ctx) (a: sv c) : Lemma (ok c ==> eqm c.m (peval (ienv c) (fst a)) (vl a)) =
  M.small_mod (vl a) c.m;
  M.lemma_mod_twice (peval (ienv c) (fst a)) c.m

irreducible let sadd_lem (c: ctx) (a b: sv c)
  : Lemma (ok c ==> peval (ienv c) (padd c.m (fst a) (fst b)) % c.m == c.o.add (vl a) (vl b))
  = sv_eqm a; sv_eqm b;
    padd_ok (ienv c) c.m (fst a) (fst b);
    introduce ok c ==> peval (ienv c) (padd c.m (fst a) (fst b)) % c.m == c.o.add (vl a) (vl b)
    with eqm_add c.m (peval (ienv c) (fst a)) (vl a) (peval (ienv c) (fst b)) (vl b)

let sadd (#c: ctx) (a b: sv c) : r: sv c { ok c ==> vl r == c.o.add (vl a) (vl b) } =
  sadd_lem c a b;
  (padd c.m (fst a) (fst b), (fun () -> c.o.add (vl a) (vl b)))

irreducible let ssub_lem (c: ctx) (a b: sv c)
  : Lemma (ok c ==> peval (ienv c) (psub c.m (fst a) (fst b)) % c.m == c.o.sub (vl a) (vl b))
  = sv_eqm a; sv_eqm b;
    psub_ok (ienv c) c.m (fst a) (fst b);
    introduce ok c ==> peval (ienv c) (psub c.m (fst a) (fst b)) % c.m == c.o.sub (vl a) (vl b)
    with begin
      let pa = peval (ienv c) (fst a) in
      let pb = peval (ienv c) (fst b) in
      eqm_sym c.m (vl b) pb;
      eqm_mul c.m (-1) (-1) pb (vl b);
      eqm_add c.m pa (vl a) ((-1) * pb) ((-1) * vl b)
    end

let ssub (#c: ctx) (a b: sv c) : r: sv c { ok c ==> vl r == c.o.sub (vl a) (vl b) } =
  ssub_lem c a b;
  (psub c.m (fst a) (fst b), (fun () -> c.o.sub (vl a) (vl b)))

irreducible let smul_lem (c: ctx) (a b: sv c)
  : Lemma (ok c ==> peval (ienv c) (reduce c.m c.fuel c.rules (pmul c.m (fst a) (fst b))) % c.m
                    == c.o.mul (vl a) (vl b))
  = let p = pmul c.m (fst a) (fst b) in
    sv_eqm a; sv_eqm b;
    pmul_ok (ienv c) c.m (fst a) (fst b);
    introduce ok c ==> peval (ienv c) (reduce c.m c.fuel c.rules p) % c.m == c.o.mul (vl a) (vl b)
    with begin
      reduce_ok (ienv c) c.m c.fuel c.rules p;
      eqm_mul c.m (peval (ienv c) (fst a)) (vl a) (peval (ienv c) (fst b)) (vl b)
    end

let smul (#c: ctx) (a b: sv c) : r: sv c { ok c ==> vl r == c.o.mul (vl a) (vl b) } =
  smul_lem c a b;
  (reduce c.m c.fuel c.rules (pmul c.m (fst a) (fst b)), (fun () -> c.o.mul (vl a) (vl b)))

(** The one fact a proof extracts: two [sv]s whose difference reduces to
    the zero polynomial denote the same field element. *)
let sv_eq (#c: ctx) (a b: sv c)
  : Lemma (requires ok c /\ Nil? (fst (ssub a b)))
          (ensures vl a == vl b)
  = let d = ssub a b in
    assert (vl d == 0);
    let x = vl a - vl b in
    assert (c.o.sub (vl a) (vl b) == x % c.m);
    if x >= 0 then M.small_mod x c.m
    else (M.lemma_mod_plus x 1 c.m; M.small_mod (x + c.m) c.m)

(** The normaliser invocation every check uses. *)
let poly_tac () : FStar.Tactics.V2.Tac unit =
  FStar.Tactics.V2.norm [primops; iota; zeta; delta; nbe];
  FStar.Tactics.V2.trivial ()

(** {2 Building contexts}

    A rule is justified by an [sv] computed in a context without rules (or
    with rules already justified) over the same point: if the monomial
    evaluates to the [sv]'s value, the rule holds. *)
let rule_intro (c: ctx) (mo: mono) (a: sv c)
  : Lemma (requires ok c /\ meval (ienv c) mo % c.m == vl a)
          (ensures eqm c.m (meval (ienv c) mo) (peval (ienv c) (fst a)))
  = let x : poly & (unit -> elem c.m) = a in
    assert (peval (ienv c) (fst x) % c.m == vl0 x)

let rules_hold_nil (m: pos) (env: list int) : Lemma (rules_hold m env []) = ()

let rules_hold_cons (m: pos) (env: list int) (r: mono) (q: poly) (rs: list rule)
  : Lemma (requires eqm m (meval env r) (peval env q) /\ rules_hold m env rs)
          (ensures rules_hold m env ((r, q) :: rs))
  = ()

let with_rules (c: ctx) (rs: list rule) : ctx = { c with rules = rs }

let ienv_with_rules (c: ctx) (rs: list rule)
  : Lemma (ienv (with_rules c rs) == ienv c /\ (with_rules c rs).m == c.m /\
           (with_rules c rs).o == c.o /\ (with_rules c rs).env == c.env)
  = ()

let ok_with_rules (c: ctx) (rs: list rule)
  : Lemma (requires fops_ok c.o /\ rules_hold c.m (ienv c) rs)
          (ensures ok (with_rules c rs))
  = ()

let sq_mono (n i: nat) : mono = mmul (unit_mono n i) (unit_mono n i)

let meval_sq (env: list int) (n i: nat)
  : Lemma (requires i < n)
          (ensures meval env (sq_mono n i) == nth0 0 env i * nth0 0 env i)
  = meval_mmul env (unit_mono n i) (unit_mono n i);
    meval_unit env n i

let ienv_nth (c: ctx) (i: nat) : Lemma (nth0 0 (ienv c) i == nth0 0 c.env i) =
  nth0_map c c.env i
