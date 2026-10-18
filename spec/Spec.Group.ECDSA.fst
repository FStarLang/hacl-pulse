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

(** The algebra behind Diffie--Hellman and ECDSA, over an abstract group.

    Both protocols are correct for reasons that have nothing to do with any
    particular curve: Diffie--Hellman because [a (b P) = (a b) P = b (a P)],
    and ECDSA because the verifier's [u1 G + u2 Q], with [Q = d G], is the
    multiple of [G] by [s^-1 (m + r d)], which is the signer's nonce.  This
    module proves those facts once, over the record {!Spec.Group.Smul.grp},
    and {!Spec.P256.Order} and {!Spec.K256.Order} instantiate them.

    Two of them need more than the monoid laws of the record.

    {ul
    {- {b Periodicity.}  Reducing a scalar modulo [q] is harmless only if
       [q P] is the identity.  This is a hypothesis here; on a curve it is a
       normalisation of [point_mul order g].}
    {- {b No zero divisors.}  A nonzero multiple of a generator of prime
       order is not the identity ({!smul_nonzero}).  The proof inverts the
       multiplier modulo [q] with Bezout, which is where primality is used:
       if [k P = 0] then [P = (u k) P = u (k P) = 0].}}

    As in {!Spec.Group.Smul}, every statement is about the record's own
    [ok] and [eqv], so the proofs never see a field equation. *)
module Spec.Group.ECDSA

open Spec.Group.Smul
module M = FStar.Math.Lemmas
module E = FStar.Math.Euclid

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"

(** {2 Equivalence chains} *)

let trans3 (#a: Type) (g: grp a) (p q r s: a)
  : Lemma (requires g.ok p /\ g.ok q /\ g.ok r /\ g.ok s /\
                    g.eqv p q /\ g.eqv q r /\ g.eqv r s)
          (ensures g.eqv p s)
  = g.eqv_trans p q r; g.eqv_trans p r s

let add_zero_r (#a: Type) (g: grp a) (p: a)
  : Lemma (requires g.ok p) (ensures g.ok (g.add p g.zero) /\ g.eqv (g.add p g.zero) p)
  = g.ok_zero ();
    g.ok_add p g.zero; g.ok_add g.zero p;
    g.add_comm p g.zero; g.add_id p;
    g.eqv_trans (g.add p g.zero) (g.add g.zero p) p

(** {2 Multiples of the identity, and of a multiple} *)

#push-options "--fuel 1"
let rec smul_of_zero (#a: Type) (g: grp a) (n: nat)
  : Lemma (ensures g.eqv (smul g n g.zero) g.zero) (decreases n)
  = g.ok_zero ();
    if n = 0 then g.eqv_refl g.zero
    else begin
      smul_of_zero g (n - 1);
      smul_ok g (n - 1) g.zero;
      g.eqv_refl g.zero;
      g.add_congr g.zero g.zero (smul g (n - 1) g.zero) g.zero;
      g.add_id g.zero;
      g.ok_add g.zero (smul g (n - 1) g.zero);
      g.ok_add g.zero g.zero;
      g.eqv_trans (smul g n g.zero) (g.add g.zero g.zero) g.zero
    end

(** [(m n) P = m (n P)].  Induction on [m]: peel one [n P] off the front
    with {!Spec.Group.Smul.smul_add}, which is exactly how [smul] unfolds on
    the right. *)
let rec smul_mul (#a: Type) (g: grp a) (m n: nat) (p: a)
  : Lemma (requires g.ok p)
          (ensures g.eqv (smul g (m * n) p) (smul g m (smul g n p)))
          (decreases m)
  = g.ok_zero ();
    if m = 0 then g.eqv_refl g.zero
    else begin
      let np = smul g n p in
      let m' = m - 1 in
      smul_mul g m' n p;
      smul_ok g n p;
      smul_ok g (m' * n) p;
      smul_ok g m' np;
      M.distributivity_sub_left m 1 n;
      assert (m * n == n + m' * n);
      smul_add g n (m' * n) p;
      g.eqv_refl np;
      g.add_congr np np (smul g (m' * n) p) (smul g m' np);
      smul_ok g (m * n) p;
      g.ok_add np (smul g (m' * n) p);
      g.ok_add np (smul g m' np);
      g.eqv_trans (smul g (m * n) p) (g.add np (smul g (m' * n) p))
                  (g.add np (smul g m' np))
    end
#pop-options

(** Diffie--Hellman: [a (b P) = b (a P)]. *)
let smul_swap (#a: Type) (g: grp a) (m n: nat) (p: a)
  : Lemma (requires g.ok p)
          (ensures g.ok (smul g m (smul g n p)) /\ g.ok (smul g n (smul g m p)) /\
                   g.eqv (smul g m (smul g n p)) (smul g n (smul g m p)))
  = smul_ok g n p; smul_ok g m p;
    smul_ok g m (smul g n p); smul_ok g n (smul g m p);
    smul_ok g (m * n) p;
    smul_mul g m n p;
    smul_mul g n m p;
    M.swap_mul m n;
    g.eqv_sym (smul g (m * n) p) (smul g m (smul g n p));
    g.eqv_trans (smul g m (smul g n p)) (smul g (m * n) p) (smul g n (smul g m p))

(** {2 A point of order [q]} *)

let has_order (#a: Type) (g: grp a) (q: pos) (p: a) : prop =
  g.ok p /\ g.eqv (smul g q p) g.zero

(** Scalars act modulo [q]. *)
let smul_mod (#a: Type) (g: grp a) (q: pos) (k: nat) (p: a)
  : Lemma (requires has_order g q p)
          (ensures g.eqv (smul g k p) (smul g (k % q) p))
  = let j = k / q in
    let r = k % q in
    M.euclidean_division_definition k q;
    g.ok_zero ();
    smul_ok g q p; smul_ok g r p; smul_ok g (j * q) p; smul_ok g k p;
    smul_ok g j (smul g q p); smul_ok g j g.zero;
    smul_add g (j * q) r p;
    smul_mul g j q p;
    smul_congr g j (smul g q p) g.zero;
    smul_of_zero g j;
    trans3 g (smul g (j * q) p) (smul g j (smul g q p)) (smul g j g.zero) g.zero;
    g.eqv_refl (smul g r p);
    g.add_congr (smul g (j * q) p) g.zero (smul g r p) (smul g r p);
    g.add_id (smul g r p);
    g.ok_add (smul g (j * q) p) (smul g r p);
    g.ok_add g.zero (smul g r p);
    trans3 g (smul g k p) (g.add (smul g (j * q) p) (smul g r p))
           (g.add g.zero (smul g r p)) (smul g r p)

(** The inverse of a unit modulo a prime, from Bezout. *)
let inv_mod (q: int) (k: int)
  : Pure nat (requires E.is_prime q /\ k % q <> 0)
             (ensures fun u -> (u * k) % q == 1)
  = let a = k % q in
    let (x, y) = E.bezout_prime q a in
    let u = y % q in
    M.lemma_mod_mul_distr_l y a q;
    M.lemma_mod_mul_distr_r y k q;
    M.lemma_mod_plus (y * a) x q;
    M.swap_mul x q;
    M.small_mod 1 q;
    M.lemma_mod_mul_distr_l y k q;
    u

#push-options "--z3rlimit 60"
(** No zero divisors: a multiple of a nonidentity point of prime order [q]
    by a scalar not divisible by [q] is not the identity. *)
let smul_nonzero (#a: Type) (g: grp a) (q: pos) (k: nat) (p: a)
  : Lemma (requires has_order g q p /\ E.is_prime q /\ ~(g.eqv p g.zero) /\ k % q <> 0)
          (ensures ~(g.eqv (smul g k p) g.zero))
  = let aux () : Lemma (requires g.eqv (smul g k p) g.zero) (ensures False) =
      let u = inv_mod q k in
      g.ok_zero ();
      smul_ok g k p; smul_ok g u (smul g k p); smul_ok g u g.zero;
      smul_ok g (u * k) p; smul_ok g 1 p;
      smul_mul g u k p;
      smul_congr g u (smul g k p) g.zero;
      smul_of_zero g u;
      trans3 g (smul g (u * k) p) (smul g u (smul g k p)) (smul g u g.zero) g.zero;
      smul_mod g q (u * k) p;
      smul_one g p;
      g.eqv_sym (smul g (u * k) p) (smul g 1 p);
      g.eqv_sym (smul g 1 p) p;
      trans3 g p (smul g 1 p) (smul g (u * k) p) g.zero
    in
    FStar.Classical.move_requires aux ()
#pop-options

(** {2 The verification equation}

    [u1 G + u2 Q], with [Q] any representative of [d G], is the multiple of
    [G] by [u1 + u2 d] reduced modulo [q]. *)
let verify_eq (#a: Type) (g: grp a) (q: pos) (gen qp: a) (d u1 u2: nat)
  : Lemma (requires has_order g q gen /\ g.ok qp /\ g.eqv qp (smul g d gen))
          (ensures g.ok (g.add (smul g u1 gen) (smul g u2 qp)) /\
                   g.eqv (g.add (smul g u1 gen) (smul g u2 qp))
                         (smul g ((u1 + u2 * d) % q) gen))
  = let a1 = smul g u1 gen in
    let k = u1 + u2 * d in
    smul_ok g u1 gen; smul_ok g d gen; smul_ok g u2 qp;
    smul_ok g u2 (smul g d gen); smul_ok g (u2 * d) gen;
    smul_ok g k gen; smul_ok g (k % q) gen;
    g.ok_add a1 (smul g u2 qp);
    g.ok_add a1 (smul g (u2 * d) gen);
    smul_congr g u2 qp (smul g d gen);
    smul_mul g u2 d gen;
    g.eqv_sym (smul g (u2 * d) gen) (smul g u2 (smul g d gen));
    g.eqv_trans (smul g u2 qp) (smul g u2 (smul g d gen)) (smul g (u2 * d) gen);
    g.eqv_refl a1;
    g.add_congr a1 a1 (smul g u2 qp) (smul g (u2 * d) gen);
    smul_add g u1 (u2 * d) gen;
    g.eqv_sym (smul g k gen) (g.add a1 (smul g (u2 * d) gen));
    smul_mod g q k gen;
    trans3 g (g.add a1 (smul g u2 qp)) (g.add a1 (smul g (u2 * d) gen))
           (smul g k gen) (smul g (k % q) gen)

(** {2 Cancellation}

    Two points with a common "negative" are equal.  This is what makes
    [(q - k) G] the negation of [k G], which is the low-S rule's reason for
    being harmless. *)
let cancel (#a: Type) (g: grp a) (p r x: a)
  : Lemma (requires g.ok p /\ g.ok r /\ g.ok x /\
                    g.eqv (g.add p x) g.zero /\ g.eqv (g.add r x) g.zero)
          (ensures g.eqv p r)
  = g.ok_zero ();
    let rx = g.add r x in
    let xr = g.add x r in
    g.ok_add r x; g.ok_add x r; g.ok_add p x;
    g.ok_add p rx; g.ok_add p xr; g.ok_add (g.add p x) r;
    g.ok_add g.zero r;
    add_zero_r g p;
    g.eqv_sym (g.add p g.zero) p;
    g.eqv_refl p;
    g.eqv_sym rx g.zero;
    g.add_congr p p g.zero rx;
    g.add_comm r x;
    g.add_congr p p rx xr;
    trans3 g p (g.add p g.zero) (g.add p rx) (g.add p xr);
    g.add_assoc p x r;
    g.eqv_sym (g.add (g.add p x) r) (g.add p xr);
    g.eqv_refl r;
    g.add_congr (g.add p x) g.zero r r;
    g.add_id r;
    trans3 g (g.add p xr) (g.add (g.add p x) r) (g.add g.zero r) r;
    g.eqv_trans p (g.add p xr) r

(** [(q - k) P] is the point that cancels [k P]. *)
let smul_neg (#a: Type) (g: grp a) (q: pos) (k: nat { k <= q }) (p x: a)
  : Lemma (requires has_order g q p /\ g.ok x /\ g.eqv (g.add x (smul g k p)) g.zero)
          (ensures g.eqv (smul g (q - k) p) x)
  = smul_ok g k p; smul_ok g (q - k) p; smul_ok g q p;
    smul_add g (q - k) k p;
    g.ok_add (smul g (q - k) p) (smul g k p);
    g.ok_zero ();
    g.eqv_sym (smul g q p) (g.add (smul g (q - k) p) (smul g k p));
    g.eqv_trans (g.add (smul g (q - k) p) (smul g k p)) (smul g q p) g.zero;
    cancel g (smul g (q - k) p) x (smul g k p)

#pop-options

(** {2 The scalar side}

    What the verifier recovers from a signature, computed in
    [Spec.ModArith] modulo the order.  With [A = m + r d] and
    [s = k^-1 A], the verifier's [u1 + u2 d = s^-1 m + s^-1 r d = s^-1 A]
    is [k]; with [-s] in place of [s] it is [-k]. *)

module MA = Spec.ModArith

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let mul_add_distr (#q: pos) (a b c: MA.elem q)
  : Lemma (MA.mul a (MA.add b c) == MA.add (MA.mul a b) (MA.mul a c))
  = M.lemma_mod_mul_distr_r a (b + c) q;
    M.distributivity_add_right a b c;
    M.lemma_mod_plus_distr_l (a * b) (a * c) q;
    M.lemma_mod_plus_distr_r ((a * b) % q) (a * c) q

let mul_neg (#q: pos) (a b: MA.elem q)
  : Lemma (MA.mul a (MA.neg b) == MA.neg (MA.mul a b))
  = calc (==) {
      (a * ((q - b) % q)) % q;
      == { M.lemma_mod_mul_distr_r a (q - b) q }
      (a * (q - b)) % q;
      == { M.distributivity_sub_right a q b }
      (- (a * b) + a * q) % q;
      == { M.lemma_mod_plus (- (a * b)) a q }
      (- (a * b)) % q;
      == { M.lemma_mod_sub_distr 0 (a * b) q }
      (- ((a * b) % q)) % q;
      == { M.lemma_mod_plus (- ((a * b) % q)) 1 q }
      (q - (a * b) % q) % q;
    }

(** [u1 + u2 d], reduced, as the ring sum. *)
let reduce_sum (#q: pos) (u1 u2 d: MA.elem q)
  : Lemma ((u1 + u2 * d) % q == MA.add u1 (MA.mul u2 d))
  = M.lemma_mod_plus_distr_r u1 (u2 * d) q

let recover_a (#q: pos { 1 < q }) (m r d si: MA.elem q)
  : Lemma ((MA.mul si m + MA.mul si r * d) % q ==
           MA.mul si (MA.add m (MA.mul r d)))
  = reduce_sum (MA.mul si m) (MA.mul si r) d;
    MA.mul_assoc si r d;
    mul_add_distr si m (MA.mul r d)

(** [s^-1 A = k] when [s = k^-1 A]: the nonce comes back. *)
let recover_nonce (#q: pos { 1 < q }) (m r d k ki si: MA.elem q)
  : Lemma (requires MA.mul k ki == MA.one /\
                    MA.mul si (MA.mul ki (MA.add m (MA.mul r d))) == MA.one)
          (ensures (MA.mul si m + MA.mul si r * d) % q == k)
  = let a = MA.add m (MA.mul r d) in
    let s = MA.mul ki a in
    recover_a m r d si;
    MA.mul_assoc k ki a;
    MA.mul_comm MA.one a; MA.mul_one a;
    assert (MA.mul k s == a);
    MA.mul_assoc si k s;
    MA.mul_comm si k;
    MA.mul_assoc k si s;
    MA.mul_one k

(** The same with [-s]: the verifier recovers [-k]. *)
let recover_neg_nonce (#q: pos { 1 < q }) (m r d k ki si: MA.elem q)
  : Lemma (requires 0 < k /\ MA.mul k ki == MA.one /\
                    MA.mul si (MA.neg (MA.mul ki (MA.add m (MA.mul r d)))) == MA.one)
          (ensures (MA.mul si m + MA.mul si r * d) % q == q - k)
  = let a = MA.add m (MA.mul r d) in
    let s = MA.mul ki a in
    recover_a m r d si;
    MA.mul_assoc k ki a;
    MA.mul_comm MA.one a; MA.mul_one a;
    assert (MA.mul k s == a);
    mul_neg k s;
    assert (MA.mul k (MA.neg s) == MA.neg a);
    MA.mul_assoc si k (MA.neg s);
    MA.mul_comm si k;
    MA.mul_assoc k si (MA.neg s);
    MA.mul_one k;
    assert (MA.mul si (MA.neg a) == k);
    mul_neg si a;
    assert (MA.neg (MA.mul si a) == k);
    M.small_mod (q - k) q;
    if MA.mul si a = 0 then () else M.small_mod (q - MA.mul si a) q

#pop-options
