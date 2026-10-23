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

(** The scalar multiple, over an abstract commutative group.

    A windowed scalar multiplication needs three facts and no more: that
    the multiple by [a + b] splits into a sum, that the multiple by [2n] is
    a doubling, and that both respect equivalence.  None of them mentions a
    curve.  They are proved here once, over a record of operations and the
    axioms they satisfy, and instantiated by {!Spec.K256.Smul} and
    {!Spec.P256.Smul}.

    Doing it this way is not only tidiness.  On the curves, [on_curve] and
    [peq] unfold to field equations over a 78-digit prime, and a goal that
    mentions a handful of them is minutes of Z3 time; the same goal over an
    abstract predicate is milliseconds.  The curve modules pay that cost
    once, in the record, and never again.

    The group is written additively because the points are.  It need not be
    a group in the strict sense -- nothing below uses inverses -- but it
    must be a commutative monoid whose equivalence is a congruence, and the
    curves are that. *)
module Spec.Group.Smul

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(** {2 The axioms}

    [ok] is the carrier -- on a curve this is [on_curve], which is not a
    refinement of the type because the addition law is total on triples --
    and [eqv] the equivalence, which is coarser than [==] because a
    projective point has many representations.  Every axiom is conditioned
    on [ok], and every operation is required to preserve it. *)
noeq type grp (a: Type) = {
  ok: a -> prop;
  eqv: a -> a -> prop;
  zero: a;
  add: a -> a -> a;
  dbl: a -> a;

  ok_zero: unit -> Lemma (ok zero);
  ok_add: (p: a) -> (q: a) ->
    Lemma (requires ok p /\ ok q) (ensures ok (add p q));
  ok_dbl: (p: a) ->
    Lemma (requires ok p) (ensures ok (dbl p));

  eqv_refl: (p: a) -> Lemma (requires ok p) (ensures eqv p p);
  eqv_sym: (p: a) -> (q: a) ->
    Lemma (requires ok p /\ ok q /\ eqv p q) (ensures eqv q p);
  eqv_trans: (p: a) -> (q: a) -> (r: a) ->
    Lemma (requires ok p /\ ok q /\ ok r /\ eqv p q /\ eqv q r)
          (ensures eqv p r);

  add_congr: (p: a) -> (p': a) -> (q: a) -> (q': a) ->
    Lemma (requires ok p /\ ok p' /\ ok q /\ ok q' /\ eqv p p' /\ eqv q q')
          (ensures eqv (add p q) (add p' q'));
  add_assoc: (p: a) -> (q: a) -> (r: a) ->
    Lemma (requires ok p /\ ok q /\ ok r)
          (ensures eqv (add (add p q) r) (add p (add q r)));
  add_comm: (p: a) -> (q: a) ->
    Lemma (requires ok p /\ ok q) (ensures eqv (add p q) (add q p));
  add_id: (p: a) ->
    Lemma (requires ok p) (ensures eqv (add zero p) p);
  dbl_is_add: (p: a) ->
    Lemma (requires ok p) (ensures eqv (dbl p) (add p p));
}

(** {2 The scalar multiple}

    Left-associated on purpose: [smul (n + 1) p] is [p] added to the
    smaller multiple, so the induction in {!smul_add} peels from the front
    and the rewrite it needs is associativity in the direction the axiom is
    stated. *)
let rec smul (#a: Type) (g: grp a) (n: nat) (p: a) : Tot a (decreases n) =
  if n = 0 then g.zero else g.add p (smul g (n - 1) p)

let rec smul_ok (#a: Type) (g: grp a) (n: nat) (p: a)
  : Lemma (requires g.ok p) (ensures g.ok (smul g n p)) (decreases n)
  = if n = 0 then g.ok_zero ()
    else (smul_ok g (n - 1) p; g.ok_add p (smul g (n - 1) p))

#push-options "--fuel 2"
let smul_one (#a: Type) (g: grp a) (p: a)
  : Lemma (requires g.ok p) (ensures g.eqv (smul g 1 p) p)
  = g.ok_zero ();
    g.add_comm p g.zero;
    g.add_id p;
    g.ok_add p g.zero;
    g.ok_add g.zero p;
    g.eqv_trans (g.add p g.zero) (g.add g.zero p) p
#pop-options

(** {2 Congruence}

    A window builds its table from a point that is only equivalent to the
    one the caller supplied -- the doubling that produced it is not the
    specification's doubling -- so every multiple has to respect
    equivalence. *)
let rec smul_congr (#a: Type) (g: grp a) (n: nat) (p q: a)
  : Lemma (requires g.ok p /\ g.ok q /\ g.eqv p q)
          (ensures g.eqv (smul g n p) (smul g n q))
          (decreases n)
  = if n = 0 then (g.ok_zero (); g.eqv_refl g.zero)
    else begin
      smul_congr g (n - 1) p q;
      smul_ok g (n - 1) p;
      smul_ok g (n - 1) q;
      g.add_congr p q (smul g (n - 1) p) (smul g (n - 1) q)
    end

(** {2 Additivity}

    The one fact a window is for.  Induction on [a], peeling a single [p]
    off the front: the step is one congruence and one associativity. *)
let rec smul_add (#a: Type) (g: grp a) (m n: nat) (p: a)
  : Lemma (requires g.ok p)
          (ensures g.eqv (smul g (m + n) p) (g.add (smul g m p) (smul g n p)))
          (decreases m)
  = smul_ok g m p;
    smul_ok g n p;
    smul_ok g (m + n) p;
    if m = 0 then begin
      g.ok_zero ();
      g.add_id (smul g n p);
      g.ok_add g.zero (smul g n p);
      g.eqv_sym (g.add g.zero (smul g n p)) (smul g n p)
    end else begin
      let m' = m - 1 in
      smul_add g m' n p;
      smul_ok g m' p;
      smul_ok g (m' + n) p;
      g.eqv_refl p;
      g.ok_add (smul g m' p) (smul g n p);
      g.add_congr p p (smul g (m' + n) p) (g.add (smul g m' p) (smul g n p));
      g.add_assoc p (smul g m' p) (smul g n p);
      g.ok_add p (smul g m' p);
      g.ok_add (g.add p (smul g m' p)) (smul g n p);
      g.ok_add p (g.add (smul g m' p) (smul g n p));
      g.eqv_sym (g.add (g.add p (smul g m' p)) (smul g n p))
                (g.add p (g.add (smul g m' p) (smul g n p)));
      g.ok_add p (smul g (m' + n) p);
      g.eqv_trans (smul g (m + n) p)
                  (g.add p (g.add (smul g m' p) (smul g n p)))
                  (g.add (smul g m p) (smul g n p))
    end

(** Doubling, which is additivity at [m = n] composed with the fact that
    the doubling operation agrees with the addition. *)
let smul_dbl (#a: Type) (g: grp a) (n: nat) (p: a)
  : Lemma (requires g.ok p)
          (ensures g.eqv (smul g (2 * n) p) (g.dbl (smul g n p)))
  = smul_ok g n p;
    smul_ok g (2 * n) p;
    smul_add g n n p;
    g.dbl_is_add (smul g n p);
    g.ok_add (smul g n p) (smul g n p);
    g.ok_dbl (smul g n p);
    g.eqv_sym (g.dbl (smul g n p)) (g.add (smul g n p) (smul g n p));
    g.eqv_trans (smul g (2 * n) p)
                (g.add (smul g n p) (smul g n p))
                (g.dbl (smul g n p))

(** {2 The two shapes a rung produces}

    A rung doubles an accumulator that is only equivalent to [smul n p],
    and adds a table entry that is only equivalent to [smul d p].  These
    are the forms an implementation's loop invariant wants: hypothesis and
    conclusion both of the shape [eqv <what the code holds> <a multiple>],
    with the equivalence reasoning already done. *)
let smul_dbl_congr (#a: Type) (g: grp a) (n: nat) (p q: a)
  : Lemma (requires g.ok p /\ g.ok q /\ g.eqv q (smul g n p))
          (ensures g.ok (g.dbl q) /\ g.eqv (g.dbl q) (smul g (2 * n) p))
  = smul_ok g n p;
    smul_ok g (2 * n) p;
    g.ok_dbl q;
    g.dbl_is_add q;
    g.add_congr q (smul g n p) q (smul g n p);
    g.ok_add q q;
    g.ok_add (smul g n p) (smul g n p);
    g.eqv_trans (g.dbl q) (g.add q q) (g.add (smul g n p) (smul g n p));
    smul_add g n n p;
    g.eqv_sym (smul g (2 * n) p) (g.add (smul g n p) (smul g n p));
    g.eqv_trans (g.dbl q) (g.add (smul g n p) (smul g n p))
                (smul g (2 * n) p)

let smul_add_congr (#a: Type) (g: grp a) (m n: nat) (p q r: a)
  : Lemma (requires g.ok p /\ g.ok q /\ g.ok r /\
                    g.eqv q (smul g m p) /\ g.eqv r (smul g n p))
          (ensures g.ok (g.add q r) /\ g.eqv (g.add q r) (smul g (m + n) p))
  = smul_ok g m p;
    smul_ok g n p;
    smul_ok g (m + n) p;
    g.ok_add q r;
    g.add_congr q (smul g m p) r (smul g n p);
    g.ok_add (smul g m p) (smul g n p);
    smul_add g m n p;
    g.eqv_sym (smul g (m + n) p) (g.add (smul g m p) (smul g n p));
    g.eqv_trans (g.add q r) (g.add (smul g m p) (smul g n p))
                (smul g (m + n) p)

(** Adding a single copy, which is the odd case of a bit-at-a-time ladder
    and the [d = 1] case of a window. *)
let smul_succ_congr (#a: Type) (g: grp a) (n: nat) (p q: a)
  : Lemma (requires g.ok p /\ g.ok q /\ g.eqv q (smul g n p))
          (ensures g.ok (g.add q p) /\ g.eqv (g.add q p) (smul g (n + 1) p))
  = smul_ok g 1 p;
    smul_one g p;
    g.eqv_sym (smul g 1 p) p;
    smul_add_congr g n 1 p q p

#pop-options

(** {2 The bit-at-a-time ladder}

    Double-and-add, most significant bit first, over an [n]-bit scalar.
    This is what every curve's [point_mul] is, and what the caller-visible
    specifications are stated in terms of; a windowed implementation has to
    be shown equivalent to it.  Proving it here rather than on the curve is
    what keeps the induction out of reach of the field equations: the only
    predicates the proof below mentions are the record's own projections,
    which are opaque.

    A curve connects its own step function to {!ladder_at} by
    [Hacl.Spec.Loops.repeati_g_ext], which is a pointwise equality of two
    unfoldings and mentions no equivalence at all. *)

module Loops = Hacl.Spec.Loops
module Math = FStar.Math.Lemmas

let gbit (k: nat) (i: nat) : b: nat { b < 2 } = (k / pow2 i) % 2

let ladder_step (#a: Type) (g: grp a) (n: nat) (k: nat) (p: a)
                (i: nat { i < n }) (acc: a) : a
  = let acc = g.dbl acc in
    if gbit k (n - 1 - i) = 1 then g.add acc p else acc

let ladder_at (#a: Type) (g: grp a) (n: nat) (k: nat) (p: a)
              (i: nat) (acc: a) : a
  = if i < n then ladder_step g n k p i acc else acc

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** [k / pow2 m] is twice [k / pow2 (m + 1)] plus the bit at [m]: one rung
    of the ladder consumes exactly one bit. *)
let shift_bit (k: nat) (m: nat)
  : Lemma (k / pow2 m == 2 * (k / pow2 (m + 1)) + gbit k m)
  = Math.pow2_plus 1 m;
    Math.division_multiplication_lemma k (pow2 m) 2;
    Math.euclidean_division_definition (k / pow2 m) 2

(** After [i] rungs the accumulator is the multiple by the top [i] bits. *)
let rec ladder_ok (#a: Type) (g: grp a) (n: nat) (k: nat) (p: a) (i: nat)
  : Lemma (requires g.ok p /\ k < pow2 n /\ i <= n)
          (ensures (let acc = Loops.repeati_g i (ladder_at g n k p) g.zero in
                    g.ok acc /\ g.eqv acc (smul g (k / pow2 (n - i)) p)))
          (decreases i)
  = if i = 0 then begin
      g.ok_zero ();
      Math.small_div k (pow2 n);
      g.eqv_refl g.zero
    end else begin
      let j = i - 1 in
      ladder_ok g n k p j;
      let acc = Loops.repeati_g j (ladder_at g n k p) g.zero in
      let e = k / pow2 (n - j) in
      Loops.unfold_repeati_g j (ladder_at g n k p) g.zero;
      shift_bit k (n - i);
      smul_dbl_congr g e p acc;
      if gbit k (n - i) = 1 then smul_succ_congr g (2 * e) p (g.dbl acc)
    end

(** The whole ladder, which is the statement a curve exports. *)
let ladder_is_smul (#a: Type) (g: grp a) (n: nat) (k: nat) (p: a)
  : Lemma (requires g.ok p /\ k < pow2 n)
          (ensures (let r = Loops.repeati_g n (ladder_at g n k p) g.zero in
                    g.ok r /\ g.eqv r (smul g k p)))
  = ladder_ok g n k p n;
    assert_norm (pow2 0 == 1)

#pop-options

(** {2 Repeated doubling}

    A fixed-base window needs the points [2^(64 j) G] compiled into the
    binary, and the only honest way to say what those constants are is as
    the result of a doubling chain.  [dblk n q] is [n] doublings; the
    lemma says that if [q] is a multiple of [p] then so is the chain, with
    the multiplier shifted left by [n].

    The chain itself is evaluated by the normaliser on concrete field
    elements, once, at typechecking time.  What cannot be evaluated is
    [smul (2^64) p], which is [2^64] additions; that is what this lemma is
    for. *)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 50"

let rec dblk (#a: Type) (g: grp a) (n: nat) (q: a) : Tot a (decreases n) =
  if n = 0 then q else dblk g (n - 1) (g.dbl q)

let rec dblk_ok (#a: Type) (g: grp a) (n: nat) (m: nat) (p q: a)
  : Lemma (requires g.ok p /\ g.ok q /\ g.eqv q (smul g m p))
          (ensures g.ok (dblk g n q) /\
                   g.eqv (dblk g n q) (smul g (pow2 n * m) p))
          (decreases n)
  = if n = 0 then assert_norm (pow2 0 == 1)
    else begin
      smul_dbl_congr g m p q;
      dblk_ok g (n - 1) (2 * m) p (g.dbl q);
      Math.pow2_plus 1 (n - 1);
      assert_norm (pow2 1 == 2);
      Math.paren_mul_right (pow2 (n - 1)) 2 m
    end

#pop-options

(** {2 Two bases}

    A double-scalar multiplication [[m]P + [n]R] shares one doubling chain
    between the two scalars: every rung doubles the accumulator once and
    adds a table entry from either side.  [lin2] is what the accumulator
    denotes, and the three lemmas after it are the three things a rung
    does to it.  Like everything above, none of them needs inverses. *)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 50"

let lin2 (#a: Type) (g: grp a) (m n: nat) (p r: a) : a =
  g.add (smul g m p) (smul g n r)

let lin2_ok (#a: Type) (g: grp a) (m n: nat) (p r: a)
  : Lemma (requires g.ok p /\ g.ok r) (ensures g.ok (lin2 g m n p r))
  = smul_ok g m p; smul_ok g n r; g.ok_add (smul g m p) (smul g n r)

(** [x + (y + z)] is [y + (x + z)]. *)
let add_lcomm (#a: Type) (g: grp a) (x y z: a)
  : Lemma (requires g.ok x /\ g.ok y /\ g.ok z)
          (ensures g.eqv (g.add x (g.add y z)) (g.add y (g.add x z)))
  = g.ok_add x y; g.ok_add y x; g.ok_add y z; g.ok_add x z;
    g.ok_add (g.add x y) z; g.ok_add (g.add y x) z;
    g.ok_add x (g.add y z); g.ok_add y (g.add x z);
    g.add_assoc x y z;
    g.eqv_sym (g.add (g.add x y) z) (g.add x (g.add y z));
    g.add_comm x y;
    g.eqv_refl z;
    g.add_congr (g.add x y) (g.add y x) z z;
    g.add_assoc y x z;
    g.eqv_trans (g.add x (g.add y z)) (g.add (g.add x y) z) (g.add (g.add y x) z);
    g.eqv_trans (g.add x (g.add y z)) (g.add (g.add y x) z) (g.add y (g.add x z))

(** [(x + y) + (z + w)] is [(x + z) + (y + w)]. *)
let add_swap (#a: Type) (g: grp a) (x y z w: a)
  : Lemma (requires g.ok x /\ g.ok y /\ g.ok z /\ g.ok w)
          (ensures g.eqv (g.add (g.add x y) (g.add z w))
                         (g.add (g.add x z) (g.add y w)))
  = g.ok_add x y; g.ok_add z w; g.ok_add x z; g.ok_add y w;
    g.ok_add y (g.add z w); g.ok_add z (g.add y w);
    g.ok_add (g.add x y) (g.add z w); g.ok_add (g.add x z) (g.add y w);
    g.ok_add x (g.add y (g.add z w)); g.ok_add x (g.add z (g.add y w));
    g.add_assoc x y (g.add z w);
    add_lcomm g y z w;
    g.eqv_refl x;
    g.add_congr x x (g.add y (g.add z w)) (g.add z (g.add y w));
    g.add_assoc x z (g.add y w);
    g.eqv_sym (g.add (g.add x z) (g.add y w)) (g.add x (g.add z (g.add y w)));
    g.eqv_trans (g.add (g.add x y) (g.add z w)) (g.add x (g.add y (g.add z w)))
                (g.add x (g.add z (g.add y w)));
    g.eqv_trans (g.add (g.add x y) (g.add z w)) (g.add x (g.add z (g.add y w)))
                (g.add (g.add x z) (g.add y w))

(** The empty combination is the identity. *)
let lin2_zero (#a: Type) (g: grp a) (p r: a)
  : Lemma (requires g.ok p /\ g.ok r)
          (ensures g.ok g.zero /\ g.eqv g.zero (lin2 g 0 0 p r))
  = g.ok_zero ();
    g.ok_add g.zero g.zero;
    g.add_id g.zero;
    g.eqv_sym (g.add g.zero g.zero) g.zero

let lin2_dbl (#a: Type) (g: grp a) (m n: nat) (p r q: a)
  : Lemma (requires g.ok p /\ g.ok r /\ g.ok q /\ g.eqv q (lin2 g m n p r))
          (ensures g.ok (g.dbl q) /\ g.eqv (g.dbl q) (lin2 g (2 * m) (2 * n) p r))
  = let mp = smul g m p in
    let nr = smul g n r in
    let l = g.add mp nr in
    smul_ok g m p; smul_ok g n r; smul_ok g (m + m) p; smul_ok g (n + n) r;
    lin2_ok g m n p r; lin2_ok g (m + m) (n + n) p r;
    g.ok_dbl q; g.ok_add q q; g.ok_add l l;
    g.ok_add mp mp; g.ok_add nr nr; g.ok_add (g.add mp mp) (g.add nr nr);
    g.dbl_is_add q;
    g.add_congr q l q l;
    add_swap g mp nr mp nr;
    smul_add g m m p; smul_add g n n r;
    g.eqv_sym (smul g (m + m) p) (g.add mp mp);
    g.eqv_sym (smul g (n + n) r) (g.add nr nr);
    g.add_congr (g.add mp mp) (smul g (m + m) p) (g.add nr nr) (smul g (n + n) r);
    g.eqv_trans (g.dbl q) (g.add q q) (g.add l l);
    g.eqv_trans (g.dbl q) (g.add l l) (g.add (g.add mp mp) (g.add nr nr));
    g.eqv_trans (g.dbl q) (g.add (g.add mp mp) (g.add nr nr))
                (lin2 g (m + m) (n + n) p r)

(** Adding a multiple of the first base. *)
let lin2_addl (#a: Type) (g: grp a) (m n d: nat) (p r q e: a)
  : Lemma (requires g.ok p /\ g.ok r /\ g.ok q /\ g.ok e /\
                    g.eqv q (lin2 g m n p r) /\ g.eqv e (smul g d p))
          (ensures g.ok (g.add q e) /\ g.eqv (g.add q e) (lin2 g (m + d) n p r))
  = let mp = smul g m p in
    let nr = smul g n r in
    let dp = smul g d p in
    let l = g.add mp nr in
    smul_ok g m p; smul_ok g n r; smul_ok g d p; smul_ok g (m + d) p;
    lin2_ok g m n p r; lin2_ok g (m + d) n p r;
    g.ok_add q e; g.ok_add l dp; g.ok_add nr dp; g.ok_add dp nr;
    g.ok_add mp (g.add nr dp); g.ok_add mp (g.add dp nr); g.ok_add mp dp;
    g.ok_add (g.add mp dp) nr;
    g.add_congr q l e dp;
    g.add_assoc mp nr dp;
    g.add_comm nr dp;
    g.eqv_refl mp;
    g.add_congr mp mp (g.add nr dp) (g.add dp nr);
    g.add_assoc mp dp nr;
    g.eqv_sym (g.add (g.add mp dp) nr) (g.add mp (g.add dp nr));
    smul_add g m d p;
    g.eqv_sym (smul g (m + d) p) (g.add mp dp);
    g.eqv_refl nr;
    g.add_congr (g.add mp dp) (smul g (m + d) p) nr nr;
    g.eqv_trans (g.add q e) (g.add l dp) (g.add mp (g.add nr dp));
    g.eqv_trans (g.add q e) (g.add mp (g.add nr dp)) (g.add mp (g.add dp nr));
    g.eqv_trans (g.add q e) (g.add mp (g.add dp nr)) (g.add (g.add mp dp) nr);
    g.eqv_trans (g.add q e) (g.add (g.add mp dp) nr) (lin2 g (m + d) n p r)

(** Adding a multiple of the second. *)
let lin2_addr (#a: Type) (g: grp a) (m n d: nat) (p r q e: a)
  : Lemma (requires g.ok p /\ g.ok r /\ g.ok q /\ g.ok e /\
                    g.eqv q (lin2 g m n p r) /\ g.eqv e (smul g d r))
          (ensures g.ok (g.add q e) /\ g.eqv (g.add q e) (lin2 g m (n + d) p r))
  = let mp = smul g m p in
    let nr = smul g n r in
    let dr = smul g d r in
    let l = g.add mp nr in
    smul_ok g m p; smul_ok g n r; smul_ok g d r; smul_ok g (n + d) r;
    lin2_ok g m n p r; lin2_ok g m (n + d) p r;
    g.ok_add q e; g.ok_add l dr; g.ok_add nr dr;
    g.ok_add mp (g.add nr dr);
    g.add_congr q l e dr;
    g.add_assoc mp nr dr;
    smul_add g n d r;
    g.eqv_sym (smul g (n + d) r) (g.add nr dr);
    g.eqv_refl mp;
    g.add_congr mp mp (g.add nr dr) (smul g (n + d) r);
    g.eqv_trans (g.add q e) (g.add l dr) (g.add mp (g.add nr dr));
    g.eqv_trans (g.add q e) (g.add mp (g.add nr dr)) (lin2 g m (n + d) p r)

(** The multiple distributes over the sum of two points. *)
let rec smul_distr (#a: Type) (g: grp a) (n: nat) (p r: a)
  : Lemma (requires g.ok p /\ g.ok r)
          (ensures g.eqv (smul g n (g.add p r)) (g.add (smul g n p) (smul g n r)))
          (decreases n)
  = g.ok_add p r;
    smul_ok g n (g.add p r); smul_ok g n p; smul_ok g n r;
    g.ok_add (smul g n p) (smul g n r);
    if n = 0 then begin
      g.ok_zero ();
      g.add_id g.zero;
      g.eqv_sym (g.add g.zero g.zero) g.zero
    end else begin
      let pr = g.add p r in
      let a1 = smul g (n - 1) p in
      let b1 = smul g (n - 1) r in
      smul_distr g (n - 1) p r;
      smul_ok g (n - 1) pr; smul_ok g (n - 1) p; smul_ok g (n - 1) r;
      g.ok_add a1 b1; g.ok_add pr (smul g (n - 1) pr); g.ok_add pr (g.add a1 b1);
      g.eqv_refl pr;
      g.add_congr pr pr (smul g (n - 1) pr) (g.add a1 b1);
      add_swap g p r a1 b1;
      g.eqv_trans (smul g n pr) (g.add pr (g.add a1 b1))
                  (g.add (smul g n p) (smul g n r))
    end

(** Every multiple of the identity is the identity. *)
let rec smul_of_zero (#a: Type) (g: grp a) (n: nat)
  : Lemma (ensures g.ok (smul g n g.zero) /\ g.eqv (smul g n g.zero) g.zero)
          (decreases n)
  = g.ok_zero ();
    smul_ok g n g.zero;
    if n = 0 then g.eqv_refl g.zero
    else begin
      smul_of_zero g (n - 1);
      smul_ok g (n - 1) g.zero;
      g.add_id (smul g (n - 1) g.zero);
      g.eqv_trans (smul g n g.zero) (smul g (n - 1) g.zero) g.zero
    end

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** Moving a term across an equation, which is where inverses come in --
    as a hypothesis about two particular points rather than as an axiom of
    the record: [u + v] is the identity.  Then [u + s = x] exactly when
    [s = x + v]. *)
let cancel (#a: Type) (g: grp a) (u v s x: a)
  : Lemma (requires g.ok u /\ g.ok v /\ g.ok s /\ g.ok x /\
                    g.eqv (g.add u v) g.zero)
          (ensures g.eqv (g.add u s) x <==> g.eqv s (g.add x v))
  = g.ok_zero ();
    g.ok_add u v; g.ok_add v u; g.ok_add u s; g.ok_add x v; g.ok_add v x;
    g.ok_add g.zero s; g.ok_add (g.add u v) s; g.ok_add (g.add v u) s;
    g.ok_add v (g.add u s);
    g.ok_add u (g.add x v); g.ok_add (g.add x v) u; g.ok_add x (g.add v u);
    g.ok_add x (g.add u v); g.ok_add x g.zero; g.ok_add g.zero x;
    let fwd () : Lemma (requires g.eqv (g.add u s) x) (ensures g.eqv s (g.add x v)) =
      g.add_id s;
      g.eqv_sym (g.add g.zero s) s;
      g.eqv_sym (g.add u v) g.zero;
      g.eqv_refl s;
      g.add_congr g.zero (g.add u v) s s;
      g.add_comm u v;
      g.add_congr (g.add u v) (g.add v u) s s;
      g.add_assoc v u s;
      g.eqv_refl v;
      g.add_congr v v (g.add u s) x;
      g.add_comm v x;
      g.eqv_trans s (g.add g.zero s) (g.add (g.add u v) s);
      g.eqv_trans s (g.add (g.add u v) s) (g.add (g.add v u) s);
      g.eqv_trans s (g.add (g.add v u) s) (g.add v (g.add u s));
      g.eqv_trans s (g.add v (g.add u s)) (g.add v x);
      g.eqv_trans s (g.add v x) (g.add x v)
    in
    let bwd () : Lemma (requires g.eqv s (g.add x v)) (ensures g.eqv (g.add u s) x) =
      g.eqv_refl u;
      g.add_congr u u s (g.add x v);
      g.add_comm u (g.add x v);
      g.add_assoc x v u;
      g.eqv_refl x;
      g.add_comm v u;
      g.add_congr x x (g.add v u) (g.add u v);
      g.add_congr x x (g.add u v) g.zero;
      g.add_comm x g.zero;
      g.add_id x;
      g.eqv_trans (g.add u s) (g.add u (g.add x v)) (g.add (g.add x v) u);
      g.eqv_trans (g.add u s) (g.add (g.add x v) u) (g.add x (g.add v u));
      g.eqv_trans (g.add u s) (g.add x (g.add v u)) (g.add x (g.add u v));
      g.eqv_trans (g.add u s) (g.add x (g.add u v)) (g.add x g.zero);
      g.eqv_trans (g.add u s) (g.add x g.zero) (g.add g.zero x);
      g.eqv_trans (g.add u s) (g.add g.zero x) x
    in
    FStar.Classical.move_requires fwd ();
    FStar.Classical.move_requires bwd ()

#pop-options
