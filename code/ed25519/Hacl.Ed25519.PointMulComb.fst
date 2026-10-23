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

(** Multiplying the generator with a signed radix-sixteen comb.

    The scalar is reduced modulo the group order, so it has 253 bits, and
    recoded into sixty-four signed digits [d_i] in [[-8, 8)]:

    {[ k = sum_i d_i 16^i = 16 sum_j d_{2j+1} 256^j + sum_j d_{2j} 256^j ]}

    Table [j] of {!Hacl.Ed25519.CombData} holds [m 256^j G] for [m] in
    [[0, 8]], affine and in the stored form [(y + x, y - x, 2 d x y)], so
    that each digit costs one seven-multiplication mixed addition and a
    constant-time scan of nine entries; a negative digit swaps the first
    two coordinates and negates the third.  The odd digits are added up,
    the sum is doubled four times, and the even digits are added on top:
    sixty-four mixed additions and four doublings in all, against the
    sixty-four full additions and sixty doublings of the four-way window.

    The layout is the reference implementation's ("ref10"); the facts
    about the tables are in {!Hacl.Ed25519.CombDataOk}, and the recoding
    and the group arithmetic in {!Spec.Ed25519.Comb}. *)
module Hacl.Ed25519.PointMulComb

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Curve25519.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module UInt = FStar.UInt
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module C = Spec.Curve25519
module E = Spec.Ed25519
module GR = Spec.Ed25519.Group
module SM = Spec.Ed25519.Smul
module O = Spec.Ed25519.Order
module CB = Spec.Ed25519.Comb
module CT = Spec.Ed25519.CombTable
module CE = Hacl.Ed25519.CombEnt
module CD = Hacl.Ed25519.CombData
module CDO = Hacl.Ed25519.CombDataOk
module LM = Hacl.Impl.Limb
module BB = Hacl.Bignum.Base
module B = Hacl.Spec.Bytes
module Math = FStar.Math.Lemmas
module P = Hacl.Ed25519.Point
module W = Hacl.Ed25519.PointWin
module Scalar = Hacl.Ed25519.Scalar
module G = Pulse.Lib.GlobalArray
module Table = Hacl.Impl.Table
module Launder = Hacl.Launder
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The spec side} *)

let vals_same (s: Seq.seq S64.t) : Lemma (vals s == LM.vals s)
  = Seq.lemma_eq_intro (vals s) (LM.vals s)

(** The point a signed digit selects from table [j]. *)
let sel_pt (j: nat { j < 32 }) (e: int { -8 <= e /\ e <= 8 }) : E.ext_point =
  if e < 0 then E.point_negate (CT.tp j (- e)) else CT.tp j e

let isq_repq (p: E.ext_point) (n: nat)
  : Lemma (requires CB.isq p n) (ensures CB.repq p n)
  = CB.isq_elim p n;
    CB.repq_intro p n

let sel_ok (j: nat { j < 32 }) (e: int { -8 <= e /\ e <= 8 })
  : Lemma (CB.affine (sel_pt j e) /\ CB.repq (sel_pt j e) (e * pow2 (8 * j)))
  = if e < 0 then begin
      let m : nat = - e in
      Math.nat_times_nat_is_nat m (pow2 (8 * j));
      let n : nat = m * pow2 (8 * j) in
      CT.tp_ok j m;
      isq_repq (CT.tp j m) n;
      CB.repq_neg (CT.tp j m) n;
      CB.to_niels_negate (CT.tp j m);
      Math.neg_mul_left m (pow2 (8 * j));
      CB.repq_cong (E.point_negate (CT.tp j m)) (- n) (e * pow2 (8 * j))
    end else begin
      Math.nat_times_nat_is_nat e (pow2 (8 * j));
      CT.tp_ok j e;
      isq_repq (CT.tp j e) (e * pow2 (8 * j))
    end

(** The absolute value of digit [v - 8], as the code computes it. *)
let absd (v: nat { v < 16 }) : (m: nat { m < 9 }) = if v < 8 then 8 - v else v - 8

(** What the selection leaves in the three registers. *)
let seln (j: nat { j < 32 }) (v: nat { v < 16 }) : CB.niels =
  if v < 8 then CB.neg_niels (CB.to_niels (CT.tp j (absd v)))
  else CB.to_niels (CT.tp j (absd v))

(** One digit's addition: the accumulator moves by [(v - 8) 256^j]. *)
let step_ok (p: E.ext_point) (n: int) (j: nat { j < 32 }) (v: nat { v < 16 })
            (r: E.ext_point)
  : Lemma (requires CB.repq p n /\ r == CB.madd p (seln j v))
          (ensures CB.repq r (n + (v - 8) * pow2 (8 * j)))
  = let e = v - 8 in
    if v < 8 then CB.to_niels_negate (CT.tp j (absd v));
    assert (seln j v == CB.to_niels (sel_pt j e));
    sel_ok j e;
    CB.madd_ok p (sel_pt j e);
    CB.repq_add p (sel_pt j e) n (e * pow2 (8 * j))

(** The table's contract, behind a name the solver cannot unfold: the
    quantifier inside is used once per digit, in [ent_ok]. *)
[@@"opaque_to_smt"]
let tok (s: Seq.seq S64.t) : prop = CE.ntok s

let tok_intro (s: Seq.seq S64.t)
  : Lemma (requires CE.ntok s) (ensures tok s /\ Seq.length s == 4320)
  = reveal_opaque (`%tok) (tok s)

let tok_len (s: Seq.seq S64.t)
  : Lemma (requires tok s) (ensures Seq.length s == 4320)
  = reveal_opaque (`%tok) (tok s)

(** The three registers read from the table are the stored form. *)
let ent_ok (s: Seq.seq S64.t) (j: nat { j < 32 }) (m: nat { m < 9 })
           (a b c: Seq.seq S64.t)
  : Lemma (requires tok s /\ Seq.length s == 4320 /\
             a == Seq.slice s (CE.eoff j m) (CE.eoff j m + 5) /\
             b == Seq.slice s (CE.eoff j m + 5) (CE.eoff j m + 10) /\
             c == Seq.slice s (CE.eoff j m + 10) (CE.eoff j m + 15))
          (ensures felem (vals a) /\ felem (vals b) /\ felem (vals c) /\
                   (fev (vals a), fev (vals b), fev (vals c)) ==
                     CB.to_niels (CT.tp j m))
  = reveal_opaque (`%tok) (tok s);
    assert (CE.nent s (CE.eoff j m) (CT.tp j m));
    vals_same a; vals_same b; vals_same c

(** The negation in registers, read back. *)
let neg_ok (j: nat { j < 32 }) (v: nat { v < 16 }) (a b c a' b' c': C.elem)
  : Lemma (requires (a, b, c) == CB.to_niels (CT.tp j (absd v)) /\
                    (v < 8 ==> a' == b /\ b' == a /\ c' == C.fsub 0 c) /\
                    (v >= 8 ==> a' == a /\ b' == b /\ c' == c))
          (ensures (a', b', c') == seln j v)
  = ()

#pop-options

(** {2 Selecting an entry}

    [select3 pa pb pc tbl o d] copies the three coordinates of entry [d]
    of the nine-entry table at [o] into [pa], [pb] and [pc], reading all
    nine.  Neither the time taken nor the addresses touched depend on [d]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn select3 (pa pb pc: A.array S64.t) (tbl: A.array S64.t) (o: SZ.t) (d: S64.t)
           (#va #vb #vc: erased (Seq.seq S64.t))
           (#pt: perm) (#vt: erased (Seq.seq S64.t))
requires A.pts_to pa va ** A.pts_to pb vb ** A.pts_to pc vc **
  A.pts_to tbl #pt vt **
  pure (Seq.length va == 5 /\ Seq.length vb == 5 /\ Seq.length vc == 5 /\
        Seq.length vt == 4320 /\ SZ.v o + 135 <= 4320 /\ S64.v d < 9)
ensures exists* (wa wb wc: Seq.seq S64.t).
  A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc **
  A.pts_to tbl #pt vt **
  pure (Seq.length vt == 4320 /\ SZ.v o + 135 <= 4320 /\ S64.v d < 9 /\
        Seq.length wa == 5 /\ Seq.length wb == 5 /\ Seq.length wc == 5 /\
        wa == Seq.slice vt (SZ.v o + 15 * S64.v d) (SZ.v o + 15 * S64.v d + 5) /\
        wb == Seq.slice vt (SZ.v o + 15 * S64.v d + 5) (SZ.v o + 15 * S64.v d + 10) /\
        wc == Seq.slice vt (SZ.v o + 15 * S64.v d + 10) (SZ.v o + 15 * S64.v d + 15))
{
  A.pts_to_len pa; A.pts_to_len pb; A.pts_to_len pc;
  A.pts_to_len tbl;
  assert_norm (pow2 64 - 1 =!= 0);
  let k : erased nat = hide (S64.v d);

  let zm = S64.zero;
  let mut mk = [| zm; 9sz |];
  Mem.track mk;
  A.pts_to_len mk;
  let mut e = 0sz;
  let mut ec = S64.classify 0uL;
  while (let ve = !e; SZ.lt ve 9sz)
  invariant exists* (ve: SZ.t) (vec: S64.t) (wm: Seq.seq S64.t).
    pts_to e ve ** pts_to ec vec ** A.pts_to mk wm **
    pure (SZ.v ve <= 9 /\ S64.v vec == SZ.v ve /\ Seq.length wm == 9 /\
          (forall (i: nat). i < SZ.v ve ==>
             BB.mask_for (Seq.index wm i) i (reveal k)))
  decreases (9 - SZ.v (!e))
  {
    let ve = !e;
    let vec = !ec;
    let m = Launder.launder (S64.eq_mask d vec);
    A.(mk.(ve) <- m);
    ec := S64.add_mod vec (S64.classify 1uL);
    e := SZ.add ve 1sz;
  };

  let mut l = 0sz;
  while (let vl = !l; SZ.lt vl 5sz)
  invariant exists* (vl: SZ.t) (wm wa wb wc: Seq.seq S64.t).
    pts_to l vl ** A.pts_to mk wm **
    A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc **
    A.pts_to tbl #pt vt **
    pure (SZ.v vl <= 5 /\ Seq.length wm == 9 /\
          Seq.length wa == 5 /\ Seq.length wb == 5 /\ Seq.length wc == 5 /\
          Seq.length vt == 4320 /\ SZ.v o + 135 <= 4320 /\ reveal k < 9 /\
          (forall (i: nat). i < 9 ==>
             BB.mask_for (Seq.index wm i) i (reveal k)) /\
          (forall (i: nat). i < SZ.v vl ==>
             Seq.index wa i == Seq.index vt (SZ.v o + 15 * reveal k + i) /\
             Seq.index wb i == Seq.index vt (SZ.v o + 15 * reveal k + 5 + i) /\
             Seq.index wc i == Seq.index vt (SZ.v o + 15 * reveal k + 10 + i)))
  decreases (5 - SZ.v (!l))
  {
    let vl = !l;
    let mut qa = S64.zero;
    let mut qb = S64.zero;
    let mut qc = S64.zero;
    let mut e2 = 0sz;
    while (let ve2 = !e2; SZ.lt ve2 9sz)
    invariant exists* (ve2: SZ.t) (xa xb xc: S64.t) (wm: Seq.seq S64.t).
      pts_to e2 ve2 ** pts_to qa xa ** pts_to qb xb ** pts_to qc xc **
      A.pts_to mk wm ** A.pts_to tbl #pt vt **
      pure (SZ.v ve2 <= 9 /\ Seq.length wm == 9 /\
            Seq.length vt == 4320 /\ SZ.v o + 135 <= 4320 /\
            reveal k < 9 /\ SZ.v vl < 5 /\
            (forall (i: nat). i < 9 ==>
               BB.mask_for (Seq.index wm i) i (reveal k)) /\
            xa == (if reveal k < SZ.v ve2
                   then Seq.index vt (SZ.v o + 15 * reveal k + SZ.v vl)
                   else S64.zero) /\
            xb == (if reveal k < SZ.v ve2
                   then Seq.index vt (SZ.v o + 15 * reveal k + 5 + SZ.v vl)
                   else S64.zero) /\
            xc == (if reveal k < SZ.v ve2
                   then Seq.index vt (SZ.v o + 15 * reveal k + 10 + SZ.v vl)
                   else S64.zero))
    decreases (9 - SZ.v (!e2))
    {
      let ve2 = !e2;
      let xa = !qa;
      let xb = !qb;
      let xc = !qc;
      let m = A.(mk.(ve2));
      BB.mask_for_is_mask m (SZ.v ve2) (reveal k);
      let at = SZ.add (SZ.add o (SZ.mul 15sz ve2)) vl;
      let ya = A.(tbl.(at));
      let yb = A.(tbl.(SZ.add at 5sz));
      let yc = A.(tbl.(SZ.add at 10sz));
      BB.or_zero xa; BB.zero_or ya;
      BB.or_zero xb; BB.zero_or yb;
      BB.or_zero xc; BB.zero_or yc;
      qa := S64.logor xa (BB.masked m ya);
      qb := S64.logor xb (BB.masked m yb);
      qc := S64.logor xc (BB.masked m yc);
      e2 := SZ.add ve2 1sz;
    };
    let xa = !qa;
    let xb = !qb;
    let xc = !qc;
    A.(pa.(vl) <- xa);
    A.(pb.(vl) <- xb);
    A.(pc.(vl) <- xc);
    l := SZ.add vl 1sz;
  };

  with wa wb wc.
    assert (A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc);
  let off : erased nat = hide (SZ.v o + 15 * reveal k);
  Seq.lemma_eq_intro wa (Seq.slice vt off (off + 5));
  Seq.lemma_eq_intro wb (Seq.slice vt (off + 5) (off + 10));
  Seq.lemma_eq_intro wc (Seq.slice vt (off + 10) (off + 15));
  Mem.wipe mk 9sz;
  ()
}

#pop-options

(** {2 The mixed addition}

    [madd x y z t a b c] is [(x, y, z, t) := madd (x, y, z, t) (a, b, c)],
    in place: every coordinate is read before any is written. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

fn madd (x y z t: A.array S64.t) (pa pb pc: A.array S64.t)
        (#vx #vy #vz #vt: erased (Seq.seq S64.t))
        (#p: perm) (#va #vb #vc: erased (Seq.seq S64.t))
requires
  A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz ** A.pts_to t vt **
  A.pts_to pa #p va ** A.pts_to pb #p vb ** A.pts_to pc #p vc **
  pure (P.pt_ok vx vy vz vt /\
        felem (vals va) /\ felem (vals vb) /\ felem (vals vc))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt **
  A.pts_to pa #p va ** A.pts_to pb #p vb ** A.pts_to pc #p vc **
  pure (P.pt_ok wx wy wz wt /\
        P.pt wx wy wz wt ==
          CB.madd (P.pt vx vy vz vt)
                  (fev (vals va), fev (vals vb), fev (vals vc)))
{
  let zz = S64.zero;
  let z128 = S128.zero;
  let mut au = [| zz; 5sz |];
  Mem.track au; A.pts_to_len au;
  let mut av = [| zz; 5sz |];
  Mem.track av; A.pts_to_len av;
  let mut aa = [| zz; 5sz |];
  Mem.track aa; A.pts_to_len aa;
  let mut ab = [| zz; 5sz |];
  Mem.track ab; A.pts_to_len ab;
  let mut ac = [| zz; 5sz |];
  Mem.track ac; A.pts_to_len ac;
  let mut ae = [| zz; 5sz |];
  Mem.track ae; A.pts_to_len ae;
  let mut aw = [| z128; 9sz |];
  Mem.track aw; A.pts_to_len aw;
  A.pts_to_len au; A.pts_to_len av; A.pts_to_len aa; A.pts_to_len ab;
  A.pts_to_len ac; A.pts_to_len ae; A.pts_to_len aw;

  fsub au y x;
  fmul aa au pb;
  fadd au y x;
  fmul ab au pa;
  fmul ac t pc;
  fscale ae z 2uL aw;
  P.double_ok (eval (vals vz));
  fsub au ab aa;
  fadd av ab aa;
  fsub aa ae ac;
  fadd ab ae ac;
  fmul x au aa;
  fmul y ab av;
  fmul z aa ab;
  fmul t au av;

  Mem.wipe aw 9sz;
  Mem.wipe ae 5sz;
  Mem.wipe ac 5sz;
  Mem.wipe ab 5sz;
  Mem.wipe aa 5sz;
  Mem.wipe av 5sz;
  Mem.wipe au 5sz;
  ()
}

#pop-options

(** {2 One digit}

    The digit's sign is a mask; its magnitude picks the entry, and the
    mask swaps the first two coordinates and negates the third. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The three registers hold the stored form of [sel_pt j (v - 8)]. *)
[@@"opaque_to_smt"]
let nok (a b c: Seq.seq S64.t) (j: nat { j < 32 }) (v: nat { v < 16 }) : prop =
  felem (vals a) /\ felem (vals b) /\ felem (vals c) /\
  (fev (vals a), fev (vals b), fev (vals c)) == seln j v

let nok_intro (a0 b0 c0 a b c: Seq.seq S64.t) (j: nat { j < 32 }) (v: nat { v < 16 })
  : Lemma (requires felem (vals a0) /\ felem (vals b0) /\ felem (vals c0) /\
                    (fev (vals a0), fev (vals b0), fev (vals c0)) ==
                      CB.to_niels (CT.tp j (absd v)) /\
                    felem (vals a) /\ felem (vals b) /\ felem (vals c) /\
                    (v < 8 ==> a == b0 /\ b == a0 /\
                               fev (vals c) == C.fsub 0 (fev (vals c0))) /\
                    (v >= 8 ==> a == a0 /\ b == b0 /\ c == c0))
          (ensures nok a b c j v)
  = reveal_opaque (`%nok) (nok a b c j v);
    neg_ok j v (fev (vals a0)) (fev (vals b0)) (fev (vals c0))
               (fev (vals a)) (fev (vals b)) (fev (vals c))

let nok_elim (a b c: Seq.seq S64.t) (j: nat { j < 32 }) (v: nat { v < 16 })
  : Lemma (requires nok a b c j v)
          (ensures felem (vals a) /\ felem (vals b) /\ felem (vals c) /\
                   (fev (vals a), fev (vals b), fev (vals c)) == seln j v)
  = reveal_opaque (`%nok) (nok a b c j v)

(** The weight of table [j]. *)
let wgt (j: nat) : pos = pow2 (8 * j)

let step_wt (p: E.ext_point) (n: int) (j: nat { j < 32 }) (v: nat { v < 16 })
            (r: E.ext_point)
  : Lemma (requires CB.repq p n /\ r == CB.madd p (seln j v))
          (ensures CB.repq r (n + (v - 8) * wgt j))
  = step_ok p n j v r

let mask_ok (v hb negm dd: nat)
  : Lemma (requires v < 16 /\ hb == v / pow2 3 /\
                    negm == (hb - 1) % pow2 64 /\
                    dd == (if negm = 0 then (v - 8) % pow2 64 else (8 - v) % pow2 64))
          (ensures (negm == 0 \/ negm == pow2 64 - 1) /\
                   (v < 8 <==> negm == pow2 64 - 1) /\ dd == absd v)
  = assert_norm (pow2 3 == 8);
    assert_norm (pow2 64 > 16)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn sel_neg (pa pb pc: A.array S64.t) (tbl: A.array S64.t) (j: SZ.t) (v: S64.t)
           (#va #vb #vc: erased (Seq.seq S64.t))
           (#ptb: perm) (#vtb: erased (Seq.seq S64.t))
requires A.pts_to pa va ** A.pts_to pb vb ** A.pts_to pc vc **
  A.pts_to tbl #ptb vtb **
  pure (SZ.v j < 32 /\ S64.v v < 16 /\ tok vtb /\
        Seq.length va == 5 /\ Seq.length vb == 5 /\ Seq.length vc == 5)
ensures exists* (wa wb wc: Seq.seq S64.t).
  A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc **
  A.pts_to tbl #ptb vtb **
  pure (SZ.v j < 32 /\ S64.v v < 16 /\
        Seq.length wa == 5 /\ Seq.length wb == 5 /\ Seq.length wc == 5 /\
        nok wa wb wc (SZ.v j) (S64.v v))
{
  A.pts_to_len tbl;
  tok_len vtb;
  let one = S64.classify 1uL;
  let eight = S64.classify 8uL;
  let hb = S64.shift_right v 3ul;
  let negm = Launder.launder (S64.sub_mod hb one);
  mask_ok (S64.v v) (S64.v hb) (S64.v negm)
    (if S64.v negm = 0 then S64.v (S64.sub_mod v eight)
     else S64.v (S64.sub_mod eight v));
  let dd = S64.select negm (S64.sub_mod eight v) (S64.sub_mod v eight);

  let o = SZ.mul 135sz j;
  select3 pa pb pc tbl o dd;
  with wa wb wc.
    assert (A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc);
  ent_ok vtb (SZ.v j) (S64.v dd) wa wb wc;

  let zz = S64.zero;
  let mut nc = [| zz; 5sz |];
  Mem.track nc; A.pts_to_len nc;
  let mut z0 = [| zz; 5sz |];
  Mem.track z0; A.pts_to_len z0;
  A.pts_to_len nc; A.pts_to_len z0;
  A.pts_to_len pa; A.pts_to_len pb; A.pts_to_len pc;

  cswap negm pa pb;
  P.set_small z0 0uL;
  fsub nc z0 pc;
  cswap negm pc nc;
  with wa' wb' wc'.
    assert (A.pts_to pa wa' ** A.pts_to pb wb' ** A.pts_to pc wc');
  nok_intro wa wb wc wa' wb' wc' (SZ.v j) (S64.v v);

  Mem.wipe z0 5sz;
  Mem.wipe nc 5sz;
  ()
}

#pop-options

(** [comb_add x y z t tbl j v] adds [(v - 8) 256^j G] to the accumulator. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn comb_add (x y z t: A.array S64.t) (tbl: A.array S64.t) (j: SZ.t) (v: S64.t)
            (n: erased int)
            (#vx #vy #vz #vt: erased (Seq.seq S64.t))
            (#ptb: perm) (#vtb: erased (Seq.seq S64.t))
requires
  A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz ** A.pts_to t vt **
  A.pts_to tbl #ptb vtb **
  pure (SZ.v j < 32 /\ S64.v v < 16 /\ tok vtb /\
        P.pt_ok vx vy vz vt /\ CB.repq (P.pt vx vy vz vt) n)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt **
  A.pts_to tbl #ptb vtb **
  pure (P.pt_ok wx wy wz wt /\
        CB.repq (P.pt wx wy wz wt) (reveal n + (S64.v v - 8) * wgt (SZ.v j)))
{
  let zz = S64.zero;
  let mut pa = [| zz; 5sz |];
  Mem.track pa; A.pts_to_len pa;
  let mut pb = [| zz; 5sz |];
  Mem.track pb; A.pts_to_len pb;
  let mut pc = [| zz; 5sz |];
  Mem.track pc; A.pts_to_len pc;
  A.pts_to_len pa; A.pts_to_len pb; A.pts_to_len pc;

  sel_neg pa pb pc tbl j v;
  with wa wb wc.
    assert (A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc);
  nok_elim wa wb wc (SZ.v j) (S64.v v);
  madd x y z t pa pb pc;
  with wx wy wz wt.
    assert (A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt);
  step_wt (P.pt vx vy vz vt) n (SZ.v j) (S64.v v) (P.pt wx wy wz wt);

  Mem.wipe pc 5sz;
  Mem.wipe pb 5sz;
  Mem.wipe pa 5sz;
  ()
}

#pop-options

(** {2 Recoding}

    Digit [i] is [nib k i + c + 8] modulo sixteen, offset by eight, and
    the carry is the quotient.  It is stored with the offset, in [[0, 16)]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let recode_step (k: nat) (i: nat) (d c: nat)
  : Lemma (requires d == CB.nib k i /\ c == CB.carry k i)
          (ensures (d + c + 8) % 16 == CB.dig k i + 8 /\
                   (d + c + 8) / 16 == CB.carry k (i + 1) /\
                   d + c + 8 < 25)
  = CB.carry_succ k i;
    CB.carry_le k i

let carry_zero (k: nat) : Lemma (CB.carry k 0 == 0)
  = assert_norm (CB.carry k 0 == 0)

let pos_ok (i: nat { i < 64 }) : Lemma (4 * i < 256 /\ (4 * i) % 4 == 0) = ()

let q_small (_: unit) : Lemma (E.q < pow2 253 /\ E.q < pow2 256)
  = assert_norm (E.q < pow2 253);
    assert_norm (pow2 253 < pow2 256)

let upd_ok (wd: Seq.seq S64.t) (vi: nat) (r: S64.t) (k: nat)
  : Lemma (requires Seq.length wd == 64 /\ vi < 64 /\
             S64.v r == CB.dig k vi + 8 /\
             (forall (i': nat). i' < vi ==> S64.v (Seq.index wd i') == CB.dig k i' + 8))
          (ensures forall (i': nat). i' < vi + 1 ==>
             S64.v (Seq.index (Seq.upd wd vi r) i') == CB.dig k i' + 8)
  = ()

(** The digit array, as a fact the solver cannot unfold. *)
[@@"opaque_to_smt"]
let dok (d: Seq.seq S64.t) (k: nat) : prop =
  Seq.length d == 64 /\
  (forall (i: nat). i < 64 ==> S64.v (Seq.index d i) == CB.dig k i + 8)

let dok_intro (d: Seq.seq S64.t) (k: nat)
  : Lemma (requires Seq.length d == 64 /\
             (forall (i: nat). i < 64 ==> S64.v (Seq.index d i) == CB.dig k i + 8))
          (ensures dok d k)
  = reveal_opaque (`%dok) (dok d k)

let dok_get (d: Seq.seq S64.t) (k: nat) (i: nat { i < 64 })
  : Lemma (requires dok d k)
          (ensures Seq.length d == 64 /\ S64.v (Seq.index d i) == CB.dig k i + 8)
  = reveal_opaque (`%dok) (dok d k)

let dok_len (d: Seq.seq S64.t) (k: nat)
  : Lemma (requires dok d k) (ensures Seq.length d == 64)
  = reveal_opaque (`%dok) (dok d k)

(** The odd half-sum for [par = 1], the even one for [par = 0]. *)
let hsum (k: nat) (par: nat) (j: nat) : int =
  if par = 1 then CB.osum k j else CB.esum k j

let hsum_zero (k: nat) (par: nat) : Lemma (hsum k par 0 == 0)
  = CB.osum_zero k; CB.esum_zero k

let hsum_succ (k: nat) (par: nat { par < 2 }) (j: nat) (n0: int) (v: int)
  : Lemma (requires v - 8 == CB.dig k (2 * j + par))
          (ensures n0 + hsum k par j + (v - 8) * wgt j == n0 + hsum k par (j + 1))
  = CB.osum_succ k j;
    CB.esum_succ k j

fn recode (dg: A.array S64.t) (kb: A.array S8.t)
          (#vd: erased (Seq.seq S64.t)) (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dg vd ** A.pts_to kb #pk vk **
  pure (Seq.length vd == 64 /\ Seq.length vk == 32)
ensures exists* (wd: Seq.seq S64.t).
  A.pts_to dg wd ** A.pts_to kb #pk vk **
  pure (dok wd (B.le_nat vk))
{
  A.pts_to_len dg;
  A.pts_to_len kb;
  assert_norm (pow2 4 == 16);
  assert_norm (pow2 4 - 1 == 15);
  carry_zero (B.le_nat vk);
  let mut i = 0sz;
  let mut c = S64.zero;
  while (let vi = !i; SZ.lt vi 64sz)
  invariant exists* (vi: SZ.t) (vc: S64.t) (wd: Seq.seq S64.t).
    pts_to i vi ** pts_to c vc ** A.pts_to dg wd ** A.pts_to kb #pk vk **
    pure (SZ.v vi <= 64 /\ Seq.length wd == 64 /\ Seq.length vk == 32 /\
          S64.v vc == CB.carry (B.le_nat vk) (SZ.v vi) /\
          (forall (i': nat). i' < SZ.v vi ==>
             S64.v (Seq.index wd i') == CB.dig (B.le_nat vk) i' + 8))
  decreases (64 - SZ.v (!i))
  {
    let vi = !i;
    let vc = !c;
    pos_ok (SZ.v vi);
    let d = W.nibble kb (SZ.mul vi 4sz);
    recode_step (B.le_nat vk) (SZ.v vi) (S64.v d) (S64.v vc);
    let s = S64.add_mod (S64.add_mod d vc) (S64.classify 8uL);
    Math.small_mod (S64.v d + S64.v vc) (pow2 64);
    Math.small_mod (S64.v d + S64.v vc + 8) (pow2 64);
    UInt.logand_mask #64 (S64.v s) 4;
    let r = S64.logand s (S64.classify 15uL);
    let c' = S64.shift_right s 4ul;
    assert (pure (S64.v r == CB.dig (B.le_nat vk) (SZ.v vi) + 8));
    assert (pure (S64.v c' == CB.carry (B.le_nat vk) (SZ.v vi + 1)));
    with wd. assert (A.pts_to dg wd);
    A.(dg.(vi) <- r);
    upd_ok wd (SZ.v vi) r (B.le_nat vk);
    c := c';
    i := SZ.add vi 1sz;
  };
  with wd. assert (A.pts_to dg wd);
  dok_intro wd (B.le_nat vk);
  ()
}

#pop-options

(** {2 The two passes} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn comb_pass (x y z t: A.array S64.t) (tbl: A.array S64.t) (dg: A.array S64.t)
             (par: SZ.t) (k: erased nat) (n0: erased int)
             (#vx #vy #vz #vt: erased (Seq.seq S64.t))
             (#ptb: perm) (#vtb: erased (Seq.seq S64.t))
             (#pd: perm) (#vd: erased (Seq.seq S64.t))
requires
  A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz ** A.pts_to t vt **
  A.pts_to tbl #ptb vtb ** A.pts_to dg #pd vd **
  pure (SZ.v par < 2 /\ tok vtb /\ dok vd k /\
        P.pt_ok vx vy vz vt /\ CB.repq (P.pt vx vy vz vt) n0)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt **
  A.pts_to tbl #ptb vtb ** A.pts_to dg #pd vd **
  pure (P.pt_ok wx wy wz wt /\
        CB.repq (P.pt wx wy wz wt) (reveal n0 + hsum k (SZ.v par) 32))
{
  A.pts_to_len dg;
  dok_len vd k;
  hsum_zero k (SZ.v par);
  with wx wy wz wt.
    assert (A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt);
  CB.repq_cong (P.pt wx wy wz wt) n0 (reveal n0 + hsum k (SZ.v par) 0);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 32sz)
  invariant exists* (vj: SZ.t) (wx wy wz wt: Seq.seq S64.t).
    pts_to j vj **
    A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz ** A.pts_to t wt **
    A.pts_to tbl #ptb vtb ** A.pts_to dg #pd vd **
    pure (SZ.v vj <= 32 /\ tok vtb /\ dok vd k /\ Seq.length vd == 64 /\
          P.pt_ok wx wy wz wt /\
          CB.repq (P.pt wx wy wz wt) (reveal n0 + hsum k (SZ.v par) (SZ.v vj)))
  decreases (32 - SZ.v (!j))
  {
    let vj = !j;
    let di = SZ.add (SZ.mul 2sz vj) par;
    let v = A.(dg.(di));
    dok_get vd k (SZ.v di);
    let nn : erased int = hide (reveal n0 + hsum k (SZ.v par) (SZ.v vj));
    comb_add x y z t tbl vj v nn;
    hsum_succ k (SZ.v par) (SZ.v vj) n0 (S64.v v);
    with wx' wy' wz' wt'.
      assert (A.pts_to x wx' ** A.pts_to y wy' ** A.pts_to z wz' ** A.pts_to t wt');
    CB.repq_cong (P.pt wx' wy' wz' wt')
      (reveal nn + (S64.v v - 8) * wgt (SZ.v vj))
      (reveal n0 + hsum k (SZ.v par) (SZ.v vj + 1));
    j := SZ.add vj 1sz;
  };
  ()
}

#pop-options

(** {2 Leaving the abstraction} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let comb_end (p: E.ext_point) (k: nat) (vk: Seq.lseq S8.t 32)
  : Lemma (requires CB.repq p (16 * CB.osum k 32 + CB.esum k 32) /\
                    k == B.le_nat vk % E.q)
          (ensures GR.on_curve p /\ GR.on_curve (E.point_mul_g vk) /\
                   E.point_equal p (E.point_mul_g vk))
  = q_small ();
    CB.recode_ok k;
    CB.repq_cong p (16 * CB.osum k 32 + CB.esum k 32) k;
    CB.repq_elim p k;
    GR.g_on_curve ();
    SM.point_mul_is_smul vk E.g;
    SM.smul_ok (B.le_nat vk) E.g;
    SM.smul_ok k E.g;
    O.smul_mod_q (B.le_nat vk);
    GR.point_equal_sym (SM.smul (B.le_nat vk) E.g) (SM.smul k E.g);
    GR.point_equal_trans p (SM.smul k E.g) (SM.smul (B.le_nat vk) E.g);
    GR.point_equal_sym (E.point_mul vk E.g) (SM.smul (B.le_nat vk) E.g);
    GR.point_equal_trans p (SM.smul (B.le_nat vk) E.g) (E.point_mul vk E.g)

let m16 (a: int) : Lemma (2 * (2 * (2 * (2 * a))) == 16 * a) = ()

let dbl4 (p1 p2 p3 p4 p5: E.ext_point) (a: int)
  : Lemma (requires CB.repq p1 a /\ p2 == E.point_double p1 /\
                    p3 == E.point_double p2 /\ p4 == E.point_double p3 /\
                    p5 == E.point_double p4)
          (ensures CB.repq p5 (16 * a))
  = CB.repq_dbl p1 a;
    CB.repq_dbl p2 (2 * a);
    CB.repq_dbl p3 (2 * (2 * a));
    CB.repq_dbl p4 (2 * (2 * (2 * a)));
    m16 a;
    CB.repq_cong p5 (2 * (2 * (2 * (2 * a)))) (16 * a)

let le_scalar (vb: Seq.seq S8.t) (x: nat)
  : Lemma (requires x < E.q /\ vb == B.nat_to_le 32 x)
          (ensures B.le_nat vb == x)
  = q_small ();
    assert_norm (8 * 32 == 256);
    B.le_nat_to_le 32 x

#pop-options

(** {2 The multiplication} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** [point_mul_g_comb o ks] is [o := [ks] G], up to [point_equal]. *)
fn point_mul_g_comb (ox oy oz ot: A.array S64.t) (ks: A.array S8.t)
                    (#vox #voy #voz #vot: erased (Seq.seq S64.t))
                    (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ks #pk vk **
  pure (P.pt_ok wx wy wz wt /\ GR.on_curve (P.pt wx wy wz wt) /\
        E.point_equal (P.pt wx wy wz wt) (E.point_mul_g vk))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ks;
  let z = S64.zero;
  let z8 = S8.zero;

  (* The scalar, reduced and recoded. *)
  let mut kq = [| z; 4sz |];
  Mem.track kq; A.pts_to_len kq;
  let mut kb = [| z8; 32sz |];
  Mem.track kb; A.pts_to_len kb;
  let mut dg = [| z; 64sz |];
  Mem.track dg; A.pts_to_len dg;
  A.pts_to_len kq; A.pts_to_len kb; A.pts_to_len dg;
  Scalar.reduce32 kq ks;
  with vq. assert (A.pts_to kq vq);
  Scalar.store_le kb kq;
  with vb. assert (A.pts_to kb vb);
  le_scalar vb (Scalar.qv vq);
  let k : erased nat = hide (B.le_nat vb);
  recode dg kb;

  let mut ux = [| z; 5sz |];
  Mem.track ux; A.pts_to_len ux;
  let mut uy = [| z; 5sz |];
  Mem.track uy; A.pts_to_len uy;
  let mut uz = [| z; 5sz |];
  Mem.track uz; A.pts_to_len uz;
  let mut ut = [| z; 5sz |];
  Mem.track ut; A.pts_to_len ut;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;

  CDO.tbl_ok ();
  tok_intro (G.static_array_elems CD.tbl_arr);
  let tbl = Table.table CD.tbl_arr 4320sz;

  P.set_infinity ox oy oz ot;
  CB.repq_zero ();
  comb_pass ox oy oz ot tbl dg 1sz k (hide 0);
  with p1x p1y p1z p1t.
    assert (A.pts_to ox p1x ** A.pts_to oy p1y ** A.pts_to oz p1z ** A.pts_to ot p1t);
  CB.repq_cong (P.pt p1x p1y p1z p1t) (0 + hsum k 1 32) (CB.osum k 32);
  P.point_double ux uy uz ut ox oy oz ot;
  with p2x p2y p2z p2t.
    assert (A.pts_to ux p2x ** A.pts_to uy p2y ** A.pts_to uz p2z ** A.pts_to ut p2t);
  P.point_double ox oy oz ot ux uy uz ut;
  with p3x p3y p3z p3t.
    assert (A.pts_to ox p3x ** A.pts_to oy p3y ** A.pts_to oz p3z ** A.pts_to ot p3t);
  P.point_double ux uy uz ut ox oy oz ot;
  with p4x p4y p4z p4t.
    assert (A.pts_to ux p4x ** A.pts_to uy p4y ** A.pts_to uz p4z ** A.pts_to ut p4t);
  P.point_double ox oy oz ot ux uy uz ut;
  with p5x p5y p5z p5t.
    assert (A.pts_to ox p5x ** A.pts_to oy p5y ** A.pts_to oz p5z ** A.pts_to ot p5t);
  dbl4 (P.pt p1x p1y p1z p1t) (P.pt p2x p2y p2z p2t) (P.pt p3x p3y p3z p3t)
       (P.pt p4x p4y p4z p4t) (P.pt p5x p5y p5z p5t) (CB.osum k 32);

  comb_pass ox oy oz ot tbl dg 0sz k (hide (16 * CB.osum k 32));
  with wx wy wz wt.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
  CB.repq_cong (P.pt wx wy wz wt) (16 * CB.osum k 32 + hsum k 0 32)
    (16 * CB.osum k 32 + CB.esum k 32);
  comb_end (P.pt wx wy wz wt) k vk;

  Table.drop_table tbl;
  Mem.wipe ut 5sz;
  Mem.wipe uz 5sz;
  Mem.wipe uy 5sz;
  Mem.wipe ux 5sz;
  Mem.wipe dg 64sz;
  Mem.wipe kb 32sz;
  Mem.wipe kq 4sz;
  ()
}

#pop-options
