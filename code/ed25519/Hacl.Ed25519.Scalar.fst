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

(** Arithmetic modulo the group order.

    Signing needs [(r + k s) mod q] and verification needs [S < q], where
    [q] is the order of the base point and not a prime of any convenient
    shape.  HACL* devotes a Barrett reduction and a 5x56-bit representation
    to this; here there is no [uint128], so both would have to be rebuilt,
    and a scalar multiplication in the group already costs a thousand times
    more than one modular multiply.  So the arithmetic is bitwise: the
    accumulator is doubled and conditionally reduced once per bit.

    That makes the whole module two primitives.  {!addc_op} adds two proper
    limb sequences and returns the carry out of the top; {!dbl_add_op}
    doubles one and shifts a bit in.  Everything else -- conditional
    subtraction, reduction of a 512-bit hash, multiplication -- is a loop
    over those two.  Both are the carry chain that
    [Spec.Curve25519.Field] already states and [Hacl.Curve25519.Field]
    already implements, so the limbs, the radix and the bound reasoning are
    shared with the field.

    Reducing modulo [q] never compares.  [a >= q] exactly when
    [a + (2^256 - q)] carries out of bit 256, and in that case the low
    limbs already hold [a - q]; so the test and the subtraction are the same
    addition, and the answer is a select on the carry.  [2^256 - q] is
    therefore the only constant in the module, and it lives in
    {!Hacl.Ed25519.Tables}.

    Every branch below is on a length or a loop counter.  The bits of the
    scalar are secret and are consumed by masks. *)
module Hacl.Ed25519.Scalar

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Curve25519.Field
open Hacl.Spec.Bytes

module S = Pulse.Lib.Slice
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Loops = Hacl.Spec.Loops
module F = Spec.Curve25519.Field
module Sc = Spec.Ed25519.Scalar
module Table = Hacl.Impl.Table
module Tables = Hacl.Ed25519.Tables

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The carry chain, keeping the carry}

    [Hacl.Curve25519.Field.carry_low_op] drops the carry out of the top
    limb, because the field folds it back in with a multiply by 38.  Here
    the carry is the answer to a question -- did the addition reach
    [2^256]? -- so it has to come back.  The loop is the same one. *)

#push-options "--z3rlimit 300"

fn carry_out_op (a: S.slice S64.t) (c: erased nat) (d: erased nat)
                (#va: erased (Seq.seq S64.t))
requires S.pts_to a va **
  pure (Seq.length va == F.nl /\ F.ble (vals va) c /\
        reveal c + reveal d < F.base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64)
returns r: S64.t
ensures exists* (va': Seq.seq S64.t).
  S.pts_to a va' **
  pure (Seq.length va' == F.nl /\ vals va' == F.carry_low (vals va) /\
        S64.v r == F.carry_out (vals va))
{
  S.pts_to_len a;
  F.div_le_of_lt (reveal c + reveal d) F.base d;
  Loops.repeati_zero F.carry_step (vals va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 15sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** S.pts_to a v **
    pure (SZ.v vk <= 15 /\ Seq.length v == F.nl /\
          vals v == F.carry_run (vals va) (SZ.v vk))
  decreases (15 - SZ.v (!k))
  {
    with v. assert (S.pts_to a v);
    let vk = !k;
    F.carry_run_chained (vals va) c d (SZ.v vk);
    F.carry_run_len (vals va) (SZ.v vk);
    let t = S.(a.(vk));
    let u = S.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S64.v t) (reveal c + reveal d) F.base;
    let lo = lo16 t;
    let up = addw u (hi16 t);
    S.((a.(vk) <- lo));
    S.((a.(SZ.add vk 1sz) <- up));
    vals_upd v (SZ.v vk) lo;
    vals_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) F.carry_step (vals va);
    k := SZ.add vk 1sz;
  };
  with v. assert (S.pts_to a v);
  F.carry_run_len (vals va) 15;
  let t = S.(a.(15sz));
  let lo = lo16 t;
  let hi = hi16 t;
  S.((a.(15sz) <- lo));
  vals_upd v 15 lo;
  assert (pure (vals (Seq.upd v 15 lo) == F.carry_low (vals va)));
  hi
}

#pop-options

(** {2 The two primitives} *)

(** Limbwise addition, then one carry pass.  Each column is below
    [2 base - 1], so a single unit of headroom normalises it, and the
    carry out is zero or one. *)
fn addc_op (a b: S.slice S64.t)
           (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires S.pts_to a va ** S.pts_to b #pb vb **
  pure (Seq.length va == F.nl /\ Seq.length vb == F.nl /\
        F.bnd (vals va) F.base /\ F.bnd (vals vb) F.base)
returns r: S64.t
ensures exists* (va': Seq.seq S64.t).
  S.pts_to a va' ** S.pts_to b #pb vb **
  pure (Seq.length va' == F.nl /\ F.bnd (vals va') F.base /\
        vals va' == Sc.addc (vals va) (vals vb) /\
        S64.v r == Sc.addc_out (vals va) (vals vb))
{
  S.pts_to_len a;
  S.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to a v ** S.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length v == F.nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vb) k) /\
          (forall (k: nat). SZ.v vi <= k /\ k < F.nl ==>
             Seq.index (vals v) k == Seq.index (vals va) k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(a.(vi));
    let y = S.(b.(vi));
    assert_norm (2 * F.base < pow2 64);
    let z = addw x y;
    S.((a.(vi) <- z));
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to a v);
  F.addw_len (vals va) (vals vb);
  assert (pure (vals v `Seq.equal` F.addw (vals va) (vals vb)));
  assert (pure (F.ble (vals va) (F.base - 1) /\ F.ble (vals vb) (F.base - 1)));
  F.addw_ble (vals va) (vals vb) (F.base - 1) (F.base - 1);
  assert_norm (2 * F.base - 2 + 1 < F.base * 2);
  assert_norm (2 * F.base - 2 + 1 < pow2 64);
  let r = carry_out_op a (2 * F.base - 2) 1;
  Sc.addc_ok (vals va) (vals vb);
  r
}

#push-options "--z3rlimit 120"

(** A doubling with a bit shifted into the bottom.  Columns reach
    [2 base - 1] here, so the chain gets two units of headroom; the carry
    out is zero by hypothesis, so [carry_low_op] serves. *)
fn dbl_add_op (a: S.slice S64.t) (b: S64.t) (#va: erased (Seq.seq S64.t))
requires S.pts_to a va **
  pure (Seq.length va == F.nl /\ F.bnd (vals va) F.base /\ S64.v b < 2 /\
        2 * F.eval (vals va) + S64.v b < pow2 256)
ensures exists* (va': Seq.seq S64.t).
  S.pts_to a va' **
  pure (Seq.length va' == F.nl /\ F.bnd (vals va') F.base /\
        vals va' == Sc.dbl_add (vals va) (S64.v b) /\
        F.eval (vals va') == 2 * F.eval (vals va) + S64.v b)
{
  S.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to a v **
    pure (SZ.v vi <= 16 /\ Seq.length v == F.nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == 2 * Seq.index (vals va) k) /\
          (forall (k: nat). SZ.v vi <= k /\ k < F.nl ==>
             Seq.index (vals v) k == Seq.index (vals va) k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(a.(vi));
    assert_norm (2 * F.base < pow2 64);
    let z = addw x x;
    S.((a.(vi) <- z));
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to a v);
  let z = S.(a.(0sz));
  assert_norm (2 * F.base + 1 < pow2 64);
  let z' = addw z b;
  S.((a.(0sz) <- z'));
  vals_upd v 0 z';
  with w. assert (S.pts_to a w);
  let y : erased (Seq.seq nat) = hide (Seq.create 1 (S64.v b) <: Seq.seq nat);
  assert (pure (Seq.length (F.scale 2 (vals va)) == F.nl));
  assert (pure (vals w `Seq.equal` F.addw (F.scale 2 (vals va)) (reveal y)));
  F.scale_ble 2 (vals va) (F.base - 1);
  assert (pure (F.ble (reveal y) 1));
  F.addw_ble (F.scale 2 (vals va)) (reveal y) (2 * F.base - 2) 1;
  assert_norm (2 * F.base - 1 + 2 < F.base * 3);
  assert_norm (2 * F.base - 1 + 2 < pow2 64);
  carry_low_op a (2 * F.base - 1) 2;
  Sc.dbl_add_ok (vals va) (S64.v b);
}

#pop-options

(** {2 Conditional subtraction}

    Add [2^256 - q] into a copy; the carry out says whether the original was
    at least [q], and if it was then the copy is the answer.  Select on the
    carry.  Nothing here looks at a limb. *)

#push-options "--z3rlimit 120"

fn csub_q_op (a t: S.slice S64.t)
             (#va: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires S.pts_to a va ** S.pts_to t vt **
  pure (Seq.length va == F.nl /\ Seq.length vt == F.nl /\
        F.bnd (vals va) F.base /\ F.eval (vals va) < 2 * Sc.q)
ensures exists* (va': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to a va' ** S.pts_to t vt' **
  pure (Seq.length va' == F.nl /\ Seq.length vt' == F.nl /\
        F.bnd (vals va') F.base /\ vals va' == Sc.csub_q (vals va) /\
        F.eval (vals va') == F.eval (vals va) % Sc.q /\
        F.eval (vals va') < Sc.q)
{
  S.pts_to_len a;
  S.pts_to_len t;
  copy t a;
  let qcs = Table.table Tables.qc_arr 16sz;
  Tables.qc_seq_ok ();
  Sc.qc_ok ();
  let c = addc_op t qcs;
  Table.drop_table qcs;
  Sc.addc_ok (vals va) Sc.qc;
  let m = S64.eq_mask c (S64.classify 1uL);
  assert (pure ((S64.v m == 0) == (S64.v c <> 1)));
  cswap m a t;
  Sc.csub_q_ok (vals va);
  Sc.q_bound ();
  with va'. assert (S.pts_to a va');
  assert (pure (vals va' == Sc.csub_q (vals va)));
}

#pop-options

(** {2 The three operations} *)

fn set_zero (a: S.slice S64.t) (#va: erased (Seq.seq S64.t))
requires S.pts_to a va ** pure (Seq.length va == F.nl)
ensures exists* (va': Seq.seq S64.t).
  S.pts_to a va' **
  pure (Seq.length va' == F.nl /\ vals va' == Sc.zero /\
        F.bnd (vals va') F.base /\ F.eval (vals va') == 0)
{
  S.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to a v **
    pure (SZ.v vi <= 16 /\ Seq.length v == F.nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index (vals v) k == 0))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    S.((a.(vi) <- S64.classify 0uL));
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to a v);
  Classical.forall_intro Sc.zero_index;
  assert (pure (vals v `Seq.equal` Sc.zero));
  Sc.zero_ok ();
}

#push-options "--z3rlimit 120"

(** [a := (2 a + b) mod q]. *)
fn qdbl_add_op (a t: S.slice S64.t) (b: S64.t)
               (#va: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires S.pts_to a va ** S.pts_to t vt **
  pure (Seq.length va == F.nl /\ Seq.length vt == F.nl /\
        F.bnd (vals va) F.base /\ F.eval (vals va) < Sc.q /\ S64.v b < 2)
ensures exists* (va': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to a va' ** S.pts_to t vt' **
  pure (Seq.length va' == F.nl /\ Seq.length vt' == F.nl /\
        F.bnd (vals va') F.base /\ F.eval (vals va') < Sc.q /\
        vals va' == Sc.qdbl_add (vals va) (S64.v b))
{
  Sc.q_bound ();
  dbl_add_op a b;
  csub_q_op a t;
  Sc.dbl_add_ok (vals va) (S64.v b);
  Sc.csub_q_ok (Sc.dbl_add (vals va) (S64.v b));
}

(** [a := (a + b) mod q]. *)
fn qadd_op (a b t: S.slice S64.t)
           (#va: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#vt: erased (Seq.seq S64.t))
requires S.pts_to a va ** S.pts_to b #pb vb ** S.pts_to t vt **
  pure (Seq.length va == F.nl /\ Seq.length vb == F.nl /\ Seq.length vt == F.nl /\
        F.bnd (vals va) F.base /\ F.bnd (vals vb) F.base /\
        F.eval (vals va) < Sc.q /\ F.eval (vals vb) < Sc.q)
ensures exists* (va': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to a va' ** S.pts_to b #pb vb ** S.pts_to t vt' **
  pure (Seq.length va' == F.nl /\ Seq.length vt' == F.nl /\
        F.bnd (vals va') F.base /\ F.eval (vals va') < Sc.q /\
        vals va' == Sc.qadd (vals va) (vals vb))
{
  Sc.q_bound ();
  Sc.addc_ok (vals va) (vals vb);
  F.eval_bnd (Sc.addc (vals va) (vals vb));
  let _ = addc_op a b;
  csub_q_op a t;
  Sc.csub_q_ok (Sc.addc (vals va) (vals vb));
}

#pop-options

(** {2 Reduction of a hash}

    [SHA-512] of something, read as a little-endian integer below [2^512],
    brought into [0, q).  Five hundred and twelve doublings; each is a
    sixteen-limb add and a conditional subtract, so about ten thousand
    machine operations -- a fifth of a single point addition. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

fn reduce_body (out t: S.slice S64.t) (h: S.slice S8.t) (i: SZ.t { SZ.v i < 512 })
               (#vo: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
               (#ph: perm) (#vh: erased (Seq.seq S8.t))
requires S.pts_to out vo ** S.pts_to t vt ** S.pts_to h #ph vh **
  pure (Seq.length vo == F.nl /\ Seq.length vt == F.nl /\ Seq.length vh == 64 /\
        F.bnd (vals vo) F.base /\ F.eval (vals vo) < Sc.q)
ensures exists* (vo': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to t vt' ** S.pts_to h #ph vh **
  pure (Seq.length vo' == F.nl /\ Seq.length vt' == F.nl /\
        F.bnd (vals vo') F.base /\ F.eval (vals vo') < Sc.q /\
        vals vo' == Sc.reduce_step (le_nat vh) (SZ.v i) (vals vo))
{
  S.pts_to_len h;
  let bi = SZ.sub 511sz i;
  let bj = SZ.div bi 8sz;
  let sh = SZ.sizet_to_uint32 (SZ.rem bi 8sz);
  assert_norm (pow2 32 > 8);
  Math.small_mod (SZ.v (SZ.rem bi 8sz)) (pow2 32);
  assert (pure (SZ.v bi == 511 - SZ.v i /\ SZ.v bj == SZ.v bi / 8 /\
                U32.v sh == SZ.v bi % 8));
  let byte = S.(h.(bj));
  let w = Cast.u8_to_u64 byte;
  let sr = S64.shift_right w sh;
  assert (pure (S64.v sr == S8.v (Seq.index vh (SZ.v bi / 8)) / pow2 (SZ.v bi % 8)));
  UInt.logand_mask #64 (S64.v sr) 1;
  assert_norm (pow2 1 == 2);
  let bit = S64.logand sr (S64.classify 1uL);
  Sc.le_nat_bit vh (SZ.v bi);
  assert (pure (S64.v bit == Sc.bit_of (le_nat vh) (SZ.v bi) /\ S64.v bit < 2));
  qdbl_add_op out t bit;
}

fn reduce_op (out t: S.slice S64.t) (h: S.slice S8.t)
             (#vo: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
             (#ph: perm) (#vh: erased (Seq.seq S8.t))
requires S.pts_to out vo ** S.pts_to t vt ** S.pts_to h #ph vh **
  pure (Seq.length vo == F.nl /\ Seq.length vt == F.nl /\ Seq.length vh == 64)
ensures exists* (vo': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to t vt' ** S.pts_to h #ph vh **
  pure (Seq.length vo' == F.nl /\ Seq.length vt' == F.nl /\
        F.bnd (vals vo') F.base /\ F.eval (vals vo') < Sc.q /\
        F.eval (vals vo') == le_nat vh % Sc.q)
{
  S.pts_to_len h;
  le_nat_bound vh;
  set_zero out;
  Loops.repeati_zero (Sc.reduce_step (le_nat vh)) Sc.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 512sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (w: Seq.seq S64.t).
    pts_to i vi ** S.pts_to out v ** S.pts_to t w ** S.pts_to h #ph vh **
    pure (SZ.v vi <= 512 /\ Seq.length v == F.nl /\ Seq.length w == F.nl /\
          vals v == Loops.repeati (SZ.v vi) (Sc.reduce_step (le_nat vh)) Sc.zero)
  decreases (512 - SZ.v (!i))
  {
    let vi = !i;
    Sc.reduce_at (le_nat vh) (SZ.v vi);
    reduce_body out t h vi;
    Loops.unfold_repeati (SZ.v vi) (Sc.reduce_step (le_nat vh)) Sc.zero;
    i := SZ.add vi 1sz;
  };
  Sc.reduce_ok (le_nat vh);
}

#pop-options

(** {2 Multiplication}

    Horner over the two hundred and fifty-six bits of the multiplier, most
    significant first.  The addition is unconditional and its result is
    selected against the accumulator on the bit, so the running time does
    not depend on the scalar. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

fn qmul_body (out a n t1 t2: S.slice S64.t) (i: SZ.t { SZ.v i < 256 })
             (#vo: erased (Seq.seq S64.t))
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#pn: perm) (#vn: erased (Seq.seq S64.t))
             (#v1: erased (Seq.seq S64.t)) (#v2: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to a #pa va ** S.pts_to n #pn vn **
         S.pts_to t1 v1 ** S.pts_to t2 v2 **
  pure (Seq.length vo == F.nl /\ Seq.length va == F.nl /\ Seq.length vn == F.nl /\
        Seq.length v1 == F.nl /\ Seq.length v2 == F.nl /\
        F.bnd (vals vo) F.base /\ F.eval (vals vo) < Sc.q /\
        F.bnd (vals va) F.base /\ F.eval (vals va) < Sc.q /\
        F.bnd (vals vn) F.base)
ensures exists* (vo': Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to a #pa va ** S.pts_to n #pn vn **
  S.pts_to t1 w1 ** S.pts_to t2 w2 **
  pure (Seq.length vo' == F.nl /\ Seq.length w1 == F.nl /\ Seq.length w2 == F.nl /\
        F.bnd (vals vo') F.base /\ F.eval (vals vo') < Sc.q /\
        vals vo' == Sc.qmul_step (vals va) (F.eval (vals vn)) (SZ.v i) (vals vo))
{
  S.pts_to_len n;
  let bi = SZ.sub 255sz i;
  let bj = SZ.div bi 16sz;
  let sh = SZ.sizet_to_uint32 (SZ.rem bi 16sz);
  assert_norm (pow2 32 > 16);
  Math.small_mod (SZ.v (SZ.rem bi 16sz)) (pow2 32);
  assert (pure (SZ.v bi == 255 - SZ.v i /\ SZ.v bj == SZ.v bi / 16 /\
                U32.v sh == SZ.v bi % 16));
  let limb = S.(n.(bj));
  let sr = S64.shift_right limb sh;
  assert (pure (S64.v sr == Seq.index (vals vn) (SZ.v bi / F.rad) / pow2 (SZ.v bi % F.rad)));
  UInt.logand_mask #64 (S64.v sr) 1;
  assert_norm (pow2 1 == 2);
  let bit = S64.logand sr (S64.classify 1uL);
  Sc.eval_bit (vals vn) (SZ.v bi);
  assert (pure (S64.v bit == Sc.bit_of (F.eval (vals vn)) (SZ.v bi) /\ S64.v bit < 2));

  qdbl_add_op out t1 (S64.classify 0uL);
  with acc. assert (S.pts_to out acc);
  copy t2 out;
  qadd_op t2 a t1;
  with sum. assert (S.pts_to t2 sum);
  let m = S64.eq_mask bit (S64.classify 1uL);
  assert (pure ((S64.v m == 0) == (S64.v bit <> 1)));
  cswap m out t2;
  with vo'. assert (S.pts_to out vo');
  assert (pure (vals vo' == Sc.qsel (S64.v bit) (vals acc) (Sc.qadd (vals acc) (vals va))));
}

fn qmul_op (out a n t1 t2: S.slice S64.t)
           (#vo: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pn: perm) (#vn: erased (Seq.seq S64.t))
           (#v1: erased (Seq.seq S64.t)) (#v2: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to a #pa va ** S.pts_to n #pn vn **
         S.pts_to t1 v1 ** S.pts_to t2 v2 **
  pure (Seq.length vo == F.nl /\ Seq.length va == F.nl /\ Seq.length vn == F.nl /\
        Seq.length v1 == F.nl /\ Seq.length v2 == F.nl /\
        F.bnd (vals va) F.base /\ F.eval (vals va) < Sc.q /\
        F.bnd (vals vn) F.base)
ensures exists* (vo': Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to a #pa va ** S.pts_to n #pn vn **
  S.pts_to t1 w1 ** S.pts_to t2 w2 **
  pure (Seq.length vo' == F.nl /\ Seq.length w1 == F.nl /\ Seq.length w2 == F.nl /\
        F.bnd (vals vo') F.base /\ F.eval (vals vo') < Sc.q /\
        F.eval (vals vo') == (F.eval (vals va) * F.eval (vals vn)) % Sc.q)
{
  S.pts_to_len n;
  F.eval_bnd (vals vn);
  set_zero out;
  Loops.repeati_zero (Sc.qmul_step (vals va) (F.eval (vals vn))) Sc.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t).
    pts_to i vi ** S.pts_to out v ** S.pts_to a #pa va ** S.pts_to n #pn vn **
    S.pts_to t1 w1 ** S.pts_to t2 w2 **
    pure (SZ.v vi <= 256 /\ Seq.length v == F.nl /\
          Seq.length w1 == F.nl /\ Seq.length w2 == F.nl /\
          vals v == Loops.repeati (SZ.v vi) (Sc.qmul_step (vals va) (F.eval (vals vn))) Sc.zero)
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    Sc.qmul_at (vals va) (F.eval (vals vn)) (SZ.v vi);
    qmul_body out a n t1 t2 vi;
    Loops.unfold_repeati (SZ.v vi) (Sc.qmul_step (vals va) (F.eval (vals vn))) Sc.zero;
    i := SZ.add vi 1sz;
  };
  Sc.qmul_ok (vals va) (F.eval (vals vn));
}

#pop-options

#pop-options
