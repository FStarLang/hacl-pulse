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

(** The scalar field [Z/n].

    The same four limbs and the same Montgomery machinery as
    [Hacl.P256.Field], with [qmod] in place of [fmod].  ECDSA needs
    addition, multiplication and inversion here, plus two decoders: one
    that insists the scalar is a proper private key, and one that reduces
    a hash modulo the order.

    Because [Hacl.Impl.Mont4] takes its modulus as data, none of this
    duplicates any code in the emitted C: the two fields share every
    operation and differ only in the table they pass.  Multiplication goes
    through [Hacl.Impl.Mont4F], the word-by-word reduction of
    [Hacl.Impl.Mont64], which is twice as fast and just as generic, so the
    sharing holds there too.  Inversion is an addition chain over it. *)
module Hacl.P256.Scalar

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Spec.Mont4
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.Impl.Bignum4
open Hacl.Impl.Mont4
open Hacl.P256.Tables
open Hacl.Impl.Exp4
open Hacl.Impl.Mont4F

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module P = Spec.P256
module MA = Spec.ModArith
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What a scalar is} *)

let qelem (v: Seq.seq S64.t) : prop = res qmod (vals v)

let qmod_m (_: unit) : Lemma (qmod.m == P.order) = ()

let qev (v: Seq.seq S64.t) : GTot P.qelem = mev qmod (vals v)

(** {2 The ring operations} *)

fn qadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == P.qadd (qev va) (qev vb))
{
  qmod_ok (); qmod_m ();
  mev_add qmod (vals va) (vals vb);
  let nm = qnm ();
  aadd out a b nm qmod;
  drop_table nm;
}

fn qmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == P.qmul (qev va) (qev vb))
{
  qmod_ok (); qmod_m ();
  mev_mul qmod (vals va) (vals vb);
  let ms = qms ();
  amulf out a b ms qmu qmod;
  drop_table ms;
  with vo'. assert (A.pts_to out vo');
  assert (pure (mev qmod (vals vo') == mev qmod (mmul qmod (vals va) (vals vb))));
}

(** [out := a * a]: the same buffer is both factors. *)
fn qsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == P.qmul (qev va) (qev va))
{
  A.share a;
  qmul out a a;
  A.gather a;
}

(** {2 Inversion}

    [x^(n-2)] by a fixed addition chain. The exponent is a constant from
    the standard, so the chain is public and straight-line: no table
    lookup depends on anything secret. The odd powers [x^1 .. x^15] come
    first; the top of [n - 2] is [ffffffff 00000000 ffffffff ffffffff],
    built from blocks of ones; the rest is a sliding window of width four
    over those odd powers. *)

(** [a := a * a], through the scratch [c]. *)
fn qsqr_ip (a c: A.array S64.t)
           (#va: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c vc **
  pure (qelem va /\ Seq.length vc == nl)
ensures exists* (va': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c vc' **
  pure (qelem va' /\ Seq.length vc' == nl /\ qev va' == MA.exp #P.order (qev va) 2)
{
  A.pts_to_len a;
  acopy c a;
  with u. assert (A.pts_to c u);
  assert (pure (qev u == qev va));
  qsqr a c;
  with v'. assert (A.pts_to a v');
  MA.exp_two (qev va);
  assert (pure (qev v' == P.qmul (qev va) (qev va)));
  assert (pure (qev v' == MA.exp #P.order (qev va) 2));
}

(** [a := a * b], through the scratch [c]. *)
fn qmul_ip (a b c: A.array S64.t)
           (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#vc: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to b #pb vb ** A.pts_to c vc **
  pure (qelem va /\ qelem vb /\ Seq.length vc == nl)
ensures exists* (va': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb ** A.pts_to c vc' **
  pure (qelem va' /\ Seq.length vc' == nl /\ qev va' == P.qmul (qev va) (qev vb))
{
  A.pts_to_len a;
  acopy c a;
  qmul a c b;
}

(** One more squaring when [b]: the tail of an odd count. *)
fn qsqr_if (b: bool) (a c: A.array S64.t) (x: erased P.qelem) (k: erased nat)
           (#va: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c vc **
  pure (qelem va /\ Seq.length vc == nl /\ qev va == MA.exp #P.order x (pow2 k))
ensures exists* (va': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c vc' **
  pure (qelem va' /\ Seq.length vc' == nl /\
        qev va' == MA.exp #P.order x (pow2 (if b then k + 1 else k)))
{
  if b {
    qsqr_ip a c;
    with v'. assert (A.pts_to a v');
    MA.exp_mul x (pow2 k) 2;
    Math.pow2_double_mult k;
    assert (pure (qev v' == MA.exp #P.order x (pow2 (k + 1))));
  } else {
    ()
  }
}

(** [a := a^(2^n)], by [n] squarings.  They alternate between [a] and
    [c], so no squaring needs a copy of its input. *)
fn qpow2_ip (a c: A.array S64.t) (n: SZ.t)
            (#va: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c vc **
  pure (qelem va /\ Seq.length vc == nl)
ensures exists* (va': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c vc' **
  pure (qelem va' /\ Seq.length vc' == nl /\
        qev va' == MA.exp #P.order (qev va) (pow2 (SZ.v n)))
{
  MA.exp_one (qev va);
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt 1sz (SZ.sub n vi))
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (u: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to c u **
    pure (SZ.v vi <= SZ.v n /\ qelem v /\ Seq.length u == nl /\
          qev v == MA.exp #P.order (qev va) (pow2 (SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to a v);
    qsqr c a;
    with u. assert (A.pts_to c u);
    qsqr a c;
    with v'. assert (A.pts_to a v');
    MA.exp_two (qev v);
    MA.exp_two (qev u);
    MA.exp_mul (qev va) (pow2 (SZ.v vi)) 2;
    Math.pow2_double_mult (SZ.v vi);
    assert (pure (qev u == MA.exp #P.order (qev va) (pow2 (SZ.v vi + 1))));
    MA.exp_mul (qev va) (pow2 (SZ.v vi + 1)) 2;
    Math.pow2_double_mult (SZ.v vi + 1);
    assert (pure (qev v' == MA.exp #P.order (qev va) (pow2 (SZ.v vi + 2))));
    i := SZ.add vi 2sz;
  };
  let vi = !i;
  qsqr_if (SZ.lt vi n) a c (hide (qev va)) (SZ.v vi);
}

(** [out := out^(2^k) * t], where [out] and [t] are known powers of [x]. *)
fn qstep (out t c: A.array S64.t) (k: SZ.t) (x: erased P.qelem) (e v: erased nat)
         (#vo: erased (Seq.seq S64.t))
         (#pt: perm) (#vt: erased (Seq.seq S64.t))
         (#vc: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t #pt vt ** A.pts_to c vc **
  pure (qelem vo /\ qelem vt /\ Seq.length vc == nl /\
        qev vo == MA.exp #P.order x e /\ qev vt == MA.exp #P.order x v)
ensures exists* (vo': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t #pt vt ** A.pts_to c vc' **
  pure (qelem vo' /\ Seq.length vc' == nl /\
        qev vo' == MA.exp #P.order x (e * pow2 (SZ.v k) + v))
{
  qpow2_ip out c k;
  with u. assert (A.pts_to out u);
  MA.exp_mul x e (pow2 (SZ.v k));
  assert (pure (qev u == MA.exp #P.order x (e * pow2 (SZ.v k))));
  qmul_ip out t c;
  with u2. assert (A.pts_to out u2);
  MA.exp_add x (e * pow2 (SZ.v k)) v;
  assert (pure (qev u2 == MA.exp #P.order x (e * pow2 (SZ.v k) + v)));
}

#push-options "--z3rlimit 400"
fn qinv (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == P.qinv (qev va))
{
  qmod_m ();
  let x : erased P.qelem = hide (qev va);
  let z = S64.zero;
  let mut x2 = [| z; 4sz |]; A.pts_to_len x2;
  let mut t3 = [| z; 4sz |]; A.pts_to_len t3;
  let mut t5 = [| z; 4sz |]; A.pts_to_len t5;
  let mut t7 = [| z; 4sz |]; A.pts_to_len t7;
  let mut t9 = [| z; 4sz |]; A.pts_to_len t9;
  let mut t11 = [| z; 4sz |]; A.pts_to_len t11;
  let mut t13 = [| z; 4sz |]; A.pts_to_len t13;
  let mut t15 = [| z; 4sz |]; A.pts_to_len t15;
  let mut c = [| z; 4sz |]; A.pts_to_len c;
  let mut e = [| z; 4sz |]; A.pts_to_len e;
  A.pts_to_len out;
  qsqr x2 a;
  MA.exp_two (qev va);
  with v1. assert (A.pts_to x2 v1);
  assert (pure (qelem v1 /\ qev v1 == MA.exp #P.order (qev va) 2));
  MA.exp_one (qev va);
  qmul t3 a x2;
  MA.exp_add (qev va) 1 2;
  with v2. assert (A.pts_to t3 v2);
  assert (pure (qelem v2 /\ qev v2 == MA.exp #P.order (qev va) 3));
  qmul t5 t3 x2;
  MA.exp_add (qev va) 3 2;
  with v3. assert (A.pts_to t5 v3);
  assert (pure (qelem v3 /\ qev v3 == MA.exp #P.order (qev va) 5));
  qmul t7 t5 x2;
  MA.exp_add (qev va) 5 2;
  with v4. assert (A.pts_to t7 v4);
  assert (pure (qelem v4 /\ qev v4 == MA.exp #P.order (qev va) 7));
  qmul t9 t7 x2;
  MA.exp_add (qev va) 7 2;
  with v5. assert (A.pts_to t9 v5);
  assert (pure (qelem v5 /\ qev v5 == MA.exp #P.order (qev va) 9));
  qmul t11 t9 x2;
  MA.exp_add (qev va) 9 2;
  with v6. assert (A.pts_to t11 v6);
  assert (pure (qelem v6 /\ qev v6 == MA.exp #P.order (qev va) 11));
  qmul t13 t11 x2;
  MA.exp_add (qev va) 11 2;
  with v7. assert (A.pts_to t13 v7);
  assert (pure (qelem v7 /\ qev v7 == MA.exp #P.order (qev va) 13));
  qmul t15 t13 x2;
  MA.exp_add (qev va) 13 2;
  with v8. assert (A.pts_to t15 v8);
  assert (pure (qelem v8 /\ qev v8 == MA.exp #P.order (qev va) 15));
  acopy out t15;
  qstep out t15 c 4sz x 15 15;
  assert_norm (15 * pow2 4 + 15 == 255);
  acopy e out;
  qstep out e c 8sz x 255 255;
  assert_norm (255 * pow2 8 + 255 == 65535);
  acopy e out;
  qstep out e c 16sz x 65535 65535;
  assert_norm (65535 * pow2 16 + 65535 == 4294967295);
  acopy e out;
  qstep out e c 64sz x 4294967295 4294967295;
  assert_norm (4294967295 * pow2 64 + 4294967295 == 79228162495817593524129366015);
  qstep out e c 32sz x 79228162495817593524129366015 4294967295;
  assert_norm (79228162495817593524129366015 * pow2 32 + 4294967295 == 340282366841710300967557013911933812735);
  qstep out t11 c 4sz x 340282366841710300967557013911933812735 11;
  assert_norm (340282366841710300967557013911933812735 * pow2 4 + 11 == 5444517869467364815480912222590941003771);
  qstep out t3 c 2sz x 5444517869467364815480912222590941003771 3;
  assert_norm (5444517869467364815480912222590941003771 * pow2 2 + 3 == 21778071477869459261923648890363764015087);
  qstep out t7 c 5sz x 21778071477869459261923648890363764015087 7;
  assert_norm (21778071477869459261923648890363764015087 * pow2 5 + 7 == 696898287291822696381556764491640448482791);
  qstep out t13 c 6sz x 696898287291822696381556764491640448482791 13;
  assert_norm (696898287291822696381556764491640448482791 * pow2 6 + 13 == 44601490386676652568419632927464988702898637);
  qstep out t15 c 4sz x 44601490386676652568419632927464988702898637 15;
  assert_norm (44601490386676652568419632927464988702898637 * pow2 4 + 15 == 713623846186826441094714126839439819246378207);
  qstep out t5 c 4sz x 713623846186826441094714126839439819246378207 5;
  assert_norm (713623846186826441094714126839439819246378207 * pow2 4 + 5 == 11417981538989223057515426029431037107942051317);
  qstep out t11 c 5sz x 11417981538989223057515426029431037107942051317 11;
  assert_norm (11417981538989223057515426029431037107942051317 * pow2 5 + 11 == 365375409247655137840493632941793187454145642155);
  qstep out t13 c 5sz x 365375409247655137840493632941793187454145642155 13;
  assert_norm (365375409247655137840493632941793187454145642155 * pow2 5 + 13 == 11692013095924964410895796254137381998532660548973);
  qstep out t7 c 5sz x 11692013095924964410895796254137381998532660548973 7;
  assert_norm (11692013095924964410895796254137381998532660548973 * pow2 5 + 7 == 374144419069598861148665480132396223953045137567143);
  qstep out t11 c 7sz x 374144419069598861148665480132396223953045137567143 11;
  assert_norm (374144419069598861148665480132396223953045137567143 * pow2 7 + 11 == 47890485640908654227029181456946716665989777608594315);
  qstep out t3 c 2sz x 47890485640908654227029181456946716665989777608594315 3;
  assert_norm (47890485640908654227029181456946716665989777608594315 * pow2 2 + 3 == 191561942563634616908116725827786866663959110434377263);
  qstep out t15 c 6sz x 191561942563634616908116725827786866663959110434377263 15;
  assert_norm (191561942563634616908116725827786866663959110434377263 * pow2 6 + 15 == 12259964324072615482119470452978359466493383067800144847);
  qstep out a c 2sz x 12259964324072615482119470452978359466493383067800144847 1;
  assert_norm (12259964324072615482119470452978359466493383067800144847 * pow2 2 + 1 == 49039857296290461928477881811913437865973532271200579389);
  qstep out t9 c 8sz x 49039857296290461928477881811913437865973532271200579389 9;
  assert_norm (49039857296290461928477881811913437865973532271200579389 * pow2 8 + 9 == 12554203467850358253690337743849840093689224261427348323593);
  qstep out t7 c 3sz x 12554203467850358253690337743849840093689224261427348323593 7;
  assert_norm (12554203467850358253690337743849840093689224261427348323593 * pow2 3 + 7 == 100433627742802866029522701950798720749513794091418786588751);
  qstep out t7 c 5sz x 100433627742802866029522701950798720749513794091418786588751 7;
  assert_norm (100433627742802866029522701950798720749513794091418786588751 * pow2 5 + 7 == 3213876087769691712944726462425559063984441410925401170840039);
  qstep out t7 c 4sz x 3213876087769691712944726462425559063984441410925401170840039 7;
  assert_norm (3213876087769691712944726462425559063984441410925401170840039 * pow2 4 + 7 == 51422017404315067407115623398808945023751062574806418733440631);
  qstep out t7 c 5sz x 51422017404315067407115623398808945023751062574806418733440631 7;
  assert_norm (51422017404315067407115623398808945023751062574806418733440631 * pow2 5 + 7 == 1645504556938082157027699948761886240760034002393805399470100199);
  qstep out t5 c 5sz x 1645504556938082157027699948761886240760034002393805399470100199 5;
  assert_norm (1645504556938082157027699948761886240760034002393805399470100199 * pow2 5 + 5 == 52656145822018629024886398360380359704321088076601772783043206373);
  qstep out t3 c 3sz x 52656145822018629024886398360380359704321088076601772783043206373 3;
  assert_norm (52656145822018629024886398360380359704321088076601772783043206373 * pow2 3 + 3 == 421249166576149032199091186883042877634568704612814182264345650987);
  qstep out t11 c 8sz x 421249166576149032199091186883042877634568704612814182264345650987 11;
  assert_norm (421249166576149032199091186883042877634568704612814182264345650987 * pow2 8 + 11 == 107839786643494152242967343842058976674449588380880430659672486652683);
  qstep out t15 c 4sz x 107839786643494152242967343842058976674449588380880430659672486652683 15;
  assert_norm (107839786643494152242967343842058976674449588380880430659672486652683 * pow2 4 + 15 == 1725436586295906435887477501472943626791193414094086890554759786442943);
  qstep out t3 c 5sz x 1725436586295906435887477501472943626791193414094086890554759786442943 3;
  assert_norm (1725436586295906435887477501472943626791193414094086890554759786442943 * pow2 5 + 3 == 55213970761469005948399280047134196057318189251010780497752313166174179);
  qstep out t3 c 5sz x 55213970761469005948399280047134196057318189251010780497752313166174179 3;
  assert_norm (55213970761469005948399280047134196057318189251010780497752313166174179 * pow2 5 + 3 == 1766847064367008190348776961508294273834182056032344975928074021317573731);
  qstep out t9 c 6sz x 1766847064367008190348776961508294273834182056032344975928074021317573731 9;
  assert_norm (1766847064367008190348776961508294273834182056032344975928074021317573731 * pow2 6 + 9 == 113078212119488524182321725536530833525387651586070078459396737364324718793);
  qstep out t5 c 4sz x 113078212119488524182321725536530833525387651586070078459396737364324718793 5;
  assert_norm (113078212119488524182321725536530833525387651586070078459396737364324718793 * pow2 4 + 5 == 1809251393911816386917147608584493336406202425377121255350347797829195500693);
  qstep out t15 c 6sz x 1809251393911816386917147608584493336406202425377121255350347797829195500693 15;
  assert_norm (1809251393911816386917147608584493336406202425377121255350347797829195500693 * pow2 6 + 15 == 115792089210356248762697446949407573529996955224135760342422259061068512044367);
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044367 == P.order - 2);
}
#pop-options

(** {2 Comparison} *)

fn qeq (a b: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem va /\ qelem vb)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (qev va = qev vb))
{
  qmod_ok (); qmod_m ();
  mev_eq qmod (vals va) (vals vb);
  aeq a b
}

fn qis_zero (a: A.array S64.t) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** pure (qelem va)
returns r: bool
ensures A.pts_to a #pa va ** pure (r == (qev va = P.qzero))
{
  qmod_ok (); qmod_m ();
  mev_iszero qmod (vals va);
  mzero_ok ();
  let z = S64.zero;
  let mut az = [| z; 4sz |]; A.pts_to_len az; A.pts_to_len az;
  azero az;
  let r = aeq a az;
  r
}

(** {2 Conversions} *)

inline_for_extraction
fn qto (out a: A.array S64.t)
       (#vo: erased (Seq.seq S64.t))
       (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ res qmod (vals va))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == eval (vals va))
{
  qmod_ok (); qmod_m ();
  mev_to qmod (vals va);
  let ms = qms ();
  let nm = qnm ();
  let r2 = qr2 ();
  amul out a r2 ms nm qmu qmod;
  drop_table ms;
  drop_table nm;
  drop_table r2;
}

inline_for_extraction
fn qfrom (out a: A.array S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == nl /\ bnd (vals vo') base /\
        eval (vals vo') == qev va)
{
  qmod_ok (); qmod_m ();
  mone_ok ();
  mev_of qmod (vals va);
  let ms = qms ();
  let nm = qnm ();
  let one = mone ();
  amul out a one ms nm qmu qmod;
  drop_table ms;
  drop_table nm;
  drop_table one;
}

(** {2 Bytes}

    Two decoders.  [qload] is the private-key and signature-component
    check: thirty-two big-endian bytes are a scalar only when they are
    strictly between zero and the order.  [qload_mod] is the hash
    conversion, which reduces instead of rejecting; one conditional
    subtraction suffices because [2^256] is below twice the order. *)

#push-options "--z3rlimit 200"

fn qload (out: A.array S64.t) (b: A.array S8.t)
         (#vo: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
returns r: bool
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (qelem vo' /\ r == (0 < be_nat vb && be_nat vb < P.order) /\
        (r ==> qev vo' == be_nat vb))
{
  qmod_ok (); qmod_m ();
  assert_norm (pow2 256 < 2 * P.order);
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; let mut asv = [| z128; 4sz |]; A.pts_to_len asv; A.pts_to_len at; A.pts_to_len asv;
  load_be at b;
  let nm = qnm ();
  let lo = abelow at asv nm qmod;
  drop_table nm;
  qto out at;
  let nz = qis_zero out;
  lo && not nz
}

fn qload_mod (out: A.array S64.t) (b: A.array S8.t)
             (#vo: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == be_nat vb % P.order)
{
  qmod_ok (); qmod_m ();
  assert_norm (pow2 256 < 2 * P.order);
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; let mut asv = [| z128; 4sz |]; A.pts_to_len asv; A.pts_to_len at; A.pts_to_len asv;
  load_be at b;
  let nm = qnm ();
  ared at asv nm qmod;
  drop_table nm;
  qto out at;
  ()
}

fn qstore (b: A.array S8.t) (a: A.array S64.t)
          (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ qelem va)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_be 32 (qev va))
{
  let z = S64.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; A.pts_to_len at;
  qfrom at a;
  store_be b at;
  ()
}

#pop-options

#pop-options
