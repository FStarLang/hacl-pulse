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
    [Hacl.K256.Field], with [qmod] in place of [fmod].  ECDSA needs
    addition, multiplication and inversion here, plus two decoders: one
    that insists the scalar is a proper private key, and one that reduces
    a hash modulo the order.

    Because [Hacl.Impl.Mont4] takes its modulus as data, none of this
    duplicates any code in the emitted C: the two fields share every
    operation and differ only in the table they pass.  Multiplication goes
    through [Hacl.Impl.Mont4F], the word-by-word reduction of
    [Hacl.Impl.Mont64], which is twice as fast and just as generic, so the
    sharing holds there too.  Inversion is an addition chain over it. *)
module Hacl.K256.Scalar

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.K256.Field
open Spec.Mont4
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.Impl.Bignum4
open Hacl.Impl.Mont4
open Hacl.K256.Tables
open Hacl.Impl.Exp4
open Hacl.Impl.Mont4F

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module K = Spec.K256
module MA = Spec.ModArith
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What a scalar is} *)

let qelem (v: Seq.seq S64.t) : prop = res qmod (vals v)

let qmod_m (_: unit) : Lemma (qmod.m == K.order) = ()

let qev (v: Seq.seq S64.t) : GTot K.qelem = mev qmod (vals v)

(** {2 The ring operations} *)

fn qadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == K.qadd (qev va) (qev vb))
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
  pure (qelem vo' /\ qev vo' == K.qmul (qev va) (qev vb))
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
  pure (qelem vo' /\ qev vo' == K.qmul (qev va) (qev va))
{
  A.share a;
  qmul out a a;
  A.gather a;
}

(** {2 Inversion}

    [x^(n-2)] by a fixed addition chain. The exponent is a constant from
    the standard, so the chain is public and straight-line: no table
    lookup depends on anything secret. The odd powers [x^1 .. x^15] come
    first; the top of [n - 2] is a hundred and twenty-seven ones and a
    zero, built from blocks of ones; the rest is a sliding window of width
    four over those odd powers. *)

(** [a := a * a], through the scratch [c]. *)
fn qsqr_ip (a c: A.array S64.t)
           (#va: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c vc **
  pure (qelem va /\ Seq.length vc == nl)
ensures exists* (va': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c vc' **
  pure (qelem va' /\ Seq.length vc' == nl /\ qev va' == MA.exp #K.order (qev va) 2)
{
  A.pts_to_len a;
  acopy c a;
  with u. assert (A.pts_to c u);
  assert (pure (qev u == qev va));
  qsqr a c;
  with v'. assert (A.pts_to a v');
  MA.exp_two (qev va);
  assert (pure (qev v' == K.qmul (qev va) (qev va)));
  assert (pure (qev v' == MA.exp #K.order (qev va) 2));
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
  pure (qelem va' /\ Seq.length vc' == nl /\ qev va' == K.qmul (qev va) (qev vb))
{
  A.pts_to_len a;
  acopy c a;
  qmul a c b;
}

(** One more squaring when [b]: the tail of an odd count. *)
fn qsqr_if (b: bool) (a c: A.array S64.t) (x: erased K.qelem) (k: erased nat)
           (#va: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c vc **
  pure (qelem va /\ Seq.length vc == nl /\ qev va == MA.exp #K.order x (pow2 k))
ensures exists* (va': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c vc' **
  pure (qelem va' /\ Seq.length vc' == nl /\
        qev va' == MA.exp #K.order x (pow2 (if b then k + 1 else k)))
{
  if b {
    qsqr_ip a c;
    with v'. assert (A.pts_to a v');
    MA.exp_mul x (pow2 k) 2;
    Math.pow2_double_mult k;
    assert (pure (qev v' == MA.exp #K.order x (pow2 (k + 1))));
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
        qev va' == MA.exp #K.order (qev va) (pow2 (SZ.v n)))
{
  MA.exp_one (qev va);
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt 1sz (SZ.sub n vi))
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (u: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to c u **
    pure (SZ.v vi <= SZ.v n /\ qelem v /\ Seq.length u == nl /\
          qev v == MA.exp #K.order (qev va) (pow2 (SZ.v vi)))
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
    assert (pure (qev u == MA.exp #K.order (qev va) (pow2 (SZ.v vi + 1))));
    MA.exp_mul (qev va) (pow2 (SZ.v vi + 1)) 2;
    Math.pow2_double_mult (SZ.v vi + 1);
    assert (pure (qev v' == MA.exp #K.order (qev va) (pow2 (SZ.v vi + 2))));
    i := SZ.add vi 2sz;
  };
  let vi = !i;
  qsqr_if (SZ.lt vi n) a c (hide (qev va)) (SZ.v vi);
}

(** [out := out^(2^k) * t], where [out] and [t] are known powers of [x]. *)
fn qstep (out t c: A.array S64.t) (k: SZ.t) (x: erased K.qelem) (e v: erased nat)
         (#vo: erased (Seq.seq S64.t))
         (#pt: perm) (#vt: erased (Seq.seq S64.t))
         (#vc: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t #pt vt ** A.pts_to c vc **
  pure (qelem vo /\ qelem vt /\ Seq.length vc == nl /\
        qev vo == MA.exp #K.order x e /\ qev vt == MA.exp #K.order x v)
ensures exists* (vo': Seq.seq S64.t) (vc': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t #pt vt ** A.pts_to c vc' **
  pure (qelem vo' /\ Seq.length vc' == nl /\
        qev vo' == MA.exp #K.order x (e * pow2 (SZ.v k) + v))
{
  qpow2_ip out c k;
  with u. assert (A.pts_to out u);
  MA.exp_mul x e (pow2 (SZ.v k));
  assert (pure (qev u == MA.exp #K.order x (e * pow2 (SZ.v k))));
  qmul_ip out t c;
  with u2. assert (A.pts_to out u2);
  MA.exp_add x (e * pow2 (SZ.v k)) v;
  assert (pure (qev u2 == MA.exp #K.order x (e * pow2 (SZ.v k) + v)));
}

#push-options "--z3rlimit 400"
fn qinv (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == K.qinv (qev va))
{
  qmod_m ();
  let x : erased K.qelem = hide (qev va);
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
  let mut e8 = [| z; 4sz |]; A.pts_to_len e8;
  let mut e16 = [| z; 4sz |]; A.pts_to_len e16;
  let mut e32 = [| z; 4sz |]; A.pts_to_len e32;
  A.pts_to_len out;
  qsqr x2 a;
  MA.exp_two (qev va);
  with v1. assert (A.pts_to x2 v1);
  assert (pure (qelem v1 /\ qev v1 == MA.exp #K.order (qev va) 2));
  MA.exp_one (qev va);
  qmul t3 a x2;
  MA.exp_add (qev va) 1 2;
  with v2. assert (A.pts_to t3 v2);
  assert (pure (qelem v2 /\ qev v2 == MA.exp #K.order (qev va) 3));
  qmul t5 t3 x2;
  MA.exp_add (qev va) 3 2;
  with v3. assert (A.pts_to t5 v3);
  assert (pure (qelem v3 /\ qev v3 == MA.exp #K.order (qev va) 5));
  qmul t7 t5 x2;
  MA.exp_add (qev va) 5 2;
  with v4. assert (A.pts_to t7 v4);
  assert (pure (qelem v4 /\ qev v4 == MA.exp #K.order (qev va) 7));
  qmul t9 t7 x2;
  MA.exp_add (qev va) 7 2;
  with v5. assert (A.pts_to t9 v5);
  assert (pure (qelem v5 /\ qev v5 == MA.exp #K.order (qev va) 9));
  qmul t11 t9 x2;
  MA.exp_add (qev va) 9 2;
  with v6. assert (A.pts_to t11 v6);
  assert (pure (qelem v6 /\ qev v6 == MA.exp #K.order (qev va) 11));
  qmul t13 t11 x2;
  MA.exp_add (qev va) 11 2;
  with v7. assert (A.pts_to t13 v7);
  assert (pure (qelem v7 /\ qev v7 == MA.exp #K.order (qev va) 13));
  qmul t15 t13 x2;
  MA.exp_add (qev va) 13 2;
  with v8. assert (A.pts_to t15 v8);
  assert (pure (qelem v8 /\ qev v8 == MA.exp #K.order (qev va) 15));
  acopy out t15;
  qstep out t15 c 4sz x 15 15;
  assert_norm (15 * pow2 4 + 15 == 255);
  acopy e8 out;
  qstep out e8 c 8sz x 255 255;
  assert_norm (255 * pow2 8 + 255 == 65535);
  acopy e16 out;
  qstep out e16 c 16sz x 65535 65535;
  assert_norm (65535 * pow2 16 + 65535 == 4294967295);
  acopy e32 out;
  qstep out e32 c 32sz x 4294967295 4294967295;
  assert_norm (4294967295 * pow2 32 + 4294967295 == 18446744073709551615);
  qstep out e32 c 32sz x 18446744073709551615 4294967295;
  assert_norm (18446744073709551615 * pow2 32 + 4294967295 == 79228162514264337593543950335);
  qstep out e16 c 16sz x 79228162514264337593543950335 65535;
  assert_norm (79228162514264337593543950335 * pow2 16 + 65535 == 5192296858534827628530496329220095);
  qstep out e8 c 8sz x 5192296858534827628530496329220095 255;
  assert_norm (5192296858534827628530496329220095 * pow2 8 + 255 == 1329227995784915872903807060280344575);
  qstep out t15 c 4sz x 1329227995784915872903807060280344575 15;
  assert_norm (1329227995784915872903807060280344575 * pow2 4 + 15 == 21267647932558653966460912964485513215);
  qstep out t7 c 3sz x 21267647932558653966460912964485513215 7;
  assert_norm (21267647932558653966460912964485513215 * pow2 3 + 7 == 170141183460469231731687303715884105727);
  qstep out t11 c 5sz x 170141183460469231731687303715884105727 11;
  assert_norm (170141183460469231731687303715884105727 * pow2 5 + 11 == 5444517870735015415413993718908291383275);
  qstep out t5 c 3sz x 5444517870735015415413993718908291383275 5;
  assert_norm (5444517870735015415413993718908291383275 * pow2 3 + 5 == 43556142965880123323311949751266331066205);
  qstep out t5 c 4sz x 43556142965880123323311949751266331066205 5;
  assert_norm (43556142965880123323311949751266331066205 * pow2 4 + 5 == 696898287454081973172991196020261297059285);
  qstep out t7 c 4sz x 696898287454081973172991196020261297059285 7;
  assert_norm (696898287454081973172991196020261297059285 * pow2 4 + 7 == 11150372599265311570767859136324180752948567);
  qstep out t13 c 5sz x 11150372599265311570767859136324180752948567 13;
  assert_norm (11150372599265311570767859136324180752948567 * pow2 5 + 13 == 356811923176489970264571492362373784094354157);
  qstep out t3 c 2sz x 356811923176489970264571492362373784094354157 3;
  assert_norm (356811923176489970264571492362373784094354157 * pow2 2 + 3 == 1427247692705959881058285969449495136377416631);
  qstep out t7 c 5sz x 1427247692705959881058285969449495136377416631 7;
  assert_norm (1427247692705959881058285969449495136377416631 * pow2 5 + 7 == 45671926166590716193865151022383844364077332199);
  qstep out t13 c 6sz x 45671926166590716193865151022383844364077332199 13;
  assert_norm (45671926166590716193865151022383844364077332199 * pow2 6 + 13 == 2923003274661805836407369665432566039300949260749);
  qstep out t11 c 5sz x 2923003274661805836407369665432566039300949260749 11;
  assert_norm (2923003274661805836407369665432566039300949260749 * pow2 5 + 11 == 93536104789177786765035829293842113257630376343979);
  qstep out t13 c 4sz x 93536104789177786765035829293842113257630376343979 13;
  assert_norm (93536104789177786765035829293842113257630376343979 * pow2 4 + 13 == 1496577676626844588240573268701473812122086021503677);
  qstep out a c 3sz x 1496577676626844588240573268701473812122086021503677 1;
  assert_norm (1496577676626844588240573268701473812122086021503677 * pow2 3 + 1 == 11972621413014756705924586149611790496976688172029417);
  qstep out t5 c 6sz x 11972621413014756705924586149611790496976688172029417 5;
  assert_norm (11972621413014756705924586149611790496976688172029417 * pow2 6 + 5 == 766247770432944429179173513575154591806508043009882693);
  qstep out t7 c 10sz x 766247770432944429179173513575154591806508043009882693 7;
  assert_norm (766247770432944429179173513575154591806508043009882693 * pow2 10 + 7 == 784637716923335095479473677900958302009864236042119877639);
  qstep out t7 c 4sz x 784637716923335095479473677900958302009864236042119877639 7;
  assert_norm (784637716923335095479473677900958302009864236042119877639 * pow2 4 + 7 == 12554203470773361527671578846415332832157827776673918042231);
  qstep out t15 c 5sz x 12554203470773361527671578846415332832157827776673918042231 15;
  assert_norm (12554203470773361527671578846415332832157827776673918042231 * pow2 5 + 15 == 401734511064747568885490523085290650629050488853565377351407);
  qstep out t15 c 4sz x 401734511064747568885490523085290650629050488853565377351407 15;
  assert_norm (401734511064747568885490523085290650629050488853565377351407 * pow2 4 + 15 == 6427752177035961102167848369364650410064807821657046037622527);
  qstep out t9 c 5sz x 6427752177035961102167848369364650410064807821657046037622527 9;
  assert_norm (6427752177035961102167848369364650410064807821657046037622527 * pow2 5 + 9 == 205688069665150755269371147819668813122073850293025473203920873);
  qstep out t11 c 6sz x 205688069665150755269371147819668813122073850293025473203920873 11;
  assert_norm (205688069665150755269371147819668813122073850293025473203920873 * pow2 6 + 11 == 13164036458569648337239753460458804039812726418753630285050935883);
  qstep out t13 c 4sz x 13164036458569648337239753460458804039812726418753630285050935883 13;
  assert_norm (13164036458569648337239753460458804039812726418753630285050935883 * pow2 4 + 13 == 210624583337114373395836055367340864637003622700058084560814974141);
  qstep out t3 c 5sz x 210624583337114373395836055367340864637003622700058084560814974141 3;
  assert_norm (210624583337114373395836055367340864637003622700058084560814974141 * pow2 5 + 3 == 6739986666787659948666753771754907668384115926401858705946079172515);
  qstep out t13 c 6sz x 6739986666787659948666753771754907668384115926401858705946079172515 13;
  assert_norm (6739986666787659948666753771754907668384115926401858705946079172515 * pow2 6 + 13 == 431359146674410236714672241392314090776583419289718957180549067040973);
  qstep out t13 c 10sz x 431359146674410236714672241392314090776583419289718957180549067040973 13;
  assert_norm (431359146674410236714672241392314090776583419289718957180549067040973 * pow2 10 + 13 == 441711766194596082395824375185729628955221421352672212152882244649956365);
  qstep out t9 c 4sz x 441711766194596082395824375185729628955221421352672212152882244649956365 9;
  assert_norm (441711766194596082395824375185729628955221421352672212152882244649956365 * pow2 4 + 9 == 7067388259113537318333190002971674063283542741642755394446115914399301849);
  qstep out t9 c 9sz x 7067388259113537318333190002971674063283542741642755394446115914399301849 9;
  assert_norm (7067388259113537318333190002971674063283542741642755394446115914399301849 * pow2 9 + 9 == 3618502788666131106986593281521497120401173883721090761956411348172442546697);
  qstep out t15 c 4sz x 3618502788666131106986593281521497120401173883721090761956411348172442546697 15;
  assert_norm (3618502788666131106986593281521497120401173883721090761956411348172442546697 * pow2 4 + 15 == 57896044618658097711785492504343953926418782139537452191302581570759080747167);
  qstep out a c 1sz x 57896044618658097711785492504343953926418782139537452191302581570759080747167 1;
  assert_norm (57896044618658097711785492504343953926418782139537452191302581570759080747167 * pow2 1 + 1 == 115792089237316195423570985008687907852837564279074904382605163141518161494335);
  assert_norm (115792089237316195423570985008687907852837564279074904382605163141518161494335 == K.order - 2);
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
ensures A.pts_to a #pa va ** pure (r == (qev va = K.qzero))
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
  pure (qelem vo' /\ r == (0 < be_nat vb && be_nat vb < K.order) /\
        (r ==> qev vo' == be_nat vb))
{
  qmod_ok (); qmod_m ();
  assert_norm (pow2 256 < 2 * K.order);
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
  pure (qelem vo' /\ qev vo' == be_nat vb % K.order)
{
  qmod_ok (); qmod_m ();
  assert_norm (pow2 256 < 2 * K.order);
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
