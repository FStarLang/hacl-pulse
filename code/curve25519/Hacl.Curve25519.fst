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

(** X25519.

    The Montgomery ladder over [Hacl.Curve25519.Field], two hundred and
    fifty-six steps of one differential addition and one doubling, with the
    scalar bit consumed as a mask rather than as a branch: the two
    conditional swaps around each step are [select]s, so the sequence of
    instructions and the sequence of addresses touched do not depend on the
    key.

    The only place a secret becomes a [bool] is [ecdh], which has to say
    whether the shared secret came out zero, and that is exactly the one bit
    the protocol is entitled to. *)
module Hacl.Curve25519

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Spec.Bytes
open Hacl.Curve25519.Field
open Hacl.Curve25519.Inverse

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Declassify = Hacl.Secret.Declassify
module Copy = Hacl.Impl.Copy
module Loops = Hacl.Spec.Loops
module C = Spec.Curve25519

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 Small constants}

    The ladder starts from [(1, 0)] and [(x1, 1)], so the only literals it
    needs are one and zero. *)

fn set_small (a: S.slice S64.t) (x: U64.t { U64.v x < base })
             (#va: erased (Seq.seq S64.t))
requires S.pts_to a va ** pure (Seq.length va == nl)
ensures exists* (va': Seq.seq S64.t).
  S.pts_to a va' **
  pure (Seq.length va' == nl /\ bnd (vals va') base /\ felem (vals va') /\
        eval (vals va') == U64.v x /\ fev (vals va') == U64.v x)
{
  S.pts_to_len a;
  let z = S64.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to a v **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> S64.v (Seq.index v k) == 0))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    S.((a.(vi) <- z));
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to a v);
  eval_zeros (vals v);
  let c = S64.classify x;
  S.((a.(0sz) <- c));
  with v'. assert (S.pts_to a v');
  vals_upd v 0 c;
  eval_upd (vals v) 0 (U64.v x);
  assert_norm (pow2 (rad * 0) == 1);
  assert_norm (base - 1 <= lim);
  assert_norm (base < pow2 255 - 19);
  Math.small_mod (U64.v x) C.prime;
  assert (pure (eval (vals v') == U64.v x /\ bnd (vals v') base));
}

(** {2 Squaring}

    [fmul] wants a destination disjoint from its arguments, so a square is a
    copy and a multiplication. *)

fn fsqr (out a c t: S.slice S64.t)
        (#vout: erased (Seq.seq S64.t)) (#vc: erased (Seq.seq S64.t))
        (#vt: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires S.pts_to out vout ** S.pts_to c vc ** S.pts_to t vt ** S.pts_to a #pa va **
  pure (Seq.length vout == nl /\ Seq.length vc == nl /\ Seq.length vt == nw /\
        felem (vals va))
ensures exists* (vout': Seq.seq S64.t) (vc': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to out vout' ** S.pts_to c vc' ** S.pts_to t vt' ** S.pts_to a #pa va **
  pure (Seq.length vc' == nl /\ Seq.length vt' == nw /\ felem (vals vout') /\
        fev (vals vout') == C.fmul (fev (vals va)) (fev (vals va)))
{
  copy c a;
  with u. assert (S.pts_to c u);
  assert (pure (vals u == vals va));
  fmul out a c t;
}

(** {2 One ladder step}

    RFC 7748 section 5's formulas, with the seven temporaries laid out so
    that nothing is read after it has been overwritten:

      [t0 = x2+z2], [t1 = x2-z2], [t2 = x3+z3], [t3 = x3-z3],
      [t4 = t3*t0], [t5 = t2*t1], then [t2 = t0^2] and [t3 = t1^2] reuse the
      two that are finished with. *)

#push-options "--z3rlimit 200"

fn add_and_double (x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 t6 t31 x1: S.slice S64.t)
                  (#vx2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t))
                  (#vx3: erased (Seq.seq S64.t)) (#vz3: erased (Seq.seq S64.t))
                  (#v0: erased (Seq.seq S64.t)) (#v1: erased (Seq.seq S64.t))
                  (#v2: erased (Seq.seq S64.t)) (#v3: erased (Seq.seq S64.t))
                  (#v4: erased (Seq.seq S64.t)) (#v5: erased (Seq.seq S64.t))
                  (#v6: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
                  (#p1: perm) (#vx1: erased (Seq.seq S64.t))
requires
  S.pts_to x2 vx2 ** S.pts_to z2 vz2 ** S.pts_to x3 vx3 ** S.pts_to z3 vz3 **
  S.pts_to t0 v0 ** S.pts_to t1 v1 ** S.pts_to t2 v2 ** S.pts_to t3 v3 **
  S.pts_to t4 v4 ** S.pts_to t5 v5 ** S.pts_to t6 v6 ** S.pts_to t31 vt **
  S.pts_to x1 #p1 vx1 **
  pure (felem (vals vx2) /\ felem (vals vz2) /\ felem (vals vx3) /\
        felem (vals vz3) /\ felem (vals vx1) /\
        Seq.length v0 == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl /\
        Seq.length v3 == nl /\ Seq.length v4 == nl /\ Seq.length v5 == nl /\
        Seq.length v6 == nl /\ Seq.length vt == nw)
ensures exists* (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t)
                (w6: Seq.seq S64.t) (wt: Seq.seq S64.t).
  S.pts_to x2 wx2 ** S.pts_to z2 wz2 ** S.pts_to x3 wx3 ** S.pts_to z3 wz3 **
  S.pts_to t0 w0 ** S.pts_to t1 w1 ** S.pts_to t2 w2 ** S.pts_to t3 w3 **
  S.pts_to t4 w4 ** S.pts_to t5 w5 ** S.pts_to t6 w6 ** S.pts_to t31 wt **
  S.pts_to x1 #p1 vx1 **
  pure (felem (vals wx2) /\ felem (vals wz2) /\ felem (vals wx3) /\
        felem (vals wz3) /\
        Seq.length w0 == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
        Seq.length w3 == nl /\ Seq.length w4 == nl /\ Seq.length w5 == nl /\
        Seq.length w6 == nl /\ Seq.length wt == nw /\
        ((fev (vals wx2), fev (vals wz2)), (fev (vals wx3), fev (vals wz3))) ==
          C.add_and_double (fev (vals vx1))
            (fev (vals vx2), fev (vals vz2))
            (fev (vals vx3), fev (vals vz3)))
{
  fadd t0 x2 z2;                          (* a  *)
  fsub t1 x2 z2;                          (* b  *)
  fadd t2 x3 z3;                          (* c  *)
  fsub t3 x3 z3;                          (* d  *)
  fmul t4 t3 t0 t31;                      (* da *)
  fmul t5 t2 t1 t31;                      (* cb *)
  fsqr t2 t0 t6 t31;                      (* aa *)
  fsqr t3 t1 t6 t31;                      (* bb *)
  fadd t0 t4 t5;                          (* da + cb *)
  fsub t1 t4 t5;                          (* da - cb *)
  fsqr x3 t0 t6 t31;                      (* x3' *)
  fsqr t4 t1 t6 t31;
  fmul z3 x1 t4 t31;                      (* z3' *)
  fsub t5 t2 t3;                          (* e = aa - bb *)
  fmul x2 t2 t3 t31;                      (* x2' = aa * bb *)
  with e. assert (S.pts_to t5 e);
  fscale t0 t5 121665uL;
  with s. assert (S.pts_to t0 s);
  Math.lemma_mod_mul_distr_r 121665 (eval (vals e)) C.prime;
  assert (pure (fev (vals s) == C.fmul C.a24 (fev (vals e))));
  fadd t1 t3 t0;                          (* bb + a24 e *)
  fmul z2 t5 t1 t31;                      (* z2' *)
}

#pop-options

(** {2 One step of the ladder}

    [ks] is the clamped scalar.  Step [i] consumes bit [255 - i], most
    significant first; the mask is the bit spread across a word, and the
    swaps are the only thing the bit does.  Kept as its own function so that
    the loop below has nothing to prove but the arithmetic on the index. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

fn ladder_one (x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 t6 t31 x1: S.slice S64.t)
              (ks: S.slice S8.t) (n: SZ.t { SZ.v n < 256 })
              (#vx2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t))
              (#vx3: erased (Seq.seq S64.t)) (#vz3: erased (Seq.seq S64.t))
              (#v0: erased (Seq.seq S64.t)) (#v1: erased (Seq.seq S64.t))
              (#v2: erased (Seq.seq S64.t)) (#v3: erased (Seq.seq S64.t))
              (#v4: erased (Seq.seq S64.t)) (#v5: erased (Seq.seq S64.t))
              (#v6: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
              (#p1: perm) (#vx1: erased (Seq.seq S64.t))
              (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  S.pts_to x2 vx2 ** S.pts_to z2 vz2 ** S.pts_to x3 vx3 ** S.pts_to z3 vz3 **
  S.pts_to t0 v0 ** S.pts_to t1 v1 ** S.pts_to t2 v2 ** S.pts_to t3 v3 **
  S.pts_to t4 v4 ** S.pts_to t5 v5 ** S.pts_to t6 v6 ** S.pts_to t31 vt **
  S.pts_to x1 #p1 vx1 ** S.pts_to ks #pk vk **
  pure (felem (vals vx2) /\ felem (vals vz2) /\ felem (vals vx3) /\
        felem (vals vz3) /\ felem (vals vx1) /\
        Seq.length v0 == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl /\
        Seq.length v3 == nl /\ Seq.length v4 == nl /\ Seq.length v5 == nl /\
        Seq.length v6 == nl /\ Seq.length vt == nw)
ensures exists* (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t)
                (w6: Seq.seq S64.t) (wt: Seq.seq S64.t).
  S.pts_to x2 wx2 ** S.pts_to z2 wz2 ** S.pts_to x3 wx3 ** S.pts_to z3 wz3 **
  S.pts_to t0 w0 ** S.pts_to t1 w1 ** S.pts_to t2 w2 ** S.pts_to t3 w3 **
  S.pts_to t4 w4 ** S.pts_to t5 w5 ** S.pts_to t6 w6 ** S.pts_to t31 wt **
  S.pts_to x1 #p1 vx1 ** S.pts_to ks #pk vk **
  pure (felem (vals wx2) /\ felem (vals wz2) /\ felem (vals wx3) /\
        felem (vals wz3) /\
        Seq.length w0 == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
        Seq.length w3 == nl /\ Seq.length w4 == nl /\ Seq.length w5 == nl /\
        Seq.length w6 == nl /\ Seq.length wt == nw /\
        ((fev (vals wx2), fev (vals wz2)), (fev (vals wx3), fev (vals wz3))) ==
          C.ladder_at (fev (vals vx1)) vk (SZ.v n)
            ((fev (vals vx2), fev (vals vz2)),
             (fev (vals vx3), fev (vals vz3))))
{
  S.pts_to_len ks;
  let bi = SZ.sub 255sz n;
  let bj = SZ.div bi 8sz;
  let sh = SZ.sizet_to_uint32 (SZ.rem bi 8sz);
  assert_norm (pow2 32 > 8);
  Math.small_mod (SZ.v (SZ.rem bi 8sz)) (pow2 32);
  assert (pure (SZ.v bi == 255 - SZ.v n /\ SZ.v bj == SZ.v bi / 8 /\
                U32.v sh == SZ.v bi % 8));
  let byte = S.(ks.(bj));
  let w = Cast.u8_to_u64 byte;
  assert (pure (S64.v w == S8.v (Seq.index vk (SZ.v bi / 8))));
  let sr = S64.shift_right w sh;
  assert (pure (S64.v sr == S64.v w / pow2 (SZ.v bi % 8)));
  UInt.logand_mask #64 (S64.v sr) 1;
  let bit = S64.logand sr (S64.classify 1uL);
  assert (pure (S64.v bit == C.ith_bit vk (SZ.v bi) /\ S64.v bit < 2));
  let sel = S64.eq_mask bit (S64.classify 1uL);
  assert (pure ((S64.v sel == 0) == (S64.v bit <> 1)));

  cswap sel x2 x3;
  cswap sel z2 z3;
  with sx2. assert (S.pts_to x2 sx2);
  with sz2. assert (S.pts_to z2 sz2);
  with sx3. assert (S.pts_to x3 sx3);
  with sz3. assert (S.pts_to z3 sz3);
  assert (pure
    (((fev (vals sx2), fev (vals sz2)), (fev (vals sx3), fev (vals sz3))) ==
      C.cswap (C.ith_bit vk (SZ.v bi))
        (fev (vals vx2), fev (vals vz2)) (fev (vals vx3), fev (vals vz3))));

  add_and_double x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 t6 t31 x1;
  with ax2. assert (S.pts_to x2 ax2);
  with az2. assert (S.pts_to z2 az2);
  with ax3. assert (S.pts_to x3 ax3);
  with az3. assert (S.pts_to z3 az3);

  cswap sel x2 x3;
  cswap sel z2 z3;
  with ux2. assert (S.pts_to x2 ux2);
  with uz2. assert (S.pts_to z2 uz2);
  with ux3. assert (S.pts_to x3 ux3);
  with uz3. assert (S.pts_to z3 uz3);
  assert (pure
    (((fev (vals ux2), fev (vals uz2)), (fev (vals ux3), fev (vals uz3))) ==
      C.cswap (C.ith_bit vk (SZ.v bi))
        (fev (vals ax2), fev (vals az2)) (fev (vals ax3), fev (vals az3))));
  assert (pure
    (((fev (vals ux2), fev (vals uz2)), (fev (vals ux3), fev (vals uz3))) ==
      C.ladder_step (fev (vals vx1)) vk (SZ.v n)
        ((fev (vals vx2), fev (vals vz2)),
         (fev (vals vx3), fev (vals vz3)))));
}

#pop-options

(** {2 The ladder}

    Two hundred and fifty-six steps, and the only thing left to check is that
    the loop counter walks [Loops.repeati_g]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn ladder (x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 t6 t31 x1: S.slice S64.t)
          (ks: S.slice S8.t)
          (#vx2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t))
          (#vx3: erased (Seq.seq S64.t)) (#vz3: erased (Seq.seq S64.t))
          (#v0: erased (Seq.seq S64.t)) (#v1: erased (Seq.seq S64.t))
          (#v2: erased (Seq.seq S64.t)) (#v3: erased (Seq.seq S64.t))
          (#v4: erased (Seq.seq S64.t)) (#v5: erased (Seq.seq S64.t))
          (#v6: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
          (#p1: perm) (#vx1: erased (Seq.seq S64.t))
          (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  S.pts_to x2 vx2 ** S.pts_to z2 vz2 ** S.pts_to x3 vx3 ** S.pts_to z3 vz3 **
  S.pts_to t0 v0 ** S.pts_to t1 v1 ** S.pts_to t2 v2 ** S.pts_to t3 v3 **
  S.pts_to t4 v4 ** S.pts_to t5 v5 ** S.pts_to t6 v6 ** S.pts_to t31 vt **
  S.pts_to x1 #p1 vx1 ** S.pts_to ks #pk vk **
  pure (felem (vals vx1) /\
        Seq.length v0 == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl /\
        Seq.length v3 == nl /\ Seq.length v4 == nl /\ Seq.length v5 == nl /\
        Seq.length v6 == nl /\ Seq.length vt == nw /\
        felem (vals vx2) /\ felem (vals vz2) /\ felem (vals vx3) /\
        felem (vals vz3) /\
        ((fev (vals vx2), fev (vals vz2)), (fev (vals vx3), fev (vals vz3))) ==
          C.ladder_init (fev (vals vx1)))
ensures exists* (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t)
                (w6: Seq.seq S64.t) (wt: Seq.seq S64.t).
  S.pts_to x2 wx2 ** S.pts_to z2 wz2 ** S.pts_to x3 wx3 ** S.pts_to z3 wz3 **
  S.pts_to t0 w0 ** S.pts_to t1 w1 ** S.pts_to t2 w2 ** S.pts_to t3 w3 **
  S.pts_to t4 w4 ** S.pts_to t5 w5 ** S.pts_to t6 w6 ** S.pts_to t31 wt **
  S.pts_to x1 #p1 vx1 ** S.pts_to ks #pk vk **
  pure (felem (vals wx2) /\ felem (vals wz2) /\
        Seq.length w0 == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
        Seq.length w3 == nl /\ Seq.length w4 == nl /\ Seq.length w5 == nl /\
        Seq.length w6 == nl /\ Seq.length wt == nw /\
        (fev (vals wx2), fev (vals wz2)) ==
          fst (C.montgomery_ladder (fev (vals vx1)) vk))
{
  Loops.repeati_g_zero (C.ladder_at (fev (vals vx1)) vk) (C.ladder_init (fev (vals vx1)));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t)
                    (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                    (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                    (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                    (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t)
                    (w6: Seq.seq S64.t) (wt: Seq.seq S64.t).
    pts_to i vi **
    S.pts_to x2 wx2 ** S.pts_to z2 wz2 ** S.pts_to x3 wx3 ** S.pts_to z3 wz3 **
    S.pts_to t0 w0 ** S.pts_to t1 w1 ** S.pts_to t2 w2 ** S.pts_to t3 w3 **
    S.pts_to t4 w4 ** S.pts_to t5 w5 ** S.pts_to t6 w6 ** S.pts_to t31 wt **
    S.pts_to x1 #p1 vx1 ** S.pts_to ks #pk vk **
    pure (SZ.v vi <= 256 /\
          felem (vals wx2) /\ felem (vals wz2) /\ felem (vals wx3) /\
          felem (vals wz3) /\
          Seq.length w0 == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
          Seq.length w3 == nl /\ Seq.length w4 == nl /\ Seq.length w5 == nl /\
          Seq.length w6 == nl /\ Seq.length wt == nw /\
          ((fev (vals wx2), fev (vals wz2)), (fev (vals wx3), fev (vals wz3))) ==
            Loops.repeati_g (SZ.v vi) (C.ladder_at (fev (vals vx1)) vk)
                            (C.ladder_init (fev (vals vx1))))
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    with wx2. assert (S.pts_to x2 wx2);
    with wz2. assert (S.pts_to z2 wz2);
    with wx3. assert (S.pts_to x3 wx3);
    with wz3. assert (S.pts_to z3 wz3);
    ladder_one x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 t6 t31 x1 ks vi;
    with ux2. assert (S.pts_to x2 ux2);
    with uz2. assert (S.pts_to z2 uz2);
    with ux3. assert (S.pts_to x3 ux3);
    with uz3. assert (S.pts_to z3 uz3);
    Loops.unfold_repeati_g (SZ.v vi) (C.ladder_at (fev (vals vx1)) vk)
                           (C.ladder_init (fev (vals vx1)));
    assert (pure
      (((fev (vals ux2), fev (vals uz2)), (fev (vals ux3), fev (vals uz3))) ==
        Loops.repeati_g (SZ.v vi + 1) (C.ladder_at (fev (vals vx1)) vk)
                        (C.ladder_init (fev (vals vx1)))));
    i := SZ.add vi 1sz;
  };
}

#pop-options

(** {2 Clamping} *)

fn clamp (ks: S.slice S8.t) (k: S.slice S8.t)
         (#vs: erased (Seq.seq S8.t)) (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires S.pts_to ks vs ** S.pts_to k #pk vk **
  pure (Seq.length vs == 32)
ensures exists* (vs': Seq.seq S8.t).
  S.pts_to ks vs' ** S.pts_to k #pk vk **
  pure (vs' == C.clamp vk)
{
  S.pts_to_len ks;
  S.pts_to_len k;
  Copy.copy_prefix ks k 32sz;
  let b0 = S.(ks.(0sz));
  S.((ks.(0sz) <- S8.logand b0 (S8.classify 0xf8uy)));
  let b31 = S.(ks.(31sz));
  S.((ks.(31sz) <- S8.logor (S8.logand b31 (S8.classify 0x7fuy)) (S8.classify 0x40uy)));
  with v. assert (S.pts_to ks v);
  assert (pure (v `Seq.equal` C.clamp vk));
}

(** {2 The scalar multiplication} *)

#push-options "--z3rlimit 300"

fn scalarmult (out k u: S.slice S8.t)
              (#vout: erased (Seq.seq S8.t))
              (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
              (#pu: perm) (#vu: erased (Seq.lseq S8.t 32))
requires S.pts_to out vout ** S.pts_to k #pk vk ** S.pts_to u #pu vu **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to k #pk vk ** S.pts_to u #pu vu **
  pure (vout' == C.scalarmult vk vu)
{
  let z = S64.zero;
  let z8 = S8.classify 0uy;
  let mut ka = [| z8; 32sz |]; A.pts_to_len ka; let ks = S.from_array ka 32sz;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let x1 = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let x2 = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let z2 = S.from_array a3 16sz;
  let mut a4 = [| z; 16sz |]; A.pts_to_len a4; let x3 = S.from_array a4 16sz;
  let mut a5 = [| z; 16sz |]; A.pts_to_len a5; let z3 = S.from_array a5 16sz;
  let mut b0 = [| z; 16sz |]; A.pts_to_len b0; let t0 = S.from_array b0 16sz;
  let mut b1 = [| z; 16sz |]; A.pts_to_len b1; let t1 = S.from_array b1 16sz;
  let mut b2 = [| z; 16sz |]; A.pts_to_len b2; let t2 = S.from_array b2 16sz;
  let mut b3 = [| z; 16sz |]; A.pts_to_len b3; let t3 = S.from_array b3 16sz;
  let mut b4 = [| z; 16sz |]; A.pts_to_len b4; let t4 = S.from_array b4 16sz;
  let mut b5 = [| z; 16sz |]; A.pts_to_len b5; let t5 = S.from_array b5 16sz;
  let mut b6 = [| z; 16sz |]; A.pts_to_len b6; let t6 = S.from_array b6 16sz;
  let mut bw = [| z; 31sz |]; A.pts_to_len bw; let t31 = S.from_array bw 31sz;
  S.pts_to_len ks; S.pts_to_len x1; S.pts_to_len x2; S.pts_to_len z2;
  S.pts_to_len x3; S.pts_to_len z3; S.pts_to_len t0; S.pts_to_len t1;
  S.pts_to_len t2; S.pts_to_len t3; S.pts_to_len t4; S.pts_to_len t5;
  S.pts_to_len t6; S.pts_to_len t31; S.pts_to_len out;

  clamp ks k;
  with vks. assert (S.pts_to ks vks);
  assert (pure (Seq.length vks == 32));

  load x1 u;
  mask_top x1;
  with vx1. assert (S.pts_to x1 vx1);
  assert_norm (base - 1 <= lim);
  assert (pure (felem (vals vx1) /\ fev (vals vx1) == C.decode_point vu));

  set_small x2 1uL;
  set_small z2 0uL;
  copy x3 x1;
  set_small z3 1uL;
  assert (pure (C.one == 1));

  ladder x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 t6 t31 x1 ks;
  with wx2. assert (S.pts_to x2 wx2);
  with wz2. assert (S.pts_to z2 wz2);

  finv t0 z2;
  with vi0. assert (S.pts_to t0 vi0);
  assert (pure (fev (vals vi0) == C.finv (fev (vals wz2))));
  fmul t1 x2 t0 t31;
  with vm. assert (S.pts_to t1 vm);
  assert (pure (fev (vals vm) == C.fmul (fev (vals wx2)) (fev (vals vi0))));
  freeze t1 t2;
  with vr. assert (S.pts_to t1 vr);
  assert (pure (eval (vals vr) == fev (vals vm)));
  store out t1;
  with vo. assert (S.pts_to out vo);
  assert (pure (vo == C.scalarmult vk vu));

  S.to_array ks; S.to_array x1; S.to_array x2; S.to_array z2;
  S.to_array x3; S.to_array z3; S.to_array t0; S.to_array t1;
  S.to_array t2; S.to_array t3; S.to_array t4; S.to_array t5;
  S.to_array t6; S.to_array t31;
}

#pop-options

(** {2 The public API} *)

(** [basepoint] is [9]; the encoding is one byte and thirty-one zeros. *)
fn set_basepoint (b: S.slice S8.t) (#vb: erased (Seq.seq S8.t))
requires S.pts_to b vb ** pure (Seq.length vb == 32)
ensures exists* (vb': Seq.seq S8.t).
  S.pts_to b vb' ** pure (vb' == C.basepoint)
{
  S.pts_to_len b;
  let z8 = S8.classify 0uy;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 32sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** S.pts_to b v **
    pure (SZ.v vi <= 32 /\ Seq.length v == 32 /\
          (forall (kk: nat). kk < SZ.v vi ==> S8.v (Seq.index v kk) == 0))
  decreases (32 - SZ.v (!i))
  {
    let vi = !i;
    S.((b.(vi) <- z8));
    i := SZ.add vi 1sz;
  };
  with v0. assert (S.pts_to b v0);
  S.((b.(0sz) <- S8.classify 9uy));
  with v. assert (S.pts_to b v);
  assert (pure (Seq.length v == 32 /\ S8.v (Seq.index v 0) == 9 /\
                (forall (i: nat). 0 < i /\ i < 32 ==> S8.v (Seq.index v i) == 0)));
  C.basepoint_eq v;
  assert (pure (v == C.basepoint));
}

fn secret_to_public (out k: S.slice S8.t)
                    (#vout: erased (Seq.seq S8.t))
                    (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires S.pts_to out vout ** S.pts_to k #pk vk **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to k #pk vk **
  pure (vout' == C.secret_to_public vk)
{
  let z8 = S8.classify 0uy;
  let mut ba = [| z8; 32sz |]; A.pts_to_len ba; let b = S.from_array ba 32sz;
  S.pts_to_len b;
  set_basepoint b;
  with vb. assert (S.pts_to b vb);
  assert (pure (Seq.length vb == 32));
  scalarmult out k b;
  S.to_array b;
}

(** {2 ECDH}

    The shared secret is rejected exactly when it is zero, which happens iff
    the peer's point had small order.  The test is a sum of the thirty-two
    bytes -- no branch -- and only its being zero escapes as a [bool]. *)

#push-options "--z3rlimit 120"

fn ecdh (out k u: S.slice S8.t)
        (#vout: erased (Seq.seq S8.t))
        (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
        (#pu: perm) (#vu: erased (Seq.lseq S8.t 32))
requires S.pts_to out vout ** S.pts_to k #pk vk ** S.pts_to u #pu vu **
  pure (Seq.length vout == 32)
returns ok: bool
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to k #pk vk ** S.pts_to u #pu vu **
  pure (vout' == fst (C.ecdh vk vu) /\ ok == snd (C.ecdh vk vu))
{
  S.pts_to_len out;
  scalarmult out k u;
  with v. assert (S.pts_to out v);
  let mut acc = S64.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 32sz)
  invariant exists* (vi: SZ.t) (a: S64.t).
    pts_to i vi ** pts_to acc a ** S.pts_to out v **
    pure (SZ.v vi <= 32 /\ S64.v a <= 255 * SZ.v vi /\
          ((S64.v a == 0) <==>
             (forall (kk: nat). kk < SZ.v vi ==> S8.v (Seq.index v kk) == 0)))
  decreases (32 - SZ.v (!i))
  {
    let vi = !i;
    let a = !acc;
    let byte = S.(out.(vi));
    let w = Cast.u8_to_u64 byte;
    assert_norm (255 * 32 + 255 < pow2 64);
    Math.small_mod (S64.v a + S64.v w) (pow2 64);
    acc := S64.add_mod a w;
    i := SZ.add vi 1sz;
  };
  let a = !acc;
  let m = S64.eq_mask a (S64.classify 0uL);
  let m8 = Cast.u64_to_u8 m;
  assert_norm ((pow2 64 - 1) % pow2 8 == pow2 8 - 1);
  let zero = Declassify.bool_of_mask m8;
  C.le_nat_zero_iff v;
  not zero
}

#pop-options

#pop-options
