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

(** The inner product of two vectors in the NTT domain, the kernel of the
    matrix-vector products.

    Adding [k] base-case products reduces every coefficient [2k] times;
    here the [k] products of a pair of coefficients are summed exactly
    instead, and the sum reduced once.  The loop runs over the 128 pairs
    with the [k] entries innermost, which is also the order that
    vectorises.  The proof that this is {!Spec.MLKEM.NTT.dot} is in
    {!Hacl.Impl.MLKEM.VecLemmas}: {!psum} names the exact sums and
    {!dot_pair} relates them to the specification's fold.

    A module of its own, behind an interface, because it needs the
    [gamma] table, and with {!Hacl.MLKEM.Tables} in scope unrelated proofs
    in the callers time out; see {!Hacl.Impl.MLKEM.Poly} for the same
    arrangement around the transform. *)
module Hacl.Impl.MLKEM.Dot

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.VecLemmas
open Hacl.MLKEM.Tables

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S16 = Hacl.Secret.UInt16
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT
module Cast = Hacl.Secret.Cast
module T = Hacl.Impl.Table
module V = Hacl.Vec256

(* The tables module carries the facts that check its literal lists, and
   they swamp the solver; all that is needed of it here is what a [gamma]
   entry is. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --using_facts_from '* -Hacl.MLKEM.Tables +Hacl.MLKEM.Tables.gamma_table_index +Hacl.MLKEM.Tables.gamma_table +Hacl.MLKEM.Tables.gamma_arr'"

(** A product of two coefficients, in thirty-two bits. *)
inline_for_extraction
let wmul32 (a b: zqt) : r: S32.t { S32.v r == S16.v a * S16.v b }
  = prod_bound (S16.v a) (S16.v b);
    assert_norm ((q - 1) * (q - 1) < pow2 32);
    Math.nat_times_nat_is_nat (S16.v a) (S16.v b);
    Math.small_mod (S16.v a * S16.v b) (pow2 32);
    S32.mul_mod (Cast.u16_to_u32 a) (Cast.u16_to_u32 b)

(** Pair [i] of [dst <- sum of u_j * v_j].  The [k] base-case products of
    the pair are sums of products of coefficients, so their sum is one
    longer such sum: it is accumulated exactly, in thirty-two bits (at most
    [8 (q - 1)^2] for [k <= 4]), and reduced once, where adding [k] reduced
    products would reduce [2k] times.  Only the [a1 b1] sum is reduced
    before it meets [gamma_i], to keep that product in range too. *)
inline_for_extraction
fn dot_pair_impl (dst u v gt: A.array zqt) (k: SZ.t) (i: SZ.t)
                 (#pu #pv #pz: perm) (#vd #vu #vv: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
         A.pts_to gt #pz gamma_table **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v i < 128 /\ Seq.length vd == n /\
               Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
               dot_prefix (SZ.v k) vd vu vv (2 * SZ.v i))
ensures exists* w. A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
        A.pts_to gt #pz gamma_table **
        pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v i < 128 /\ Seq.length w == n /\
              Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
              dot_prefix (SZ.v k) w vu vv (2 * SZ.v i + 2))
{
  A.pts_to_len dst;
  A.pts_to_len u;
  A.pts_to_len v;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  assert_norm (8 * ((q - 1) * (q - 1)) < pow2 32);
  SZ.fits_u32_implies_fits (SZ.v i + SZ.v i);
  let j2 = SZ.add i i;
  let ii = SZ.v i;
  psum_zero vu vv (2 * ii) (2 * ii);
  psum_zero vu vv (2 * ii + 1) (2 * ii + 1);
  psum_zero vu vv (2 * ii) (2 * ii + 1);
  psum_zero vu vv (2 * ii + 1) (2 * ii);
  let mut s00 = S32.zero;
  let mut s11 = S32.zero;
  let mut s01 = S32.zero;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj k)
  invariant exists* (vj: SZ.t) (x00 x11 x01: S32.t).
    pts_to j vj ** pts_to s00 x00 ** pts_to s11 x11 ** pts_to s01 x01 **
    A.pts_to u #pu vu ** A.pts_to v #pv vv **
    pure (SZ.v vj <= SZ.v k /\
          S32.v x00 == psum vu vv (2 * ii) (2 * ii) (SZ.v vj) /\
          S32.v x11 == psum vu vv (2 * ii + 1) (2 * ii + 1) (SZ.v vj) /\
          S32.v x01 == psum vu vv (2 * ii) (2 * ii + 1) (SZ.v vj) +
                       psum vu vv (2 * ii + 1) (2 * ii) (SZ.v vj))
  decreases (SZ.v k - SZ.v (!j))
  {
    let vj = !j;
    let jj = SZ.v vj;
    psum_step (SZ.v k) vu vv ii jj;
    psum_small vu vv (2 * ii) (2 * ii) (jj + 1);
    psum_small vu vv (2 * ii + 1) (2 * ii + 1) (jj + 1);
    psum_small vu vv (2 * ii) (2 * ii + 1) (jj + 1);
    psum_small vu vv (2 * ii + 1) (2 * ii) (jj + 1);
    Math.lemma_mult_le_right n (jj + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (jj * n);
    SZ.fits_u32_implies_fits (jj * n + 2 * ii + 1);
    let o0 = SZ.add (SZ.mul vj 256sz) j2;
    let o1 = SZ.add o0 1sz;
    let a0 = A.(u.(o0));
    let a1 = A.(u.(o1));
    let b0 = A.(v.(o0));
    let b1 = A.(v.(o1));
    let x00 = !s00;
    let x11 = !s11;
    let x01 = !s01;
    let p00 = wmul32 a0 b0;
    let p11 = wmul32 a1 b1;
    let p01 = wmul32 a0 b1;
    let p10 = wmul32 a1 b0;
    Math.small_mod (S32.v x00 + S32.v p00) (pow2 32);
    Math.small_mod (S32.v x11 + S32.v p11) (pow2 32);
    Math.small_mod (S32.v p01 + S32.v p10) (pow2 32);
    Math.small_mod (S32.v x01 + (S32.v p01 + S32.v p10)) (pow2 32);
    s00 := S32.add_mod x00 p00;
    s11 := S32.add_mod x11 p11;
    s01 := S32.add_mod x01 (S32.add_mod p01 p10);
    SZ.fits_u32_implies_fits (jj + 1);
    j := SZ.add vj 1sz;
  };
  let x00 = !s00;
  let x11 = !s11;
  let x01 = !s01;
  psum_small vu vv (2 * ii) (2 * ii) (SZ.v k);
  let g = A.(gt.(i));
  let r11 = zq_reduce32 x11;
  prod_bound (S16.v r11) (S16.v g);
  Math.nat_times_nat_is_nat (S16.v r11) (S16.v g);
  Math.small_mod (S16.v r11 * S16.v g) (pow2 32);
  let rg = S32.mul_mod (Cast.u16_to_u32 r11) (Cast.u16_to_u32 g);
  Math.small_mod (S32.v x00 + S32.v rg) (pow2 32);
  let c0 = zq_reduce32 (S32.add_mod x00 rg);
  let c1 = zq_reduce32 x01;
  dot_pair_out (SZ.v k) vu vv ii (S32.v x00) (S32.v x11) (S32.v x01) (S16.v g) c0 c1;
  dot_prefix_upd (SZ.v k) vd vu vv ii c0 c1;
  SZ.fits_u32_implies_fits (2 * ii + 1);
  A.((dst.(j2) <- c0));
  A.((dst.(SZ.add j2 1sz) <- c1));
}

inline_for_extraction
fn dot_ (dst u v: A.array zqt) (k: SZ.t)
        (#pu #pv: perm) (#vd #vu #vv: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vd == n /\
               Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n)
ensures exists* w. A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == n /\
        Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
        as_poly w == dot #(SZ.v k) (as_zqs vu) (as_zqs vv))
{
  A.pts_to_len dst;
  let gt = T.table gamma_arr 128sz;
  with pz. assert (A.pts_to gt #pz gamma_table);
  dot_prefix_zero (SZ.v k) vd vu vv;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 128sz)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
    A.pts_to gt #pz gamma_table **
    pure (SZ.v vi <= 128 /\ Seq.length w == n /\
          dot_prefix (SZ.v k) w vu vv (2 * SZ.v vi))
  decreases (128 - SZ.v (!i))
  {
    let vi = !i;
    dot_pair_impl dst u v gt k vi;
    HSZ.fits32 ();
    assert_norm (128 < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let vi' = SZ.add vi 1sz;
    assert (pure (2 * SZ.v vi' == 2 * SZ.v vi + 2));
    i := vi';
  };
  T.drop_table gt;
  with vi w. assert (pts_to i vi ** A.pts_to dst w);
  assert (pure (SZ.v vi == 128 /\ 2 * SZ.v vi == n));
  dot_prefix_full (SZ.v k) w vu vv;
  assert (pure (as_poly w == dot #(SZ.v k) (as_zqs vu) (as_zqs vv)));
}

[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn dot_avx2 (dst u v: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
            (#pu #pv: perm) (#vd #vu #vv: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vd == n /\
               Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n)
ensures exists* w. A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == n /\
        Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
        as_poly w == dot #(SZ.v k) (as_zqs vu) (as_zqs vv))
{
  dot_ dst u v k
}

fn dot (dst u v: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
        (#pu #pv: perm) (#vd #vu #vv: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vd == n /\
               Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n)
ensures exists* w. A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == n /\
        Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
        as_poly w == dot #(SZ.v k) (as_zqs vu) (as_zqs vv))
{
  if (V.supported ()) { dot_avx2 dst u v k } else { dot_ dst u v k }
}

#pop-options
