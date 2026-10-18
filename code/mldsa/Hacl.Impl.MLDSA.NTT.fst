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

(** The number-theoretic transform for ML-DSA.

    The structure is {!Hacl.Impl.MLKEM.NTT}'s, with eight layers instead
    of seven (ML-DSA's ring splits completely, so the last layer has
    half-width one) and thirty-two-bit coefficients.  The pointwise
    product is just that, coefficient by coefficient.

    The specification's layers are {i pointwise}: [ntt_layer_at e f t] says
    what coefficient [t] of the output is as a function of the whole input,
    with no reference to the order the coefficients are produced in.  The
    implementation is the textbook in-place butterfly network anyway,
    because that is what is fast: each layer is an outer loop over blocks,
    reading the block's root (and its Shoup companion) once, and an inner
    loop of [len] butterflies, each of which reads its two coefficients
    before writing either.  [len] is a literal at every call site, so the
    inner loop has a constant trip count and C compilers vectorise it.

    The bridge between the two shapes is {!part}: after [c] butterflies of
    the block starting at [lo], the coefficients below [lo + c] and those in
    [[lo + len, lo + len + c)] hold the layer's output and every other one
    still holds its input.  {!layer_split} is what says that a block and an
    offset name the same butterfly as the specification's divisions. *)
module Hacl.Impl.MLDSA.NTT

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq
open Hacl.MLDSA.Tables

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module T = Hacl.Impl.Table
module HSZ = Hacl.SizeT
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** Carrying [(b, c)] with [t = b * 2len + c] is the same as dividing:
    [b] is the block [t] falls in, and [c < len] is exactly the test for
    being in the lower half of the butterfly. *)
let layer_split (e: nat { e <= 7 }) (b c: nat)
  : Lemma (requires c < pow2 (e + 1) /\ b * pow2 (e + 1) + c < n)
          (ensures (let t = b * pow2 (e + 1) + c in
                    b < pow2 (7 - e) /\
                    zidx e t == pow2 (7 - e) + b /\
                    zidx_inv e t == 2 * pow2 (7 - e) - 1 - b /\
                    (((t / pow2 e) % 2 == 0) <==> c < pow2 e)))
  = let p = pow2 e in
    let d = pow2 (e + 1) in
    let t = b * d + c in
    Math.pow2_plus 1 e;
    assert_norm (pow2 1 == 2);
    assert (d == 2 * p);
    Math.lemma_div_plus c b d;
    Math.small_div c d;
    assert (t / d == b);
    assert_norm (n == pow2 8);
    Math.pow2_plus (7 - e) (e + 1);
    KZ.div_lt t (pow2 (7 - e)) d;
    Math.pow2_plus 1 (7 - e);
    Math.lemma_div_plus c (2 * b) p;
    assert (t / p == c / p + 2 * b);
    Math.lemma_mod_plus (c / p) b 2;
    assert ((t / p) % 2 == (c / p) % 2);
    if c < p then Math.small_div c p
    else begin
      Math.lemma_div_le p c p;
      Math.lemma_div_lt_nat c (e + 1) e;
      Math.small_div (c / p) 2
    end

(** {2 One layer, in place}

    A layer is [2^(7-e)] blocks of [2 len] coefficients, [len = 2^e], and
    block [b] pairs [f[lo + c]] with [f[lo + len + c]] for [c < len] under
    the one root [zetas (2^(7-e) + b)].  The loops below walk exactly that:
    an outer loop over blocks that reads the root and its Shoup companion
    once, and an inner loop over [c] whose trip count [len] is a literal
    at every call site, so a C compiler sees a constant-length loop of
    independent thirty-two-bit butterflies and vectorises it.

    The invariant {!part} says which coefficients have been overwritten
    with the layer's output and that the rest still hold the input; the
    butterfly reads its two inputs before writing either, which is what
    makes doing it in place agree with the pointwise specification. *)

let in_done (lo len c k: nat) : bool
  = k < lo + c || (lo + len <= k && k < lo + len + c)

[@@"opaque_to_smt"]
let part (res: poly) (vs v: Seq.seq zqt) (lo len c: nat) : prop
  = Seq.length vs == n /\ Seq.length v == n /\
    (forall (k: nat). k < n ==>
       S32.v (Seq.index v k) ==
         (if in_done lo len c k then Seq.index res k else S32.v (Seq.index vs k)))

let part_start (res: poly) (vs: Seq.seq zqt) (len: nat)
  : Lemma (requires Seq.length vs == n) (ensures part res vs vs 0 len 0)
  = reveal_opaque (`%part) (part res vs vs 0 len 0)

let part_next (res: poly) (vs v: Seq.seq zqt) (lo len: nat)
  : Lemma (requires part res vs v lo len len)
          (ensures part res vs v (lo + 2 * len) len 0)
  = reveal_opaque (`%part) (part res vs v lo len len);
    reveal_opaque (`%part) (part res vs v (lo + 2 * len) len 0)

let part_done (res: poly) (vs v: Seq.seq zqt) (len: nat)
  : Lemma (requires part res vs v n len 0)
          (ensures Seq.length v == n /\ as_poly v == res)
  = reveal_opaque (`%part) (part res vs v n len 0);
    as_poly_intro v res

let part_len (res: poly) (vs v: Seq.seq zqt) (lo len c: nat)
  : Lemma (requires part res vs v lo len c)
          (ensures Seq.length vs == n /\ Seq.length v == n)
  = reveal_opaque (`%part) (part res vs v lo len c)

let part_read (res: poly) (vs v: Seq.seq zqt) (lo len c: nat)
  : Lemma (requires part res vs v lo len c /\ c < len /\ lo + 2 * len <= n)
          (ensures Seq.length vs == n /\ Seq.length v == n /\
                   S32.v (Seq.index v (lo + c)) == S32.v (Seq.index vs (lo + c)) /\
                   S32.v (Seq.index v (lo + len + c)) == S32.v (Seq.index vs (lo + len + c)))
  = reveal_opaque (`%part) (part res vs v lo len c)

let part_step (res: poly) (vs v: Seq.seq zqt) (lo len c: nat) (a d: zqt)
  : Lemma (requires part res vs v lo len c /\ c < len /\ lo + 2 * len <= n /\
                    S32.v a == Seq.index res (lo + c) /\
                    S32.v d == Seq.index res (lo + len + c))
          (ensures Seq.length v == n /\
                   part res vs (Seq.upd (Seq.upd v (lo + c) a) (lo + len + c) d) lo len (c + 1))
  = reveal_opaque (`%part) (part res vs v lo len c);
    let v1 = Seq.upd v (lo + c) a in
    let v' = Seq.upd v1 (lo + len + c) d in
    let aux (k: nat { k < n })
      : Lemma (S32.v (Seq.index v' k) ==
                 (if in_done lo len (c + 1) k then Seq.index res k else S32.v (Seq.index vs k)))
      = if k = lo + len + c then Seq.lemma_index_upd1 v1 (lo + len + c) d
        else begin
          Seq.lemma_index_upd2 v1 (lo + len + c) d k;
          if k = lo + c then Seq.lemma_index_upd1 v (lo + c) a
          else Seq.lemma_index_upd2 v (lo + c) a k
        end
    in
    FStar.Classical.forall_intro aux;
    reveal_opaque (`%part) (part res vs v' lo len (c + 1))

(** Blocks tile the polynomial: a block that starts inside it ends inside
    it, and there are [2^(7-e)] of them. *)
let block_fits (e: nat { e <= 7 }) (b: nat)
  : Lemma (requires b * pow2 (e + 1) < n)
          (ensures b * pow2 (e + 1) + pow2 (e + 1) <= n /\
                   b * pow2 (e + 1) + 2 * pow2 e <= n /\
                   zidx e (b * pow2 (e + 1)) == pow2 (7 - e) + b /\
                   zidx_inv e (b * pow2 (e + 1)) == 2 * pow2 (7 - e) - 1 - b)
  = let d = pow2 (e + 1) in
    let k = pow2 (7 - e) in
    n_pow2 ();
    Math.pow2_plus (7 - e) (e + 1);
    assert (n == k * d);
    if b >= k then Math.lemma_mult_le_right d k b;
    Math.lemma_mult_le_right d (b + 1) k;
    Math.distributivity_add_left b 1 d;
    Math.pow2_plus 1 e;
    assert_norm (pow2 1 == 2);
    layer_split e b 0

(** What the layer's output is at the two ends of one butterfly. *)
let ntt_pair (e: nat { e <= 7 }) (f: poly) (b c: nat)
  : Lemma (requires c < pow2 e /\ b * pow2 (e + 1) + 2 * pow2 e <= n)
          (ensures (let lo = b * pow2 (e + 1) in
                    let len = pow2 e in
                    lo + len + c < n /\
                    (let z = zetas (zidx e lo) in
                     Seq.index (ntt_layer e f) (lo + c) ==
                       add (Seq.index f (lo + c)) (mul z (Seq.index f (lo + len + c))) /\
                     Seq.index (ntt_layer e f) (lo + len + c) ==
                       sub (Seq.index f (lo + c)) (mul z (Seq.index f (lo + len + c))))))
  = let lo = b * pow2 (e + 1) in
    let len = pow2 e in
    Math.pow2_plus 1 e;
    assert_norm (pow2 1 == 2);
    layer_split e b 0;
    layer_split e b c;
    layer_split e b (c + len);
    ntt_layer_index e f (lo + c);
    ntt_layer_index e f (lo + len + c)

let intt_pair (e: nat { e <= 7 }) (f: poly) (b c: nat)
  : Lemma (requires c < pow2 e /\ b * pow2 (e + 1) + 2 * pow2 e <= n)
          (ensures (let lo = b * pow2 (e + 1) in
                    let len = pow2 e in
                    lo + len + c < n /\
                    (let z = zetas (zidx_inv e lo) in
                     Seq.index (intt_layer e f) (lo + c) ==
                       add (Seq.index f (lo + c)) (Seq.index f (lo + len + c)) /\
                     Seq.index (intt_layer e f) (lo + len + c) ==
                       mul z (sub (Seq.index f (lo + len + c)) (Seq.index f (lo + c))))))
  = let lo = b * pow2 (e + 1) in
    let len = pow2 e in
    Math.pow2_plus 1 e;
    assert_norm (pow2 1 == 2);
    layer_split e b 0;
    layer_split e b c;
    layer_split e b (c + len);
    intt_layer_index e f (lo + c);
    intt_layer_index e f (lo + len + c)

(** One block of Cooley-Tukey butterflies under the root [z]. *)
inline_for_extraction
fn ntt_block (f: A.array zqt) (lo len: SZ.t) (z: zqt) (zs: S32.t)
             (#e: erased nat) (#b: erased nat) (#vs #vf: erased (Seq.seq zqt))
requires A.pts_to f vf **
         pure (reveal e <= 7 /\ SZ.v len == pow2 (reveal e) /\
               Seq.length vs == n /\
               SZ.v lo == reveal b * pow2 (reveal e + 1) /\ SZ.v lo + 2 * SZ.v len <= n /\
               S32.v z == zetas (zidx (reveal e) (SZ.v lo)) /\
               S32.v zs == shoup_of (S32.v z) /\
               part (ntt_layer (reveal e) (as_poly vs)) vs vf (SZ.v lo) (SZ.v len) 0)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\
              part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v len))
{
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc len)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to f v **
    pure (reveal e <= 7 /\ Seq.length vs == n /\ SZ.v vc <= SZ.v len /\
          part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc))
  decreases (SZ.v len - SZ.v (!c))
  {
    let vc = !c;
    with v. assert (A.pts_to f v);
    part_read (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc);
    ntt_pair (reveal e) (as_poly vs) (reveal b) (SZ.v vc);
    SZ.fits_u32_implies_fits (SZ.v lo + SZ.v len + SZ.v vc);
    let i = SZ.add lo vc;
    let j = SZ.add i len;
    let x = A.(f.(i));
    let y = A.(f.(j));
    let t = zq_mul_shoup z zs y;
    let a = zq_add x t;
    let d = zq_sub x t;
    A.(f.(i) <- a);
    A.(f.(j) <- d);
    part_step (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc) a d;
    c := SZ.add vc 1sz;
  };
}

(** One block of Gentleman-Sande butterflies: the root multiplies after
    the subtraction rather than before it, which is what makes the two
    layers mutually inverse rather than merely similar. *)
inline_for_extraction
fn intt_block (f: A.array zqt) (lo len: SZ.t) (z: zqt) (zs: S32.t)
              (#e: erased nat) (#b: erased nat) (#vs #vf: erased (Seq.seq zqt))
requires A.pts_to f vf **
         pure (reveal e <= 7 /\ SZ.v len == pow2 (reveal e) /\
               Seq.length vs == n /\
               SZ.v lo == reveal b * pow2 (reveal e + 1) /\ SZ.v lo + 2 * SZ.v len <= n /\
               S32.v z == zetas (zidx_inv (reveal e) (SZ.v lo)) /\
               S32.v zs == shoup_of (S32.v z) /\
               part (intt_layer (reveal e) (as_poly vs)) vs vf (SZ.v lo) (SZ.v len) 0)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\
              part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v len))
{
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc len)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to f v **
    pure (reveal e <= 7 /\ Seq.length vs == n /\ SZ.v vc <= SZ.v len /\
          part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc))
  decreases (SZ.v len - SZ.v (!c))
  {
    let vc = !c;
    with v. assert (A.pts_to f v);
    part_read (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc);
    intt_pair (reveal e) (as_poly vs) (reveal b) (SZ.v vc);
    SZ.fits_u32_implies_fits (SZ.v lo + SZ.v len + SZ.v vc);
    let i = SZ.add lo vc;
    let j = SZ.add i len;
    let x = A.(f.(i));
    let y = A.(f.(j));
    let a = zq_add x y;
    let d = zq_mul_shoup z zs (zq_sub y x);
    A.(f.(i) <- a);
    A.(f.(j) <- d);
    part_step (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc) a d;
    c := SZ.add vc 1sz;
  };
}

(** [f <- ntt_layer e f].  [len] is [2^e] and [half] is [2^(7-e)], the
    number of roots the earlier layers have consumed; both are literals at
    every call site. *)
inline_for_extraction
fn ntt_layer_impl (f: A.array zqt) (len half: SZ.t)
                  (#e: erased nat) (#vs: erased (Seq.seq zqt))
requires A.pts_to f vs **
         pure (reveal e <= 7 /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == ntt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 256sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 256sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  Math.pow2_plus 1 (reveal e);
  assert_norm (pow2 1 == 2);
  Math.pow2_le_compat 8 (reveal e + 1);
  assert_norm (pow2 8 == 256);
  let dbl = SZ.add len len;
  part_start (ntt_layer (reveal e) (as_poly vs)) vs (SZ.v len);
  let mut lo = 0sz;
  let mut b = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vb: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to b vb ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (reveal e <= 7 /\ Seq.length vs == n /\
          SZ.v vlo <= n /\ SZ.v vlo == SZ.v vb * pow2 (reveal e + 1) /\
          part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len) 0)
  decreases (n - SZ.v (!lo))
  {
    let vlo = !lo;
    let vb = !b;
    block_fits (reveal e) (SZ.v vb);
    SZ.fits_u32_implies_fits (SZ.v half + SZ.v vb);
    let zi = SZ.add half vb;
    let z = A.(zt.(zi));
    let zs = A.(zst.(zi));
    ntt_block f vlo len z zs #e #(SZ.v vb) #vs;
    with v. assert (A.pts_to f v);
    part_next (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len);
    Math.distributivity_add_left (SZ.v vb) 1 (pow2 (reveal e + 1));
    lo := SZ.add vlo dbl;
    b := SZ.add vb 1sz;
  };
  with v. assert (A.pts_to f v);
  part_done (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v len);
  T.drop_table zst;
  T.drop_table zt;
}

(** [f <- intt_layer e f]: the roots are read from the far end of the
    table. *)
inline_for_extraction
fn intt_layer_impl (f: A.array zqt) (len half: SZ.t)
                   (#e: erased nat) (#vs: erased (Seq.seq zqt))
requires A.pts_to f vs **
         pure (reveal e <= 7 /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == intt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 256sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 256sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  Math.pow2_plus 1 (reveal e);
  assert_norm (pow2 1 == 2);
  Math.pow2_le_compat 8 (reveal e + 1);
  assert_norm (pow2 8 == 256);
  Math.pow2_le_compat 7 (7 - reveal e);
  assert_norm (pow2 7 == 128);
  let dbl = SZ.add len len;
  let top = SZ.sub (SZ.add half half) 1sz;
  part_start (intt_layer (reveal e) (as_poly vs)) vs (SZ.v len);
  let mut lo = 0sz;
  let mut b = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vb: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to b vb ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (reveal e <= 7 /\ Seq.length vs == n /\
          SZ.v vlo <= n /\ SZ.v vlo == SZ.v vb * pow2 (reveal e + 1) /\
          part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len) 0)
  decreases (n - SZ.v (!lo))
  {
    let vlo = !lo;
    let vb = !b;
    block_fits (reveal e) (SZ.v vb);
    let zi = SZ.sub top vb;
    let z = A.(zt.(zi));
    let zs = A.(zst.(zi));
    intt_block f vlo len z zs #e #(SZ.v vb) #vs;
    with v. assert (A.pts_to f v);
    part_next (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len);
    Math.distributivity_add_left (SZ.v vb) 1 (pow2 (reveal e + 1));
    lo := SZ.add vlo dbl;
    b := SZ.add vb 1sz;
  };
  with v. assert (A.pts_to f v);
  part_done (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v len);
  T.drop_table zst;
  T.drop_table zt;
}

(** {2 The transforms} *)

let ntt_compose (a0 a1 a2 a3 a4 a5 a6 a7 a8: poly)
  : Lemma (requires a1 == ntt_layer 7 a0 /\ a2 == ntt_layer 6 a1 /\ a3 == ntt_layer 5 a2 /\
                    a4 == ntt_layer 4 a3 /\ a5 == ntt_layer 3 a4 /\ a6 == ntt_layer 2 a5 /\
                    a7 == ntt_layer 1 a6 /\ a8 == ntt_layer 0 a7)
          (ensures a8 == ntt a0)
  = ntt_unfold a0

(** [f <- NTT(f)], in place. *)
fn ntt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
requires A.pts_to f vf ** pure (Seq.length vf == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == ntt (as_poly vf))
{
  A.pts_to_len f;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  ntt_layer_impl f 128sz 1sz #7;
  with v1. assert (A.pts_to f v1);
  ntt_layer_impl f 64sz 2sz #6;
  with v2. assert (A.pts_to f v2);
  ntt_layer_impl f 32sz 4sz #5;
  with v3. assert (A.pts_to f v3);
  ntt_layer_impl f 16sz 8sz #4;
  with v4. assert (A.pts_to f v4);
  ntt_layer_impl f 8sz 16sz #3;
  with v5. assert (A.pts_to f v5);
  ntt_layer_impl f 4sz 32sz #2;
  with v6. assert (A.pts_to f v6);
  ntt_layer_impl f 2sz 64sz #1;
  with v7. assert (A.pts_to f v7);
  ntt_layer_impl f 1sz 128sz #0;
  with v8. assert (A.pts_to f v8);
  ntt_compose (as_poly vf) (as_poly v1) (as_poly v2) (as_poly v3) (as_poly v4)
    (as_poly v5) (as_poly v6) (as_poly v7) (as_poly v8);
  ()
}

[@@"opaque_to_smt"]
let scale_val (x: zqt) : GTot zq = mul inv_256 (S32.v x)

let scale_step (w v: Seq.seq zqt) (i: nat) (x: zqt)
  : Lemma (requires Seq.length w == n /\ Seq.length v == n /\ i < n /\
                    (forall (k: nat). k < i ==> S32.v (Seq.index v k) == scale_val (Seq.index w k)) /\
                    (forall (k: nat). i <= k /\ k < n ==> Seq.index v k == Seq.index w k) /\
                    S32.v x == mul inv_256 (S32.v (Seq.index w i)))
          (ensures (let v = Seq.upd v i x in
                    Seq.length v == n /\
                    (forall (k: nat). k < i + 1 ==> S32.v (Seq.index v k) == scale_val (Seq.index w k)) /\
                    (forall (k: nat). i + 1 <= k /\ k < n ==> Seq.index v k == Seq.index w k)))
  = reveal_opaque (`%scale_val) scale_val

let intt_compose (a0 a1 a2 a3 a4 a5 a6 a7 a8: poly)
  : Lemma (requires a1 == intt_layer 0 a0 /\ a2 == intt_layer 1 a1 /\ a3 == intt_layer 2 a2 /\
                    a4 == intt_layer 3 a3 /\ a5 == intt_layer 4 a4 /\ a6 == intt_layer 5 a5 /\
                    a7 == intt_layer 6 a6 /\ a8 == intt_layer 7 a7)
          (ensures intt a0 == poly_scale inv_256 a8)
  = intt_unfold a0

let scale_done (w v: Seq.seq zqt) (i: nat)
  : Lemma (requires Seq.length w == n /\ Seq.length v == n /\ i == n /\
                    (forall (k: nat). k < i ==> S32.v (Seq.index v k) == scale_val (Seq.index w k)))
          (ensures as_poly v == poly_scale inv_256 (as_poly w))
  = reveal_opaque (`%scale_val) scale_val;
    as_poly_intro v (poly_scale inv_256 (as_poly w))

let loop_exit (vi: SZ.t)
  : Lemma (requires false == SZ.lt vi 256sz /\ SZ.v vi <= n) (ensures SZ.v vi == n)
  = ()

fn scale_inplace (f: A.array zqt) (#w: erased (Seq.seq zqt))
requires A.pts_to f w ** pure (Seq.length w == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length w == n /\ Seq.length v == n /\
              as_poly v == poly_scale inv_256 (as_poly w))
{
  A.pts_to_len f;
  let ci : zqt = S32.classify 8347681ul;
  let cs : S32.t = S32.classify 4278190082ul;
  assert_norm (shoup_of 8347681 == 4278190082);
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to f v **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length w == n /\
          (forall (k: nat). k < SZ.v vi ==> S32.v (Seq.index v k) == scale_val (Seq.index w k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < n ==> Seq.index v k == Seq.index w k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to f v);
    let x = A.(f.(vi));
    let y = zq_mul_shoup ci cs x;
    scale_step w v (SZ.v vi) y;
    A.(f.(vi) <- y);
    i := SZ.add vi 1sz;
  };
  with (vi: SZ.t) (v: Seq.seq zqt). assert (pts_to i vi ** A.pts_to f v);
  loop_exit vi;
  scale_done w v (SZ.v vi);
  ()
}

(** [f <- NTT^-1(f)]: the layers the other way, then the scaling by
    [256^-1], one Shoup multiplication per coefficient. *)
fn intt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
requires A.pts_to f vf ** pure (Seq.length vf == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == intt (as_poly vf))
{
  A.pts_to_len f;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  intt_layer_impl f 1sz 128sz #0;
  with u1. assert (A.pts_to f u1);
  intt_layer_impl f 2sz 64sz #1;
  with u2. assert (A.pts_to f u2);
  intt_layer_impl f 4sz 32sz #2;
  with u3. assert (A.pts_to f u3);
  intt_layer_impl f 8sz 16sz #3;
  with u4. assert (A.pts_to f u4);
  intt_layer_impl f 16sz 8sz #4;
  with u5. assert (A.pts_to f u5);
  intt_layer_impl f 32sz 4sz #5;
  with u6. assert (A.pts_to f u6);
  intt_layer_impl f 64sz 2sz #6;
  with u7. assert (A.pts_to f u7);
  intt_layer_impl f 128sz 1sz #7;
  with w. assert (A.pts_to f w);
  intt_compose (as_poly vf) (as_poly u1) (as_poly u2) (as_poly u3) (as_poly u4)
    (as_poly u5) (as_poly u6) (as_poly u7) (as_poly w);
  scale_inplace f;
}

(** {2 The pointwise product} *)

[@@"opaque_to_smt"]
let prod_val (x y: zqt) : GTot zq = mul (S32.v x) (S32.v y)

let prod_step (va vb v: Seq.seq zqt) (i: nat) (r: zqt)
  : Lemma (requires Seq.length va == n /\ Seq.length vb == n /\ Seq.length v == n /\ i < n /\
                    (forall (k: nat). k < i ==>
                       S32.v (Seq.index v k) == prod_val (Seq.index va k) (Seq.index vb k)) /\
                    S32.v r == mul (S32.v (Seq.index va i)) (S32.v (Seq.index vb i)))
          (ensures (let v = Seq.upd v i r in
                    Seq.length v == n /\
                    (forall (k: nat). k < i + 1 ==>
                       S32.v (Seq.index v k) == prod_val (Seq.index va k) (Seq.index vb k))))
  = reveal_opaque (`%prod_val) prod_val

let prod_done (va vb v: Seq.seq zqt) (i: nat)
  : Lemma (requires Seq.length va == n /\ Seq.length vb == n /\ Seq.length v == n /\ i == n /\
                    (forall (k: nat). k < i ==>
                       S32.v (Seq.index v k) == prod_val (Seq.index va k) (Seq.index vb k)))
          (ensures as_poly v == poly_mul (as_poly va) (as_poly vb))
  = reveal_opaque (`%prod_val) prod_val;
    as_poly_intro v (poly_mul (as_poly va) (as_poly vb))

(** [dst <- a * b], coefficient by coefficient: the product in the NTT
    domain. *)
fn multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == poly_mul (as_poly va) (as_poly vb))
{
  A.pts_to_len dst;
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= n /\ Seq.length v == n /\
          Seq.length va == n /\ Seq.length vb == n /\
          (forall (k: nat). k < SZ.v vi ==>
             S32.v (Seq.index v k) == prod_val (Seq.index va k) (Seq.index vb k)))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to dst v);
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let r = zq_mul x y;
    prod_step va vb v (SZ.v vi) r;
    A.(dst.(vi) <- r);
    i := SZ.add vi 1sz;
  };
  with (vi: SZ.t) (v: Seq.seq zqt). assert (pts_to i vi ** A.pts_to dst v);
  loop_exit vi;
  prod_done va vb v (SZ.v vi);
  ()
}

#pop-options
