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

(** The number-theoretic transform.

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
module Hacl.Impl.MLKEM.NTT

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq
open Hacl.MLKEM.Tables

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S16 = Hacl.Secret.UInt16
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module T = Hacl.Impl.Table
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** Carrying [(b, c)] with [t = b * 2len + c] is the same as dividing:
    [b] is the block [t] falls in, and [c < len] is exactly the test for
    being in the lower half of the butterfly. *)
let layer_split (e: nat { 1 <= e /\ e <= 7 }) (b c: nat)
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
    div_lt t (pow2 (7 - e)) d;
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
    independent sixteen-bit butterflies and vectorises it.

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
       S16.v (Seq.index v k) ==
         (if in_done lo len c k then Seq.index res k else S16.v (Seq.index vs k)))

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
                   S16.v (Seq.index v (lo + c)) == S16.v (Seq.index vs (lo + c)) /\
                   S16.v (Seq.index v (lo + len + c)) == S16.v (Seq.index vs (lo + len + c)))
  = reveal_opaque (`%part) (part res vs v lo len c)

let part_step (res: poly) (vs v: Seq.seq zqt) (lo len c: nat) (a d: zqt)
  : Lemma (requires part res vs v lo len c /\ c < len /\ lo + 2 * len <= n /\
                    S16.v a == Seq.index res (lo + c) /\
                    S16.v d == Seq.index res (lo + len + c))
          (ensures Seq.length v == n /\
                   part res vs (Seq.upd (Seq.upd v (lo + c) a) (lo + len + c) d) lo len (c + 1))
  = reveal_opaque (`%part) (part res vs v lo len c);
    let v' = Seq.upd (Seq.upd v (lo + c) a) (lo + len + c) d in
    reveal_opaque (`%part) (part res vs v' lo len (c + 1))

(** Blocks tile the polynomial: a block that starts inside it ends inside
    it, and there are [2^(7-e)] of them. *)
let block_fits (e: nat { 1 <= e /\ e <= 7 }) (b: nat)
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
let ntt_pair (e: nat { 1 <= e /\ e <= 7 }) (f: poly) (b c: nat)
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

let intt_pair (e: nat { 1 <= e /\ e <= 7 }) (f: poly) (b c: nat)
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
fn ntt_block (f: A.array zqt) (lo len: SZ.t) (z: zqt) (zs: S16.t)
             (#e: erased nat) (#b: erased nat) (#vs #vf: erased (Seq.seq zqt))
requires A.pts_to f vf **
         pure (1 <= reveal e /\ reveal e <= 7 /\ SZ.v len == pow2 (reveal e) /\
               Seq.length vs == n /\
               SZ.v lo == reveal b * pow2 (reveal e + 1) /\ SZ.v lo + 2 * SZ.v len <= n /\
               S16.v z == zetas (zidx (reveal e) (SZ.v lo)) /\
               S16.v zs == (S16.v z * pow2 16) / q /\
               part (ntt_layer (reveal e) (as_poly vs)) vs vf (SZ.v lo) (SZ.v len) 0)
ensures exists* v. A.pts_to f v **
        pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\
              part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v len))
{
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc len)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to f v **
    pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\ SZ.v vc <= SZ.v len /\
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
fn intt_block (f: A.array zqt) (lo len: SZ.t) (z: zqt) (zs: S16.t)
              (#e: erased nat) (#b: erased nat) (#vs #vf: erased (Seq.seq zqt))
requires A.pts_to f vf **
         pure (1 <= reveal e /\ reveal e <= 7 /\ SZ.v len == pow2 (reveal e) /\
               Seq.length vs == n /\
               SZ.v lo == reveal b * pow2 (reveal e + 1) /\ SZ.v lo + 2 * SZ.v len <= n /\
               S16.v z == zetas (zidx_inv (reveal e) (SZ.v lo)) /\
               S16.v zs == (S16.v z * pow2 16) / q /\
               part (intt_layer (reveal e) (as_poly vs)) vs vf (SZ.v lo) (SZ.v len) 0)
ensures exists* v. A.pts_to f v **
        pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\
              part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v len))
{
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc len)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to f v **
    pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\ SZ.v vc <= SZ.v len /\
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
         pure (1 <= reveal e /\ reveal e <= 7 /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == ntt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 128sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 128sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  Math.pow2_plus 1 (reveal e);
  assert_norm (pow2 1 == 2);
  Math.pow2_le_compat 8 (reveal e + 1);
  assert_norm (pow2 8 == 256);
  let dbl = SZ.add len len;
  Math.pow2_double_sum (reveal e);
  assert (pure (SZ.v dbl == pow2 (reveal e + 1)));
  part_start (ntt_layer (reveal e) (as_poly vs)) vs (SZ.v len);
  let mut lo = 0sz;
  let mut b = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vb: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to b vb ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\
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
         pure (1 <= reveal e /\ reveal e <= 7 /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == intt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 128sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 128sz;
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
  Math.pow2_double_sum (reveal e);
  assert (pure (SZ.v dbl == pow2 (reveal e + 1)));
  let top = SZ.sub (SZ.add half half) 1sz;
  part_start (intt_layer (reveal e) (as_poly vs)) vs (SZ.v len);
  let mut lo = 0sz;
  let mut b = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vb: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to b vb ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\
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

(** [f <- NTT(f)], in place.  The scratch buffer is no longer used; it
    stays in the signature so the callers do not change. *)
fn ntt_inplace (f tmp: A.array zqt) (#vf #vt: erased (Seq.seq zqt))
requires A.pts_to f vf ** A.pts_to tmp vt **
         pure (Seq.length vf == n /\ Seq.length vt == n)
ensures exists* v w. A.pts_to f v ** A.pts_to tmp w **
        pure (Seq.length vf == n /\ Seq.length v == n /\ Seq.length w == n /\
              as_poly v == ntt (as_poly vf))
{
  A.pts_to_len f;
  A.pts_to_len tmp;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  ntt_layer_impl f 128sz 1sz #7;
  with v7. assert (A.pts_to f v7);
  ntt_layer_impl f 64sz 2sz #6;
  with v6. assert (A.pts_to f v6);
  ntt_layer_impl f 32sz 4sz #5;
  with v5. assert (A.pts_to f v5);
  ntt_layer_impl f 16sz 8sz #4;
  with v4. assert (A.pts_to f v4);
  ntt_layer_impl f 8sz 16sz #3;
  with v3. assert (A.pts_to f v3);
  ntt_layer_impl f 4sz 32sz #2;
  with v2. assert (A.pts_to f v2);
  ntt_layer_impl f 2sz 64sz #1;
  with v1. assert (A.pts_to f v1);
  ntt_unfold (as_poly vf);
  assert (pure (as_poly v1 == ntt_layer 1 (ntt_layer 2 (ntt_layer 3 (ntt_layer 4
             (ntt_layer 5 (ntt_layer 6 (ntt_layer 7 (as_poly vf)))))))));
}

let scale_step (w v: Seq.seq zqt) (i: nat) (x: zqt)
  : Lemma (requires Seq.length w == n /\ Seq.length v == n /\ i < n /\
                    (forall (k: nat). k < n ==>
                       S16.v (Seq.index v k) ==
                         (if k < i then mul inv_128 (S16.v (Seq.index w k))
                          else S16.v (Seq.index w k))) /\
                    S16.v x == mul inv_128 (S16.v (Seq.index w i)))
          (ensures (let v' = Seq.upd v i x in
                    Seq.length v' == n /\
                    (forall (k: nat). k < n ==>
                       S16.v (Seq.index v' k) ==
                         (if k < i + 1 then mul inv_128 (S16.v (Seq.index w k))
                          else S16.v (Seq.index w k)))))
  = ()

(** [f <- NTT^-1(f)].  The layers run the other way and the whole thing is
    scaled by [128^-1] at the end. *)
fn intt_inplace (f tmp: A.array zqt) (#vf #vt: erased (Seq.seq zqt))
requires A.pts_to f vf ** A.pts_to tmp vt **
         pure (Seq.length vf == n /\ Seq.length vt == n)
ensures exists* v w. A.pts_to f v ** A.pts_to tmp w **
        pure (Seq.length vf == n /\ Seq.length v == n /\ Seq.length w == n /\
              as_poly v == intt (as_poly vf))
{
  A.pts_to_len f;
  A.pts_to_len tmp;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  intt_layer_impl f 2sz 64sz #1;
  with v1. assert (A.pts_to f v1);
  intt_layer_impl f 4sz 32sz #2;
  with v2. assert (A.pts_to f v2);
  intt_layer_impl f 8sz 16sz #3;
  with v3. assert (A.pts_to f v3);
  intt_layer_impl f 16sz 8sz #4;
  with v4. assert (A.pts_to f v4);
  intt_layer_impl f 32sz 4sz #5;
  with v5. assert (A.pts_to f v5);
  intt_layer_impl f 64sz 2sz #6;
  with v6. assert (A.pts_to f v6);
  intt_layer_impl f 128sz 1sz #7;
  with w. assert (A.pts_to f w);
  intt_unfold (as_poly vf);
  assert (pure (as_poly w == intt_layer 7 (intt_layer 6 (intt_layer 5 (intt_layer 4
               (intt_layer 3 (intt_layer 2 (intt_layer 1 (as_poly vf)))))))));
  let ci : zqt = S16.classify 3303us;
  let cs : S16.t = S16.classify 65024us;
  assert_norm ((3303 * pow2 16) / q == 65024);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to f v **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length w == n /\
          (forall (k: nat). k < n ==>
             S16.v (Seq.index v k) ==
               (if k < SZ.v vi then mul inv_128 (S16.v (Seq.index w k))
                else S16.v (Seq.index w k))))
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
  with v. assert (A.pts_to f v);
  as_poly_intro v (poly_scale inv_128 (as_poly w));
  assert (pure (as_poly v == poly_scale inv_128 (as_poly w)));
}

(** {2 The pointwise product}
    [dst <- MultiplyNTTs(a, b)].  Algorithm 11 is 128 independent products
    of linear polynomials modulo [X^2 - gamma_i]; the loop runs over the
    128 pairs and writes two coefficients at a time, and [gamma_i] comes
    out of the one zeta table by {!gammas_zetas}. *)
(* Extending a pointwise property by the two indices just written.  Stated as
   a top-level lemma: the case analysis is trivial here, but ruinous when it
   has to happen inside the Pulse proof state. *)
let extend_by_two (v: Seq.seq zqt) (res: poly) (i: nat { 2 * i + 2 <= n })
  : Lemma (requires Seq.length v == n /\
                    (forall (k: nat). k < 2 * i ==>
                       S16.v (Seq.index v k) == Seq.index res k) /\
                    S16.v (Seq.index v (2 * i)) == Seq.index res (2 * i) /\
                    S16.v (Seq.index v (2 * i + 1)) == Seq.index res (2 * i + 1))
          (ensures forall (k: nat). k < 2 * i + 2 ==>
                     S16.v (Seq.index v k) == Seq.index res k)
  = ()

(* The two coefficients of the [i]th base-case product, at concrete indices. *)
let multiply_ntts_pair (f g: poly) (i: nat { i < 128 })
  : Lemma (Seq.index (multiply_ntts f g) (2 * i) ==
             add (mul (Seq.index f (2 * i)) (Seq.index g (2 * i)))
                 (mul (mul (Seq.index f (2 * i + 1)) (Seq.index g (2 * i + 1)))
                      (gammas i)) /\
           Seq.index (multiply_ntts f g) (2 * i + 1) ==
             add (mul (Seq.index f (2 * i)) (Seq.index g (2 * i + 1)))
                 (mul (Seq.index f (2 * i + 1)) (Seq.index g (2 * i))))
  = multiply_ntts_index f g (2 * i);
    multiply_ntts_index f g (2 * i + 1);
    Math.cancel_mul_div i 2;
    Math.lemma_div_plus 1 i 2;
    Math.lemma_mod_plus 1 i 2;
    Math.lemma_mod_plus 0 i 2;
    assert ((2 * i) / 2 == i /\ (2 * i) % 2 == 0);
    assert ((2 * i + 1) / 2 == i /\ (2 * i + 1) % 2 == 1)

let pair_bound (i: nat { i < 128 }) : Lemma (2 * i + 2 <= n) = ()

(** One of the 128 quadratic products, as a function of its own for the
    same reason the butterflies are. *)
#push-options "--z3rlimit 600"
inline_for_extraction
fn base_mul (dst a b zt: A.array zqt) (i: SZ.t)
            (#pa #pb #pz: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         A.pts_to zt #pz zeta_table **
         pure (SZ.v i < 128 /\ Seq.length vd == n /\
               Seq.length va == n /\ Seq.length vb == n /\
               (forall (k: nat). k < 2 * SZ.v i ==>
                  S16.v (Seq.index vd k) ==
                    Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k))
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        A.pts_to zt #pz zeta_table **
        pure (SZ.v i < 128 /\ Seq.length v == n /\
              Seq.length va == n /\ Seq.length vb == n /\
              (forall (k: nat). k < 2 * SZ.v i + 2 ==>
                 S16.v (Seq.index v k) ==
                   Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k))
{
  A.pts_to_len dst;
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  SZ.fits_u32_implies_fits (SZ.v i + SZ.v i);
  let j = SZ.add i i;
  SZ.fits_u32_implies_fits (SZ.v j + 1);
  let j1 = SZ.add j 1sz;
  let z = A.(zt.(i));
  gammas_zetas (SZ.v i);
  multiply_ntts_index (as_poly va) (as_poly vb) (SZ.v j);
  multiply_ntts_index (as_poly va) (as_poly vb) (SZ.v j1);
  let g = zq_mul (zq_mul z z) (S16.classify 17us);
  let a0 = A.(a.(j));
  let a1 = A.(a.(j1));
  let b0 = A.(b.(j));
  let b1 = A.(b.(j1));
  Math.cancel_mul_div (SZ.v i) 2;
  Math.lemma_div_plus 1 (SZ.v i) 2;
  Math.lemma_mod_plus 1 (SZ.v i) 2;
  assert (pure (S16.v g == gammas (SZ.v i)));
  multiply_ntts_pair (as_poly va) (as_poly vb) (SZ.v i);
  as_poly_index va (SZ.v j);
  as_poly_index va (SZ.v j1);
  as_poly_index vb (SZ.v j);
  as_poly_index vb (SZ.v j1);
  let c0 = zq_add (zq_mul a0 b0) (zq_mul (zq_mul a1 b1) g);
  let c1 = zq_add (zq_mul a0 b1) (zq_mul a1 b0);
  assert (pure (S16.v c0 ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb)) (SZ.v j)));
  assert (pure (S16.v c1 ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb)) (SZ.v j1)));
  assert (pure (SZ.v j == 2 * SZ.v i /\ SZ.v j1 == 2 * SZ.v i + 1));
  A.((dst.(j) <- c0));
  with v0. assert (A.pts_to dst v0);
  assert (pure (Seq.index v0 (SZ.v j) == c0 /\
                (forall (k: nat). k < Seq.length v0 /\ k <> SZ.v j ==>
                   Seq.index v0 k == Seq.index vd k)));
  A.((dst.(j1) <- c1));
  with v1. assert (A.pts_to dst v1);
  assert (pure (Seq.index v1 (SZ.v j1) == c1 /\
                (forall (k: nat). k < Seq.length v1 /\ k <> SZ.v j1 ==>
                   Seq.index v1 k == Seq.index v0 k)));
  assert (pure (Seq.length v1 == n /\ Seq.index v1 (SZ.v j) == c0));
  (* The two freshly written entries, at concrete indices. *)
  assert (pure (S16.v (Seq.index v1 (2 * SZ.v i)) ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb))
                            (2 * SZ.v i)));
  assert (pure (S16.v (Seq.index v1 (2 * SZ.v i + 1)) ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb))
                            (2 * SZ.v i + 1)));
  (* Everything below them is untouched by the two writes. *)
  assert (pure (forall (k: nat). k < 2 * SZ.v i ==>
                  S16.v (Seq.index v1 k) ==
                    Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k));
  extend_by_two v1 (multiply_ntts (as_poly va) (as_poly vb)) (SZ.v i);
  assert (pure (forall (k: nat). k < 2 * SZ.v i + 2 ==>
                  S16.v (Seq.index v1 k) ==
                    Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k));
}

#pop-options

fn multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == multiply_ntts (as_poly va) (as_poly vb))
{
  A.pts_to_len dst;
  A.pts_to_len a;
  A.pts_to_len b;
  let zt = T.table zeta_arr 128sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 128sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    A.pts_to zt #pz zeta_table **
    pure (SZ.v vi <= 128 /\ Seq.length v == n /\
          Seq.length va == n /\ Seq.length vb == n /\
          (forall (k: nat). k < 2 * SZ.v vi ==>
             S16.v (Seq.index v k) ==
               Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k))
  decreases (128 - SZ.v (!i))
  {
    let vi = !i;
    assert (pure (SZ.v vi < 128));
    pair_bound (SZ.v vi);
    base_mul dst a b zt vi;
    HSZ.fits32 ();
    assert_norm (128 < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  T.drop_table zt;
  with v. assert (A.pts_to dst v);
  as_poly_intro v (multiply_ntts (as_poly va) (as_poly vb));
  assert (pure (as_poly v == multiply_ntts (as_poly va) (as_poly vb)));
}

#pop-options
