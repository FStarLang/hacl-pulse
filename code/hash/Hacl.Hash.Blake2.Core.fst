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

(** BLAKE2's compression function, written once for both widths.

    Every function takes the [Spec.Blake2.params] record as a monomorphized
    binder, so Custard emits one copy for BLAKE2b and one for BLAKE2s with the
    four rotation distances and the round count folded to literals.

    The message schedule arrives as a slice of a hundred and sixty [size_t],
    which is [sigma_arr], a [static const] array in the program image.  It is
    passed down rather than recomputed because [sigma_at] is a
    hundred-and-sixty-way if-chain, and a twelve-round compression looks the
    schedule up a hundred and ninety-two times. *)
module Hacl.Hash.Blake2.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Spec.Blake2
open Spec.Blake2.Constants

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module A = Pulse.Lib.Array
module U32 = FStar.UInt32
module G = FStar.Ghost
module GA = Pulse.Lib.GlobalArray

(** {2 The message schedule as a table} *)

(** What it means for a slice to hold the schedule. *)
let sigma_ok (s: Seq.seq SZ.t) : prop =
  Seq.length s == 160 /\ (forall (j: nat). j < 160 ==> SZ.v (Seq.index s j) == sigma_at j)

(** The schedule as a [static const] array in the program image; see
    [Hacl.Impl.Table].  Filling it used to be a hundred and sixty stores per
    hash. *)
let sigma_arr : GA.static_array SZ.t = GA.mk_static_array sigma_list

let sigma_len (_: unit)
  : Lemma (Seq.length (GA.static_array_elems sigma_arr) == 160)
  = assert_norm (List.Tot.length sigma_list == 160)

(** {2 The mixing function}

    All four reads happen before any write, which is what the specification
    says: every one of [g]'s right-hand sides is in terms of the working
    vector as it was on entry. *)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

fn g_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
          (vv: A.array t) (a b c d: SZ.t) (x y: t)
          (#v0: erased (Seq.seq t))
requires A.pts_to vv v0 **
         pure (Seq.length v0 == 16 /\ SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 **
  pure (Seq.length v0 == 16 /\
        SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16 /\
        Seq.length v1 == 16 /\ v1 == g p v0 (SZ.v a) (SZ.v b) (SZ.v c) (SZ.v d) x y)
{
  A.pts_to_len vv;
  let ra = A.(vv.(a));
  let rb = A.(vv.(b));
  let rc = A.(vv.(c));
  let rd = A.(vv.(d));

  let a1 = add_mod #t (add_mod #t ra rb) x;
  let d1 = rotate_right #t (logxor #t rd a1) p.rot1;
  let c1 = add_mod #t rc d1;
  let b1 = rotate_right #t (logxor #t rb c1) p.rot2;
  let a2 = add_mod #t (add_mod #t a1 b1) y;
  let d2 = rotate_right #t (logxor #t d1 a2) p.rot3;
  let c2 = add_mod #t c1 d2;
  let b2 = rotate_right #t (logxor #t b1 c2) p.rot4;

  A.((vv.(a) <- a2));
  A.((vv.(b) <- b2));
  A.((vv.(c) <- c2));
  A.((vv.(d) <- d2));
}

#pop-options

(** {2 One round}

    Four mixes: the columns, then, in a second function, the diagonals.  Eight
    in one function is a postcondition that no rlimit discharges; four is
    routine.

    [base] is [16 * r], carried in rather than multiplied out, so that no
    product appears in a proof obligation, and [r] itself is erased. *)

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

fn mix_columns (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (vv: A.array t) (m: A.array t) (sg: A.array SZ.t) (base: SZ.t) (r: G.erased nat)
               (#v0: erased (Seq.seq t))
               (#pm: perm) (#vm: erased (Seq.seq t))
               (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires A.pts_to vv v0 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs /\
               G.reveal r < 10 /\ SZ.v base == 16 * G.reveal r)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ G.reveal r < 10 /\
        Seq.length v1 == 16 /\ v1 == columns p vm v0 (G.reveal r))
{
  A.pts_to_len vv;
  A.pts_to_len m;
  A.pts_to_len sg;

  let s0 = A.(sg.(base));
  let s1 = A.(sg.(SZ.add base 1sz));
  let s2 = A.(sg.(SZ.add base 2sz));
  let s3 = A.(sg.(SZ.add base 3sz));
  let s4 = A.(sg.(SZ.add base 4sz));
  let s5 = A.(sg.(SZ.add base 5sz));
  let s6 = A.(sg.(SZ.add base 6sz));
  let s7 = A.(sg.(SZ.add base 7sz));

  g_impl p vv 0sz 4sz  8sz 12sz A.(m.(s0)) A.(m.(s1));
  g_impl p vv 1sz 5sz  9sz 13sz A.(m.(s2)) A.(m.(s3));
  g_impl p vv 2sz 6sz 10sz 14sz A.(m.(s4)) A.(m.(s5));
  g_impl p vv 3sz 7sz 11sz 15sz A.(m.(s6)) A.(m.(s7));
}

fn mix_diagonals (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (vv: A.array t) (m: A.array t) (sg: A.array SZ.t) (base: SZ.t) (r: G.erased nat)
                 (#v0: erased (Seq.seq t))
                 (#pm: perm) (#vm: erased (Seq.seq t))
                 (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires A.pts_to vv v0 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs /\
               G.reveal r < 10 /\ SZ.v base == 16 * G.reveal r)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ G.reveal r < 10 /\
        Seq.length v1 == 16 /\ v1 == diagonals p vm v0 (G.reveal r))
{
  A.pts_to_len vv;
  A.pts_to_len m;
  A.pts_to_len sg;

  let s8  = A.(sg.(SZ.add base  8sz));
  let s9  = A.(sg.(SZ.add base  9sz));
  let s10 = A.(sg.(SZ.add base 10sz));
  let s11 = A.(sg.(SZ.add base 11sz));
  let s12 = A.(sg.(SZ.add base 12sz));
  let s13 = A.(sg.(SZ.add base 13sz));
  let s14 = A.(sg.(SZ.add base 14sz));
  let s15 = A.(sg.(SZ.add base 15sz));

  g_impl p vv 0sz 5sz 10sz 15sz A.(m.(s8))  A.(m.(s9));
  g_impl p vv 1sz 6sz 11sz 12sz A.(m.(s10)) A.(m.(s11));
  g_impl p vv 2sz 7sz  8sz 13sz A.(m.(s12)) A.(m.(s13));
  g_impl p vv 3sz 4sz  9sz 14sz A.(m.(s14)) A.(m.(s15));
}

fn round_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
              (vv: A.array t) (m: A.array t) (sg: A.array SZ.t) (base: SZ.t) (r: G.erased nat)
              (#v0: erased (Seq.seq t))
              (#pm: perm) (#vm: erased (Seq.seq t))
              (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires A.pts_to vv v0 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs /\
               G.reveal r < 10 /\ SZ.v base == 16 * G.reveal r)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ G.reveal r < 10 /\
        Seq.length v1 == 16 /\ v1 == round p vm v0 (G.reveal r))
{
  mix_columns p vv m sg base r;
  mix_diagonals p vv m sg base r;
}

#pop-options

(** {2 The compression function}

    Four pieces, matching the four stages [Spec.Blake2] names: load the working
    vector, mix the counter in, run the rounds, fold the halves back into the
    state.  Splitting it this way is not only for readability -- a single
    function containing sixteen stores, three updates and a loop was well past
    what the solver would take in one query. *)

(** The two halves of the block counter.  [of_sizet_lo] and [of_sizet_hi] are
    honest about [size_t] possibly being wider than sixty-four bits; a caller
    that promises it is not gets the exact low and high words of the
    counter. *)
let sizet_lo_eq (#t: Type0) {| w: word t |} (x: SZ.t)
  : Lemma (requires SZ.v x < pow2 64)
          (ensures of_sizet_lo #t x == low_word #t (SZ.v x))
  = Math.small_mod (SZ.v x) (pow2 64);
    w.v_extensional (of_sizet_lo #t x) (low_word #t (SZ.v x))

let sizet_hi_eq (#t: Type0) {| w: word t |} (x: SZ.t)
  : Lemma (requires SZ.v x < pow2 64)
          (ensures of_sizet_hi #t x == low_word #t (SZ.v x / pow2 (bits #t)))
  = Math.small_mod (SZ.v x) (pow2 64);
    w.v_extensional (of_sizet_hi #t x) (low_word #t (SZ.v x / pow2 (bits #t)))

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** [vv := h ++ iv].  Unrolled: sixteen stores, and one extensionality
    argument over sixteen indices, is cheaper than a loop invariant that has to
    talk about two source slices at once. *)
fn load_vector (#t: Type0) {| w: word t |}
               (vv: A.array t) (h: A.array t) (ivs: A.array t)
               (#v0: erased (Seq.seq t))
               (#ph: perm) (#vh: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
requires A.pts_to vv v0 ** A.pts_to h #ph vh ** A.pts_to ivs #pi vi **
         pure (Seq.length v0 == 16 /\ Seq.length vh == 8 /\ Seq.length vi == 8)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to h #ph vh ** A.pts_to ivs #pi vi **
  pure (Seq.length vh == 8 /\ Seq.length vi == 8 /\
        Seq.length v1 == 16 /\ v1 == Seq.append (reveal vh) (reveal vi))
{
  A.pts_to_len vv;
  A.pts_to_len h;
  A.pts_to_len ivs;

  A.(vv.(0sz) <- h.(0sz));
  A.(vv.(1sz) <- h.(1sz));
  A.(vv.(2sz) <- h.(2sz));
  A.(vv.(3sz) <- h.(3sz));
  A.(vv.(4sz) <- h.(4sz));
  A.(vv.(5sz) <- h.(5sz));
  A.(vv.(6sz) <- h.(6sz));
  A.(vv.(7sz) <- h.(7sz));
  A.(vv.(8sz)  <- ivs.(0sz));
  A.(vv.(9sz)  <- ivs.(1sz));
  A.(vv.(10sz) <- ivs.(2sz));
  A.(vv.(11sz) <- ivs.(3sz));
  A.(vv.(12sz) <- ivs.(4sz));
  A.(vv.(13sz) <- ivs.(5sz));
  A.(vv.(14sz) <- ivs.(6sz));
  A.(vv.(15sz) <- ivs.(7sz));

  with v1. assert (A.pts_to vv v1);
  assert (pure (Seq.equal v1 (Seq.append (reveal vh) (reveal vi))));
}

(** [Spec.Blake2.init_vector]. *)
fn init_vector_impl (#t: Type0) {| w: word t |}
                    ([@@@FStar.Attributes.monomorphize] p: params t)
                    (vv: A.array t) (h: A.array t) (ivs: A.array t)
                    (ctr: SZ.t) (last: bool)
                    (#v0: erased (Seq.seq t))
                    (#ph: perm) (#vh: erased (Seq.seq t))
                    (#pi: perm) (#vi: erased (Seq.seq t))
requires A.pts_to vv v0 ** A.pts_to h #ph vh ** A.pts_to ivs #pi vi **
         pure (Seq.length v0 == 16 /\ Seq.length vh == 8 /\ Seq.length vi == 8 /\
               SZ.v ctr < pow2 64 /\ reveal vi == G.reveal p.iv)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to h #ph vh ** A.pts_to ivs #pi vi **
  pure (Seq.length vh == 8 /\ Seq.length v1 == 16 /\
        v1 == init_vector p (reveal vh) (SZ.v ctr) last)
{
  load_vector vv h ivs;
  sizet_lo_eq #t ctr;
  sizet_hi_eq #t ctr;

  let x12 = A.(vv.(12sz));
  A.(vv.(12sz) <- logxor x12 (of_sizet_lo ctr));
  let x13 = A.(vv.(13sz));
  A.(vv.(13sz) <- logxor x13 (of_sizet_hi ctr));

  if last {
    let x14 = A.(vv.(14sz));
    A.(vv.(14sz) <- lognot x14);
    A.pts_to_len vv;
  } else {
    A.pts_to_len vv;
  }
}

(** The round loop.  [base] is the offset of the current round's sixteen
    entries in the schedule table; it advances by sixteen and wraps at a
    hundred and sixty, which is exactly [16 * (i % 10)] -- BLAKE2b's eleventh
    and twelfth rounds reuse the first and second permutations. *)
#push-options "--z3rlimit 600 --fuel 1 --ifuel 0"

fn rounds_impl (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (vv: A.array t) (m: A.array t) (sg: A.array SZ.t)
               (#v0: erased (Seq.seq t))
               (#pm: perm) (#vm: erased (Seq.seq t))
               (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires A.pts_to vv v0 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs)
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ Seq.length v1 == 16 /\
        v1 == rounds_upto p (reveal vm) (reveal v0) (rounds p))
{
  A.pts_to_len vv;
  A.pts_to_len m;

  let nr = p.nrounds;
  let mut i = 0sz;
  let mut base = 0sz;

  while (let vi = !i; SZ.lt vi nr)
  invariant exists* (vi: SZ.t) (vb: SZ.t) (v1: Seq.seq t).
    pts_to i vi ** pts_to base vb ** A.pts_to vv v1 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
    pure (SZ.v vi <= SZ.v nr /\ SZ.v vb == 16 * (SZ.v vi % 10) /\
          Seq.length v0 == 16 /\
          Seq.length vm == 16 /\ Seq.length v1 == 16 /\ sigma_ok vs /\
          v1 == rounds_upto p (reveal vm) (reveal v0) (SZ.v vi))
  decreases (SZ.v nr - SZ.v (!i))
  {
    let vi = !i;
    let vb = !base;
    round_impl p vv m sg vb (G.hide (SZ.v vi % 10));
    let nb = SZ.add vb 16sz;
    if (SZ.eq nb 160sz) {
      base := 0sz;
    } else {
      base := nb;
    };
    i := SZ.add vi 1sz;
  };
}

#pop-options

(** The feedforward, [Spec.Blake2.mix_state]. *)
fn mix_state_impl (#t: Type0) {| w: word t |}
                  (h: A.array t) (vv: A.array t)
                  (#vh: erased (Seq.seq t))
                  (#pv: perm) (#v4: erased (Seq.seq t))
requires A.pts_to h vh ** A.pts_to vv #pv v4 **
         pure (Seq.length vh == 8 /\ Seq.length v4 == 16)
ensures exists* (vh': Seq.seq t). A.pts_to h vh' ** A.pts_to vv #pv v4 **
  pure (Seq.length vh == 8 /\ Seq.length v4 == 16 /\ Seq.length vh' == 8 /\
        vh' == mix_state #t (reveal vh) (reveal v4))
{
  A.pts_to_len h;
  A.pts_to_len vv;

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vc: Seq.seq t).
    pts_to i vi ** A.pts_to h vc ** A.pts_to vv #pv v4 **
    pure (SZ.v vi <= 8 /\ Seq.length vc == 8 /\ Seq.length v4 == 16 /\
          (forall (j: nat). j < SZ.v vi ==>
            Seq.index vc j == logxor #t (logxor #t (Seq.index (reveal vh) j)
                                                   (Seq.index (reveal v4) j))
                                        (Seq.index (reveal v4) (j + 8))) /\
          (forall (j: nat). SZ.v vi <= j /\ j < 8 ==>
            Seq.index vc j == Seq.index (reveal vh) j))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(h.(vi));
    let b = A.(vv.(vi));
    let c = A.(vv.(SZ.add vi 8sz));
    A.(h.(vi) <- logxor (logxor a b) c);
    i := SZ.add vi 1sz;
  };

  with vc. assert (A.pts_to h vc);
  assert (pure (Seq.equal vc (mix_state #t (reveal vh) (reveal v4))));
}

(** [Spec.Blake2.compress]: the state [h] is updated in place, using [vv] as
    scratch. *)
fn compress_impl (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (h: A.array t) (m: A.array t) (vv: A.array t) (ivs: A.array t)
                 (sg: A.array SZ.t) (ctr: SZ.t) (last: bool)
                 (#vh: erased (Seq.seq t))
                 (#v0: erased (Seq.seq t))
                 (#pm: perm) (#vm: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires A.pts_to h vh ** A.pts_to m #pm vm ** A.pts_to vv v0 **
         A.pts_to ivs #pi vi ** A.pts_to sg #ps vs **
         pure (Seq.length vh == 8 /\ Seq.length vm == 16 /\ Seq.length v0 == 16 /\
               Seq.length vi == 8 /\ sigma_ok vs /\
               SZ.v ctr < pow2 64 /\ reveal vi == G.reveal p.iv)
ensures exists* (vh': Seq.seq t) (v1: Seq.seq t).
  A.pts_to h vh' ** A.pts_to m #pm vm ** A.pts_to vv v1 **
  A.pts_to ivs #pi vi ** A.pts_to sg #ps vs **
  pure (Seq.length vh == 8 /\ Seq.length vm == 16 /\ Seq.length v1 == 16 /\
        Seq.length vh' == 8 /\
        vh' == compress p (reveal vh) (reveal vm) (SZ.v ctr) last)
{
  init_vector_impl p vv h ivs ctr last;
  rounds_impl p vv m sg;
  mix_state_impl h vv;
}

#pop-options
