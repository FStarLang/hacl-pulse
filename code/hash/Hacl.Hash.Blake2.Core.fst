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
open Hacl.Impl.Table

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

(** Take the schedule table, here rather than from a caller.

    It used to be a parameter, threaded from the four entry points down
    through six functions to [round_impl].  Nothing ever passed anything else
    -- there is one sigma table in BLAKE2 and both widths share it -- so the
    parameter existed only to be constant-propagated away, and whether it was
    propagated away was the C compiler's decision rather than ours.  gcc took
    it by cloning [compress_impl], which is spent against the
    [ipa-cp-large-unit-insns] budget for the whole translation unit; compiling
    with [-fno-ipa-cp], which is what an exhausted budget looks like, costs
    BLAKE2 thirteen to fifteen percent.  Read from the global here it costs
    nothing and cannot be taken away: the C is a local pointer to a [static
    const] array, and both compilers fold the hundred and ninety-two literal
    subscripts at [-O1]. *)
inline_for_extraction
fn sigma_table (_: unit)
requires emp
returns sg: A.array SZ.t
ensures exists* (ps: perm) (vs: Seq.seq SZ.t). A.pts_to sg #ps vs ** pure (sigma_ok vs)
{
  sigma_len ();
  let sg = table sigma_arr 160sz;
  sigma_seq_ok ();
  sg
}

(** {2 The mixing function}

    All four reads happen before any write, which is what the specification
    says: every one of [g]'s right-hand sides is in terms of the working
    vector as it was on entry. *)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

inline_for_extraction
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
    product appears in a proof obligation, and [r] itself is erased.

    The whole round is [inline_for_extraction], and that is the point of the
    unrolling below: with [base] a literal at every call site, [sg.(base + k)]
    is a read of a known element of a [static const] table, so all sixteen
    schedule indices fold to constants and the sixteen message reads become
    sixteen named words.  While a round was a call taking a loop-carried
    [base], none of that was available to either C compiler, and the two
    disagreed about what to do instead -- inlining the round was worth 1.35x
    to clang and cost gcc 15%.  Removing the thing they were guessing about
    is what makes them agree.  See the note above [Hacl.Impl.Mont256.amul]. *)

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

inline_for_extraction
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

  (* The offsets carry their value in a refinement on [SZ.add]'s return type,
     which is dropped when the application is left inline. *)
  let o1 = SZ.add base 1sz;
  let o2 = SZ.add base 2sz;
  let o3 = SZ.add base 3sz;
  let o4 = SZ.add base 4sz;
  let o5 = SZ.add base 5sz;
  let o6 = SZ.add base 6sz;
  let o7 = SZ.add base 7sz;
  assert (pure (SZ.v o1 == SZ.v base + 1 /\ SZ.v o2 == SZ.v base + 2 /\
                SZ.v o3 == SZ.v base + 3 /\ SZ.v o4 == SZ.v base + 4 /\
                SZ.v o5 == SZ.v base + 5 /\ SZ.v o6 == SZ.v base + 6 /\
                SZ.v o7 == SZ.v base + 7));

  let s0 = A.(sg.(base));
  let s1 = A.(sg.(o1));
  let s2 = A.(sg.(o2));
  let s3 = A.(sg.(o3));
  let s4 = A.(sg.(o4));
  let s5 = A.(sg.(o5));
  let s6 = A.(sg.(o6));
  let s7 = A.(sg.(o7));

  let m0 = A.(m.(s0));
  let m1 = A.(m.(s1));
  let m2 = A.(m.(s2));
  let m3 = A.(m.(s3));
  let m4 = A.(m.(s4));
  let m5 = A.(m.(s5));
  let m6 = A.(m.(s6));
  let m7 = A.(m.(s7));

  g_impl p vv 0sz 4sz  8sz 12sz m0 m1;
  g_impl p vv 1sz 5sz  9sz 13sz m2 m3;
  g_impl p vv 2sz 6sz 10sz 14sz m4 m5;
  g_impl p vv 3sz 7sz 11sz 15sz m6 m7;
}

inline_for_extraction
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

inline_for_extraction
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
inline_for_extraction
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
inline_for_extraction
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

(** One round, as a step of the loop that is no longer a loop.  [n] counts
    rounds from the start of the compression and [vinit] is the working vector
    the compression began with, so the precondition and the postcondition are
    the same predicate at [n] and [n + 1].  That keeps each of the twelve
    steps below a single unfolding of [rounds_upto] rather than one query
    carrying the whole chain.

    [n] and [vinit] are erased; only [base] reaches the C, and at every call
    site it is a literal. *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"

inline_for_extraction
fn round_step (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (vv: A.array t) (m: A.array t) (sg: A.array SZ.t)
              (base: SZ.t) (n: G.erased nat) (vinit: G.erased (Seq.seq t))
              (#v0: erased (Seq.seq t))
              (#pm: perm) (#vm: erased (Seq.seq t))
              (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires A.pts_to vv v0 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\
               Seq.length (G.reveal vinit) == 16 /\ sigma_ok vs /\
               SZ.v base == 16 * (G.reveal n % 10) /\
               v0 == rounds_upto p (reveal vm) (G.reveal vinit) (G.reveal n))
ensures exists* (v1: Seq.seq t). A.pts_to vv v1 ** A.pts_to m #pm vm ** A.pts_to sg #ps vs **
  pure (Seq.length vm == 16 /\ Seq.length (G.reveal vinit) == 16 /\
        Seq.length v1 == 16 /\ sigma_ok vs /\
        v1 == rounds_upto p (reveal vm) (G.reveal vinit) (G.reveal n + 1))
{
  round_impl p vv m sg base (G.hide (G.reveal n % 10));
}

#pop-options

(** The rounds, unrolled.  [base] is the offset of a round's sixteen entries
    in the schedule table, and it used to be a loop-carried variable that
    advanced by sixteen and wrapped at a hundred and sixty -- exactly
    [16 * (i % 10)], BLAKE2b's eleventh and twelfth rounds reusing the first
    and second permutations.

    Written out, every [base] is a literal, so every one of the hundred and
    ninety-two schedule lookups folds and the message words are read by name.
    That is worth 1.3x to gcc and 1.6x to clang, and it is the only form in
    which the two agree; see the note above [round_impl].  The first ten
    rounds are common to both widths and the last two are BLAKE2b's, under a
    test on a field that is a literal after monomorphization, so exactly one
    arm survives in the C. *)
#push-options "--z3rlimit 600 --fuel 1 --ifuel 0"

inline_for_extraction
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

  round_step p vv m sg   0sz (G.hide 0) v0;
  round_step p vv m sg  16sz (G.hide 1) v0;
  round_step p vv m sg  32sz (G.hide 2) v0;
  round_step p vv m sg  48sz (G.hide 3) v0;
  round_step p vv m sg  64sz (G.hide 4) v0;
  round_step p vv m sg  80sz (G.hide 5) v0;
  round_step p vv m sg  96sz (G.hide 6) v0;
  round_step p vv m sg 112sz (G.hide 7) v0;
  round_step p vv m sg 128sz (G.hide 8) v0;
  round_step p vv m sg 144sz (G.hide 9) v0;

  let nr = p.nrounds;
  nrounds_cases nr;
  if (SZ.gt nr 10sz) {
    round_step p vv m sg  0sz (G.hide 10) v0;
    round_step p vv m sg 16sz (G.hide 11) v0;
  } else {
    A.pts_to_len vv;
  }
}

#pop-options

(** The feedforward, [Spec.Blake2.mix_state]. *)
inline_for_extraction
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

(** [Spec.Blake2.compress]: the state [h] is updated in place.

    The sixteen-word working vector is allocated here rather than passed in,
    and this function is deliberately *not* [inline_for_extraction] -- the two
    facts go together.  Everything below it is inlined, so a compression is
    one straight-line body of twelve unrolled rounds, and the working vector
    is a local array that provably does not escape it.  Both C compilers
    therefore keep all sixteen words in registers for the whole compression,
    which is where most of the 1.3x (gcc) and 1.6x (clang) comes from.

    Inlining this function as well would put that body at each of its four
    call sites in each of eight instantiations.  It was measured: it buys
    clang nothing over this and costs gcc a fifth of its gain, because
    thirty-two copies do not fit where eight do.  A caller-allocated scratch
    array was measured too, and gives up half the win in both compilers --
    a pointer parameter may alias, so the words stay in memory.

    The schedule table is taken here too, from the global, rather than being
    a parameter; see {!sigma_table}.  [ivs] is the initialisation vector and
    [last] the final-block flag.  gcc used to clone this function on all
    three, and clang did not, which is why it was inlined before the rounds
    were unrolled.  Custard monomorphizes on [p], so the eight copies have
    the round count and the rotations as constants already. *)
fn compress_impl (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (h: A.array t) (m: A.array t) (ivs: A.array t)
                 (ctr: SZ.t) (last: bool)
                 (#vh: erased (Seq.seq t))
                 (#pm: perm) (#vm: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
requires A.pts_to h vh ** A.pts_to m #pm vm ** A.pts_to ivs #pi vi **
         pure (Seq.length vh == 8 /\ Seq.length vm == 16 /\
               Seq.length vi == 8 /\
               SZ.v ctr < pow2 64 /\ reveal vi == G.reveal p.iv)
ensures exists* (vh': Seq.seq t).
  A.pts_to h vh' ** A.pts_to m #pm vm ** A.pts_to ivs #pi vi **
  pure (Seq.length vh == 8 /\ Seq.length vm == 16 /\
        Seq.length vh' == 8 /\
        vh' == compress p (reveal vh) (reveal vm) (SZ.v ctr) last)
{
  let z0: t = zero #t #w;
  let mut vv = [| z0; 16sz |];
  A.pts_to_len vv;
  let sg = sigma_table ();
  init_vector_impl p vv h ivs ctr last;
  rounds_impl p vv m sg;
  drop_table sg;
  mix_state_impl h vv;
}

#pop-options
