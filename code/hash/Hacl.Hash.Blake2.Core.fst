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
    filled by [fill_sigma], for the same reason the SHA-3 round constants do:
    the direct-to-C backend cannot emit a constant global, so a table has to be
    written into memory by somebody.  Filling it once per hash and passing it
    down costs a hundred and sixty stores; evaluating the if-chain at each of
    the hundred and ninety-two lookups a twelve-round compression makes would
    cost a great deal more. *)
module Hacl.Hash.Blake2.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Spec.Blake2
open Spec.Blake2.Constants

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module A = Pulse.Lib.Array
module U32 = FStar.UInt32
module G = FStar.Ghost

(** {2 The message schedule as a table} *)

(** [sigma_at] as a machine function: a hundred and sixty way switch on a
    public index.

    Both this and [sigma_at] itself are [opaque_to_smt].  A transparent
    hundred-and-sixty-way if-chain is a hundred and sixty copies of itself in
    every query that so much as mentions the table, which is enough on its own
    to time out the loop's termination check.  The refined return type says
    everything a caller needs. *)
[@@"opaque_to_smt"]
inline_for_extraction
let sigma_sz (k: SZ.t { SZ.v k < 160 }) : (x: SZ.t { SZ.v x == sigma_at (SZ.v k) }) =
  reveal_opaque (`%sigma_at) sigma_at;
  if SZ.eq k 0sz then 0sz else
  if SZ.eq k 1sz then 1sz else
  if SZ.eq k 2sz then 2sz else
  if SZ.eq k 3sz then 3sz else
  if SZ.eq k 4sz then 4sz else
  if SZ.eq k 5sz then 5sz else
  if SZ.eq k 6sz then 6sz else
  if SZ.eq k 7sz then 7sz else
  if SZ.eq k 8sz then 8sz else
  if SZ.eq k 9sz then 9sz else
  if SZ.eq k 10sz then 10sz else
  if SZ.eq k 11sz then 11sz else
  if SZ.eq k 12sz then 12sz else
  if SZ.eq k 13sz then 13sz else
  if SZ.eq k 14sz then 14sz else
  if SZ.eq k 15sz then 15sz else
  if SZ.eq k 16sz then 14sz else
  if SZ.eq k 17sz then 10sz else
  if SZ.eq k 18sz then 4sz else
  if SZ.eq k 19sz then 8sz else
  if SZ.eq k 20sz then 9sz else
  if SZ.eq k 21sz then 15sz else
  if SZ.eq k 22sz then 13sz else
  if SZ.eq k 23sz then 6sz else
  if SZ.eq k 24sz then 1sz else
  if SZ.eq k 25sz then 12sz else
  if SZ.eq k 26sz then 0sz else
  if SZ.eq k 27sz then 2sz else
  if SZ.eq k 28sz then 11sz else
  if SZ.eq k 29sz then 7sz else
  if SZ.eq k 30sz then 5sz else
  if SZ.eq k 31sz then 3sz else
  if SZ.eq k 32sz then 11sz else
  if SZ.eq k 33sz then 8sz else
  if SZ.eq k 34sz then 12sz else
  if SZ.eq k 35sz then 0sz else
  if SZ.eq k 36sz then 5sz else
  if SZ.eq k 37sz then 2sz else
  if SZ.eq k 38sz then 15sz else
  if SZ.eq k 39sz then 13sz else
  if SZ.eq k 40sz then 10sz else
  if SZ.eq k 41sz then 14sz else
  if SZ.eq k 42sz then 3sz else
  if SZ.eq k 43sz then 6sz else
  if SZ.eq k 44sz then 7sz else
  if SZ.eq k 45sz then 1sz else
  if SZ.eq k 46sz then 9sz else
  if SZ.eq k 47sz then 4sz else
  if SZ.eq k 48sz then 7sz else
  if SZ.eq k 49sz then 9sz else
  if SZ.eq k 50sz then 3sz else
  if SZ.eq k 51sz then 1sz else
  if SZ.eq k 52sz then 13sz else
  if SZ.eq k 53sz then 12sz else
  if SZ.eq k 54sz then 11sz else
  if SZ.eq k 55sz then 14sz else
  if SZ.eq k 56sz then 2sz else
  if SZ.eq k 57sz then 6sz else
  if SZ.eq k 58sz then 5sz else
  if SZ.eq k 59sz then 10sz else
  if SZ.eq k 60sz then 4sz else
  if SZ.eq k 61sz then 0sz else
  if SZ.eq k 62sz then 15sz else
  if SZ.eq k 63sz then 8sz else
  if SZ.eq k 64sz then 9sz else
  if SZ.eq k 65sz then 0sz else
  if SZ.eq k 66sz then 5sz else
  if SZ.eq k 67sz then 7sz else
  if SZ.eq k 68sz then 2sz else
  if SZ.eq k 69sz then 4sz else
  if SZ.eq k 70sz then 10sz else
  if SZ.eq k 71sz then 15sz else
  if SZ.eq k 72sz then 14sz else
  if SZ.eq k 73sz then 1sz else
  if SZ.eq k 74sz then 11sz else
  if SZ.eq k 75sz then 12sz else
  if SZ.eq k 76sz then 6sz else
  if SZ.eq k 77sz then 8sz else
  if SZ.eq k 78sz then 3sz else
  if SZ.eq k 79sz then 13sz else
  if SZ.eq k 80sz then 2sz else
  if SZ.eq k 81sz then 12sz else
  if SZ.eq k 82sz then 6sz else
  if SZ.eq k 83sz then 10sz else
  if SZ.eq k 84sz then 0sz else
  if SZ.eq k 85sz then 11sz else
  if SZ.eq k 86sz then 8sz else
  if SZ.eq k 87sz then 3sz else
  if SZ.eq k 88sz then 4sz else
  if SZ.eq k 89sz then 13sz else
  if SZ.eq k 90sz then 7sz else
  if SZ.eq k 91sz then 5sz else
  if SZ.eq k 92sz then 15sz else
  if SZ.eq k 93sz then 14sz else
  if SZ.eq k 94sz then 1sz else
  if SZ.eq k 95sz then 9sz else
  if SZ.eq k 96sz then 12sz else
  if SZ.eq k 97sz then 5sz else
  if SZ.eq k 98sz then 1sz else
  if SZ.eq k 99sz then 15sz else
  if SZ.eq k 100sz then 14sz else
  if SZ.eq k 101sz then 13sz else
  if SZ.eq k 102sz then 4sz else
  if SZ.eq k 103sz then 10sz else
  if SZ.eq k 104sz then 0sz else
  if SZ.eq k 105sz then 7sz else
  if SZ.eq k 106sz then 6sz else
  if SZ.eq k 107sz then 3sz else
  if SZ.eq k 108sz then 9sz else
  if SZ.eq k 109sz then 2sz else
  if SZ.eq k 110sz then 8sz else
  if SZ.eq k 111sz then 11sz else
  if SZ.eq k 112sz then 13sz else
  if SZ.eq k 113sz then 11sz else
  if SZ.eq k 114sz then 7sz else
  if SZ.eq k 115sz then 14sz else
  if SZ.eq k 116sz then 12sz else
  if SZ.eq k 117sz then 1sz else
  if SZ.eq k 118sz then 3sz else
  if SZ.eq k 119sz then 9sz else
  if SZ.eq k 120sz then 5sz else
  if SZ.eq k 121sz then 0sz else
  if SZ.eq k 122sz then 15sz else
  if SZ.eq k 123sz then 4sz else
  if SZ.eq k 124sz then 8sz else
  if SZ.eq k 125sz then 6sz else
  if SZ.eq k 126sz then 2sz else
  if SZ.eq k 127sz then 10sz else
  if SZ.eq k 128sz then 6sz else
  if SZ.eq k 129sz then 15sz else
  if SZ.eq k 130sz then 14sz else
  if SZ.eq k 131sz then 9sz else
  if SZ.eq k 132sz then 11sz else
  if SZ.eq k 133sz then 3sz else
  if SZ.eq k 134sz then 0sz else
  if SZ.eq k 135sz then 8sz else
  if SZ.eq k 136sz then 12sz else
  if SZ.eq k 137sz then 2sz else
  if SZ.eq k 138sz then 13sz else
  if SZ.eq k 139sz then 7sz else
  if SZ.eq k 140sz then 1sz else
  if SZ.eq k 141sz then 4sz else
  if SZ.eq k 142sz then 10sz else
  if SZ.eq k 143sz then 5sz else
  if SZ.eq k 144sz then 10sz else
  if SZ.eq k 145sz then 2sz else
  if SZ.eq k 146sz then 8sz else
  if SZ.eq k 147sz then 4sz else
  if SZ.eq k 148sz then 7sz else
  if SZ.eq k 149sz then 6sz else
  if SZ.eq k 150sz then 1sz else
  if SZ.eq k 151sz then 5sz else
  if SZ.eq k 152sz then 15sz else
  if SZ.eq k 153sz then 11sz else
  if SZ.eq k 154sz then 9sz else
  if SZ.eq k 155sz then 14sz else
  if SZ.eq k 156sz then 3sz else
  if SZ.eq k 157sz then 12sz else
  if SZ.eq k 158sz then 13sz else
  0sz

(** What it means for a slice to hold the schedule. *)
let sigma_ok (s: Seq.seq SZ.t) : prop =
  Seq.length s == 160 /\ (forall (j: nat). j < 160 ==> SZ.v (Seq.index s j) == sigma_at j)

fn fill_sigma (b: S.slice SZ.t) (#v0: erased (Seq.seq SZ.t))
requires S.pts_to b v0 ** pure (Seq.length v0 == 160)
ensures exists* (v1: Seq.seq SZ.t). S.pts_to b v1 ** pure (sigma_ok v1)
{
  S.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 160sz)
  invariant exists* (vi: SZ.t) (v1: Seq.seq SZ.t).
    pts_to i vi ** S.pts_to b v1 **
    pure (SZ.v vi <= 160 /\ Seq.length v1 == 160 /\ (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index v1 j) == sigma_at j))
  decreases (160 - SZ.v (!i))
  {
    let vi = !i;
    S.((b.(vi) <- sigma_sz vi));
    i := SZ.add vi 1sz;
  };
}


(** {2 The mixing function}

    All four reads happen before any write, which is what the specification
    says: every one of [g]'s right-hand sides is in terms of the working
    vector as it was on entry. *)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

fn g_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
          (vv: S.slice t) (a b c d: SZ.t) (x y: t)
          (#v0: erased (Seq.seq t))
requires S.pts_to vv v0 **
         pure (Seq.length v0 == 16 /\ SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 **
  pure (Seq.length v0 == 16 /\
        SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16 /\
        Seq.length v1 == 16 /\ v1 == g p v0 (SZ.v a) (SZ.v b) (SZ.v c) (SZ.v d) x y)
{
  S.pts_to_len vv;
  let ra = S.(vv.(a));
  let rb = S.(vv.(b));
  let rc = S.(vv.(c));
  let rd = S.(vv.(d));

  let a1 = add_mod #t (add_mod #t ra rb) x;
  let d1 = rotate_right #t (logxor #t rd a1) p.rot1;
  let c1 = add_mod #t rc d1;
  let b1 = rotate_right #t (logxor #t rb c1) p.rot2;
  let a2 = add_mod #t (add_mod #t a1 b1) y;
  let d2 = rotate_right #t (logxor #t d1 a2) p.rot3;
  let c2 = add_mod #t c1 d2;
  let b2 = rotate_right #t (logxor #t b1 c2) p.rot4;

  S.((vv.(a) <- a2));
  S.((vv.(b) <- b2));
  S.((vv.(c) <- c2));
  S.((vv.(d) <- d2));
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
               (vv: S.slice t) (m: S.slice t) (sg: S.slice SZ.t) (base: SZ.t) (r: G.erased nat)
               (#v0: erased (Seq.seq t))
               (#pm: perm) (#vm: erased (Seq.seq t))
               (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires S.pts_to vv v0 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs /\
               G.reveal r < 10 /\ SZ.v base == 16 * G.reveal r)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ G.reveal r < 10 /\
        Seq.length v1 == 16 /\ v1 == columns p vm v0 (G.reveal r))
{
  S.pts_to_len vv;
  S.pts_to_len m;
  S.pts_to_len sg;

  let s0 = S.(sg.(base));
  let s1 = S.(sg.(SZ.add base 1sz));
  let s2 = S.(sg.(SZ.add base 2sz));
  let s3 = S.(sg.(SZ.add base 3sz));
  let s4 = S.(sg.(SZ.add base 4sz));
  let s5 = S.(sg.(SZ.add base 5sz));
  let s6 = S.(sg.(SZ.add base 6sz));
  let s7 = S.(sg.(SZ.add base 7sz));

  g_impl p vv 0sz 4sz  8sz 12sz S.(m.(s0)) S.(m.(s1));
  g_impl p vv 1sz 5sz  9sz 13sz S.(m.(s2)) S.(m.(s3));
  g_impl p vv 2sz 6sz 10sz 14sz S.(m.(s4)) S.(m.(s5));
  g_impl p vv 3sz 7sz 11sz 15sz S.(m.(s6)) S.(m.(s7));
}

fn mix_diagonals (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (vv: S.slice t) (m: S.slice t) (sg: S.slice SZ.t) (base: SZ.t) (r: G.erased nat)
                 (#v0: erased (Seq.seq t))
                 (#pm: perm) (#vm: erased (Seq.seq t))
                 (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires S.pts_to vv v0 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs /\
               G.reveal r < 10 /\ SZ.v base == 16 * G.reveal r)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ G.reveal r < 10 /\
        Seq.length v1 == 16 /\ v1 == diagonals p vm v0 (G.reveal r))
{
  S.pts_to_len vv;
  S.pts_to_len m;
  S.pts_to_len sg;

  let s8  = S.(sg.(SZ.add base  8sz));
  let s9  = S.(sg.(SZ.add base  9sz));
  let s10 = S.(sg.(SZ.add base 10sz));
  let s11 = S.(sg.(SZ.add base 11sz));
  let s12 = S.(sg.(SZ.add base 12sz));
  let s13 = S.(sg.(SZ.add base 13sz));
  let s14 = S.(sg.(SZ.add base 14sz));
  let s15 = S.(sg.(SZ.add base 15sz));

  g_impl p vv 0sz 5sz 10sz 15sz S.(m.(s8))  S.(m.(s9));
  g_impl p vv 1sz 6sz 11sz 12sz S.(m.(s10)) S.(m.(s11));
  g_impl p vv 2sz 7sz  8sz 13sz S.(m.(s12)) S.(m.(s13));
  g_impl p vv 3sz 4sz  9sz 14sz S.(m.(s14)) S.(m.(s15));
}

fn round_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
              (vv: S.slice t) (m: S.slice t) (sg: S.slice SZ.t) (base: SZ.t) (r: G.erased nat)
              (#v0: erased (Seq.seq t))
              (#pm: perm) (#vm: erased (Seq.seq t))
              (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires S.pts_to vv v0 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs /\
               G.reveal r < 10 /\ SZ.v base == 16 * G.reveal r)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
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
               (vv: S.slice t) (h: S.slice t) (ivs: S.slice t)
               (#v0: erased (Seq.seq t))
               (#ph: perm) (#vh: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
requires S.pts_to vv v0 ** S.pts_to h #ph vh ** S.pts_to ivs #pi vi **
         pure (Seq.length v0 == 16 /\ Seq.length vh == 8 /\ Seq.length vi == 8)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 ** S.pts_to h #ph vh ** S.pts_to ivs #pi vi **
  pure (Seq.length vh == 8 /\ Seq.length vi == 8 /\
        Seq.length v1 == 16 /\ v1 == Seq.append (reveal vh) (reveal vi))
{
  S.pts_to_len vv;
  S.pts_to_len h;
  S.pts_to_len ivs;

  S.(vv.(0sz) <- h.(0sz));
  S.(vv.(1sz) <- h.(1sz));
  S.(vv.(2sz) <- h.(2sz));
  S.(vv.(3sz) <- h.(3sz));
  S.(vv.(4sz) <- h.(4sz));
  S.(vv.(5sz) <- h.(5sz));
  S.(vv.(6sz) <- h.(6sz));
  S.(vv.(7sz) <- h.(7sz));
  S.(vv.(8sz)  <- ivs.(0sz));
  S.(vv.(9sz)  <- ivs.(1sz));
  S.(vv.(10sz) <- ivs.(2sz));
  S.(vv.(11sz) <- ivs.(3sz));
  S.(vv.(12sz) <- ivs.(4sz));
  S.(vv.(13sz) <- ivs.(5sz));
  S.(vv.(14sz) <- ivs.(6sz));
  S.(vv.(15sz) <- ivs.(7sz));

  with v1. assert (S.pts_to vv v1);
  assert (pure (Seq.equal v1 (Seq.append (reveal vh) (reveal vi))));
}

(** [Spec.Blake2.init_vector]. *)
fn init_vector_impl (#t: Type0) {| w: word t |}
                    ([@@@FStar.Attributes.monomorphize] p: params t)
                    (vv: S.slice t) (h: S.slice t) (ivs: S.slice t)
                    (ctr: SZ.t) (last: bool)
                    (#v0: erased (Seq.seq t))
                    (#ph: perm) (#vh: erased (Seq.seq t))
                    (#pi: perm) (#vi: erased (Seq.seq t))
requires S.pts_to vv v0 ** S.pts_to h #ph vh ** S.pts_to ivs #pi vi **
         pure (Seq.length v0 == 16 /\ Seq.length vh == 8 /\ Seq.length vi == 8 /\
               SZ.v ctr < pow2 64 /\ reveal vi == G.reveal p.iv)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 ** S.pts_to h #ph vh ** S.pts_to ivs #pi vi **
  pure (Seq.length vh == 8 /\ Seq.length v1 == 16 /\
        v1 == init_vector p (reveal vh) (SZ.v ctr) last)
{
  load_vector vv h ivs;
  sizet_lo_eq #t ctr;
  sizet_hi_eq #t ctr;

  let x12 = S.(vv.(12sz));
  S.(vv.(12sz) <- logxor x12 (of_sizet_lo ctr));
  let x13 = S.(vv.(13sz));
  S.(vv.(13sz) <- logxor x13 (of_sizet_hi ctr));

  if last {
    let x14 = S.(vv.(14sz));
    S.(vv.(14sz) <- lognot x14);
    S.pts_to_len vv;
  } else {
    S.pts_to_len vv;
  }
}

(** The round loop.  [base] is the offset of the current round's sixteen
    entries in the schedule table; it advances by sixteen and wraps at a
    hundred and sixty, which is exactly [16 * (i % 10)] -- BLAKE2b's eleventh
    and twelfth rounds reuse the first and second permutations. *)
#push-options "--z3rlimit 600 --fuel 1 --ifuel 0"

fn rounds_impl (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (vv: S.slice t) (m: S.slice t) (sg: S.slice SZ.t)
               (#v0: erased (Seq.seq t))
               (#pm: perm) (#vm: erased (Seq.seq t))
               (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires S.pts_to vv v0 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
         pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ sigma_ok vs)
ensures exists* (v1: Seq.seq t). S.pts_to vv v1 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
  pure (Seq.length v0 == 16 /\ Seq.length vm == 16 /\ Seq.length v1 == 16 /\
        v1 == rounds_upto p (reveal vm) (reveal v0) (rounds p))
{
  S.pts_to_len vv;
  S.pts_to_len m;

  let nr = p.nrounds;
  let mut i = 0sz;
  let mut base = 0sz;

  while (let vi = !i; SZ.lt vi nr)
  invariant exists* (vi: SZ.t) (vb: SZ.t) (v1: Seq.seq t).
    pts_to i vi ** pts_to base vb ** S.pts_to vv v1 ** S.pts_to m #pm vm ** S.pts_to sg #ps vs **
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
                  (h: S.slice t) (vv: S.slice t)
                  (#vh: erased (Seq.seq t))
                  (#pv: perm) (#v4: erased (Seq.seq t))
requires S.pts_to h vh ** S.pts_to vv #pv v4 **
         pure (Seq.length vh == 8 /\ Seq.length v4 == 16)
ensures exists* (vh': Seq.seq t). S.pts_to h vh' ** S.pts_to vv #pv v4 **
  pure (Seq.length vh == 8 /\ Seq.length v4 == 16 /\ Seq.length vh' == 8 /\
        vh' == mix_state #t (reveal vh) (reveal v4))
{
  S.pts_to_len h;
  S.pts_to_len vv;

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vc: Seq.seq t).
    pts_to i vi ** S.pts_to h vc ** S.pts_to vv #pv v4 **
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
    let a = S.(h.(vi));
    let b = S.(vv.(vi));
    let c = S.(vv.(SZ.add vi 8sz));
    S.(h.(vi) <- logxor (logxor a b) c);
    i := SZ.add vi 1sz;
  };

  with vc. assert (S.pts_to h vc);
  assert (pure (Seq.equal vc (mix_state #t (reveal vh) (reveal v4))));
}

(** [Spec.Blake2.compress]: the state [h] is updated in place, using [vv] as
    scratch. *)
fn compress_impl (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (h: S.slice t) (m: S.slice t) (vv: S.slice t) (ivs: S.slice t)
                 (sg: S.slice SZ.t) (ctr: SZ.t) (last: bool)
                 (#vh: erased (Seq.seq t))
                 (#v0: erased (Seq.seq t))
                 (#pm: perm) (#vm: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#ps: perm) (#vs: erased (Seq.seq SZ.t))
requires S.pts_to h vh ** S.pts_to m #pm vm ** S.pts_to vv v0 **
         S.pts_to ivs #pi vi ** S.pts_to sg #ps vs **
         pure (Seq.length vh == 8 /\ Seq.length vm == 16 /\ Seq.length v0 == 16 /\
               Seq.length vi == 8 /\ sigma_ok vs /\
               SZ.v ctr < pow2 64 /\ reveal vi == G.reveal p.iv)
ensures exists* (vh': Seq.seq t) (v1: Seq.seq t).
  S.pts_to h vh' ** S.pts_to m #pm vm ** S.pts_to vv v1 **
  S.pts_to ivs #pi vi ** S.pts_to sg #ps vs **
  pure (Seq.length vh == 8 /\ Seq.length vm == 16 /\ Seq.length v1 == 16 /\
        Seq.length vh' == 8 /\
        vh' == compress p (reveal vh) (reveal vm) (SZ.v ctr) last)
{
  init_vector_impl p vv h ivs ctr last;
  rounds_impl p vv m sg;
  mix_state_impl h vv;
}

#pop-options
