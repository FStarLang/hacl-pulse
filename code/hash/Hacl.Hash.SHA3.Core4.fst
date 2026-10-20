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

(** Four Keccak-f[1600] permutations at once, with AVX2.

    Each of the twenty-five lanes of the state is one 256-bit vector holding
    that lane of four independent states, one per sixty-four-bit word.
    Keccak-f is nothing but xors, and-nots and rotations by constants, all of
    which act word by word, so the four-way round is the scalar round of
    [Hacl.Hash.SHA3.Core] with every operation replaced by its vector
    counterpart: [Hacl.Vec256.Lane64.xor64], [andnot64] and [rotl64].

    {b The specification is the scalar one, four times.}  [col vs k] is the
    [k]th state a vector state holds, read off one word of every lane; each
    step below is specified as [col vst k == step (col vst0 k)] for every
    [k], and is proved one lane at a time against the same index lemmas the
    scalar steps use.  There is no new model of Keccak.

    {b The interface is four ordinary states.}  [permute4] takes four
    twenty-five-word arrays, the same ones the scalar sponge works on, packs
    them into vectors, runs the twenty-four rounds, and unpacks them again.
    Its postcondition is the scalar [permute] on each.  A caller that runs
    four sponges in lock step replaces four calls to
    [Hacl.Hash.SHA3.Core.permute_impl] by one call to [permute4] and changes
    nothing else; packing and unpacking cost about a tenth of what the four
    scalar permutations would have.

    [permute4] is the only function here that is not
    [inline_for_extraction]; it carries the AVX2 target, and its callers
    must check [Hacl.Vec256.supported] first. *)
module Hacl.Hash.SHA3.Core4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S64 = Hacl.Secret.UInt64
module U32 = FStar.UInt32
module Loops = Hacl.Spec.Loops
module Mem = Hacl.Mem
module V = Hacl.Vec256
module L = Hacl.Vec256.Lane64

(** {2 The four states a vector state holds} *)

let col (vs: Seq.seq V.t { Seq.length vs == 25 }) (k: nat { k < 4 }) : GTot state =
  Seq.init_ghost 25 (fun i -> L.lane_s (Seq.index vs i) k)

let col_index (vs: Seq.seq V.t { Seq.length vs == 25 }) (k: nat { k < 4 }) (i: nat { i < 25 })
  : Lemma (Seq.index (col vs k) i == L.lane_s (Seq.index vs i) k)
          [SMTPat (Seq.index (col vs k) i)]
  = ()

(** Two vector states hold the same [k]th state when every lane agrees. *)
(** Each step is proved one lane at a time against an opaque prefix
    predicate, so that a Pulse verification condition sees twenty-five
    applications of an uninterpreted symbol rather than twenty-five nested
    quantifiers over four states each.  The lemmas that open the
    predicates are pure F*, with nothing else in their context. *)

let col_eq (vs: Seq.seq V.t { Seq.length vs == 25 }) (k: nat { k < 4 }) (s: state)
  : Lemma (requires forall (m: nat). m < 25 ==> L.lane_s (Seq.index vs m) k == Seq.index s m)
          (ensures col vs k == s)
  = assert (Seq.equal (col vs k) s)

let unfold_repeati4 (vs: Seq.seq V.t { Seq.length vs == 25 }) (n: nat)
  : Lemma (forall (k: nat). k < 4 ==>
             Loops.repeati (n + 1) round (col vs k) == round n (Loops.repeati n round (col vs k)))
  = introduce forall (k: nat). k < 4 ==>
      Loops.repeati (n + 1) round (col vs k) == round n (Loops.repeati n round (col vs k))
    with introduce _ ==> _ with Loops.unfold_repeati n round (col vs k)

(** {2 Rotation by a literal}

    As in the scalar code, rho's one zero offset is a branch on a literal,
    which folds away. *)

inline_for_extraction
let rotl4 (x: V.t) (k: U32.t { U32.v k < 64 })
  : (y: V.t { forall (j: nat). j < 4 ==> L.lane_s y j == rotl (L.lane_s x j) (U32.v k) })
  = if k = 0ul then x else (U32.uv_inv k; L.rotl64 x k)

(** {2 theta} *)

(** [c] holds column [x]'s parity, in all four states. *)
[@@"opaque_to_smt"]
let c_ok (vs: Seq.seq V.t { Seq.length vs == 25 }) (x: nat { x < 5 }) (c: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s c k == theta_c (col vs k) x

(** [d] holds what theta folds into column [x], in all four states. *)
[@@"opaque_to_smt"]
let d_ok (vs: Seq.seq V.t { Seq.length vs == 25 }) (x: nat { x < 5 }) (d: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s d k == theta_d (col vs k) x

(** The first [i] lanes of [vs] are theta's. *)
[@@"opaque_to_smt"]
let theta_pre (vs vs0: Seq.seq V.t) (i: nat) : prop =
  Seq.length vs == 25 /\ Seq.length vs0 == 25 /\
  (forall (k: nat) (m: nat). k < 4 /\ m < i /\ m < 25 ==>
     L.lane_s (Seq.index vs m) k == Seq.index (theta (col vs0 k)) m)

inline_for_extraction
let parity4 (a0 a1 a2 a3 a4: V.t) : V.t =
  L.xor64 (L.xor64 (L.xor64 (L.xor64 a0 a1) a2) a3) a4

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let parity4_ok (vs: Seq.seq V.t { Seq.length vs == 25 }) (x: nat { x < 5 })
  : Lemma (c_ok vs x (parity4 (Seq.index vs x) (Seq.index vs (x + 5)) (Seq.index vs (x + 10))
                              (Seq.index vs (x + 15)) (Seq.index vs (x + 20))))
  = reveal_opaque (`%c_ok) (c_ok vs x);
    let c = parity4 (Seq.index vs x) (Seq.index vs (x + 5)) (Seq.index vs (x + 10))
                    (Seq.index vs (x + 15)) (Seq.index vs (x + 20)) in
    introduce forall (k: nat). k < 4 ==> L.lane_s c k == theta_c (col vs k) x
    with introduce _ ==> _ with theta_c_eq (col vs k) x

let d_ok_intro (vs: Seq.seq V.t { Seq.length vs == 25 }) (x: nat { x < 5 })
               (xm xp: (y: nat { y < 5 })) (cm cp: V.t)
  : Lemma (requires xm == (x + 4) % 5 /\ xp == (x + 1) % 5 /\ c_ok vs xm cm /\ c_ok vs xp cp)
          (ensures d_ok vs x (L.xor64 cm (rotl4 cp 1ul)))
  = reveal_opaque (`%c_ok) (c_ok vs xm);
    reveal_opaque (`%c_ok) (c_ok vs xp);
    reveal_opaque (`%d_ok) (d_ok vs x)

let theta_pre_zero (vs vs0: Seq.seq V.t)
  : Lemma (requires Seq.length vs == 25 /\ Seq.length vs0 == 25)
          (ensures theta_pre vs vs0 0)
  = reveal_opaque (`%theta_pre) (theta_pre vs vs0 0)

let theta_pre_step (vs vs0: Seq.seq V.t) (i: nat { i < 25 }) (d: V.t)
  : Lemma (requires theta_pre vs vs0 i /\ Seq.length vs0 == 25 /\ d_ok vs0 (i % 5) d)
          (ensures Seq.length vs == 25 /\
                   theta_pre (Seq.upd vs i (L.xor64 (Seq.index vs0 i) d)) vs0 (i + 1))
  = reveal_opaque (`%theta_pre) (theta_pre vs vs0 i);
    reveal_opaque (`%theta_pre) (theta_pre (Seq.upd vs i (L.xor64 (Seq.index vs0 i) d)) vs0 (i + 1));
    reveal_opaque (`%d_ok) (d_ok vs0 (i % 5));
    introduce forall (k: nat). k < 4 ==>
      Seq.index (theta (col vs0 k)) i == S64.logxor (L.lane_s (Seq.index vs0 i) k) (theta_d (col vs0 k) (i % 5))
    with introduce _ ==> _ with theta_index (col vs0 k) i

let theta_pre_done (vs vs0: Seq.seq V.t)
  : Lemma (requires theta_pre vs vs0 25)
          (ensures Seq.length vs == 25 /\ Seq.length vs0 == 25 /\
                   (forall (k: nat). k < 4 ==> col vs k == theta (col vs0 k)))
  = reveal_opaque (`%theta_pre) (theta_pre vs vs0 25);
    introduce forall (k: nat). k < 4 ==> col vs k == theta (col vs0 k)
    with introduce _ ==> _ with col_eq vs k (theta (col vs0 k))

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

inline_for_extraction
fn theta4_lane (st: A.array V.t) (vst0: erased (Seq.seq V.t))
               (i: SZ.t) (a: V.t) (d: V.t)
               (#vst: erased (Seq.seq V.t))
requires A.pts_to st vst **
         pure (Seq.length vst0 == 25 /\ SZ.v i < 25 /\
               a == Seq.index vst0 (SZ.v i) /\ d_ok vst0 (SZ.v i % 5) d /\
               theta_pre vst vst0 (SZ.v i))
ensures exists* (vst': Seq.seq V.t).
  A.pts_to st vst' ** pure (theta_pre vst' vst0 (SZ.v i + 1))
{
  theta_pre_step vst vst0 (SZ.v i) d;
  A.pts_to_len st;
  A.((st.(i) <- L.xor64 a d));
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
fn theta4_impl (st: A.array V.t) (#vst0: erased (Seq.seq V.t))
requires A.pts_to st vst0 ** pure (Seq.length vst0 == 25)
ensures exists* (vst: Seq.seq V.t).
  A.pts_to st vst **
  pure (theta_pre vst vst0 25)
{
  A.pts_to_len st;
  let s00 = A.(st.(0sz));
  let s01 = A.(st.(1sz));
  let s02 = A.(st.(2sz));
  let s03 = A.(st.(3sz));
  let s04 = A.(st.(4sz));
  let s05 = A.(st.(5sz));
  let s06 = A.(st.(6sz));
  let s07 = A.(st.(7sz));
  let s08 = A.(st.(8sz));
  let s09 = A.(st.(9sz));
  let s10 = A.(st.(10sz));
  let s11 = A.(st.(11sz));
  let s12 = A.(st.(12sz));
  let s13 = A.(st.(13sz));
  let s14 = A.(st.(14sz));
  let s15 = A.(st.(15sz));
  let s16 = A.(st.(16sz));
  let s17 = A.(st.(17sz));
  let s18 = A.(st.(18sz));
  let s19 = A.(st.(19sz));
  let s20 = A.(st.(20sz));
  let s21 = A.(st.(21sz));
  let s22 = A.(st.(22sz));
  let s23 = A.(st.(23sz));
  let s24 = A.(st.(24sz));
  let c0 = parity4 s00 s05 s10 s15 s20;
  let c1 = parity4 s01 s06 s11 s16 s21;
  let c2 = parity4 s02 s07 s12 s17 s22;
  let c3 = parity4 s03 s08 s13 s18 s23;
  let c4 = parity4 s04 s09 s14 s19 s24;
  parity4_ok vst0 0;
  parity4_ok vst0 1;
  parity4_ok vst0 2;
  parity4_ok vst0 3;
  parity4_ok vst0 4;
  let d0 = L.xor64 c4 (rotl4 c1 1ul);
  d_ok_intro vst0 0 4 1 c4 c1;
  let d1 = L.xor64 c0 (rotl4 c2 1ul);
  d_ok_intro vst0 1 0 2 c0 c2;
  let d2 = L.xor64 c1 (rotl4 c3 1ul);
  d_ok_intro vst0 2 1 3 c1 c3;
  let d3 = L.xor64 c2 (rotl4 c4 1ul);
  d_ok_intro vst0 3 2 4 c2 c4;
  let d4 = L.xor64 c3 (rotl4 c0 1ul);
  d_ok_intro vst0 4 3 0 c3 c0;
  theta_pre_zero vst0 vst0;
  theta4_lane st vst0 0sz s00 d0;
  theta4_lane st vst0 1sz s01 d1;
  theta4_lane st vst0 2sz s02 d2;
  theta4_lane st vst0 3sz s03 d3;
  theta4_lane st vst0 4sz s04 d4;
  theta4_lane st vst0 5sz s05 d0;
  theta4_lane st vst0 6sz s06 d1;
  theta4_lane st vst0 7sz s07 d2;
  theta4_lane st vst0 8sz s08 d3;
  theta4_lane st vst0 9sz s09 d4;
  theta4_lane st vst0 10sz s10 d0;
  theta4_lane st vst0 11sz s11 d1;
  theta4_lane st vst0 12sz s12 d2;
  theta4_lane st vst0 13sz s13 d3;
  theta4_lane st vst0 14sz s14 d4;
  theta4_lane st vst0 15sz s15 d0;
  theta4_lane st vst0 16sz s16 d1;
  theta4_lane st vst0 17sz s17 d2;
  theta4_lane st vst0 18sz s18 d3;
  theta4_lane st vst0 19sz s19 d4;
  theta4_lane st vst0 20sz s20 d0;
  theta4_lane st vst0 21sz s21 d1;
  theta4_lane st vst0 22sz s22 d2;
  theta4_lane st vst0 23sz s23 d3;
  theta4_lane st vst0 24sz s24 d4;
}

#pop-options

(** {2 rho and pi} *)

(** The first [i] lanes of [vb] are rho-pi's of [vs]. *)
[@@"opaque_to_smt"]
let rho_pre (vb vs: Seq.seq V.t) (i: nat) : prop =
  Seq.length vb == 25 /\ Seq.length vs == 25 /\
  (forall (k: nat) (m: nat). k < 4 /\ m < i /\ m < 25 ==>
     L.lane_s (Seq.index vb m) k == Seq.index (rho_pi (col vs k)) m)

#push-options "--z3rlimit 100"

let rho_pre_zero (vb vs: Seq.seq V.t)
  : Lemma (requires Seq.length vb == 25 /\ Seq.length vs == 25)
          (ensures rho_pre vb vs 0)
  = reveal_opaque (`%rho_pre) (rho_pre vb vs 0)

[@@"opaque_to_smt"]
let rho_ok (i: nat { i < 25 }) (j: nat { j < 25 }) (r: U32.t) : prop = j == rho_pi_src i /\ U32.v r == rotc j

let rho_lane_new (vs: Seq.seq V.t { Seq.length vs == 25 }) (i: nat { i < 25 }) (j: nat { j < 25 })
                 (r: U32.t { U32.v r < 64 }) (k: nat { k < 4 })
  : Lemma (requires rho_ok i j r)
          (ensures L.lane_s (rotl4 (Seq.index vs j) r) k == Seq.index (rho_pi (col vs k)) i)
  = reveal_opaque (`%rho_ok) (rho_ok i j r);
    rho_pi_index (col vs k) i;
    col_index vs k j

let rho_lane_old (vb vs: Seq.seq V.t) (i: nat { i < 25 }) (y: V.t) (k: nat { k < 4 })
                 (m: nat { m < i })
  : Lemma (requires rho_pre vb vs i)
          (ensures Seq.length vb == 25 /\ Seq.length vs == 25 /\
                   L.lane_s (Seq.index (Seq.upd vb i y) m) k == Seq.index (rho_pi (col vs k)) m)
  = reveal_opaque (`%rho_pre) (rho_pre vb vs i)

let rho_pre_len (vb vs: Seq.seq V.t) (i: nat)
  : Lemma (requires rho_pre vb vs i) (ensures Seq.length vb == 25 /\ Seq.length vs == 25)
  = reveal_opaque (`%rho_pre) (rho_pre vb vs i)

(** [y] is lane [i] of rho-pi of [vs], in all four states. *)
[@@"opaque_to_smt"]
let rho_new (vs: Seq.seq V.t { Seq.length vs == 25 }) (i: nat { i < 25 }) (y: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s y k == Seq.index (rho_pi (col vs k)) i

let rho_new_intro (vs: Seq.seq V.t { Seq.length vs == 25 }) (i: nat { i < 25 })
                  (j: nat { j < 25 }) (r: U32.t { U32.v r < 64 })
  : Lemma (requires rho_ok i j r) (ensures rho_new vs i (rotl4 (Seq.index vs j) r))
  = introduce forall (k: nat). k < 4 ==>
      L.lane_s (rotl4 (Seq.index vs j) r) k == Seq.index (rho_pi (col vs k)) i
    with introduce _ ==> _ with rho_lane_new vs i j r k;
    reveal_opaque (`%rho_new) (rho_new vs i (rotl4 (Seq.index vs j) r))

let rho_new_lane (vs: Seq.seq V.t { Seq.length vs == 25 }) (i: nat { i < 25 }) (y: V.t)
                 (k: nat { k < 4 })
  : Lemma (requires rho_new vs i y)
          (ensures L.lane_s y k == Seq.index (rho_pi (col vs k)) i)
  = reveal_opaque (`%rho_new) (rho_new vs i y)

let rho_pre_upd (vb vs: Seq.seq V.t) (i: nat { i < 25 }) (y: V.t)
  : Lemma (requires rho_pre vb vs i /\ Seq.length vs == 25 /\ rho_new vs i y)
          (ensures Seq.length vb == 25 /\ rho_pre (Seq.upd vb i y) vs (i + 1))
  = rho_pre_len vb vs i;
    let vb' = Seq.upd vb i y in
    introduce forall (k: nat) (m: nat). k < 4 /\ m < i + 1 /\ m < 25 ==>
      L.lane_s (Seq.index vb' m) k == Seq.index (rho_pi (col vs k)) m
    with introduce _ ==> _ with begin
      if m < i then rho_lane_old vb vs i y k m else rho_new_lane vs i y k
    end;
    reveal_opaque (`%rho_pre) (rho_pre vb' vs (i + 1))

let rho_pre_step (vb vs: Seq.seq V.t) (i: nat { i < 25 }) (j: nat { j < 25 })
                 (r: U32.t { U32.v r < 64 })
  : Lemma (requires rho_pre vb vs i /\ Seq.length vs == 25 /\
                    j == rho_pi_src i /\ U32.v r == rotc j)
          (ensures Seq.length vb == 25 /\
                   rho_pre (Seq.upd vb i (rotl4 (Seq.index vs j) r)) vs (i + 1))
  = reveal_opaque (`%rho_ok) (rho_ok i j r);
    rho_pre_len vb vs i;
    rho_new_intro vs i j r;
    rho_pre_upd vb vs i (rotl4 (Seq.index vs j) r)

let rho_pre_done (vb vs: Seq.seq V.t)
  : Lemma (requires rho_pre vb vs 25)
          (ensures Seq.length vb == 25 /\ Seq.length vs == 25 /\
                   (forall (k: nat). k < 4 ==> col vb k == rho_pi (col vs k)))
  = reveal_opaque (`%rho_pre) (rho_pre vb vs 25);
    introduce forall (k: nat). k < 4 ==> col vb k == rho_pi (col vs k)
    with introduce _ ==> _ with col_eq vb k (rho_pi (col vs k))

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

inline_for_extraction
fn rho_pi4_lane (st: A.array V.t) (b: A.array V.t) (i: SZ.t) (j: SZ.t) (k: U32.t)
                (#pst: perm) (#vst: erased (Seq.seq V.t)) (#vb: erased (Seq.seq V.t))
requires A.pts_to st #pst vst ** A.pts_to b vb **
         pure (Seq.length vst == 25 /\
               SZ.v i < 25 /\ SZ.v j < 25 /\ U32.v k < 64 /\
               SZ.v j == rho_pi_src (SZ.v i) /\ U32.v k == rotc (SZ.v j) /\
               rho_pre vb vst (SZ.v i))
ensures exists* (vb': Seq.seq V.t).
  A.pts_to st #pst vst ** A.pts_to b vb' ** pure (rho_pre vb' vst (SZ.v i + 1))
{
  rho_pre_step vb vst (SZ.v i) (SZ.v j) k;
  A.pts_to_len st;
  A.pts_to_len b;
  let a = A.(st.(j));
  A.((b.(i) <- rotl4 a k));
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
fn rho_pi4_impl (st: A.array V.t) (b: A.array V.t)
                (#pst: perm) (#vst: erased (Seq.seq V.t)) (#vb0: erased (Seq.seq V.t))
requires A.pts_to st #pst vst ** A.pts_to b vb0 **
         pure (Seq.length vst == 25 /\ Seq.length vb0 == 25)
ensures exists* (vb: Seq.seq V.t).
  A.pts_to st #pst vst ** A.pts_to b vb **
  pure (rho_pre vb vst 25)
{
  rotc_lit ();
  rho_pre_zero vb0 vst;
  rho_pi4_lane st b 0sz 0sz 0ul;
  rho_pi4_lane st b 1sz 6sz 44ul;
  rho_pi4_lane st b 2sz 12sz 43ul;
  rho_pi4_lane st b 3sz 18sz 21ul;
  rho_pi4_lane st b 4sz 24sz 14ul;
  rho_pi4_lane st b 5sz 3sz 28ul;
  rho_pi4_lane st b 6sz 9sz 20ul;
  rho_pi4_lane st b 7sz 10sz 3ul;
  rho_pi4_lane st b 8sz 16sz 45ul;
  rho_pi4_lane st b 9sz 22sz 61ul;
  rho_pi4_lane st b 10sz 1sz 1ul;
  rho_pi4_lane st b 11sz 7sz 6ul;
  rho_pi4_lane st b 12sz 13sz 25ul;
  rho_pi4_lane st b 13sz 19sz 8ul;
  rho_pi4_lane st b 14sz 20sz 18ul;
  rho_pi4_lane st b 15sz 4sz 27ul;
  rho_pi4_lane st b 16sz 5sz 36ul;
  rho_pi4_lane st b 17sz 11sz 10ul;
  rho_pi4_lane st b 18sz 17sz 15ul;
  rho_pi4_lane st b 19sz 23sz 56ul;
  rho_pi4_lane st b 20sz 2sz 62ul;
  rho_pi4_lane st b 21sz 8sz 55ul;
  rho_pi4_lane st b 22sz 14sz 39ul;
  rho_pi4_lane st b 23sz 15sz 41ul;
  rho_pi4_lane st b 24sz 21sz 2ul;
}

#pop-options

(** {2 chi} *)

(** The first [i] lanes of [vs] are chi's of [vb]. *)
[@@"opaque_to_smt"]
let chi_pre (vs vb: Seq.seq V.t) (i: nat) : prop =
  Seq.length vs == 25 /\ Seq.length vb == 25 /\
  (forall (k: nat) (m: nat). k < 4 /\ m < i /\ m < 25 ==>
     L.lane_s (Seq.index vs m) k == Seq.index (chi (col vb k)) m)

#push-options "--z3rlimit 100"

let chi_pre_zero (vs vb: Seq.seq V.t)
  : Lemma (requires Seq.length vs == 25 /\ Seq.length vb == 25)
          (ensures chi_pre vs vb 0)
  = reveal_opaque (`%chi_pre) (chi_pre vs vb 0)

let chi_pre_len (vs vb: Seq.seq V.t) (i: nat)
  : Lemma (requires chi_pre vs vb i) (ensures Seq.length vs == 25 /\ Seq.length vb == 25)
  = reveal_opaque (`%chi_pre) (chi_pre vs vb i)

let chi_val (vb: Seq.seq V.t { Seq.length vb == 25 }) (i j1 j2: (j: nat { j < 25 })) : V.t =
  L.xor64 (Seq.index vb i) (L.andnot64 (Seq.index vb j1) (Seq.index vb j2))

let chi_lane_new (vb: Seq.seq V.t { Seq.length vb == 25 }) (i j1 j2: (j: nat { j < 25 }))
                 (k: nat { k < 4 })
  : Lemma (requires j1 == idx ((i % 5 + 1) % 5) (i / 5) /\
                    j2 == idx ((i % 5 + 2) % 5) (i / 5))
          (ensures L.lane_s (chi_val vb i j1 j2) k == Seq.index (chi (col vb k)) i)
  = chi_index (col vb k) i;
    col_index vb k i;
    col_index vb k j1;
    col_index vb k j2

let chi_lane_old (vs vb: Seq.seq V.t) (i: nat { i < 25 }) (y: V.t) (k: nat { k < 4 })
                 (m: nat { m < i })
  : Lemma (requires chi_pre vs vb i)
          (ensures Seq.length vs == 25 /\ Seq.length vb == 25 /\
                   L.lane_s (Seq.index (Seq.upd vs i y) m) k == Seq.index (chi (col vb k)) m)
  = reveal_opaque (`%chi_pre) (chi_pre vs vb i)

[@@"opaque_to_smt"]
let chi_new (vb: Seq.seq V.t { Seq.length vb == 25 }) (i: nat { i < 25 }) (y: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s y k == Seq.index (chi (col vb k)) i

let chi_new_intro (vb: Seq.seq V.t { Seq.length vb == 25 }) (i j1 j2: (j: nat { j < 25 }))
  : Lemma (requires j1 == idx ((i % 5 + 1) % 5) (i / 5) /\
                    j2 == idx ((i % 5 + 2) % 5) (i / 5))
          (ensures chi_new vb i (chi_val vb i j1 j2))
  = introduce forall (k: nat). k < 4 ==>
      L.lane_s (chi_val vb i j1 j2) k == Seq.index (chi (col vb k)) i
    with introduce _ ==> _ with chi_lane_new vb i j1 j2 k;
    reveal_opaque (`%chi_new) (chi_new vb i (chi_val vb i j1 j2))

let chi_new_lane (vb: Seq.seq V.t { Seq.length vb == 25 }) (i: nat { i < 25 }) (y: V.t)
                 (k: nat { k < 4 })
  : Lemma (requires chi_new vb i y)
          (ensures L.lane_s y k == Seq.index (chi (col vb k)) i)
  = reveal_opaque (`%chi_new) (chi_new vb i y)

let chi_pre_upd (vs vb: Seq.seq V.t) (i: nat { i < 25 }) (y: V.t)
  : Lemma (requires chi_pre vs vb i /\ Seq.length vb == 25 /\ chi_new vb i y)
          (ensures Seq.length vs == 25 /\ chi_pre (Seq.upd vs i y) vb (i + 1))
  = chi_pre_len vs vb i;
    let vs' = Seq.upd vs i y in
    introduce forall (k: nat) (m: nat). k < 4 /\ m < i + 1 /\ m < 25 ==>
      L.lane_s (Seq.index vs' m) k == Seq.index (chi (col vb k)) m
    with introduce _ ==> _ with begin
      if m < i then chi_lane_old vs vb i y k m else chi_new_lane vb i y k
    end;
    reveal_opaque (`%chi_pre) (chi_pre vs' vb (i + 1))

let chi_pre_step (vs vb: Seq.seq V.t) (i: nat { i < 25 }) (j1 j2: (j: nat { j < 25 }))
  : Lemma (requires chi_pre vs vb i /\ Seq.length vb == 25 /\
                    j1 == idx ((i % 5 + 1) % 5) (i / 5) /\
                    j2 == idx ((i % 5 + 2) % 5) (i / 5))
          (ensures Seq.length vs == 25 /\
                   chi_pre (Seq.upd vs i (chi_val vb i j1 j2)) vb (i + 1))
  = chi_new_intro vb i j1 j2;
    chi_pre_upd vs vb i (chi_val vb i j1 j2)

let chi_pre_done (vs vb: Seq.seq V.t)
  : Lemma (requires chi_pre vs vb 25)
          (ensures Seq.length vs == 25 /\ Seq.length vb == 25 /\
                   (forall (k: nat). k < 4 ==> col vs k == chi (col vb k)))
  = reveal_opaque (`%chi_pre) (chi_pre vs vb 25);
    introduce forall (k: nat). k < 4 ==> col vs k == chi (col vb k)
    with introduce _ ==> _ with col_eq vs k (chi (col vb k))

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

inline_for_extraction
fn chi4_lane (b: A.array V.t) (st: A.array V.t) (i: SZ.t) (j1: SZ.t) (j2: SZ.t)
             (#pb: perm) (#vb: erased (Seq.seq V.t)) (#vst: erased (Seq.seq V.t))
requires A.pts_to b #pb vb ** A.pts_to st vst **
         pure (Seq.length vb == 25 /\
               SZ.v i < 25 /\ SZ.v j1 < 25 /\ SZ.v j2 < 25 /\
               SZ.v j1 == idx ((SZ.v i % 5 + 1) % 5) (SZ.v i / 5) /\
               SZ.v j2 == idx ((SZ.v i % 5 + 2) % 5) (SZ.v i / 5) /\
               chi_pre vst vb (SZ.v i))
ensures exists* (vst': Seq.seq V.t).
  A.pts_to b #pb vb ** A.pts_to st vst' ** pure (chi_pre vst' vb (SZ.v i + 1))
{
  chi_pre_step vst vb (SZ.v i) (SZ.v j1) (SZ.v j2);
  A.pts_to_len b;
  A.pts_to_len st;
  let a0 = A.(b.(i));
  let a1 = A.(b.(j1));
  let a2 = A.(b.(j2));
  A.((st.(i) <- L.xor64 a0 (L.andnot64 a1 a2)));
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
fn chi4_impl (b: A.array V.t) (st: A.array V.t)
             (#pb: perm) (#vb: erased (Seq.seq V.t)) (#vst0: erased (Seq.seq V.t))
requires A.pts_to b #pb vb ** A.pts_to st vst0 **
         pure (Seq.length vb == 25 /\ Seq.length vst0 == 25)
ensures exists* (vst: Seq.seq V.t).
  A.pts_to b #pb vb ** A.pts_to st vst **
  pure (chi_pre vst vb 25)
{
  chi_pre_zero vst0 vb;
  chi4_lane b st 0sz 1sz 2sz;
  chi4_lane b st 1sz 2sz 3sz;
  chi4_lane b st 2sz 3sz 4sz;
  chi4_lane b st 3sz 4sz 0sz;
  chi4_lane b st 4sz 0sz 1sz;
  chi4_lane b st 5sz 6sz 7sz;
  chi4_lane b st 6sz 7sz 8sz;
  chi4_lane b st 7sz 8sz 9sz;
  chi4_lane b st 8sz 9sz 5sz;
  chi4_lane b st 9sz 5sz 6sz;
  chi4_lane b st 10sz 11sz 12sz;
  chi4_lane b st 11sz 12sz 13sz;
  chi4_lane b st 12sz 13sz 14sz;
  chi4_lane b st 13sz 14sz 10sz;
  chi4_lane b st 14sz 10sz 11sz;
  chi4_lane b st 15sz 16sz 17sz;
  chi4_lane b st 16sz 17sz 18sz;
  chi4_lane b st 17sz 18sz 19sz;
  chi4_lane b st 18sz 19sz 15sz;
  chi4_lane b st 19sz 15sz 16sz;
  chi4_lane b st 20sz 21sz 22sz;
  chi4_lane b st 21sz 22sz 23sz;
  chi4_lane b st 22sz 23sz 24sz;
  chi4_lane b st 23sz 24sz 20sz;
  chi4_lane b st 24sz 20sz 21sz;
}

#pop-options

(** {2 One round, and the permutation} *)

(** iota on lane zero: the round constant broadcast to all four states. *)
let iota4 (n: nat { n < 24 }) (v1: Seq.seq V.t { Seq.length v1 == 25 }) (x: V.t)
  : Lemma (requires forall (j: nat). j < 4 ==>
             L.lane_s x j == S64.logxor (L.lane_s (Seq.index v1 0) j) (Seq.index rc n))
          (ensures forall (k: nat). k < 4 ==> col (Seq.upd v1 0 x) k == iota n (col v1 k))
  = introduce forall (k: nat). k < 4 ==> col (Seq.upd v1 0 x) k == iota n (col v1 k)
    with introduce _ ==> _ with
      assert (Seq.equal (col (Seq.upd v1 0 x) k) (iota n (col v1 k)))

(** [vst] is round [n] of [vst0] in all four states, and the first [n]
    rounds; opaque for the same reason as the step predicates. *)
[@@"opaque_to_smt"]
let round_ok (vst vst0: Seq.seq V.t) (n: nat) : prop =
  Seq.length vst == 25 /\ Seq.length vst0 == 25 /\
  (forall (k: nat). k < 4 ==> col vst k == round n (col vst0 k))

[@@"opaque_to_smt"]
let rounds_ok (vst vst0: Seq.seq V.t) (n: nat) : prop =
  Seq.length vst == 25 /\ Seq.length vst0 == 25 /\
  (forall (k: nat). k < 4 ==> col vst k == Loops.repeati n round (col vst0 k))

let rounds_ok_zero (vst0: Seq.seq V.t)
  : Lemma (requires Seq.length vst0 == 25) (ensures rounds_ok vst0 vst0 0)
  = introduce forall (k: nat). k < 4 ==> col vst0 k == Loops.repeati 0 round (col vst0 k)
    with introduce _ ==> _ with Loops.repeati_zero round (col vst0 k);
    reveal_opaque (`%rounds_ok) (rounds_ok vst0 vst0 0)

let rounds_ok_step (vst1 vst vst0: Seq.seq V.t) (n: nat)
  : Lemma (requires rounds_ok vst vst0 n /\ round_ok vst1 vst n)
          (ensures rounds_ok vst1 vst0 (n + 1))
  = reveal_opaque (`%rounds_ok) (rounds_ok vst vst0 n);
    reveal_opaque (`%round_ok) (round_ok vst1 vst n);
    unfold_repeati4 vst0 n;
    reveal_opaque (`%rounds_ok) (rounds_ok vst1 vst0 (n + 1))

let rounds_ok_done (vst vst0: Seq.seq V.t) (v0 v1 v2 v3 w0 w1 w2 w3: Seq.seq S64.t)
  : Lemma (requires rounds_ok vst vst0 24 /\ Seq.length vst == 25 /\ Seq.length vst0 == 25 /\
                    col vst0 0 == v0 /\ col vst0 1 == v1 /\
                    col vst0 2 == v2 /\ col vst0 3 == v3 /\
                    w0 == col vst 0 /\ w1 == col vst 1 /\ w2 == col vst 2 /\ w3 == col vst 3)
          (ensures Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
                   Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
                   w0 == permute v0 /\ w1 == permute v1 /\ w2 == permute v2 /\ w3 == permute v3)
  = reveal_opaque (`%rounds_ok) (rounds_ok vst vst0 24)

let rounds_ok_len (vst vst0: Seq.seq V.t) (n: nat)
  : Lemma (requires rounds_ok vst vst0 n)
          (ensures Seq.length vst == 25 /\ Seq.length vst0 == 25)
  = reveal_opaque (`%rounds_ok) (rounds_ok vst vst0 n)

let round4_done (n: nat { n < 24 }) (vst0 vt vr v1: Seq.seq V.t) (x: V.t)
  : Lemma (requires theta_pre vt vst0 25 /\ rho_pre vr vt 25 /\ chi_pre v1 vr 25 /\
                    Seq.length v1 == 25 /\
                    x == L.xor64 (Seq.index v1 0) (V.bcast64 (Seq.index rc n)))
          (ensures round_ok (Seq.upd v1 0 x) vst0 n)
  = theta_pre_done vt vst0;
    rho_pre_done vr vt;
    chi_pre_done v1 vr;
    iota4 n v1 x;
    reveal_opaque (`%round_ok) (round_ok (Seq.upd v1 0 x) vst0 n)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

inline_for_extraction
fn round4_impl (st: A.array V.t) (b: A.array V.t)
               (rc_tbl: A.array S64.t) (n: SZ.t)
               (#vst0: erased (Seq.seq V.t)) (#vb0: erased (Seq.seq V.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ SZ.v n < 24)
ensures exists* (vst: Seq.seq V.t) (vb: Seq.seq V.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
        Seq.length vb == 25 /\ round_ok vst vst0 (SZ.v n))
{
  A.pts_to_len st;
  A.pts_to_len rc_tbl;
  theta4_impl st;
  with vt. assert (A.pts_to st vt);
  A.pts_to_len st;
  A.pts_to_len b;
  rho_pi4_impl st b;
  with vr. assert (A.pts_to b vr);
  A.pts_to_len b;
  chi4_impl b st;
  with v1. assert (A.pts_to st v1);
  chi_pre_len v1 vr 25;
  let x0 = A.(st.(0sz));
  let r = A.(rc_tbl.(n));
  let x = L.xor64 x0 (V.bcast64 r);
  A.((st.(0sz) <- x));
  with v2. assert (A.pts_to st v2);
  assert (pure (x0 == Seq.index v1 0));
  assert (pure (r == Seq.index rc (SZ.v n)));
  assert (pure (v2 == Seq.upd v1 0 x));
  round4_done (SZ.v n) vst0 vt vr v1 x;
  assert (pure (round_ok v2 vst0 (SZ.v n)));
}

#pop-options

(** {2 Packing and unpacking} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

[@@"opaque_to_smt"]
let pack_pre (vst: Seq.seq V.t) (v0 v1 v2 v3: Seq.seq S64.t) (i: nat) : prop =
  Seq.length vst == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
  Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
  (forall (m: nat). m < i /\ m < 25 ==>
     L.lane_s (Seq.index vst m) 0 == Seq.index v0 m /\
     L.lane_s (Seq.index vst m) 1 == Seq.index v1 m /\
     L.lane_s (Seq.index vst m) 2 == Seq.index v2 m /\
     L.lane_s (Seq.index vst m) 3 == Seq.index v3 m)

let pack_pre_zero (vst: Seq.seq V.t) (v0 v1 v2 v3: Seq.seq S64.t)
  : Lemma (requires Seq.length vst == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
                    Seq.length v2 == 25 /\ Seq.length v3 == 25)
          (ensures pack_pre vst v0 v1 v2 v3 0)
  = reveal_opaque (`%pack_pre) (pack_pre vst v0 v1 v2 v3 0)

let pack_pre_len (vst: Seq.seq V.t) (v0 v1 v2 v3: Seq.seq S64.t) (i: nat)
  : Lemma (requires pack_pre vst v0 v1 v2 v3 i)
          (ensures Seq.length vst == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
                   Seq.length v2 == 25 /\ Seq.length v3 == 25)
  = reveal_opaque (`%pack_pre) (pack_pre vst v0 v1 v2 v3 i)

let pack_pre_step (vst: Seq.seq V.t) (v0 v1 v2 v3: Seq.seq S64.t) (i: nat { i < 25 }) (x: V.t)
  : Lemma (requires Seq.length vst == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
                    Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
                    pack_pre vst v0 v1 v2 v3 i /\
                    S64.v (L.lane_s x 0) == S64.v (Seq.index v0 i) /\
                    S64.v (L.lane_s x 1) == S64.v (Seq.index v1 i) /\
                    S64.v (L.lane_s x 2) == S64.v (Seq.index v2 i) /\
                    S64.v (L.lane_s x 3) == S64.v (Seq.index v3 i))
          (ensures Seq.length vst == 25 /\ pack_pre (Seq.upd vst i x) v0 v1 v2 v3 (i + 1))
  = reveal_opaque (`%pack_pre) (pack_pre vst v0 v1 v2 v3 i);
    S64.v_extensional (L.lane_s x 0) (Seq.index v0 i);
    S64.v_extensional (L.lane_s x 1) (Seq.index v1 i);
    S64.v_extensional (L.lane_s x 2) (Seq.index v2 i);
    S64.v_extensional (L.lane_s x 3) (Seq.index v3 i);
    reveal_opaque (`%pack_pre) (pack_pre (Seq.upd vst i x) v0 v1 v2 v3 (i + 1))

let pack_pre_done (vst: Seq.seq V.t) (v0 v1 v2 v3: Seq.seq S64.t)
  : Lemma (requires pack_pre vst v0 v1 v2 v3 25)
          (ensures Seq.length vst == 25 /\
                   col vst 0 == v0 /\ col vst 1 == v1 /\ col vst 2 == v2 /\ col vst 3 == v3)
  = reveal_opaque (`%pack_pre) (pack_pre vst v0 v1 v2 v3 25);
    col_eq vst 0 v0;
    col_eq vst 1 v1;
    col_eq vst 2 v2;
    col_eq vst 3 v3

[@@"opaque_to_smt"]
let unpack_pre (vst: Seq.seq V.t) (w0 w1 w2 w3: Seq.seq S64.t) (i: nat) : prop =
  Seq.length vst == 25 /\ Seq.length w0 == 25 /\ Seq.length w1 == 25 /\
  Seq.length w2 == 25 /\ Seq.length w3 == 25 /\
  (forall (m: nat). m < i /\ m < 25 ==>
     Seq.index w0 m == L.lane_s (Seq.index vst m) 0 /\
     Seq.index w1 m == L.lane_s (Seq.index vst m) 1 /\
     Seq.index w2 m == L.lane_s (Seq.index vst m) 2 /\
     Seq.index w3 m == L.lane_s (Seq.index vst m) 3)

let unpack_pre_zero (vst: Seq.seq V.t) (w0 w1 w2 w3: Seq.seq S64.t)
  : Lemma (requires Seq.length vst == 25 /\ Seq.length w0 == 25 /\ Seq.length w1 == 25 /\
                    Seq.length w2 == 25 /\ Seq.length w3 == 25)
          (ensures unpack_pre vst w0 w1 w2 w3 0)
  = reveal_opaque (`%unpack_pre) (unpack_pre vst w0 w1 w2 w3 0)

let unpack_pre_len (vst: Seq.seq V.t) (w0 w1 w2 w3: Seq.seq S64.t) (i: nat)
  : Lemma (requires unpack_pre vst w0 w1 w2 w3 i)
          (ensures Seq.length vst == 25 /\ Seq.length w0 == 25 /\ Seq.length w1 == 25 /\
                   Seq.length w2 == 25 /\ Seq.length w3 == 25)
  = reveal_opaque (`%unpack_pre) (unpack_pre vst w0 w1 w2 w3 i)

let unpack_pre_step (vst: Seq.seq V.t) (w0 w1 w2 w3: Seq.seq S64.t) (i: nat { i < 25 })
  : Lemma (requires Seq.length vst == 25 /\ Seq.length w0 == 25 /\ Seq.length w1 == 25 /\
                    Seq.length w2 == 25 /\ Seq.length w3 == 25 /\
                    unpack_pre vst w0 w1 w2 w3 i)
          (ensures unpack_pre vst
                     (Seq.upd w0 i (L.lane_s (Seq.index vst i) 0))
                     (Seq.upd w1 i (L.lane_s (Seq.index vst i) 1))
                     (Seq.upd w2 i (L.lane_s (Seq.index vst i) 2))
                     (Seq.upd w3 i (L.lane_s (Seq.index vst i) 3)) (i + 1))
  = reveal_opaque (`%unpack_pre) (unpack_pre vst w0 w1 w2 w3 i);
    let x = Seq.index vst i in
    let w0' = Seq.upd w0 i (L.lane_s x 0) in
    let w1' = Seq.upd w1 i (L.lane_s x 1) in
    let w2' = Seq.upd w2 i (L.lane_s x 2) in
    let w3' = Seq.upd w3 i (L.lane_s x 3) in
    introduce forall (m: nat). m < i + 1 /\ m < 25 ==>
      Seq.index w0' m == L.lane_s (Seq.index vst m) 0 /\
      Seq.index w1' m == L.lane_s (Seq.index vst m) 1 /\
      Seq.index w2' m == L.lane_s (Seq.index vst m) 2 /\
      Seq.index w3' m == L.lane_s (Seq.index vst m) 3
    with introduce _ ==> _ with begin
      if m < i then () else ()
    end;
    reveal_opaque (`%unpack_pre) (unpack_pre vst w0' w1' w2' w3' (i + 1))

let unpack_pre_done (vst: Seq.seq V.t) (w0 w1 w2 w3: Seq.seq S64.t)
  : Lemma (requires unpack_pre vst w0 w1 w2 w3 25)
          (ensures Seq.length vst == 25 /\
                   w0 == col vst 0 /\ w1 == col vst 1 /\ w2 == col vst 2 /\ w3 == col vst 3)
  = reveal_opaque (`%unpack_pre) (unpack_pre vst w0 w1 w2 w3 25);
    assert (Seq.equal w0 (col vst 0));
    assert (Seq.equal w1 (col vst 1));
    assert (Seq.equal w2 (col vst 2));
    assert (Seq.equal w3 (col vst 3))

(** [st[i]] holds lane [i] of each of the four states. *)
inline_for_extraction
fn pack (st: A.array V.t) (s0 s1 s2 s3: A.array S64.t)
        (#vst0: erased (Seq.seq V.t))
        (#v0 #v1 #v2 #v3: erased (Seq.seq S64.t))
requires A.pts_to st vst0 **
         A.pts_to s0 v0 ** A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to s3 v3 **
         pure (Seq.length vst0 == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
               Seq.length v2 == 25 /\ Seq.length v3 == 25)
ensures exists* (vst: Seq.seq V.t).
  A.pts_to st vst **
  A.pts_to s0 v0 ** A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to s3 v3 **
  pure (Seq.length vst == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
        Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
        col vst 0 == reveal v0 /\ col vst 1 == reveal v1 /\
        col vst 2 == reveal v2 /\ col vst 3 == reveal v3)
{
  A.pts_to_len st;
  pack_pre_zero vst0 v0 v1 v2 v3;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq V.t).
    pts_to i vi ** A.pts_to st vst **
    A.pts_to s0 v0 ** A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to s3 v3 **
    pure (SZ.v vi <= 25 /\ Seq.length vst == 25 /\
          Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
          Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
          pack_pre vst v0 v1 v2 v3 (SZ.v vi))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    with vst. assert (A.pts_to st vst);
    let x0 = A.(s0.(vi));
    let x1 = A.(s1.(vi));
    let x2 = A.(s2.(vi));
    let x3 = A.(s3.(vi));
    let x = V.set64 x0 x1 x2 x3;
    assert (pure (S64.v (L.lane_s x 0) == S64.v x0 /\ S64.v (L.lane_s x 1) == S64.v x1 /\
                  S64.v (L.lane_s x 2) == S64.v x2 /\ S64.v (L.lane_s x 3) == S64.v x3));
    pack_pre_step vst v0 v1 v2 v3 (SZ.v vi) x;
    A.((st.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vst. assert (A.pts_to st vst);
  pack_pre_done vst v0 v1 v2 v3;
  assert (pure (Seq.equal (col vst 0) v0 /\ Seq.equal (col vst 1) v1 /\
                Seq.equal (col vst 2) v2 /\ Seq.equal (col vst 3) v3));
}

(** Lane [i] of state [k] back out of [st[i]], through a four-word buffer. *)
inline_for_extraction
fn unpack (st: A.array V.t) (s0 s1 s2 s3: A.array S64.t) (tmp: A.array S64.t)
          (#vst: erased (Seq.seq V.t))
          (#v0 #v1 #v2 #v3: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires A.pts_to st vst **
         A.pts_to s0 v0 ** A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to s3 v3 **
         A.pts_to tmp vt **
         pure (Seq.length vst == 25 /\ Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
               Seq.length v2 == 25 /\ Seq.length v3 == 25 /\ Seq.length vt == 4)
ensures exists* (w0 w1 w2 w3 wt: Seq.seq S64.t).
  A.pts_to st vst **
  A.pts_to s0 w0 ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to s3 w3 **
  A.pts_to tmp wt **
  pure (Seq.length vst == 25 /\ Seq.length wt == 4 /\
        w0 == col vst 0 /\ w1 == col vst 1 /\ w2 == col vst 2 /\ w3 == col vst 3)
{
  A.pts_to_len st;
  A.pts_to_len s0;
  A.pts_to_len s1;
  A.pts_to_len s2;
  A.pts_to_len s3;
  unpack_pre_zero vst v0 v1 v2 v3;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (w0 w1 w2 w3 wt: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst **
    A.pts_to s0 w0 ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to s3 w3 **
    A.pts_to tmp wt **
    pure (SZ.v vi <= 25 /\ Seq.length vst == 25 /\ Seq.length wt == 4 /\
          Seq.length w0 == 25 /\ Seq.length w1 == 25 /\
          Seq.length w2 == 25 /\ Seq.length w3 == 25 /\
          unpack_pre vst w0 w1 w2 w3 (SZ.v vi))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    with w0 w1 w2 w3. assert (A.pts_to s0 w0 ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to s3 w3);
    unpack_pre_step vst w0 w1 w2 w3 (SZ.v vi);
    let x = A.(st.(vi));
    V.store64 tmp x;
    with wt. assert (A.pts_to tmp wt);
    assert (pure (Seq.index wt 0 == L.lane_s x 0 /\ Seq.index wt 1 == L.lane_s x 1 /\
                  Seq.index wt 2 == L.lane_s x 2 /\ Seq.index wt 3 == L.lane_s x 3));
    let y0 = A.(tmp.(0sz));
    let y1 = A.(tmp.(1sz));
    let y2 = A.(tmp.(2sz));
    let y3 = A.(tmp.(3sz));
    A.((s0.(vi) <- y0));
    A.((s1.(vi) <- y1));
    A.((s2.(vi) <- y2));
    A.((s3.(vi) <- y3));
    i := SZ.add vi 1sz;
  };
  with w0 w1 w2 w3. assert (A.pts_to s0 w0 ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to s3 w3);
  unpack_pre_done vst w0 w1 w2 w3;
  assert (pure (Seq.equal w0 (col vst 0) /\ Seq.equal w1 (col vst 1) /\
                Seq.equal w2 (col vst 2) /\ Seq.equal w3 (col vst 3)));
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Twenty-four rounds on the packed state; not unrolled, for the same
    reason as the scalar loop. *)
inline_for_extraction
fn rounds4 (st: A.array V.t) (b: A.array V.t) (rc_tbl: A.array S64.t)
           (#vst0: erased (Seq.seq V.t)) (#vb0: erased (Seq.seq V.t))
           (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
ensures exists* (vst: Seq.seq V.t) (vb: Seq.seq V.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\ Seq.length vb == 25 /\
        rounds_ok vst vst0 24)
{
  rounds_ok_zero vst0;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 24sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq V.t) (vb: Seq.seq V.t).
    pts_to i vi ** A.pts_to st vst ** A.pts_to b vb **
    A.pts_to rc_tbl #prc vrc **
    pure (Seq.length vst0 == 25 /\ SZ.v vi <= 24 /\ Seq.length vst == 25 /\
          Seq.length vb == 25 /\
          rounds_ok vst vst0 (SZ.v vi))
  decreases (24 - SZ.v (!i))
  {
    let vi = !i;
    with vst. assert (A.pts_to st vst);
    round4_impl st b rc_tbl vi;
    with vst1. assert (A.pts_to st vst1);
    rounds_ok_step vst1 vst vst0 (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with vst. assert (A.pts_to st vst);
  rounds_ok_len vst vst0 (SZ.v 24sz);
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Four states, each permuted: [s_k <- permute s_k]. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_prologue "__attribute__((target(\"avx2\")))" ""]
fn permute4 (s0 s1 s2 s3: A.array S64.t) (rc_tbl: A.array S64.t)
            (#v0 #v1 #v2 #v3: erased (Seq.seq S64.t))
            (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to s0 v0 ** A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to s3 v3 **
         A.pts_to rc_tbl #prc vrc **
         pure (Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
               Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
ensures exists* (w0 w1 w2 w3: Seq.seq S64.t).
  A.pts_to s0 w0 ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to s3 w3 **
  A.pts_to rc_tbl #prc vrc **
  pure (Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
        Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
        w0 == permute v0 /\ w1 == permute v1 /\ w2 == permute v2 /\ w3 == permute v3)
{
  let z = V.zero ();
  let mut st = [| z; 25sz |];
  Mem.track st;
  A.pts_to_len st;
  let mut b = [| z; 25sz |];
  Mem.track b;
  A.pts_to_len b;
  let z64 = S64.classify 0uL;
  let mut tmp = [| z64; 4sz |];
  Mem.track tmp;
  A.pts_to_len tmp;
  pack st s0 s1 s2 s3;
  with vp. assert (A.pts_to st vp);
  rounds4 st b rc_tbl;
  with vr. assert (A.pts_to st vr);
  unpack st s0 s1 s2 s3 tmp;
  with w0 w1 w2 w3. assert (A.pts_to s0 w0 ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to s3 w3);
  rounds_ok_done vr vp v0 v1 v2 v3 w0 w1 w2 w3;
  Mem.wipe tmp 4sz;
  Mem.wipe b 25sz;
  Mem.wipe st 25sz;
}

#pop-options
