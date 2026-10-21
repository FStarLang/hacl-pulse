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
    counterpart: [Hacl.Vec256.Lane64.xor64], [andnot64] and [rotl64].  Like
    the scalar round it is fused -- one read of the input, theta's column
    values and the rho-pi lanes in registers, chi and iota written straight
    to the other buffer of a ping-pong pair -- which is 1.35x over doing
    theta, rho-pi and chi as three sweeps of the state.

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

(** {2 theta's column values} *)

(** [c] holds column [x]'s parity, in all four states. *)
[@@"opaque_to_smt"]
let c_ok (vs: Seq.seq V.t { Seq.length vs == 25 }) (x: nat { x < 5 }) (c: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s c k == theta_c (col vs k) x

(** [d] holds what theta folds into column [x], in all four states. *)
[@@"opaque_to_smt"]
let d_ok (vs: Seq.seq V.t { Seq.length vs == 25 }) (x: nat { x < 5 }) (d: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s d k == theta_d (col vs k) x

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

#pop-options

(** {2 The pieces of a fused round} *)

(** [y] holds lane [i] of [rho_pi (theta a)], in all four states. *)
[@@"opaque_to_smt"]
let b_ok (vs: Seq.seq V.t { Seq.length vs == 25 }) (i: nat { i < 25 }) (y: V.t) : prop =
  forall (k: nat). k < 4 ==> L.lane_s y k == Seq.index (rho_pi (theta (col vs k))) i

(** The first [i] lanes of [ve] are round [n] of [va], in all four states. *)
[@@"opaque_to_smt"]
let fr_pre (ve va: Seq.seq V.t) (n: nat) (i: nat) : prop =
  Seq.length ve == 25 /\ Seq.length va == 25 /\ n < 24 /\
  (forall (k: nat) (m: nat). k < 4 /\ m < i /\ m < 25 ==>
     L.lane_s (Seq.index ve m) k == Seq.index (round n (col va k)) m)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let b_ok_intro (vs: Seq.seq V.t { Seq.length vs == 25 }) (i: nat { i < 25 })
               (r: U32.t { U32.v r < 64 }) (s d: V.t)
  : Lemma (requires U32.v r == rotc (rho_pi_src i) /\ s == Seq.index vs (rho_pi_src i) /\
                    d_ok vs (rho_pi_src i % 5) d)
          (ensures b_ok vs i (rotl4 (L.xor64 s d) r))
  = let j = rho_pi_src i in
    reveal_opaque (`%d_ok) (d_ok vs (j % 5) d);
    introduce forall (k: nat). k < 4 ==>
      L.lane_s (rotl4 (L.xor64 s d) r) k == Seq.index (rho_pi (theta (col vs k))) i
    with introduce _ ==> _ with begin
      theta_index (col vs k) j;
      rho_pi_index (theta (col vs k)) i
    end;
    reveal_opaque (`%b_ok) (b_ok vs i (rotl4 (L.xor64 s d) r))

let fr_pre_len (ve va: Seq.seq V.t) (n: nat) (i: nat)
  : Lemma (requires fr_pre ve va n i)
          (ensures Seq.length ve == 25 /\ Seq.length va == 25 /\ n < 24)
  = reveal_opaque (`%fr_pre) (fr_pre ve va n i)

let fr_pre_step (ve va: Seq.seq V.t) (n: nat) (i: nat { 0 < i /\ i < 25 }) (b0 b1 b2: V.t)
  : Lemma (requires fr_pre ve va n i /\ Seq.length va == 25 /\
                    b_ok va i b0 /\
                    b_ok va (idx ((i % 5 + 1) % 5) (i / 5)) b1 /\
                    b_ok va (idx ((i % 5 + 2) % 5) (i / 5)) b2)
          (ensures Seq.length ve == 25 /\
                   fr_pre (Seq.upd ve i (L.xor64 b0 (L.andnot64 b1 b2))) va n (i + 1))
  = reveal_opaque (`%fr_pre) (fr_pre ve va n i);
    let i1 = idx ((i % 5 + 1) % 5) (i / 5) in
    let i2 = idx ((i % 5 + 2) % 5) (i / 5) in
    reveal_opaque (`%b_ok) (b_ok va i b0);
    reveal_opaque (`%b_ok) (b_ok va i1 b1);
    reveal_opaque (`%b_ok) (b_ok va i2 b2);
    introduce forall (k: nat). k < 4 ==>
      L.lane_s (L.xor64 b0 (L.andnot64 b1 b2)) k == Seq.index (round n (col va k)) i
    with introduce _ ==> _ with begin
      chi_index (rho_pi (theta (col va k))) i;
      round_index (col va k) n i
    end;
    let ve' = Seq.upd ve i (L.xor64 b0 (L.andnot64 b1 b2)) in
    introduce forall (k: nat) (m: nat). k < 4 /\ m < i + 1 /\ m < 25 ==>
      L.lane_s (Seq.index ve' m) k == Seq.index (round n (col va k)) m
    with introduce _ ==> _ with begin
      if m < i then () else ()
    end;
    reveal_opaque (`%fr_pre) (fr_pre ve' va n (i + 1))

let bcast_lane (r: S64.t) (k: nat { k < 4 })
  : Lemma (L.lane_s (V.bcast64 r) k == r)
  = L.lane_s_v (V.bcast64 r) k;
    S64.v_extensional (L.lane_s (V.bcast64 r) k) r

let lane0_ok (va: Seq.seq V.t { Seq.length va == 25 }) (n: nat { n < 24 }) (r: S64.t)
             (b0 b1 b2: V.t) (k: nat { k < 4 })
  : Lemma (requires r == Seq.index rc n /\
                    b_ok va 0 b0 /\ b_ok va 1 b1 /\ b_ok va 2 b2)
          (ensures L.lane_s (L.xor64 (L.xor64 b0 (L.andnot64 b1 b2)) (V.bcast64 r)) k ==
                   Seq.index (round n (col va k)) 0)
  = reveal_opaque (`%b_ok) (b_ok va 0 b0);
    reveal_opaque (`%b_ok) (b_ok va 1 b1);
    reveal_opaque (`%b_ok) (b_ok va 2 b2);
    let s = col va k in
    let rp = rho_pi (theta s) in
    bcast_lane r k;
    chi_index rp 0;
    assert_norm (idx ((0 % 5 + 1) % 5) (0 / 5) == 1 /\ idx ((0 % 5 + 2) % 5) (0 / 5) == 2);
    round_index0 s n

let fr_pre_one (ve va: Seq.seq V.t) (n: nat { n < 24 }) (x: V.t)
  : Lemma (requires Seq.length ve == 25 /\ Seq.length va == 25 /\
                    (forall (k: nat). k < 4 ==> L.lane_s x k == Seq.index (round n (col va k)) 0))
          (ensures fr_pre (Seq.upd ve 0 x) va n 1)
  = reveal_opaque (`%fr_pre) (fr_pre (Seq.upd ve 0 x) va n 1)

let fr_pre_step0 (ve va: Seq.seq V.t) (n: nat { n < 24 }) (r: S64.t) (b0 b1 b2: V.t)
  : Lemma (requires Seq.length ve == 25 /\ Seq.length va == 25 /\
                    r == Seq.index rc n /\
                    b_ok va 0 b0 /\ b_ok va 1 b1 /\ b_ok va 2 b2)
          (ensures fr_pre (Seq.upd ve 0 (L.xor64 (L.xor64 b0 (L.andnot64 b1 b2)) (V.bcast64 r)))
                          va n 1)
  = let x = L.xor64 (L.xor64 b0 (L.andnot64 b1 b2)) (V.bcast64 r) in
    introduce forall (k: nat). k < 4 ==> L.lane_s x k == Seq.index (round n (col va k)) 0
    with introduce _ ==> _ with lane0_ok va n r b0 b1 b2 k;
    fr_pre_one ve va n x

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** One lane of [rho_pi (theta a)], from registers; see the scalar
    [Hacl.Hash.SHA3.Core.bval]. *)
inline_for_extraction
fn bval4 (va: erased (Seq.seq V.t)) (i: SZ.t) (s: V.t) (d: V.t) (r: U32.t)
requires pure (Seq.length va == 25 /\ SZ.v i < 25 /\ U32.v r < 64 /\
               s == Seq.index va (rho_pi_src (SZ.v i)) /\
               d_ok va (rho_pi_src (SZ.v i) % 5) d /\
               U32.v r == rotc (rho_pi_src (SZ.v i)))
returns y: V.t
ensures pure (Seq.length va == 25 /\ SZ.v i < 25 /\ b_ok va (SZ.v i) y)
{
  b_ok_intro va (SZ.v i) r s d;
  rotl4 (L.xor64 s d) r
}

(** One output lane other than lane 0. *)
inline_for_extraction
fn chi4_out (e: A.array V.t) (va: erased (Seq.seq V.t)) (n: erased nat)
            (i: SZ.t) (b0: V.t) (b1: V.t) (b2: V.t)
            (#ve: erased (Seq.seq V.t))
requires A.pts_to e ve **
         pure (Seq.length va == 25 /\ 0 < SZ.v i /\ SZ.v i < 25 /\
               b_ok va (SZ.v i) b0 /\
               b_ok va (idx ((SZ.v i % 5 + 1) % 5) (SZ.v i / 5)) b1 /\
               b_ok va (idx ((SZ.v i % 5 + 2) % 5) (SZ.v i / 5)) b2 /\
               fr_pre ve va n (SZ.v i))
ensures exists* (ve': Seq.seq V.t).
  A.pts_to e ve' ** pure (fr_pre ve' va n (SZ.v i + 1))
{
  fr_pre_step ve va n (SZ.v i) b0 b1 b2;
  fr_pre_len ve va n (SZ.v i);
  A.pts_to_len e;
  A.((e.(i) <- L.xor64 b0 (L.andnot64 b1 b2)));
}

(** Lane 0, with iota folded in. *)
inline_for_extraction
fn chi4_out0 (e: A.array V.t) (va: erased (Seq.seq V.t)) (n: erased nat)
             (r: S64.t) (b0: V.t) (b1: V.t) (b2: V.t)
             (#ve: erased (Seq.seq V.t))
requires A.pts_to e ve **
         pure (Seq.length va == 25 /\ Seq.length ve == 25 /\ n < 24 /\
               r == Seq.index rc n /\
               b_ok va 0 b0 /\ b_ok va 1 b1 /\ b_ok va 2 b2)
ensures exists* (ve': Seq.seq V.t).
  A.pts_to e ve' ** pure (fr_pre ve' va n 1)
{
  fr_pre_step0 ve va n r b0 b1 b2;
  A.pts_to_len e;
  A.((e.(0sz) <- L.xor64 (L.xor64 b0 (L.andnot64 b1 b2)) (V.bcast64 r)));
}

#pop-options

(** {2 One round, and the permutation} *)

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

let fr_pre_done (ve va: Seq.seq V.t) (n: nat)
  : Lemma (requires fr_pre ve va n 25)
          (ensures round_ok ve va n)
  = reveal_opaque (`%fr_pre) (fr_pre ve va n 25);
    introduce forall (k: nat). k < 4 ==> col ve k == round n (col va k)
    with introduce _ ==> _ with col_eq ve k (round n (col va k));
    reveal_opaque (`%round_ok) (round_ok ve va n)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** [e] becomes round [n] of [a]; the scalar [fround], four ways. *)
inline_for_extraction
fn fround4 (a: A.array V.t) (e: A.array V.t)
           (rc_tbl: A.array S64.t) (n: SZ.t)
           (#pa: perm) (#va: erased (Seq.seq V.t)) (#ve0: erased (Seq.seq V.t))
           (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to e ve0 ** A.pts_to rc_tbl #prc vrc **
         pure (Seq.length va == 25 /\ Seq.length ve0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ SZ.v n < 24)
ensures exists* (ve: Seq.seq V.t).
  A.pts_to a #pa va ** A.pts_to e ve ** A.pts_to rc_tbl #prc vrc **
  pure (fr_pre ve va (SZ.v n) 25)
{
  A.pts_to_len a;
  A.pts_to_len e;
  A.pts_to_len rc_tbl;
  rotc_lit ();
  rho_pi_src_lit ();
  chi_nbr_lit ();
  let s00 = A.(a.(0sz));
  let s01 = A.(a.(1sz));
  let s02 = A.(a.(2sz));
  let s03 = A.(a.(3sz));
  let s04 = A.(a.(4sz));
  let s05 = A.(a.(5sz));
  let s06 = A.(a.(6sz));
  let s07 = A.(a.(7sz));
  let s08 = A.(a.(8sz));
  let s09 = A.(a.(9sz));
  let s10 = A.(a.(10sz));
  let s11 = A.(a.(11sz));
  let s12 = A.(a.(12sz));
  let s13 = A.(a.(13sz));
  let s14 = A.(a.(14sz));
  let s15 = A.(a.(15sz));
  let s16 = A.(a.(16sz));
  let s17 = A.(a.(17sz));
  let s18 = A.(a.(18sz));
  let s19 = A.(a.(19sz));
  let s20 = A.(a.(20sz));
  let s21 = A.(a.(21sz));
  let s22 = A.(a.(22sz));
  let s23 = A.(a.(23sz));
  let s24 = A.(a.(24sz));
  let c0 = parity4 s00 s05 s10 s15 s20;
  let c1 = parity4 s01 s06 s11 s16 s21;
  let c2 = parity4 s02 s07 s12 s17 s22;
  let c3 = parity4 s03 s08 s13 s18 s23;
  let c4 = parity4 s04 s09 s14 s19 s24;
  parity4_ok va 0;
  parity4_ok va 1;
  parity4_ok va 2;
  parity4_ok va 3;
  parity4_ok va 4;
  let d0 = L.xor64 c4 (rotl4 c1 1ul);
  d_ok_intro va 0 4 1 c4 c1;
  let d1 = L.xor64 c0 (rotl4 c2 1ul);
  d_ok_intro va 1 0 2 c0 c2;
  let d2 = L.xor64 c1 (rotl4 c3 1ul);
  d_ok_intro va 2 1 3 c1 c3;
  let d3 = L.xor64 c2 (rotl4 c4 1ul);
  d_ok_intro va 3 2 4 c2 c4;
  let d4 = L.xor64 c3 (rotl4 c0 1ul);
  d_ok_intro va 4 3 0 c3 c0;
  let b00 = bval4 va 0sz s00 d0 0ul;
  let b01 = bval4 va 1sz s06 d1 44ul;
  let b02 = bval4 va 2sz s12 d2 43ul;
  let b03 = bval4 va 3sz s18 d3 21ul;
  let b04 = bval4 va 4sz s24 d4 14ul;
  let r = A.(rc_tbl.(n));
  chi4_out0 e va (SZ.v n) r b00 b01 b02;
  chi4_out e va (SZ.v n) 1sz b01 b02 b03;
  chi4_out e va (SZ.v n) 2sz b02 b03 b04;
  chi4_out e va (SZ.v n) 3sz b03 b04 b00;
  chi4_out e va (SZ.v n) 4sz b04 b00 b01;
  let b05 = bval4 va 5sz s03 d3 28ul;
  let b06 = bval4 va 6sz s09 d4 20ul;
  let b07 = bval4 va 7sz s10 d0 3ul;
  let b08 = bval4 va 8sz s16 d1 45ul;
  let b09 = bval4 va 9sz s22 d2 61ul;
  chi4_out e va (SZ.v n) 5sz b05 b06 b07;
  chi4_out e va (SZ.v n) 6sz b06 b07 b08;
  chi4_out e va (SZ.v n) 7sz b07 b08 b09;
  chi4_out e va (SZ.v n) 8sz b08 b09 b05;
  chi4_out e va (SZ.v n) 9sz b09 b05 b06;
  let b10 = bval4 va 10sz s01 d1 1ul;
  let b11 = bval4 va 11sz s07 d2 6ul;
  let b12 = bval4 va 12sz s13 d3 25ul;
  let b13 = bval4 va 13sz s19 d4 8ul;
  let b14 = bval4 va 14sz s20 d0 18ul;
  chi4_out e va (SZ.v n) 10sz b10 b11 b12;
  chi4_out e va (SZ.v n) 11sz b11 b12 b13;
  chi4_out e va (SZ.v n) 12sz b12 b13 b14;
  chi4_out e va (SZ.v n) 13sz b13 b14 b10;
  chi4_out e va (SZ.v n) 14sz b14 b10 b11;
  let b15 = bval4 va 15sz s04 d4 27ul;
  let b16 = bval4 va 16sz s05 d0 36ul;
  let b17 = bval4 va 17sz s11 d1 10ul;
  let b18 = bval4 va 18sz s17 d2 15ul;
  let b19 = bval4 va 19sz s23 d3 56ul;
  chi4_out e va (SZ.v n) 15sz b15 b16 b17;
  chi4_out e va (SZ.v n) 16sz b16 b17 b18;
  chi4_out e va (SZ.v n) 17sz b17 b18 b19;
  chi4_out e va (SZ.v n) 18sz b18 b19 b15;
  chi4_out e va (SZ.v n) 19sz b19 b15 b16;
  let b20 = bval4 va 20sz s02 d2 62ul;
  let b21 = bval4 va 21sz s08 d3 55ul;
  let b22 = bval4 va 22sz s14 d4 39ul;
  let b23 = bval4 va 23sz s15 d0 41ul;
  let b24 = bval4 va 24sz s21 d1 2ul;
  chi4_out e va (SZ.v n) 20sz b20 b21 b22;
  chi4_out e va (SZ.v n) 21sz b21 b22 b23;
  chi4_out e va (SZ.v n) 22sz b22 b23 b24;
  chi4_out e va (SZ.v n) 23sz b23 b24 b20;
  chi4_out e va (SZ.v n) 24sz b24 b20 b21;
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


#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** Twenty-four rounds on the packed state, as twelve double rounds
    [st -> b -> st], as in the scalar loop. *)
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
    pure (Seq.length vst0 == 25 /\ SZ.v vi <= 24 /\ SZ.v vi % 2 == 0 /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\
          rounds_ok vst vst0 (SZ.v vi))
  decreases (24 - SZ.v (!i))
  {
    let vi = !i;
    with vst. assert (A.pts_to st vst);
    fround4 st b rc_tbl vi;
    with vb1. assert (A.pts_to b vb1);
    fr_pre_len vb1 vst (SZ.v vi) 25;
    fr_pre_done vb1 vst (SZ.v vi);
    rounds_ok_step vb1 vst vst0 (SZ.v vi);
    let vj = SZ.add vi 1sz;
    fround4 b st rc_tbl vj;
    with vst2. assert (A.pts_to st vst2);
    fr_pre_len vst2 vb1 (SZ.v vj) 25;
    fr_pre_done vst2 vb1 (SZ.v vj);
    rounds_ok_step vst2 vb1 vst0 (SZ.v vj);
    i := SZ.add vi 2sz;
  };
  with vst. assert (A.pts_to st vst);
  rounds_ok_len vst vst0 (SZ.v 24sz);
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Four states, each permuted: [s_k <- permute s_k]. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_prologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
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
