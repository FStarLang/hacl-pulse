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

(** Four PRFs at once, over the four-way Keccak.

    A noise vector is [k] calls of [PRF_eta(s, b) = SHAKE256(s || b, 64 eta)]
    with the same seed and consecutive counters.  Each is one 33-byte absorb
    and at most two squeezed blocks, so it costs one Keccak permutation for
    [eta = 2] and two for [eta = 3].  Four of them side by side share every
    permutation: one {!Hacl.Hash.SHA3.Core4.permute4} ends the four absorbs,
    and, for [eta = 3], a second one produces the four second blocks.

    The squeeze is {!Hacl.Hash.SHA3.Sponge.squeeze_block} on each lane, and
    {!prf_lane} is the whole correctness argument: the bytes it wrote are
    [Spec.SHA3.squeeze] by {!Spec.SHA3.squeeze_range_eq}. *)
module Hacl.Impl.MLKEM.PRF4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Sample
open Spec.SHA3
open Spec.SHA3.Constants
open Hacl.Impl.Table
open Hacl.Hash.SHA3
open Hacl.Hash.SHA3.Sponge

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module Loops = Hacl.Spec.Loops
module HSZ = Hacl.SizeT
module Mem = Hacl.Mem
module Copy = Hacl.Impl.Copy
module K4 = Hacl.Hash.SHA3.Core4
module S4 = Hacl.Impl.MLKEM.Sample4

(** {2 One lane} *)

let lane_msg (vs: Seq.seq S8.t) (b: U8.t) : Seq.seq S8.t = Seq.snoc vs (S8.classify b)

#push-options "--fuel 2 --ifuel 0 --z3rlimit 100"

(** A lane's output is its PRF: the first [min el 136] bytes are the
    absorbed state [a], the rest are [permute a]. *)
let prf_lane (eta: pos { eta <= 3 }) (vs: Seq.lseq S8.t 32) (b: U8.t)
             (a: state) (w: Seq.seq S8.t)
  : Lemma (requires Seq.length w == 192 /\
                    a == absorb 136 shake_suffix (lane_msg vs b) /\
                    (forall (k: nat). k < 64 * eta /\ k < 136 ==>
                       Seq.index w k == state_byte a k) /\
                    (forall (k: nat). 136 <= k /\ k < 64 * eta ==>
                       Seq.index w k == state_byte (permute a) (k - 136)))
          (ensures Seq.slice w 0 (64 * eta) == prf eta vs b)
  = let el = 64 * eta in
    assert (squeeze_state 0 a == a);
    assert (squeeze_state 1 a == permute a);
    squeeze_range_eq 136 a el 0 (if el < 136 then el else 136);
    if el > 136 then squeeze_range_eq 136 a el 136 (el - 136);
    Seq.lemma_eq_intro (Seq.slice w 0 el) (prf eta vs b)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** All but the last permutation of the absorb of [s || byte]; not inlined,
    so that the four calls below share one copy.  The message length [mlen]
    is always 33, but passed in: inlined as a constant, the whole-block loop
    of the absorb becomes [while (i < 0)], which gcc's [-Wtype-limits]
    rejects. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn prf_absorb_pre (st: A.array S64.t) (b: A.array S64.t) (rc_tbl: A.array S64.t)
                  (s: A.array S8.t) (byte: U8.t) (mlen: SZ.t)
                  (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
                  (#prc: perm) (#vrc: erased (Seq.seq S64.t))
                  (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         A.pts_to s #p vs **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ Seq.length vs == 32 /\
               SZ.v mlen == 33)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  A.pts_to s #p vs **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length vs == 32 /\
        permute vst == absorb 136 shake_suffix (lane_msg vs byte))
{
  A.pts_to_len s;
  let z8 = S8.classify 0uy;
  let mut msg = [| z8; 33sz |];
  Mem.track msg;
  A.pts_to_len msg;
  Copy.copy_prefix msg s 32sz;
  A.((msg.(32sz) <- S8.classify byte));
  with vm. assert (A.pts_to msg vm);
  Seq.lemma_eq_intro (reveal vm) (lane_msg vs byte);
  absorb_pre st b rc_tbl msg mlen 136sz shake_suffix;
  Mem.wipe msg 33sz;
}

#pop-options

(** {2 Four lanes} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** [o_j[0, 64 eta) <- PRF_eta(s, b_j)] for [j < 4].  The caller checks
    {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn prf4_impl (o0 o1 o2 o3: A.array S8.t) (s: A.array S8.t)
             (b0 b1 b2 b3: U8.t) (eta: SZ.t)
             (#vo0 #vo1 #vo2 #vo3: erased (Seq.seq S8.t))
             (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to o0 vo0 ** A.pts_to o1 vo1 ** A.pts_to o2 vo2 ** A.pts_to o3 vo3 **
         A.pts_to s #p vs **
         pure (Seq.length vs == 32 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vo0 == 192 /\ Seq.length vo1 == 192 /\
               Seq.length vo2 == 192 /\ Seq.length vo3 == 192)
ensures exists* (w0 w1 w2 w3: Seq.seq S8.t).
  A.pts_to o0 w0 ** A.pts_to o1 w1 ** A.pts_to o2 w2 ** A.pts_to o3 w3 **
  A.pts_to s #p vs **
  pure (Seq.length vs == 32 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length w0 == 192 /\ Seq.length w1 == 192 /\
        Seq.length w2 == 192 /\ Seq.length w3 == 192 /\
        Seq.slice w0 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b0 /\
        Seq.slice w1 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b1 /\
        Seq.slice w2 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b2 /\
        Seq.slice w3 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b3)
{
  A.pts_to_len o0;
  A.pts_to_len o1;
  A.pts_to_len o2;
  A.pts_to_len o3;
  A.pts_to_len s;
  HSZ.fits32 ();
  assert_norm (64 * 3 < pow2 32);
  SZ.fits_u32_implies_fits (64 * SZ.v eta);
  let z64 = S64.classify 0uL;
  let mut st0 = [| z64; 25sz |];
  Mem.track st0;
  A.pts_to_len st0;
  let mut st1 = [| z64; 25sz |];
  Mem.track st1;
  A.pts_to_len st1;
  let mut st2 = [| z64; 25sz |];
  Mem.track st2;
  A.pts_to_len st2;
  let mut st3 = [| z64; 25sz |];
  Mem.track st3;
  A.pts_to_len st3;
  let mut barr = [| z64; 25sz |];
  Mem.track barr;
  A.pts_to_len barr;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  prf_absorb_pre st0 barr rc_tbl s b0 33sz;
  prf_absorb_pre st1 barr rc_tbl s b1 33sz;
  prf_absorb_pre st2 barr rc_tbl s b2 33sz;
  prf_absorb_pre st3 barr rc_tbl s b3 33sz;
  K4.permute4 st0 st1 st2 st3 rc_tbl;
  with a0. assert (A.pts_to st0 a0);
  with a1. assert (A.pts_to st1 a1);
  with a2. assert (A.pts_to st2 a2);
  with a3. assert (A.pts_to st3 a3);

  let el = SZ.mul 64sz eta;
  let big = SZ.gt el 136sz;
  let c1 = (if big then 136sz else el);
  let c2 = (if big then SZ.sub el 136sz else 0sz);
  squeeze_block_lanes o0 0sz c1 st0;
  squeeze_block_lanes o1 0sz c1 st1;
  squeeze_block_lanes o2 0sz c1 st2;
  squeeze_block_lanes o3 0sz c1 st3;
  S4.permute4_if big st0 st1 st2 st3 rc_tbl;
  squeeze_block_lanes o0 136sz c2 st0;
  squeeze_block_lanes o1 136sz c2 st1;
  squeeze_block_lanes o2 136sz c2 st2;
  squeeze_block_lanes o3 136sz c2 st3;
  with w0. assert (A.pts_to o0 w0);
  with w1. assert (A.pts_to o1 w1);
  with w2. assert (A.pts_to o2 w2);
  with w3. assert (A.pts_to o3 w3);
  prf_lane (SZ.v eta) vs b0 a0 w0;
  prf_lane (SZ.v eta) vs b1 a1 w1;
  prf_lane (SZ.v eta) vs b2 a2 w2;
  prf_lane (SZ.v eta) vs b3 a3 w3;

  drop_table rc_tbl;
  Mem.wipe barr 25sz;
  Mem.wipe st3 25sz;
  Mem.wipe st2 25sz;
  Mem.wipe st1 25sz;
  Mem.wipe st0 25sz;
}

#pop-options
