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

(** ExpandMask, four polynomials at a time over the four-way Keccak.

    Each polynomial of the mask [y] is [SHAKE256(rho'' || u16(kappa + r))],
    576 or 640 bytes: one 66-byte absorb and five squeezed blocks, so five
    Keccak permutations.  Four of them side by side share every
    permutation ({!shake4}).  A lane's squeeze is tracked by {!lane_ok}:
    how many bytes are out, how many permutations the state has had.

    {!expand_mask_impl} takes polynomials four at a time while at least two
    are left and the machine has AVX2; when fewer than four are left, the
    window slides back so that it ends at [l], recomputing (and rewriting
    with the same values) one or two polynomials already done.  ML-DSA-44
    is one window, ML-DSA-87 two (the second recomputes one), and
    ML-DSA-65 one window and one scalar polynomial. *)
module Hacl.Impl.MLDSA.Mask4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3.Constants
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Hacl.Impl.Table
open Hacl.Hash.SHA3
open Hacl.Hash.SHA3.Sponge
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Encode
open Hacl.Impl.MLDSA.VecCodec
open Hacl.Impl.MLDSA.XOF
open Hacl.Impl.MLDSA.SampleLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module HSZ = Hacl.SizeT
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module SHA3 = Spec.SHA3
module Mem = Hacl.Mem
module V = Hacl.Vec256
module K4 = Hacl.Hash.SHA3.Core4
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Seeds} *)

let gamma1_zq (g1bits: SZ.t { SZ.v g1bits == 17 \/ SZ.v g1bits == 19 })
  : r: zqt { S32.v r == pow2 (SZ.v g1bits) }
  = assert_norm (pow2 17 == 131072);
    assert_norm (pow2 19 == 524288);
    if g1bits = 17sz then S32.classify 131072ul else S32.classify 524288ul

let seed_16_full (rho: Seq.seq S8.t) (x: nat { x < pow2 16 }) (v: Seq.seq S8.t)
  : Lemma (requires Seq.length v == Seq.length rho + 2 /\
                    (forall (t: nat). t < Seq.length rho ==> Seq.index v t == Seq.index rho t) /\
                    S8.v (Seq.index v (Seq.length rho)) == x % 256 /\
                    S8.v (Seq.index v (Seq.length rho + 1)) == x / 256)
          (ensures v == seed_16 rho x)
  = assert_norm (pow2 16 == 65536);
    let s = seed_16 rho x in
    let aux (t: nat { t < Seq.length v }) : Lemma (Seq.index v t == Seq.index s t)
      = if t < Seq.length rho then ()
        else S8.v_extensional (Seq.index v t) (Seq.index s t)
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro v s

let expand_mask_at (p: params) (rho: Seq.lseq S8.t 64) (a: nat { a < max_attempts })
                   (r: nat { r < p.l })
  : Lemma (kappa_bound p a r;
           KZ.flat_at p.l n (expand_mask p rho a) r == expand_mask_poly p rho (a * p.l + r))
  = vec_at_of_fun_g p.l (fun r ->
      kappa_bound p a r;
      expand_mask_poly p rho (a * p.l + r)) r

let seed_bytes (k: SZ.t) (kv: nat)
  : Lemma (requires SZ.v k == kv /\ kv < pow2 16)
          (ensures (let x = SZ.sizet_to_uint32 k in
                    U32.v x == kv /\
                    S8.v (S8.classify (Cast.uint32_to_uint8 (U32.rem x 256ul))) == kv % 256 /\
                    S8.v (S8.classify (Cast.uint32_to_uint8 (U32.div x 256ul))) == kv / 256))
  = assert_norm (pow2 16 == 65536);
    assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 8 == 256);
    Math.small_mod kv (pow2 32);
    Math.small_mod (kv % 256) 256;
    Math.small_mod (kv / 256) 256

(** {2 One lane} *)

(** A SHAKE256 lane for [msg], asked for [blen] bytes: the first [m] are
    out in [w], and the state has had [q] permutations since the absorb. *)
[@@"opaque_to_smt"]
let lane_ok (msg: Seq.seq S8.t) (blen: nat) (m: nat) (q: nat)
            (vst: Seq.seq S64.t) (w: Seq.seq S8.t) : prop =
  Seq.length vst == 25 /\
  vst == SHA3.squeeze_state q (SHA3.absorb 136 SHA3.shake_suffix msg) /\
  Seq.length w == 640 /\ m <= blen /\ blen <= 640 /\
  (forall (k: nat). k < m ==> Seq.index w k == Seq.index (SHA3.shake256 msg blen) k)

let lane_ok_elim (msg: Seq.seq S8.t) (blen: nat) (m: nat) (q: nat)
                 (vst: Seq.seq S64.t) (w: Seq.seq S8.t)
  : Lemma (requires lane_ok msg blen m q vst w)
          (ensures Seq.length vst == 25 /\ Seq.length w == 640 /\ m <= blen /\ blen <= 640)
  = reveal_opaque (`%lane_ok) (lane_ok msg blen m q vst w)

let lane_init (msg: Seq.seq S8.t) (blen: nat) (vst: Seq.seq S64.t) (w: Seq.seq S8.t)
  : Lemma (requires Seq.length vst == 25 /\ Seq.length w == 640 /\ blen <= 640 /\
                    SHA3.permute vst == SHA3.absorb 136 SHA3.shake_suffix msg)
          (ensures lane_ok msg blen 0 0 (SHA3.permute vst) w)
  = squeeze_state_zero (SHA3.absorb 136 SHA3.shake_suffix msg);
    reveal_opaque (`%lane_ok) (lane_ok msg blen 0 0 (SHA3.permute vst) w)

(** One more permutation. *)
let lane_adv (msg: Seq.seq S8.t) (blen: nat) (m: nat) (q: nat)
             (vst: Seq.seq S64.t) (w: Seq.seq S8.t)
  : Lemma (requires lane_ok msg blen m q vst w)
          (ensures Seq.length vst == 25 /\ lane_ok msg blen m (q + 1) (SHA3.permute vst) w)
  = reveal_opaque (`%lane_ok) (lane_ok msg blen m q vst w);
    squeeze_state_succ q (SHA3.absorb 136 SHA3.shake_suffix msg);
    reveal_opaque (`%lane_ok) (lane_ok msg blen m (q + 1) (SHA3.permute vst) w)

(** [cnt] more bytes, read from the state of block [q]. *)
let lane_sq (msg: Seq.seq S8.t) (blen: nat) (q: nat) (cnt: nat)
            (vst: Seq.seq S64.t) (w w': Seq.seq S8.t)
  : Lemma (requires Seq.length vst == 25 /\ Seq.length w == 640 /\ blen <= 640 /\
                    lane_ok msg blen (136 * q) q vst w /\ cnt <= 136 /\
                    136 * q + cnt <= blen /\ Seq.length w' == 640 /\
                    (forall (k: nat). 136 * q <= k /\ k < 136 * q + cnt ==>
                       Seq.index w' k == SHA3.state_byte vst (k - 136 * q)) /\
                    (forall (k: nat). k < 640 /\ k < 136 * q ==>
                       Seq.index w' k == Seq.index w k))
          (ensures lane_ok msg blen (136 * q + cnt) q vst w')
  = reveal_opaque (`%lane_ok) (lane_ok msg blen (136 * q) q vst w);
    let a = SHA3.absorb 136 SHA3.shake_suffix msg in
    let base = 136 * q in
    Math.cancel_mul_mod q 136;
    Math.cancel_mul_div q 136;
    assert (base == q * 136);
    assert (base % 136 == 0 /\ base / 136 == q);
    SHA3.squeeze_range_eq 136 a blen base cnt;
    assert (SHA3.shake256 msg blen == SHA3.squeeze 136 a blen);
    let aux (k: nat { k < base + cnt })
      : Lemma (Seq.index w' k == Seq.index (SHA3.shake256 msg blen) k)
      = if k < base then () else ()
    in
    Classical.forall_intro aux;
    reveal_opaque (`%lane_ok) (lane_ok msg blen (136 * q + cnt) q vst w')

let lane_done (msg: Seq.seq S8.t) (blen: nat) (q: nat)
              (vst: Seq.seq S64.t) (w: Seq.seq S8.t)
  : Lemma (requires lane_ok msg blen blen q vst w)
          (ensures Seq.length w == 640 /\ blen <= 640 /\
                   Seq.slice w 0 blen == SHA3.shake256 msg blen)
  = reveal_opaque (`%lane_ok) (lane_ok msg blen blen q vst w);
    Seq.lemma_eq_intro (Seq.slice w 0 blen) (SHA3.shake256 msg blen)

(** Squeezes bytes [136 q, 136 q + cnt) of a lane.  Reached only from the
    x86-64 [shake4], so guarded like it. *)
[@@custard_c_closure_guard "defined(__x86_64__)"]
fn sq_lane (out: A.array S8.t) (q: SZ.t) (cnt: SZ.t) (st: A.array S64.t)
           (msg: erased (Seq.seq S8.t)) (blen: erased nat)
           (#vst: erased (Seq.seq S64.t)) (#w: erased (Seq.seq S8.t))
requires A.pts_to out w ** A.pts_to st vst **
         pure (lane_ok msg blen (136 * SZ.v q) (SZ.v q) vst w /\ SZ.v cnt <= 136 /\
               136 * SZ.v q + SZ.v cnt <= blen)
ensures exists* (w': Seq.seq S8.t). A.pts_to out w' ** A.pts_to st vst **
  pure (lane_ok msg blen (136 * SZ.v q + SZ.v cnt) (SZ.v q) vst w')
{
  lane_ok_elim msg blen (136 * SZ.v q) (SZ.v q) vst w;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (136 * SZ.v q);
  let base = SZ.mul 136sz q;
  assert (pure (SZ.v base == 136 * SZ.v q));
  squeeze_block_lanes out base cnt st;
  with w'. assert (A.pts_to out w');
  assert (pure (Seq.length w' == 640));
  assert (pure (forall (k: nat). 136 * SZ.v q <= k /\ k < 136 * SZ.v q + SZ.v cnt ==>
                  Seq.index w' k == SHA3.state_byte vst (k - 136 * SZ.v q)));
  assert (pure (forall (k: nat). k < 640 /\ k < 136 * SZ.v q ==>
                  Seq.index w' k == Seq.index w k));
  lane_sq msg blen (SZ.v q) (SZ.v cnt) vst w w';
  assert (pure (lane_ok msg blen (136 * SZ.v q + SZ.v cnt) (SZ.v q) vst w'));
}

(** All but the last permutation of the absorb of [rho || u16(x)].  The
    message length [mlen] is always 66, but passed in, as in
    {!Hacl.Impl.MLKEM.PRF4.prf_absorb_pre}: inlined as a constant, the
    whole-block loop of the absorb becomes [while (i < 0)], which gcc's
    [-Wtype-limits] rejects. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn seed_absorb_pre (st: A.array S64.t) (b: A.array S64.t) (rc_tbl: A.array S64.t)
                   (rho: A.array S8.t) (x: SZ.t) (mlen: SZ.t)
                   (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
                   (#prc: perm) (#vrc: erased (Seq.seq S64.t))
                   (#p: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         A.pts_to rho #p vr **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ Seq.length vr == 64 /\
               SZ.v x < pow2 16 /\ SZ.v mlen == 66)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  A.pts_to rho #p vr **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length vr == 64 /\
        SZ.v x < pow2 16 /\
        SHA3.permute vst == SHA3.absorb 136 SHA3.shake_suffix (seed_16 vr (SZ.v x)))
{
  A.pts_to_len rho;
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 16 == 65536);
  let z8 = S8.classify 0uy;
  let mut msg = [| z8; 66sz |];
  Mem.track msg;
  A.pts_to_len msg;
  Copy.copy_prefix msg rho 64sz;
  let xv = SZ.sizet_to_uint32 x;
  seed_bytes x (SZ.v x);
  let b0 = Cast.uint32_to_uint8 (U32.rem xv 256ul);
  let b1 = Cast.uint32_to_uint8 (U32.div xv 256ul);
  A.((msg.(64sz) <- S8.classify b0));
  A.((msg.(65sz) <- S8.classify b1));
  with vm. assert (A.pts_to msg vm);
  seed_16_full vr (SZ.v x) vm;
  absorb_pre st b rc_tbl msg mlen 136sz SHA3.shake_suffix;
  Mem.wipe msg 66sz;
}

#pop-options

(** {2 Four lanes} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let lane_msg (vr: Seq.seq S8.t) (x: SZ.t { SZ.v x < pow2 16 }) : GTot (Seq.seq S8.t) =
  seed_16 vr (SZ.v x)

(** [o_j[0, blen) <- SHAKE256(rho || u16(x_j), blen)] for [j < 4], for
    the [blen] of ExpandMask.  The caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn shake4 (o0 o1 o2 o3: A.array S8.t) (rho: A.array S8.t)
          (x0 x1 x2 x3: SZ.t) (blen: SZ.t)
          (#vo0 #vo1 #vo2 #vo3: erased (Seq.seq S8.t))
          (#p: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to o0 vo0 ** A.pts_to o1 vo1 ** A.pts_to o2 vo2 ** A.pts_to o3 vo3 **
         A.pts_to rho #p vr **
         pure (Seq.length vr == 64 /\ 544 < SZ.v blen /\ SZ.v blen <= 640 /\
               SZ.v x0 < pow2 16 /\ SZ.v x1 < pow2 16 /\
               SZ.v x2 < pow2 16 /\ SZ.v x3 < pow2 16 /\
               Seq.length vo0 == 640 /\ Seq.length vo1 == 640 /\
               Seq.length vo2 == 640 /\ Seq.length vo3 == 640)
ensures exists* (w0 w1 w2 w3: Seq.seq S8.t).
  A.pts_to o0 w0 ** A.pts_to o1 w1 ** A.pts_to o2 w2 ** A.pts_to o3 w3 **
  A.pts_to rho #p vr **
  pure (Seq.length vr == 64 /\ 544 < SZ.v blen /\ SZ.v blen <= 640 /\
        SZ.v x0 < pow2 16 /\ SZ.v x1 < pow2 16 /\
        SZ.v x2 < pow2 16 /\ SZ.v x3 < pow2 16 /\
        Seq.length w0 == 640 /\ Seq.length w1 == 640 /\
        Seq.length w2 == 640 /\ Seq.length w3 == 640 /\
        Seq.slice w0 0 (SZ.v blen) == SHA3.shake256 (lane_msg vr x0) (SZ.v blen) /\
        Seq.slice w1 0 (SZ.v blen) == SHA3.shake256 (lane_msg vr x1) (SZ.v blen) /\
        Seq.slice w2 0 (SZ.v blen) == SHA3.shake256 (lane_msg vr x2) (SZ.v blen) /\
        Seq.slice w3 0 (SZ.v blen) == SHA3.shake256 (lane_msg vr x3) (SZ.v blen))
{
  A.pts_to_len o0;
  A.pts_to_len o1;
  A.pts_to_len o2;
  A.pts_to_len o3;
  A.pts_to_len rho;
  HSZ.fits32 ();
  let m0 : erased (Seq.seq S8.t) = hide (lane_msg vr x0);
  let m1 : erased (Seq.seq S8.t) = hide (lane_msg vr x1);
  let m2 : erased (Seq.seq S8.t) = hide (lane_msg vr x2);
  let m3 : erased (Seq.seq S8.t) = hide (lane_msg vr x3);
  let bl : erased nat = hide (SZ.v blen);
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

  seed_absorb_pre st0 barr rc_tbl rho x0 66sz;
  seed_absorb_pre st1 barr rc_tbl rho x1 66sz;
  seed_absorb_pre st2 barr rc_tbl rho x2 66sz;
  seed_absorb_pre st3 barr rc_tbl rho x3 66sz;
  with a0. assert (A.pts_to st0 a0);
  with a1. assert (A.pts_to st1 a1);
  with a2. assert (A.pts_to st2 a2);
  with a3. assert (A.pts_to st3 a3);
  K4.permute4 st0 st1 st2 st3 rc_tbl;
  lane_init m0 bl a0 vo0;
  lane_init m1 bl a1 vo1;
  lane_init m2 bl a2 vo2;
  lane_init m3 bl a3 vo3;

  let mut q = 0sz;
  while (let vq = !q; SZ.lt vq 4sz)
  invariant exists* (vq: SZ.t) (s0 s1 s2 s3: Seq.seq S64.t) (w0 w1 w2 w3: Seq.seq S8.t).
    pts_to q vq **
    A.pts_to st0 s0 ** A.pts_to st1 s1 ** A.pts_to st2 s2 ** A.pts_to st3 s3 **
    A.pts_to o0 w0 ** A.pts_to o1 w1 ** A.pts_to o2 w2 ** A.pts_to o3 w3 **
    A.pts_to rc_tbl #prc vrc **
    pure (SZ.v vq <= 4 /\ reveal vrc == (rc <: Seq.seq S64.t) /\
          544 < reveal bl /\ reveal bl == SZ.v blen /\
          lane_ok m0 bl (136 * SZ.v vq) (SZ.v vq) s0 w0 /\
          lane_ok m1 bl (136 * SZ.v vq) (SZ.v vq) s1 w1 /\
          lane_ok m2 bl (136 * SZ.v vq) (SZ.v vq) s2 w2 /\
          lane_ok m3 bl (136 * SZ.v vq) (SZ.v vq) s3 w3)
  decreases (4 - SZ.v (!q))
  {
    let vq = !q;
    sq_lane o0 vq 136sz st0 m0 bl;
    sq_lane o1 vq 136sz st1 m1 bl;
    sq_lane o2 vq 136sz st2 m2 bl;
    sq_lane o3 vq 136sz st3 m3 bl;
    with s0. assert (A.pts_to st0 s0);
    with s1. assert (A.pts_to st1 s1);
    with s2. assert (A.pts_to st2 s2);
    with s3. assert (A.pts_to st3 s3);
    with w0. assert (A.pts_to o0 w0);
    with w1. assert (A.pts_to o1 w1);
    with w2. assert (A.pts_to o2 w2);
    with w3. assert (A.pts_to o3 w3);
    lane_ok_elim m0 bl (136 * SZ.v vq + 136) (SZ.v vq) s0 w0;
    lane_ok_elim m1 bl (136 * SZ.v vq + 136) (SZ.v vq) s1 w1;
    lane_ok_elim m2 bl (136 * SZ.v vq + 136) (SZ.v vq) s2 w2;
    lane_ok_elim m3 bl (136 * SZ.v vq + 136) (SZ.v vq) s3 w3;
    K4.permute4 st0 st1 st2 st3 rc_tbl;
    lane_adv m0 bl (136 * SZ.v vq + 136) (SZ.v vq) s0 w0;
    lane_adv m1 bl (136 * SZ.v vq + 136) (SZ.v vq) s1 w1;
    lane_adv m2 bl (136 * SZ.v vq + 136) (SZ.v vq) s2 w2;
    lane_adv m3 bl (136 * SZ.v vq + 136) (SZ.v vq) s3 w3;
    assert (pure (136 * (SZ.v vq + 1) == 136 * SZ.v vq + 136));
    q := SZ.add vq 1sz;
  };
  let last = SZ.sub blen 544sz;
  sq_lane o0 4sz last st0 m0 bl;
  sq_lane o1 4sz last st1 m1 bl;
  sq_lane o2 4sz last st2 m2 bl;
  sq_lane o3 4sz last st3 m3 bl;
  with s0. assert (A.pts_to st0 s0);
  with s1. assert (A.pts_to st1 s1);
  with s2. assert (A.pts_to st2 s2);
  with s3. assert (A.pts_to st3 s3);
  with w0. assert (A.pts_to o0 w0);
  with w1. assert (A.pts_to o1 w1);
  with w2. assert (A.pts_to o2 w2);
  with w3. assert (A.pts_to o3 w3);
  lane_done m0 bl 4 s0 w0;
  lane_done m1 bl 4 s1 w1;
  lane_done m2 bl 4 s2 w2;
  lane_done m3 bl 4 s3 w3;

  drop_table rc_tbl;
  Mem.wipe barr 25sz;
  Mem.wipe st3 25sz;
  Mem.wipe st2 25sz;
  Mem.wipe st1 25sz;
  Mem.wipe st0 25sz;
}

#pop-options

(** {2 ExpandMask} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let mask_step2 (p: params) (rho: Seq.lseq S8.t 64) (a: nat { a < max_attempts })
               (r: nat { r < p.l })
               (w0 w1: Seq.seq zqt) (b: Seq.seq zqt) (buf: Seq.seq S8.t)
  : Lemma (requires
      Seq.length w0 == p.l * n /\ Seq.length w1 == p.l * n /\ Seq.length b == n /\
      (forall (i: nat). i < p.l * n ==>
         Seq.index w1 i == (if r * n <= i && i < r * n + n
                            then Seq.index b (i - r * n) else Seq.index w0 i)) /\
      prefix_eq w0 (expand_mask p rho a) (r * n) /\
      (kappa_bound p a r;
       mask_bound p;
       Seq.length buf == 32 * z_bits p /\
       buf == SHA3.shake256 (seed_16 rho (a * p.l + r)) (32 * z_bits p) /\
       as_poly b == bit_unpack (gamma1 p) (z_bits p) buf))
    (ensures prefix_eq w1 (expand_mask p rho a) ((r + 1) * n))
  = reveal_opaque (`%prefix_eq) (prefix_eq w0 (expand_mask p rho a) (r * n));
    reveal_opaque (`%prefix_eq) (prefix_eq w1 (expand_mask p rho a) ((r + 1) * n));
    expand_mask_at p rho a r;
    Math.lemma_mult_le_right n r p.l;
    introduce forall (i: nat). i < r * n ==>
                S32.v (Seq.index w0 i) == Seq.index (expand_mask p rho a) i
    with introduce _ ==> _ with assert (i < p.l * n);
    flat_step p.l r w0 w1 b (expand_mask p rho a)

let prefix_mono (w: Seq.seq zqt) (r: Seq.seq zq) (m m': nat)
  : Lemma (requires prefix_eq w r m /\ m' <= m) (ensures prefix_eq w r m')
  = reveal_opaque (`%prefix_eq) (prefix_eq w r m);
    reveal_opaque (`%prefix_eq) (prefix_eq w r m')

(** Unpacks polynomial [r] of the mask from its SHAKE256 output [ob]. *)
fn mask_lane (p: erased params) (y: A.array zqt) (ob: A.array S8.t)
             (g1bits: SZ.t) (r: SZ.t)
             (vr: erased (Seq.seq S8.t)) (a: erased (x: nat { x < max_attempts }))
             (#vy: erased (Seq.seq zqt)) (#vo: erased (Seq.seq S8.t))
requires A.pts_to y vy ** A.pts_to ob vo **
         pure (Seq.length vr == 64 /\ SZ.v r < p.l /\ SZ.v g1bits == p.gamma1_bits /\
               Seq.length vy == p.l * n /\ Seq.length vo == 32 * z_bits p /\
               prefix_eq vy (expand_mask p vr a) (SZ.v r * n) /\
               (kappa_bound p a (SZ.v r);
                mask_bound p;
                vo == SHA3.shake256 (seed_16 vr (a * p.l + SZ.v r)) (32 * z_bits p)))
ensures exists* (v: Seq.seq zqt). A.pts_to y v ** A.pts_to ob vo **
  pure (Seq.length vr == 64 /\ Seq.length v == p.l * n /\
        prefix_eq v (expand_mask p vr a) ((SZ.v r + 1) * n))
{
  A.pts_to_len y;
  A.pts_to_len ob;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  mask_bound p;
  Math.lemma_mult_le_right n (SZ.v r + 1) p.l;
  Math.distributivity_add_left (SZ.v r) 1 n;
  Math.lemma_mult_le_right n p.l 8;
  SZ.fits_u32_implies_fits (SZ.v r * n + n);
  let zb = SZ.add g1bits 1sz;
  let gb = gamma1_zq g1bits;
  let lo = SZ.mul r 256sz;
  let hi = SZ.add lo 256sz;
  let blk = Sub.sub y lo hi;
  unpack_poly blk ob zb true gb;
  with bk. assert (A.pts_to blk bk);
  Sub.unsub y (SZ.v lo) (SZ.v hi) blk;
  with w1. assert (A.pts_to y w1);
  assert (pure (SZ.v lo == SZ.v r * n /\ SZ.v hi == SZ.v r * n + n));
  assert (pure (Seq.length w1 == p.l * n /\ Seq.length bk == n));
  assert (pure (forall (i: nat). i < p.l * n ==>
         Seq.index w1 i == (if SZ.v r * n <= i && i < SZ.v r * n + n
                            then Seq.index bk (i - SZ.v r * n) else Seq.index vy i)));
  assert (pure (as_poly bk == bit_unpack (gamma1 p) (z_bits p) vo));
  mask_step2 p vr a (SZ.v r) vy w1 bk vo;
  assert (pure (prefix_eq w1 (expand_mask p vr a) ((SZ.v r + 1) * n)));
}

(** Polynomial [r] of the mask, one SHAKE256. *)
fn mask_one (p: erased params) (y: A.array zqt) (rho: A.array S8.t)
            (g1bits: SZ.t) (kappa: SZ.t) (r: SZ.t)
            (a: erased (x: nat { x < max_attempts }))
            (#vy: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to y vy ** A.pts_to rho #pr vr **
         pure (SZ.v r < p.l /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v kappa == a * p.l /\ Seq.length vr == 64 /\
               Seq.length vy == p.l * n /\
               prefix_eq vy (expand_mask p vr a) (SZ.v r * n))
ensures exists* (v: Seq.seq zqt). A.pts_to y v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length v == p.l * n /\
        prefix_eq v (expand_mask p vr a) ((SZ.v r + 1) * n))
{
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (pow2 16 == 65536);
  mask_bound p;
  kappa_bound p a (SZ.v r);
  let blen = SZ.mul 32sz (SZ.add g1bits 1sz);
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 66sz |];
  Mem.track sd;
  let mut buf = [| z8; 640sz |];
  Mem.track buf;
  A.pts_to_len sd;
  A.pts_to_len buf;
  Copy.copy_prefix sd rho 64sz;
  let x = SZ.add kappa r;
  let xv = SZ.sizet_to_uint32 x;
  seed_bytes x (SZ.v x);
  let b0 = Cast.uint32_to_uint8 (U32.rem xv 256ul);
  let b1 = Cast.uint32_to_uint8 (U32.div xv 256ul);
  A.((sd.(64sz) <- S8.classify b0));
  A.((sd.(65sz) <- S8.classify b1));
  with vsd. assert (A.pts_to sd vsd);
  seed_16_full vr (SZ.v x) vsd;
  let ob = Sub.sub buf 0sz blen;
  Hacl.Hash.SHA3.shake256 ob blen sd 66sz;
  mask_lane p y ob g1bits r vr a;
  Sub.unsub buf 0 (SZ.v blen) ob;
  Mem.wipe buf 640sz;
  Mem.wipe sd 66sz;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** One lane of {!mask4}: [o] holds polynomial [r]'s SHAKE256 output. *)
inline_for_extraction
fn mask4_lane (p: erased params) (y: A.array zqt) (o: A.array S8.t)
              (g1bits: SZ.t) (r: SZ.t) (x: SZ.t)
              (vr: erased (Seq.seq S8.t)) (a: erased (x: nat { x < max_attempts }))
              (#vy: erased (Seq.seq zqt)) (#vo: erased (Seq.seq S8.t))
requires A.pts_to y vy ** A.pts_to o vo **
         pure (Seq.length vr == 64 /\ SZ.v r < p.l /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v x == a * p.l + SZ.v r /\ SZ.v x < pow2 16 /\
               Seq.length vy == p.l * n /\ Seq.length vo == 640 /\
               prefix_eq vy (expand_mask p vr a) (SZ.v r * n) /\
               (mask_bound p;
                Seq.slice vo 0 (32 * z_bits p) ==
                  SHA3.shake256 (lane_msg vr x) (32 * z_bits p)))
ensures exists* (v: Seq.seq zqt). A.pts_to y v ** A.pts_to o vo **
  pure (Seq.length vr == 64 /\ Seq.length v == p.l * n /\
        prefix_eq v (expand_mask p vr a) ((SZ.v r + 1) * n))
{
  A.pts_to_len o;
  mask_bound p;
  HSZ.fits32 ();
  let blen = SZ.mul 32sz (SZ.add g1bits 1sz);
  let ob = Sub.sub o 0sz blen;
  mask_lane p y ob g1bits r vr a;
  Sub.unsub_id o 0 (SZ.v blen) ob;
}

(** Polynomials [s .. s + 4) of the mask, sampled together.  Uses AVX2:
    the caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn mask4 (p: erased params) (y: A.array zqt) (rho: A.array S8.t)
         (g1bits: SZ.t) (kappa: SZ.t) (s: SZ.t)
         (a: erased (x: nat { x < max_attempts }))
         (#vy: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to y vy ** A.pts_to rho #pr vr **
         pure (SZ.v s + 4 <= p.l /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v kappa == a * p.l /\ Seq.length vr == 64 /\
               Seq.length vy == p.l * n /\
               prefix_eq vy (expand_mask p vr a) (SZ.v s * n))
ensures exists* (v: Seq.seq zqt). A.pts_to y v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length v == p.l * n /\
        prefix_eq v (expand_mask p vr a) ((SZ.v s + 4) * n))
{
  A.pts_to_len rho;
  HSZ.fits32 ();
  mask_bound p;
  kappa_bound p a (SZ.v s);
  kappa_bound p a (SZ.v s + 3);
  assert_norm (pow2 16 == 65536);
  assert (pure (32 * z_bits p == 576 \/ 32 * z_bits p == 640));
  let blen = SZ.mul 32sz (SZ.add g1bits 1sz);
  let s1 = SZ.add s 1sz;
  let s2 = SZ.add s 2sz;
  let s3 = SZ.add s 3sz;
  let x0 = SZ.add kappa s;
  let x1 = SZ.add kappa s1;
  let x2 = SZ.add kappa s2;
  let x3 = SZ.add kappa s3;
  let z8 = S8.classify 0uy;
  let mut o0 = [| z8; 640sz |];
  Mem.track o0;
  A.pts_to_len o0;
  let mut o1 = [| z8; 640sz |];
  Mem.track o1;
  A.pts_to_len o1;
  let mut o2 = [| z8; 640sz |];
  Mem.track o2;
  A.pts_to_len o2;
  let mut o3 = [| z8; 640sz |];
  Mem.track o3;
  A.pts_to_len o3;
  shake4 o0 o1 o2 o3 rho x0 x1 x2 x3 blen;
  mask4_lane p y o0 g1bits s x0 vr a;
  mask4_lane p y o1 g1bits s1 x1 vr a;
  mask4_lane p y o2 g1bits s2 x2 vr a;
  mask4_lane p y o3 g1bits s3 x3 vr a;
  Mem.wipe o3 640sz;
  Mem.wipe o2 640sz;
  Mem.wipe o1 640sz;
  Mem.wipe o0 640sz;
}

(** Algorithm 34: [y <- ExpandMask(rho'', kappa)], four polynomials at a
    time where it can (see the module comment). *)
fn expand_mask_impl (p: erased params) (y: A.array zqt) (rho: A.array S8.t)
                    ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                    (kappa: SZ.t) (a: erased (x: nat { x < max_attempts }))
                    (#vy: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to y vy ** A.pts_to rho #pr vr **
         pure (SZ.v l == p.l /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v kappa == a * p.l /\
               Seq.length vr == 64 /\ Seq.length vy == p.l * n)
ensures exists* (v: Seq.seq zqt). A.pts_to y v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length v == p.l * n /\
        as_zqs v == expand_mask p vr a)
{
  A.pts_to_len y;
  A.pts_to_len rho;
  HSZ.fits32 ();
  prefix_zero vy (expand_mask p vr a);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc l)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to y v ** A.pts_to rho #pr vr **
    pure (SZ.v vc <= p.l /\ SZ.v l == p.l /\ SZ.v kappa == a * p.l /\
          SZ.v g1bits == p.gamma1_bits /\
          Seq.length v == p.l * n /\ Seq.length vr == 64 /\
          prefix_eq v (expand_mask p vr a) (SZ.v vc * n))
  decreases (SZ.v l - SZ.v (!c))
  {
    let vc = !c;
    if (Hacl.X64.x86_64) {
      if (SZ.lte (SZ.add vc 2sz) l && SZ.gte l 4sz && V.supported ()) {
        let s = (if SZ.lte (SZ.add vc 4sz) l then vc else SZ.sub l 4sz);
        with v. assert (A.pts_to y v);
        Math.lemma_mult_le_right n (SZ.v s) (SZ.v vc);
        prefix_mono v (expand_mask p vr a) (SZ.v vc * n) (SZ.v s * n);
        mask4 p y rho g1bits kappa s a;
        with v'. assert (A.pts_to y v');
        assert (pure (SZ.v s + 4 >= SZ.v vc + 1));
        c := SZ.add s 4sz;
      } else {
        mask_one p y rho g1bits kappa vc a;
        c := SZ.add vc 1sz;
      }
    } else {
      mask_one p y rho g1bits kappa vc a;
      c := SZ.add vc 1sz;
    }
  };
  with v. assert (A.pts_to y v);
  prefix_done p.l v (expand_mask p vr a);
  assert (pure (as_zqs v == expand_mask p vr a));
}

#pop-options
