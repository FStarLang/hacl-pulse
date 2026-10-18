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

(** The Keccak sponge: absorb, then squeeze.

    Whole message blocks are exclusive-or'd into the state straight out of the
    caller's buffer -- there is no copy and no per-block staging area.  Only
    the last block is built, in a two-hundred byte stack buffer, because it
    carries the padding.

    Everything here is parameterised by the rate as a [size_t], so one copy of
    this code serves SHA3-224 through SHA3-512 and both SHAKEs -- but the
    functions are [inline_for_extraction], so the parameter is the caller's
    literal by the time a C compiler sees it.  Sharing one copy costs the
    absorb loop two integer divisions by a runtime value and a variable
    length on every block copy; see the note above [keccak_impl] in
    [Hacl.Hash.SHA3]. *)
module Hacl.Hash.SHA3.Sponge

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants
open Hacl.Hash.SHA3.Core
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module G = FStar.Ghost
module Loops = Hacl.Spec.Loops
module Mem = Hacl.Mem

(** {2 Shifts with a runtime offset} *)

let shiftl_u32 (x: S64.t) (k: U32.t { U32.v k < 64 }) : (y: S64.t { y == shiftl x (U32.v k) }) =
  if k = 0ul then x else (U32.uv_inv k; S64.shift_left x k)

let shiftr_u32 (x: S64.t) (k: U32.t { U32.v k < 64 }) : (y: S64.t { y == shiftr x (U32.v k) }) =
  if k = 0ul then x else (U32.uv_inv k; S64.shift_right x k)

(** [8 * j] as a shift offset, for [j < 8]. *)
let shift8 (j: SZ.t { SZ.v j < 8 }) : (k: U32.t { U32.v k == 8 * SZ.v j }) =
  Math.small_mod (8 * SZ.v j) (pow2 32);
  SZ.sizet_to_uint32 (SZ.mul 8sz j)

(** {2 Reading a lane} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** The little-endian lane at byte offset [off]. *)
inline_for_extraction
fn lane_at (msg: A.array S8.t) (off: SZ.t) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to msg #pm vm ** pure (SZ.v off + 8 <= Seq.length vm)
returns x: S64.t
ensures A.pts_to msg #pm vm **
        pure (SZ.v off + 8 <= Seq.length vm /\
              x == lane_of (Seq.slice vm (SZ.v off) (SZ.v off + 8)))
{
  A.pts_to_len msg;
  let mut acc = S64.zero;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (a: S64.t).
    pts_to j vj ** pts_to acc a ** A.pts_to msg #pm vm **
    pure (SZ.v off + 8 <= Seq.length vm /\ SZ.v vj <= 8 /\
          a == Loops.repeati (SZ.v vj)
                 (lane_of_step (Seq.slice vm (SZ.v off) (SZ.v off + 8))) S64.zero)
  decreases (8 - SZ.v (!j))
  {
    let vj = !j;
    let byte = A.(msg.(SZ.add off vj));
    let a = !acc;
    acc := S64.logor a (shiftl_u32 (Cast.u8_to_u64 byte) (shift8 vj));
    Loops.unfold_repeati (SZ.v vj)
      (lane_of_step (Seq.slice vm (SZ.v off) (SZ.v off + 8))) S64.zero;
    j := SZ.add vj 1sz;
  };
  !acc
}

#pop-options

(** {2 Exclusive-or of one block} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** [st <- xor_block r msg[off .. off+r) st]. *)
inline_for_extraction
fn xor_block_at (st: A.array S64.t) (msg: A.array S8.t) (off: SZ.t) (r: SZ.t)
                (#vst0: erased (Seq.seq S64.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to msg #pm vm **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
               Seq.length vst0 == 25 /\ SZ.v off + SZ.v r <= Seq.length vm)
ensures exists* (vst: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to msg #pm vm **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
        Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
        SZ.v off + SZ.v r <= Seq.length vm /\
        vst == xor_block (SZ.v r) (Seq.slice vm (SZ.v off) (SZ.v off + SZ.v r)) vst0)
{
  A.pts_to_len st;
  A.pts_to_len msg;
  let nl = SZ.div r 8sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi nl)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst ** A.pts_to msg #pm vm **
    pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
          Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
          SZ.v off + SZ.v r <= Seq.length vm /\
          SZ.v vi <= rate_lanes (SZ.v r) /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index vst k ==
             Seq.index (xor_block (SZ.v r) (Seq.slice vm (SZ.v off) (SZ.v off + SZ.v r)) vst0) k) /\
          (forall (k: nat). SZ.v vi <= k /\ k < 25 ==> Seq.index vst k == Seq.index vst0 k))
  decreases (SZ.v nl - SZ.v (!i))
  {
    let vi = !i;
    let o = SZ.add off (SZ.mul 8sz vi);
    assert (pure (SZ.v o + 8 <= Seq.length vm));
    let l = lane_at msg o;
    let a = A.(st.(vi));
    A.((st.(vi) <- S64.logxor a l));
    Seq.slice_slice vm (SZ.v off) (SZ.v off + SZ.v r) (8 * SZ.v vi) (8 * SZ.v vi + 8);
    xor_block_index (SZ.v r) (Seq.slice vm (SZ.v off) (SZ.v off + SZ.v r)) vst0 (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with vst. assert (A.pts_to st vst);
  Classical.forall_intro
    (xor_block_index (SZ.v r) (Seq.slice vm (SZ.v off) (SZ.v off + SZ.v r)) (reveal vst0));
  assert (pure (Seq.length
    (xor_block (SZ.v r) (Seq.slice vm (SZ.v off) (SZ.v off + SZ.v r)) vst0) == 25));
  assert (pure (reveal vst `Seq.equal`
    xor_block (SZ.v r) (Seq.slice vm (SZ.v off) (SZ.v off + SZ.v r)) vst0));
}

#pop-options

(** {2 Absorbing} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** [st <- zero_state]. *)
inline_for_extraction
fn zero_state_impl (st: A.array S64.t) (#vst0: erased (Seq.seq S64.t))
requires A.pts_to st vst0 ** pure (Seq.length vst0 == 25)
ensures exists* (vst: Seq.seq S64.t).
  A.pts_to st vst ** pure (Seq.length vst == 25 /\ vst == zero_state)
{
  A.pts_to_len st;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst **
    pure (SZ.v vi <= 25 /\ Seq.length vst == 25 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vst k == S64.zero))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    A.((st.(vi) <- S64.zero));
    i := SZ.add vi 1sz;
  };
  with vst. assert (A.pts_to st vst);
  assert (pure (reveal vst `Seq.equal` zero_state));
}

(** Absorb the [len msg / r] whole blocks, in place, out of the caller's
    buffer.  Leaves the state at [repeati (len msg / r) (absorb_step ...)]. *)
inline_for_extraction
fn absorb_full (st: A.array S64.t) (b: A.array S64.t)
               (rc_tbl: A.array S64.t)
               (msg: A.array S8.t) (n: SZ.t) (r: SZ.t) (suffix: G.erased U8.t)
               (#vb0: erased (Seq.seq S64.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
               (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to st (zero_state <: Seq.seq S64.t) ** A.pts_to b vb0 **
         A.pts_to rc_tbl #prc vrc ** A.pts_to msg #pm vm **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
               Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
         ** pure (SZ.v n == Seq.length vm)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb **
  A.pts_to rc_tbl #prc vrc ** A.pts_to msg #pm vm **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
        Seq.length vst == 25 /\ Seq.length vb == 25 /\
        vst == Loops.repeati (Seq.length vm / SZ.v r)
                 (absorb_step (SZ.v r) (padded (SZ.v r) suffix vm)) zero_state)
{
  A.pts_to_len st;
  A.pts_to_len msg;
  let q = SZ.div n r;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi q)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
    pts_to i vi ** A.pts_to st vst ** A.pts_to b vb **
    A.pts_to rc_tbl #prc vrc ** A.pts_to msg #pm vm **
    pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\
          SZ.v vi <= Seq.length vm / SZ.v r /\
          vst == Loops.repeati (SZ.v vi)
                   (absorb_step (SZ.v r) (padded (SZ.v r) suffix vm)) zero_state)
  decreases (SZ.v q - SZ.v (!i))
  {
    let vi = !i;
    let off = SZ.mul vi r;
    Math.lemma_mult_le_right (SZ.v r) (SZ.v vi + 1) (SZ.v n / SZ.v r);
    Math.distributivity_add_left (SZ.v vi) 1 (SZ.v r);
    Math.multiply_fractions (SZ.v n) (SZ.v r);
    assert (pure (SZ.v off + SZ.v r <= Seq.length vm));
    with vst0. assert (A.pts_to st vst0);
    block_at_full (SZ.v r) suffix vm (SZ.v vi);
    Loops.unfold_repeati (SZ.v vi)
      (absorb_step (SZ.v r) (padded (SZ.v r) suffix vm)) zero_state;
    xor_block_at st msg off r;
    permute_impl st b rc_tbl;
    i := SZ.add vi 1sz;
  };
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** Build the last block -- the [len msg % r] leftover bytes plus pad10*1 with
    the domain-separation suffix -- into [blk], which must be zeroed. *)
inline_for_extraction
fn last_block (blk: A.array S8.t) (msg: A.array S8.t) (n: SZ.t) (r: SZ.t) (suffix: U8.t)
              (#vk0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to blk vk0 ** A.pts_to msg #pm vm **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\ Seq.length vk0 == SZ.v r)
         ** pure (SZ.v n == Seq.length vm)
ensures exists* (vk: Seq.seq S8.t).
  A.pts_to blk vk ** A.pts_to msg #pm vm **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\ Seq.length vk == SZ.v r /\
        vk == block_at (SZ.v r) (padded (SZ.v r) suffix vm) (Seq.length vm / SZ.v r))
{
  A.pts_to_len blk;
  A.pts_to_len msg;
  let m = SZ.rem n r;
  Math.euclidean_division_definition (SZ.v n) (SZ.v r);
  copy_range blk 0sz msg (SZ.sub n m) m;
  let mut k = m;
  while (let vk1 = !k; SZ.lt vk1 r)
  invariant exists* (vki: SZ.t) (vk: Seq.seq S8.t).
    pts_to k vki ** A.pts_to blk vk ** A.pts_to msg #pm vm **
    pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\ Seq.length vk == SZ.v r /\
          SZ.v m <= SZ.v vki /\ SZ.v vki <= SZ.v r /\ SZ.v m == Seq.length vm % SZ.v r /\
          (forall (t: nat). t < SZ.v m ==>
             Seq.index vk t == Seq.index vm (Seq.length vm - SZ.v m + t)) /\
          (forall (t: nat). SZ.v m <= t /\ t < SZ.v vki ==>
             Seq.index vk t == pad_byte suffix (SZ.v r - SZ.v m) (t - SZ.v m)))
  decreases (SZ.v r - SZ.v (!k))
  {
    let vki = !k;
    let a = (if SZ.eq vki m then suffix else 0uy);
    let z = (if SZ.eq vki (SZ.sub r 1sz) then 0x80uy else 0uy);
    A.((blk.(vki) <- S8.classify (U8.logor a z)));
    k := SZ.add vki 1sz;
  };
  with vk. assert (A.pts_to blk vk);
  assert (pure (Seq.length vk == SZ.v r /\ SZ.v m == Seq.length vm % SZ.v r));
  assert (pure (forall (t: nat). t < Seq.length vm % SZ.v r ==>
                  Seq.index vk t == Seq.index vm (Seq.length vm - Seq.length vm % SZ.v r + t)));
  assert (pure (forall (t: nat). Seq.length vm % SZ.v r <= t /\ t < SZ.v r ==>
                  Seq.index vk t ==
                  pad_byte suffix (SZ.v r - Seq.length vm % SZ.v r)
                                  (t - Seq.length vm % SZ.v r)));
  block_at_last (SZ.v r) suffix (reveal vm) (reveal vk);
  assert (pure (reveal vk ==
                block_at (SZ.v r) (padded (SZ.v r) suffix vm) (Seq.length vm / SZ.v r)));
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** The whole absorb phase: [st <- absorb r suffix msg]. *)
inline_for_extraction
fn absorb_impl (st: A.array S64.t) (b: A.array S64.t)
               (rc_tbl: A.array S64.t)
               (msg: A.array S8.t) (n: SZ.t) (r: SZ.t) (suffix: U8.t)
               (#vst0: erased (Seq.seq S64.t))
               (#vb0: erased (Seq.seq S64.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
               (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 **
         A.pts_to rc_tbl #prc vrc ** A.pts_to msg #pm vm **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
               Seq.length vst0 == 25 /\
               Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
         ** pure (SZ.v n == Seq.length vm)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb **
  A.pts_to rc_tbl #prc vrc ** A.pts_to msg #pm vm **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
        Seq.length vst == 25 /\ Seq.length vb == 25 /\
        vst == absorb (SZ.v r) suffix vm)
{
  A.pts_to_len st;
  A.pts_to_len msg;
  zero_state_impl st;
  absorb_full st b rc_tbl msg n r (G.hide suffix);
  let z8 = S8.classify 0uy;
  let mut arr = [| z8; 200sz |];
  Mem.track arr;
  A.pts_to_len arr;
  let blk = Sub.sub arr 0sz r;
  last_block blk msg n r suffix;
  with vk. assert (A.pts_to blk vk);
  nblocks_eq (SZ.v r) vm;
  Loops.unfold_repeati (Seq.length vm / SZ.v r)
    (absorb_step (SZ.v r) (padded (SZ.v r) suffix vm)) zero_state;
  xor_block_at st blk 0sz r;
  permute_impl st b rc_tbl;
  Sub.unsub arr 0 (SZ.v r) blk;
  Mem.wipe arr 200sz;
  ()
}

#pop-options

(** {2 Squeezing} *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** Write [cnt] bytes of the current state to [out[base ..)]. *)
inline_for_extraction
fn squeeze_block (out: A.array S8.t) (base: SZ.t) (cnt: SZ.t)
                 (st: A.array S64.t) (#pst: perm) (#vst: erased (Seq.seq S64.t))
                 (#vout0: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to st #pst vst **
         pure (Seq.length vst == 25 /\ SZ.v cnt <= 200 /\
               SZ.v base + SZ.v cnt <= Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to st #pst vst **
  pure (Seq.length vst == 25 /\ SZ.v cnt <= 200 /\ Seq.length vout == Seq.length vout0 /\
        SZ.v base + SZ.v cnt <= Seq.length vout /\
        (forall (k: nat). SZ.v base <= k /\ k < SZ.v base + SZ.v cnt ==>
           Seq.index vout k == state_byte vst (k - SZ.v base)) /\
        (forall (k: nat). k < Seq.length vout0 /\ (k < SZ.v base \/ SZ.v base + SZ.v cnt <= k) ==>
           Seq.index vout k == Seq.index vout0 k))
{
  A.pts_to_len out;
  A.pts_to_len st;
  let mut t = 0sz;
  while (let vt = !t; SZ.lt vt cnt)
  invariant exists* (vt: SZ.t) (vout: Seq.seq S8.t).
    pts_to t vt ** A.pts_to out vout ** A.pts_to st #pst vst **
    pure (Seq.length vst == 25 /\ SZ.v cnt <= 200 /\ SZ.v vt <= SZ.v cnt /\
          Seq.length vout == Seq.length vout0 /\
          SZ.v base + SZ.v cnt <= Seq.length vout /\
          (forall (k: nat). SZ.v base <= k /\ k < SZ.v base + SZ.v vt ==>
             Seq.index vout k == state_byte vst (k - SZ.v base)) /\
          (forall (k: nat). k < Seq.length vout0 /\
             (k < SZ.v base \/ SZ.v base + SZ.v vt <= k) ==>
             Seq.index vout k == Seq.index vout0 k))
  decreases (SZ.v cnt - SZ.v (!t))
  {
    let vt = !t;
    let lane = SZ.div vt 8sz;
    let byte = SZ.rem vt 8sz;
    Math.lemma_div_le (SZ.v vt) 199 8;
    assert (pure (SZ.v lane < 25 /\ SZ.v byte < 8));
    let x = A.(st.(lane));
    A.((out.(SZ.add base vt) <- Cast.u64_to_u8 (shiftr_u32 x (shift8 byte))));
    t := SZ.add vt 1sz;
  };
}

#pop-options

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

(** The whole squeeze phase: [out <- squeeze r st (len out)]. *)
inline_for_extraction
fn squeeze_impl (out: A.array S8.t) (outlen: SZ.t) (st: A.array S64.t) (b: A.array S64.t)
                (rc_tbl: A.array S64.t) (r: SZ.t)
                (#vout0: erased (Seq.seq S8.t)) (#vst0: erased (Seq.seq S64.t))
                (#vb0: erased (Seq.seq S64.t))
                (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to out vout0 ** A.pts_to st vst0 ** A.pts_to b vb0 **
         A.pts_to rc_tbl #prc vrc **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
               Seq.length vst0 == 25 /\
               Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
         ** pure (SZ.v outlen == Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t) (vst: Seq.seq S64.t)
                (vb: Seq.seq S64.t).
  A.pts_to out vout ** A.pts_to st vst ** A.pts_to b vb **
  A.pts_to rc_tbl #prc vrc **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
        Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
        Seq.length vout == Seq.length vout0 /\
        vout == squeeze (SZ.v r) vst0 (Seq.length vout0))
{
  A.pts_to_len out;
  A.pts_to_len st;
  let mut base = 0sz;
  while (let vb1 = !base; SZ.lt vb1 outlen)
  invariant exists* (vbase: SZ.t) (vout: Seq.seq S8.t) (vst: Seq.seq S64.t)
                    (vb: Seq.seq S64.t).
    pts_to base vbase ** A.pts_to out vout ** A.pts_to st vst **
    A.pts_to b vb **
    A.pts_to rc_tbl #prc vrc **
    pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
          Seq.length vst0 == 25 /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\
          Seq.length vout == Seq.length vout0 /\
          SZ.v vbase <= Seq.length vout0 /\
          (SZ.v vbase < Seq.length vout0 ==>
             (SZ.v vbase % SZ.v r == 0 /\
              vst == squeeze_state (SZ.v vbase / SZ.v r) vst0)) /\
          (forall (k: nat). k < SZ.v vbase ==>
             Seq.index vout k == Seq.index (squeeze (SZ.v r) vst0 (Seq.length vout0)) k))
  decreases (Seq.length vout0 - SZ.v (!base))
  {
    let vbase = !base;
    let q = SZ.div vbase r;
    let cnt = szmin r (SZ.sub outlen vbase);
    Math.euclidean_division_definition (SZ.v vbase) (SZ.v r);
    squeeze_range_eq (SZ.v r) (reveal vst0) (Seq.length vout0) (SZ.v vbase) (SZ.v cnt);
    squeeze_block out vbase cnt st;
    Loops.unfold_repeati (SZ.v q) (fun _ st -> permute st) (reveal vst0);
    permute_impl st b rc_tbl;
    Math.lemma_div_plus 0 (SZ.v q) (SZ.v r);
    Math.lemma_mod_plus 0 (SZ.v q) (SZ.v r);
    Math.distributivity_add_left (SZ.v q) 1 (SZ.v r);
    Math.lemma_div_plus 0 (SZ.v q + 1) (SZ.v r);
    Math.lemma_mod_plus 0 (SZ.v q + 1) (SZ.v r);
    base := SZ.add vbase cnt;
  };
  with vout. assert (A.pts_to out vout);
  assert (pure (Seq.length (squeeze (SZ.v r) vst0 (Seq.length vout0)) == Seq.length vout0));
  assert (pure (reveal vout `Seq.equal` squeeze (SZ.v r) vst0 (Seq.length vout0)));
}

#pop-options
