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

(** SHA3-224/256/384/512 and SHAKE128/256, one shot.

    Every entry point is the same three lines -- allocate, absorb, squeeze --
    with a different rate and domain-separation byte.  The state, the two
    scratch buffers and the two constant tables all live on the stack, so
    nothing here allocates. *)
module Hacl.Hash.SHA3

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants
open Hacl.Hash.SHA3.Core
open Hacl.Hash.SHA3.Sponge

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32


(** {2 The constant tables}

    Custard cannot emit a constant global, so both tables are written into a
    stack array on entry, exactly as the SHA-2 round constants are. *)

#push-options "--z3rlimit 1000 --fuel 1 --ifuel 1"

(** The twenty-four iota constants. *)
fn fill_rc (b: S.slice S64.t) (#v0: erased (Seq.seq S64.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 24 (S64.classify 0uL))
ensures S.pts_to b (rc <: Seq.seq S64.t)
{
  S.pts_to_len b;
  S.((b.(0sz) <- S64.classify 0x0000000000000001uL)); S.pts_to_len b;
  S.((b.(1sz) <- S64.classify 0x0000000000008082uL)); S.pts_to_len b;
  S.((b.(2sz) <- S64.classify 0x800000000000808auL)); S.pts_to_len b;
  S.((b.(3sz) <- S64.classify 0x8000000080008000uL)); S.pts_to_len b;
  S.((b.(4sz) <- S64.classify 0x000000000000808buL)); S.pts_to_len b;
  S.((b.(5sz) <- S64.classify 0x0000000080000001uL)); S.pts_to_len b;
  S.((b.(6sz) <- S64.classify 0x8000000080008081uL)); S.pts_to_len b;
  S.((b.(7sz) <- S64.classify 0x8000000000008009uL)); S.pts_to_len b;
  S.((b.(8sz) <- S64.classify 0x000000000000008auL)); S.pts_to_len b;
  S.((b.(9sz) <- S64.classify 0x0000000000000088uL)); S.pts_to_len b;
  S.((b.(10sz) <- S64.classify 0x0000000080008009uL)); S.pts_to_len b;
  S.((b.(11sz) <- S64.classify 0x000000008000000auL)); S.pts_to_len b;
  S.((b.(12sz) <- S64.classify 0x000000008000808buL)); S.pts_to_len b;
  S.((b.(13sz) <- S64.classify 0x800000000000008buL)); S.pts_to_len b;
  S.((b.(14sz) <- S64.classify 0x8000000000008089uL)); S.pts_to_len b;
  S.((b.(15sz) <- S64.classify 0x8000000000008003uL)); S.pts_to_len b;
  S.((b.(16sz) <- S64.classify 0x8000000000008002uL)); S.pts_to_len b;
  S.((b.(17sz) <- S64.classify 0x8000000000000080uL)); S.pts_to_len b;
  S.((b.(18sz) <- S64.classify 0x000000000000800auL)); S.pts_to_len b;
  S.((b.(19sz) <- S64.classify 0x800000008000000auL)); S.pts_to_len b;
  S.((b.(20sz) <- S64.classify 0x8000000080008081uL)); S.pts_to_len b;
  S.((b.(21sz) <- S64.classify 0x8000000000008080uL)); S.pts_to_len b;
  S.((b.(22sz) <- S64.classify 0x0000000080000001uL)); S.pts_to_len b;
  S.((b.(23sz) <- S64.classify 0x8000000080008008uL)); S.pts_to_len b;
}

(** [rotc] as a machine function.  A twenty-five way switch on a public
    index; the offsets are shift amounts and depend on nothing secret. *)
inline_for_extraction
let rotc_u32 (i: SZ.t { SZ.v i < 25 }) : (x: U32.t { U32.v x == rotc (SZ.v i) }) =
  if SZ.eq i  0sz then  0ul else
  if SZ.eq i  1sz then  1ul else
  if SZ.eq i  2sz then 62ul else
  if SZ.eq i  3sz then 28ul else
  if SZ.eq i  4sz then 27ul else
  if SZ.eq i  5sz then 36ul else
  if SZ.eq i  6sz then 44ul else
  if SZ.eq i  7sz then  6ul else
  if SZ.eq i  8sz then 55ul else
  if SZ.eq i  9sz then 20ul else
  if SZ.eq i 10sz then  3ul else
  if SZ.eq i 11sz then 10ul else
  if SZ.eq i 12sz then 43ul else
  if SZ.eq i 13sz then 25ul else
  if SZ.eq i 14sz then 39ul else
  if SZ.eq i 15sz then 41ul else
  if SZ.eq i 16sz then 45ul else
  if SZ.eq i 17sz then 15ul else
  if SZ.eq i 18sz then 21ul else
  if SZ.eq i 19sz then  8ul else
  if SZ.eq i 20sz then 18ul else
  if SZ.eq i 21sz then  2ul else
  if SZ.eq i 22sz then 61ul else
  if SZ.eq i 23sz then 56ul else
  14ul

(** The twenty-five rho offsets. *)
fn fill_rotc (b: S.slice U32.t) (#v0: erased (Seq.seq U32.t))
requires S.pts_to b v0 ** pure (Seq.length v0 == 25)
ensures exists* (v: Seq.seq U32.t).
  S.pts_to b v **
  pure (Seq.length v == 25 /\ (forall (j: nat). j < 25 ==> U32.v (Seq.index v j) == rotc j))
{
  S.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 25sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq U32.t).
    pts_to i vi ** S.pts_to b v **
    pure (SZ.v vi <= 25 /\ Seq.length v == 25 /\
          (forall (j: nat). j < SZ.v vi ==> U32.v (Seq.index v j) == rotc j))
  decreases (25 - SZ.v (!i))
  {
    let vi = !i;
    S.((b.(vi) <- rotc_u32 vi));
    i := SZ.add vi 1sz;
  };
}

#pop-options


(** {2 The sponge, wrapped}

    [keccak_impl] is the only real code in this module; the named algorithms
    below are partial applications of it. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn keccak_impl (out: S.slice S8.t) (msg: S.slice S8.t) (r: SZ.t) (suffix: U8.t)
               (#vout0: erased (Seq.seq S8.t))
               (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200)
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
        vout == keccak (SZ.v r) suffix vm (Seq.length vout0))
{
  S.pts_to_len out;
  let z64 = S64.classify 0uL;

  let mut starr = [| z64; 25sz |];
  A.pts_to_len starr;
  let st = S.from_array starr 25sz;
  S.pts_to_len st;

  let mut barr = [| z64; 25sz |];
  A.pts_to_len barr;
  let bb = S.from_array barr 25sz;
  S.pts_to_len bb;

  let mut carr = [| z64; 5sz |];
  A.pts_to_len carr;
  let cc = S.from_array carr 5sz;
  S.pts_to_len cc;

  let mut rcarr = [| z64; 24sz |];
  A.pts_to_len rcarr;
  let rc_tbl = S.from_array rcarr 24sz;
  S.pts_to_len rc_tbl;
  fill_rc rc_tbl;

  let mut rotarr = [| 0ul; 25sz |];
  A.pts_to_len rotarr;
  let rotc_tbl = S.from_array rotarr 25sz;
  S.pts_to_len rotc_tbl;
  fill_rotc rotc_tbl;

  absorb_impl st bb cc rotc_tbl rc_tbl msg r suffix;
  squeeze_impl out st bb cc rotc_tbl rc_tbl r;

  S.to_array rotc_tbl;
  S.to_array rc_tbl;
  S.to_array cc;
  S.to_array bb;
  S.to_array st;
}

#pop-options


(** {2 The named algorithms} *)

fn sha3_224_impl (out: S.slice S8.t) (msg: S.slice S8.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm ** pure (Seq.length vout0 == 28)
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (Seq.length vout0 == 28 /\ vout == sha3_224 vm)
{
  keccak_impl out msg 144sz sha3_suffix;
}

fn sha3_256_impl (out: S.slice S8.t) (msg: S.slice S8.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm ** pure (Seq.length vout0 == 32)
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (Seq.length vout0 == 32 /\ vout == sha3_256 vm)
{
  keccak_impl out msg 136sz sha3_suffix;
}

fn sha3_384_impl (out: S.slice S8.t) (msg: S.slice S8.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm ** pure (Seq.length vout0 == 48)
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (Seq.length vout0 == 48 /\ vout == sha3_384 vm)
{
  keccak_impl out msg 104sz sha3_suffix;
}

fn sha3_512_impl (out: S.slice S8.t) (msg: S.slice S8.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm ** pure (Seq.length vout0 == 64)
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (Seq.length vout0 == 64 /\ vout == sha3_512 vm)
{
  keccak_impl out msg 72sz sha3_suffix;
}

fn shake128_impl (out: S.slice S8.t) (msg: S.slice S8.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (vout == shake128 vm (Seq.length vout0))
{
  keccak_impl out msg 168sz shake_suffix;
}

fn shake256_impl (out: S.slice S8.t) (msg: S.slice S8.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires S.pts_to out vout0 ** S.pts_to msg #pm vm
ensures exists* (vout: Seq.seq S8.t).
  S.pts_to out vout ** S.pts_to msg #pm vm **
  pure (vout == shake256 vm (Seq.length vout0))
{
  keccak_impl out msg 136sz shake_suffix;
}
