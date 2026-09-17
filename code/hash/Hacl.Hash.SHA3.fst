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
    with a different rate and domain-separation byte.  The state and the two
    scratch buffers live on the stack and the two constant tables live in the
    program image, so nothing here allocates. *)
module Hacl.Hash.SHA3

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants
open Hacl.Impl.Table
open Hacl.Hash.SHA3.Core
open Hacl.Hash.SHA3.Sponge

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module G = Pulse.Lib.GlobalArray

(** {2 The constant tables}

    It is a [static const] array in the program image; see [Hacl.Impl.Table].
    The rho offsets used to live in a table beside it, but every round is now
    unrolled and every rotation is an immediate, so there is nothing left to
    look up. *)

let rc_arr : G.static_array S64.t = G.mk_static_array rc_list

let table_lens (_: unit)
  : Lemma (Seq.length (G.static_array_elems rc_arr) == 24)
  = assert_norm (List.Tot.length rc_list == 24)

(** {2 The sponge, wrapped}

    [keccak_impl] is the only real code in this module; the named algorithms
    below are partial applications of it. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn keccak_impl (out: A.array S8.t) (out_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t) (r: SZ.t) (suffix: U8.t)
               (#vout0: erased (Seq.seq S8.t))
               (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm **
         pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200)
         ** pure (SZ.v out_len == Seq.length vout0)
         ** pure (SZ.v msg_len == Seq.length vm)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (SZ.v r % 8 == 0 /\ 0 < SZ.v r /\ SZ.v r < 200 /\
        vout == keccak (SZ.v r) suffix vm (Seq.length vout0))
{
  A.pts_to_len out;
  let z64 = S64.classify 0uL;

  let mut starr = [| z64; 25sz |];
  A.pts_to_len starr;
  A.pts_to_len starr;

  let mut barr = [| z64; 25sz |];
  A.pts_to_len barr;
  A.pts_to_len barr;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;

  absorb_impl starr barr rc_tbl msg msg_len r suffix;
  squeeze_impl out out_len starr barr rc_tbl r;

  drop_table rc_tbl;
  ()
}

#pop-options

(** {2 The named algorithms} *)

fn sha3_224 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm ** pure (Seq.length vout0 == 28)
         ** pure (SZ.v msg_len == Seq.length vm)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (Seq.length vout0 == 28 /\ vout == Spec.SHA3.sha3_224 vm)
{
  keccak_impl out 28sz msg msg_len 144sz sha3_suffix;
}

fn sha3_256 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm ** pure (Seq.length vout0 == 32)
         ** pure (SZ.v msg_len == Seq.length vm)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (Seq.length vout0 == 32 /\ vout == Spec.SHA3.sha3_256 vm)
{
  keccak_impl out 32sz msg msg_len 136sz sha3_suffix;
}

fn sha3_384 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm ** pure (Seq.length vout0 == 48)
         ** pure (SZ.v msg_len == Seq.length vm)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (Seq.length vout0 == 48 /\ vout == Spec.SHA3.sha3_384 vm)
{
  keccak_impl out 48sz msg msg_len 104sz sha3_suffix;
}

fn sha3_512 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm ** pure (Seq.length vout0 == 64)
         ** pure (SZ.v msg_len == Seq.length vm)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (Seq.length vout0 == 64 /\ vout == Spec.SHA3.sha3_512 vm)
{
  keccak_impl out 64sz msg msg_len 72sz sha3_suffix;
}

fn shake128 (out: A.array S8.t) (out_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm
         ** pure (SZ.v msg_len == Seq.length vm)
         ** pure (SZ.v out_len == Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (vout == Spec.SHA3.shake128 vm (Seq.length vout0))
{
  keccak_impl out out_len msg msg_len 168sz shake_suffix;
}

fn shake256 (out: A.array S8.t) (out_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
                 (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm
         ** pure (SZ.v msg_len == Seq.length vm)
         ** pure (SZ.v out_len == Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to out vout ** A.pts_to msg #pm vm **
  pure (vout == Spec.SHA3.shake256 vm (Seq.length vout0))
{
  keccak_impl out out_len msg msg_len 136sz shake_suffix;
}
