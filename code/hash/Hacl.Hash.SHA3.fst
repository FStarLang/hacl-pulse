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

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module G = Pulse.Lib.GlobalArray


(** {2 The constant tables}

    Both are [static const] arrays in the program image; see
    [Hacl.Impl.Table].  The rho offsets are public [uint32_t]s -- they are
    shift amounts, and how far a lane rotates depends on nothing secret -- so
    that table is not even a secret one. *)

let rc_arr   : G.static_array S64.t = G.mk_static_array rc_list
let rotc_arr : G.static_array U32.t = G.mk_static_array rotc_list

let table_lens (_: unit)
  : Lemma (Seq.length (G.static_array_elems rc_arr) == 24 /\
           Seq.length (G.static_array_elems rotc_arr) == 25)
  = assert_norm (List.Tot.length rc_list == 24);
    assert_norm (List.Tot.length rotc_list == 25)


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

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  let rotc_tbl = table rotc_arr 25sz;
  rotc_seq_ok ();

  absorb_impl st bb cc rotc_tbl rc_tbl msg r suffix;
  squeeze_impl out st bb cc rotc_tbl rc_tbl r;

  drop_table rotc_tbl;
  drop_table rc_tbl;
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
