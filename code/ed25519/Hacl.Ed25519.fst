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

(** Ed25519, as RFC 8032 describes it.

    Everything below is assembled from parts that are already verified:
    the field and the ladder come from Curve25519, the group law from
    [Hacl.Ed25519.Point], the encodings from [Hacl.Ed25519.Encoding], the
    arithmetic modulo the group order from [Hacl.Ed25519.Scalar], and the
    hash from [Hacl.Streaming.SHA2].  What is left is the plumbing, and the
    one thing that makes it interesting: every hash in the protocol is over
    a *concatenation*, and rather than build the concatenation in memory
    the streaming interface is used to feed the pieces one after another.
    Signing therefore needs no buffer proportional to the message. *)
module Hacl.Ed25519

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Bytes
open Spec.Curve25519.Field
open Hacl.Curve25519.Field
open Hacl.Ed25519.Encoding

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module C = Spec.Curve25519
module E = Spec.Ed25519
module Sc = Spec.Ed25519.Scalar
module P = Hacl.Ed25519.Point
module Table = Hacl.Impl.Table
module Tables = Hacl.Ed25519.Tables
module Scalar = Hacl.Ed25519.Scalar
module Hash = Hacl.Hash.SHA2
module Stream = Hacl.Streaming.SHA2
module SHA2 = Spec.SHA2

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

(** {2 The base point}

    [g] is a constant, so its extended coordinates are built on the spot
    from the two tables: [z] is one and [t] is [x y]. *)

fn point_mul_g (ox oy oz ot: S.slice S64.t) (ks: S.slice S8.t)
               (#vox: erased (Seq.seq S64.t)) (#voy: erased (Seq.seq S64.t))
               (#voz: erased (Seq.seq S64.t)) (#vot: erased (Seq.seq S64.t))
               (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  S.pts_to ot vot ** S.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl)
ensures exists* (wx: Seq.seq S64.t) (wy: Seq.seq S64.t)
                (wz: Seq.seq S64.t) (wt: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  S.pts_to ot wt ** S.pts_to ks #pk vk **
  pure (P.pt_ok wx wy wz wt /\ P.pt wx wy wz wt == E.point_mul_g vk)
{
  S.pts_to_len ox;
  let zz = S64.zero;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let gz = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let gt = S.from_array a2 16sz;
  let mut a3 = [| zz; 31sz |]; A.pts_to_len a3; let tw = S.from_array a3 31sz;
  let mut a4 = [| zz; 16sz |]; A.pts_to_len a4; let gx = S.from_array a4 16sz;
  let mut a5 = [| zz; 16sz |]; A.pts_to_len a5; let gy = S.from_array a5 16sz;
  S.pts_to_len gz; S.pts_to_len gt; S.pts_to_len tw;
  S.pts_to_len gx; S.pts_to_len gy;

  (* The tables are read-only, but [point_mul] wants the four coordinates
     at one permission, so the two constants are copied in. *)
  let gxt = Table.table Tables.gx_arr 16sz;
  copy gx gxt;
  Table.drop_table gxt;
  let gyt = Table.table Tables.gy_arr 16sz;
  copy gy gyt;
  Table.drop_table gyt;
  Tables.gx_ok ();
  Tables.gy_ok ();
  assert_norm (1 < base);
  P.set_small gz 1uL;
  fmul gt gx gy tw;
  P.point_mul ox oy oz ot gx gy gz gt ks;
  S.to_array gz;
  S.to_array gt;
  S.to_array tw;
  S.to_array gx;
  S.to_array gy;
}

(** {2 Hash to scalar}

    Every hash in Ed25519 is immediately read little-endian and reduced
    modulo the group order, then written back out as thirty-two bytes. *)

fn hash_to_scalar (out: S.slice S8.t) (h: S.slice S8.t)
                  (#vout: erased (Seq.seq S8.t))
                  (#ph: perm) (#vh: erased (Seq.lseq S8.t 64))
requires S.pts_to out vout ** S.pts_to h #ph vh **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to h #ph vh **
  pure (vout' == E.scalar_bytes (E.sha512_mod_q vh))
{
  let zz = S64.zero;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let acc = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let t1 = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let t2 = S.from_array a3 16sz;
  S.pts_to_len acc; S.pts_to_len t1; S.pts_to_len t2;
  Scalar.reduce_op acc t1 t2 h;
  store out acc;
  S.to_array acc;
  S.to_array t1;
  S.to_array t2;
}

(** {2 Keys}

    The seed is hashed once; the low half clamps into the scalar and the
    high half is the nonce prefix. *)

#push-options "--z3rlimit 150"

fn secret_expand (low prefix: S.slice S8.t) (secret: S.slice S8.t)
                 (#vlow: erased (Seq.seq S8.t)) (#vpre: erased (Seq.seq S8.t))
                 (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires S.pts_to low vlow ** S.pts_to prefix vpre ** S.pts_to secret #ps vs **
  pure (Seq.length vlow == 32 /\ Seq.length vpre == 32)
ensures exists* (wl: Seq.seq S8.t) (wp: Seq.seq S8.t).
  S.pts_to low wl ** S.pts_to prefix wp ** S.pts_to secret #ps vs **
  pure (wl == E.expand_low vs /\ wp == E.expand_prefix vs)
{
  S.pts_to_len low; S.pts_to_len prefix; S.pts_to_len secret;
  let z8 = S8.zero;
  let mut a1 = [| z8; 64sz |]; A.pts_to_len a1; let h = S.from_array a1 64sz;
  S.pts_to_len h;
  assert_norm (32 < pow2 61);
  Hash.sha512 h secret;
  with vh. assert (S.pts_to h vh);
  S.pts_to_len h;

  let lo = S.subslice h 0sz 32sz;
  Hacl.Curve25519.clamp low lo;
  unfold S.subslice_rest;
  S.join lo _ _;
  S.join _ _ h;
  with vh2. assert (S.pts_to h vh2);
  S.pts_to_len h;
  assert (pure (Seq.equal vh2 vh));

  let hi = S.subslice h 32sz 64sz;
  with vhi. assert (S.pts_to hi vhi);
  S.pts_to_len hi;
  Hacl.Impl.Copy.copy_prefix prefix hi 32sz;
  with wp. assert (S.pts_to prefix wp);
  assert (pure (Seq.equal wp vhi));
  unfold S.subslice_rest;
  S.join hi _ _;
  S.join _ _ h;

  with vh'. assert (S.pts_to h vh');
  assert (pure (Seq.equal vh' vh));
  assert (pure (reveal vh == E.sha512 vs));
  assert (pure (E.expand_prefix vs == Seq.slice (E.sha512 vs) 32 64));
  assert (pure (E.expand_low vs == C.clamp (Seq.slice (E.sha512 vs) 0 32)));
  assert (pure (reveal vhi == Seq.slice (reveal vh) 32 64));
  assert (pure (reveal wp == E.expand_prefix vs));
  S.to_array h;
}

#pop-options

fn secret_to_public (out: S.slice S8.t) (secret: S.slice S8.t)
                    (#vout: erased (Seq.seq S8.t))
                    (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires S.pts_to out vout ** S.pts_to secret #ps vs **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to secret #ps vs **
  pure (vout' == E.secret_to_public vs)
{
  S.pts_to_len out;
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut b1 = [| z8; 32sz |]; A.pts_to_len b1; let low = S.from_array b1 32sz;
  let mut b2 = [| z8; 32sz |]; A.pts_to_len b2; let pre = S.from_array b2 32sz;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let px = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let py = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let pz = S.from_array a3 16sz;
  let mut a4 = [| zz; 16sz |]; A.pts_to_len a4; let pt = S.from_array a4 16sz;
  S.pts_to_len low; S.pts_to_len pre;
  S.pts_to_len px; S.pts_to_len py; S.pts_to_len pz; S.pts_to_len pt;

  secret_expand low pre secret;
  point_mul_g px py pz pt low;
  point_compress out px py pz pt;

  S.to_array low; S.to_array pre;
  S.to_array px; S.to_array py; S.to_array pz; S.to_array pt;
}

(** The ninety-six byte expanded key: public key, scalar, nonce prefix.

    The three pieces are written one at a time, each into its own
    subslice, so only one subslice is ever live. *)
fn expand_keys (out: S.slice S8.t) (secret: S.slice S8.t)
               (#vout: erased (Seq.seq S8.t))
               (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires S.pts_to out vout ** S.pts_to secret #ps vs **
  pure (Seq.length vout == 96)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to secret #ps vs **
  pure (vout' == E.expand_keys vs)
{
  S.pts_to_len out;
  let z8 = S8.zero;
  let mut b1 = [| z8; 32sz |]; A.pts_to_len b1; let low = S.from_array b1 32sz;
  let mut b2 = [| z8; 32sz |]; A.pts_to_len b2; let pre = S.from_array b2 32sz;
  S.pts_to_len low; S.pts_to_len pre;
  secret_expand low pre secret;
  with wl. assert (S.pts_to low wl);
  with wp. assert (S.pts_to pre wp);
  S.pts_to_len low; S.pts_to_len pre;

  let s0 = S.subslice out 0sz 32sz;
  secret_to_public s0 secret;
  with pubv. assert (S.pts_to s0 pubv);
  S.pts_to_len s0;
  unfold S.subslice_rest;
  S.join s0 _ _;
  S.join _ _ out;
  with o1. assert (S.pts_to out o1);
  S.pts_to_len out;

  let s1 = S.subslice out 32sz 64sz;
  Hacl.Impl.Copy.copy_prefix s1 low 32sz;
  with v1. assert (S.pts_to s1 v1);
  assert (pure (Seq.equal v1 wl));
  unfold S.subslice_rest;
  S.join s1 _ _;
  S.join _ _ out;
  with o2. assert (S.pts_to out o2);
  S.pts_to_len out;

  let s2 = S.subslice out 64sz 96sz;
  Hacl.Impl.Copy.copy_prefix s2 pre 32sz;
  with v2. assert (S.pts_to s2 v2);
  assert (pure (Seq.equal v2 wp));
  unfold S.subslice_rest;
  S.join s2 _ _;
  S.join _ _ out;
  with o3. assert (S.pts_to out o3);
  S.pts_to_len out;

  S.to_array low;
  S.to_array pre;
  assert (pure (Seq.equal o3 (Seq.append pubv (Seq.append wl wp))));
}

#pop-options
