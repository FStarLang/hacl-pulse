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

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module C = Spec.Curve25519
module E = Spec.Ed25519
module Sc = Spec.Ed25519.Scalar
module P = Hacl.Ed25519.Point
module Table = Hacl.Impl.Table
module Sub = Hacl.Impl.Sub
module Tables = Hacl.Ed25519.Tables
module Scalar = Hacl.Ed25519.Scalar
module Hash = Hacl.Hash.SHA2
module Stream = Hacl.Streaming.SHA2
module SHA2 = Spec.SHA2

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

(** {2 The base point}

    [g] is a constant, so its extended coordinates are built on the spot
    from the two tables: [z] is one and [t] is [x y]. *)

fn point_mul_g (ox oy oz ot: A.array S64.t) (ks: A.array S8.t)
               (#vox: erased (Seq.seq S64.t)) (#voy: erased (Seq.seq S64.t))
               (#voz: erased (Seq.seq S64.t)) (#vot: erased (Seq.seq S64.t))
               (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ot vot ** A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl)
ensures exists* (wx: Seq.seq S64.t) (wy: Seq.seq S64.t)
                (wz: Seq.seq S64.t) (wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ot wt ** A.pts_to ks #pk vk **
  pure (P.pt_ok wx wy wz wt /\ P.pt wx wy wz wt == E.point_mul_g vk)
{
  A.pts_to_len ox;
  let zz = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut a1 = [| zz; 8sz |]; A.pts_to_len a1; let mut a2 = [| zz; 8sz |]; A.pts_to_len a2; let mut a3 = [| z128; 15sz |]; A.pts_to_len a3; let mut a4 = [| zz; 8sz |]; A.pts_to_len a4; let mut a5 = [| zz; 8sz |]; A.pts_to_len a5; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5;

  (* The tables are read-only, but [point_mul] wants the four coordinates
     at one permission, so the two constants are copied in. *)
  let gxt = Table.table Tables.gx_arr 8sz;
  copy a4 gxt;
  Table.drop_table gxt;
  let gyt = Table.table Tables.gy_arr 8sz;
  copy a5 gyt;
  Table.drop_table gyt;
  Tables.gx_ok ();
  Tables.gy_ok ();
  assert_norm (1 < base);
  P.set_small a1 1uL;
  fmul a2 a4 a5 a3;
  P.point_mul ox oy oz ot a4 a5 a1 a2 ks;
  ()
}

(** {2 Hash to scalar}

    Every hash in Ed25519 is immediately read little-endian and reduced
    modulo the group order, then written back out as thirty-two bytes. *)

fn hash_to_scalar (out: A.array S8.t) (h: A.array S8.t)
                  (#vout: erased (Seq.seq S8.t))
                  (#ph: perm) (#vh: erased (Seq.lseq S8.t 64))
requires A.pts_to out vout ** A.pts_to h #ph vh **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to h #ph vh **
  pure (vout' == E.scalar_bytes (E.sha512_mod_q vh))
{
  let zz = S64.zero;
  let mut a1 = [| zz; 8sz |]; A.pts_to_len a1; let mut a2 = [| zz; 8sz |]; A.pts_to_len a2; let mut a3 = [| zz; 8sz |]; A.pts_to_len a3; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  Scalar.reduce_op a1 a2 a3 h;
  store out a1;
  ()
}

(** {2 Keys}

    The seed is hashed once; the low half clamps into the scalar and the
    high half is the nonce prefix. *)

#push-options "--z3rlimit 150"

fn secret_expand (low prefix: A.array S8.t) (secret: A.array S8.t)
                 (#vlow: erased (Seq.seq S8.t)) (#vpre: erased (Seq.seq S8.t))
                 (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires A.pts_to low vlow ** A.pts_to prefix vpre ** A.pts_to secret #ps vs **
  pure (Seq.length vlow == 32 /\ Seq.length vpre == 32)
ensures exists* (wl: Seq.seq S8.t) (wp: Seq.seq S8.t).
  A.pts_to low wl ** A.pts_to prefix wp ** A.pts_to secret #ps vs **
  pure (wl == E.expand_low vs /\ wp == E.expand_prefix vs)
{
  A.pts_to_len low; A.pts_to_len prefix; A.pts_to_len secret;
  let z8 = S8.zero;
  let mut a1 = [| z8; 64sz |]; A.pts_to_len a1; A.pts_to_len a1;
  assert_norm (32 < pow2 61);
  Hash.sha512 a1 secret 32sz;
  with vh. assert (A.pts_to a1 vh);
  A.pts_to_len a1;

  let lo = Sub.sub a1 0sz 32sz;
  Hacl.Curve25519.clamp low lo;
  Sub.unsub a1 0 32 lo;
  with vh2. assert (A.pts_to a1 vh2);
  A.pts_to_len a1;
  assert (pure (Seq.equal vh2 vh));

  let hi = Sub.sub a1 32sz 64sz;
  with vhi. assert (A.pts_to hi vhi);
  A.pts_to_len hi;
  Hacl.Impl.Copy.copy_prefix prefix hi 32sz;
  with wp. assert (A.pts_to prefix wp);
  assert (pure (Seq.equal wp vhi));
  Sub.unsub a1 32 64 hi;

  with vh'. assert (A.pts_to a1 vh');
  assert (pure (Seq.equal vh' vh));
  assert (pure (reveal vh == E.sha512 vs));
  assert (pure (E.expand_prefix vs == Seq.slice (E.sha512 vs) 32 64));
  assert (pure (E.expand_low vs == C.clamp (Seq.slice (E.sha512 vs) 0 32)));
  assert (pure (reveal vhi == Seq.slice (reveal vh) 32 64));
  assert (pure (reveal wp == E.expand_prefix vs));
  ()
}

#pop-options

fn secret_to_public (out: A.array S8.t) (secret: A.array S8.t)
                    (#vout: erased (Seq.seq S8.t))
                    (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires A.pts_to out vout ** A.pts_to secret #ps vs **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to secret #ps vs **
  pure (vout' == E.secret_to_public vs)
{
  A.pts_to_len out;
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut b1 = [| z8; 32sz |]; A.pts_to_len b1; let mut b2 = [| z8; 32sz |]; A.pts_to_len b2; let mut a1 = [| zz; 8sz |]; A.pts_to_len a1; let mut a2 = [| zz; 8sz |]; A.pts_to_len a2; let mut a3 = [| zz; 8sz |]; A.pts_to_len a3; let mut a4 = [| zz; 8sz |]; A.pts_to_len a4; A.pts_to_len b1; A.pts_to_len b2;
  A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3; A.pts_to_len a4;

  secret_expand b1 b2 secret;
  point_mul_g a1 a2 a3 a4 b1;
  point_compress out a1 a2 a3 a4;

  ()
}

(** The ninety-six byte expanded key: public key, scalar, nonce prefix.

    The three pieces are written one at a time, each into its own
    subslice, so only one subslice is ever live. *)
fn expand_keys (out: A.array S8.t) (secret: A.array S8.t)
               (#vout: erased (Seq.seq S8.t))
               (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires A.pts_to out vout ** A.pts_to secret #ps vs **
  pure (Seq.length vout == 96)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to secret #ps vs **
  pure (vout' == E.expand_keys vs)
{
  A.pts_to_len out;
  let z8 = S8.zero;
  let mut b1 = [| z8; 32sz |]; A.pts_to_len b1; let mut b2 = [| z8; 32sz |]; A.pts_to_len b2; A.pts_to_len b1; A.pts_to_len b2;
  secret_expand b1 b2 secret;
  with wl. assert (A.pts_to b1 wl);
  with wp. assert (A.pts_to b2 wp);
  A.pts_to_len b1; A.pts_to_len b2;

  let s0 = Sub.sub out 0sz 32sz;
  secret_to_public s0 secret;
  with pubv. assert (A.pts_to s0 pubv);
  A.pts_to_len s0;
  Sub.unsub out 0 32 s0;
  with o1. assert (A.pts_to out o1);
  A.pts_to_len out;

  let s1 = Sub.sub out 32sz 64sz;
  Hacl.Impl.Copy.copy_prefix s1 b1 32sz;
  with v1. assert (A.pts_to s1 v1);
  assert (pure (Seq.equal v1 wl));
  Sub.unsub out 32 64 s1;
  with o2. assert (A.pts_to out o2);
  A.pts_to_len out;

  let s2 = Sub.sub out 64sz 96sz;
  Hacl.Impl.Copy.copy_prefix s2 b2 32sz;
  with v2. assert (A.pts_to s2 v2);
  assert (pure (Seq.equal v2 wp));
  Sub.unsub out 64 96 s2;
  with o3. assert (A.pts_to out o3);
  A.pts_to_len out;

  assert (pure (Seq.equal o3 (Seq.append pubv (Seq.append wl wp))));
}

#pop-options

(** {2 Hashing a concatenation}

    [H(a | msg)] and [H(a | b | msg)] without ever materialising the
    concatenation: the streaming state absorbs the pieces in order. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"

fn hash2 (out a msg: A.array S8.t) (mlen: SZ.t)
         (#vout: erased (Seq.seq S8.t))
         (#pa: perm) (#va: erased (Seq.lseq S8.t 32))
         (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to msg #pm vm **
  pure (Seq.length vout == 64 /\ SZ.fits (64 + Seq.length vm) /\
        SZ.v mlen == Seq.length vm)
returns _: unit
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to msg #pm vm **
  pure (vout' == E.sha512 (Seq.append va vm))
{
  A.pts_to_len out; A.pts_to_len a; A.pts_to_len msg;
  let z64 = S64.zero;
  let z8 = S8.zero;
  let mut c1 = [| z64; 8sz |]; A.pts_to_len c1; let mut c2 = [| z8; 128sz |]; A.pts_to_len c2; let mut c3 = [| 0sz; 1sz |]; A.pts_to_len c3; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3;
  assert_norm (E.max_msg == pow2 32);
  assert_norm (pow2 32 + 64 < pow2 61);
  Stream.sha512_init c1 c2 c3;
  Stream.sha512_update c1 c2 c3 a 32sz (Seq.empty #S8.t);
  Stream.sha512_update c1 c2 c3 msg mlen (Seq.append (Seq.empty #S8.t) va);
  Stream.sha512_digest c1 c2 c3 out
    (Seq.append (Seq.append (Seq.empty #S8.t) va) vm);
  assert (pure (Seq.equal (Seq.append (Seq.append (Seq.empty #S8.t) va) vm)
                          (Seq.append va vm)));
  ()
}

fn hash3 (out a b msg: A.array S8.t) (mlen: SZ.t)
         (#vout: erased (Seq.seq S8.t))
         (#pa: perm) (#va: erased (Seq.lseq S8.t 32))
         (#pb: perm) (#vb: erased (Seq.lseq S8.t 32))
         (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to msg #pm vm **
  pure (Seq.length vout == 64 /\ SZ.fits (64 + Seq.length vm) /\
        SZ.v mlen == Seq.length vm)
returns _: unit
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to msg #pm vm **
  pure (vout' == E.sha512 (Seq.append va (Seq.append vb vm)))
{
  A.pts_to_len out; A.pts_to_len a; A.pts_to_len b; A.pts_to_len msg;
  let z64 = S64.zero;
  let z8 = S8.zero;
  let mut c1 = [| z64; 8sz |]; A.pts_to_len c1; let mut c2 = [| z8; 128sz |]; A.pts_to_len c2; let mut c3 = [| 0sz; 1sz |]; A.pts_to_len c3; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3;
  assert_norm (E.max_msg == pow2 32);
  assert_norm (pow2 32 + 64 < pow2 61);
  Stream.sha512_init c1 c2 c3;
  Stream.sha512_update c1 c2 c3 a 32sz (Seq.empty #S8.t);
  Stream.sha512_update c1 c2 c3 b 32sz (Seq.append (Seq.empty #S8.t) va);
  Stream.sha512_update c1 c2 c3 msg mlen
    (Seq.append (Seq.append (Seq.empty #S8.t) va) vb);
  Stream.sha512_digest c1 c2 c3 out
    (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) va) vb) vm);
  assert (pure (Seq.equal
                  (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) va) vb) vm)
                  (Seq.append va (Seq.append vb vm))));
  ()
}

(** {2 A thirty-two byte scalar, reduced}

    The secret scalar is stored as thirty-two bytes but is used modulo the
    group order.  Zero-extending to sixty-four bytes lets the same
    reduction serve, and costs only the extra doublings. *)

fn scalar_reduce32 (acc t1 t2: A.array S64.t) (sb: A.array S8.t)
                   (#vacc: erased (Seq.seq S64.t))
                   (#v1: erased (Seq.seq S64.t)) (#v2: erased (Seq.seq S64.t))
                   (#psb: perm) (#vsb: erased (Seq.lseq S8.t 32))
requires A.pts_to acc vacc ** A.pts_to t1 v1 ** A.pts_to t2 v2 **
  A.pts_to sb #psb vsb **
  pure (Seq.length vacc == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl)
ensures exists* (w: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t).
  A.pts_to acc w ** A.pts_to t1 w1 ** A.pts_to t2 w2 ** A.pts_to sb #psb vsb **
  pure (Seq.length w == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
        bnd (vals w) base /\ eval (vals w) < Sc.q /\
        eval (vals w) == le_nat vsb % Sc.q)
{
  A.pts_to_len sb;
  let z8 = S8.zero;
  let mut c1 = [| z8; 64sz |]; A.pts_to_len c1; A.pts_to_len c1;
  Hacl.Impl.Copy.copy_prefix c1 sb 32sz;
  with vh. assert (A.pts_to c1 vh);
  A.pts_to_len c1;
  le_nat_split vh 32;
  assert (pure (forall (i: nat). i < 32 ==>
                  S8.v (Seq.index (Seq.slice vh 32 64) i) == 0));
  le_nat_zeros (Seq.slice vh 32 64);
  assert (pure (Seq.equal (Seq.slice vh 0 32) vsb));
  Scalar.reduce_op acc t1 t2 c1;
  ()
}

#push-options "--z3rlimit 600"

(** The two halves of the signature buffer, reassembled.  Pulse leaves the
    buffer as a nest of slices and appends; naming the halves and joining
    them here keeps that term out of the SMT query. *)
let join32 (o a b: Seq.seq S8.t)
  : Lemma (requires Seq.length o == 64 /\ Seq.length a == 32 /\
                    Seq.length b == 32 /\
                    Seq.equal (Seq.slice o 0 32) a /\
                    Seq.equal (Seq.slice o 32 64) b)
          (ensures o == Seq.append a b)
  = Seq.lemma_split o 32;
    Seq.lemma_eq_elim o (Seq.append a b)

(** {2 Signing}

    [r = H(prefix | msg) mod q], [R = [r]B], [k = H(R | A | msg) mod q] and
    [S = r + k s mod q]; the signature is [R | S]. *)

fn sign_expanded (sg: A.array S8.t) (pub sk prefix: A.array S8.t)
                 (msg: A.array S8.t) (mlen: SZ.t)
                 (#vsg: erased (Seq.seq S8.t))
                 (#ppub: perm) (#vpub: erased (Seq.lseq S8.t 32))
                 (#psk: perm) (#vsk: erased (Seq.lseq S8.t 32))
                 (#ppre: perm) (#vpre: erased (Seq.lseq S8.t 32))
                 (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires A.pts_to sg vsg ** A.pts_to pub #ppub vpub ** A.pts_to sk #psk vsk **
  A.pts_to prefix #ppre vpre ** A.pts_to msg #pm vm **
  pure (Seq.length vsg == 64 /\ SZ.fits (64 + Seq.length vm) /\
        SZ.v mlen == Seq.length vm)
returns _: unit
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to sg vsg' ** A.pts_to pub #ppub vpub ** A.pts_to sk #psk vsk **
  A.pts_to prefix #ppre vpre ** A.pts_to msg #pm vm **
  pure (vsg' == E.sign_expanded vpub vsk vpre vm)
{
  A.pts_to_len sg;
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut c1 = [| z8; 64sz |]; A.pts_to_len c1; let mut c2 = [| z8; 32sz |]; A.pts_to_len c2; let mut c3 = [| z8; 32sz |]; A.pts_to_len c3; let mut c4 = [| z8; 32sz |]; A.pts_to_len c4; let mut a1 = [| zz; 8sz |]; A.pts_to_len a1; let mut a2 = [| zz; 8sz |]; A.pts_to_len a2; let mut a3 = [| zz; 8sz |]; A.pts_to_len a3; let mut a4 = [| zz; 8sz |]; A.pts_to_len a4; let mut a5 = [| zz; 8sz |]; A.pts_to_len a5; let mut a6 = [| zz; 8sz |]; A.pts_to_len a6; let mut a7 = [| zz; 8sz |]; A.pts_to_len a7; let mut a8 = [| zz; 8sz |]; A.pts_to_len a8; let mut a9 = [| zz; 8sz |]; A.pts_to_len a9; let mut aa = [| zz; 8sz |]; A.pts_to_len aa; let mut ab = [| zz; 8sz |]; A.pts_to_len ab; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3; A.pts_to_len c4;
  A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3; A.pts_to_len a4;
  A.pts_to_len a5; A.pts_to_len a6; A.pts_to_len a7;
  A.pts_to_len a8; A.pts_to_len a9; A.pts_to_len aa; A.pts_to_len ab;

  hash2 c1 prefix msg mlen;
  Scalar.reduce_op a1 a5 a6 c1;
  store c2 a1;
  point_mul_g a8 a9 aa ab c2;
  point_compress c3 a8 a9 aa ab;
  with vrr. assert (A.pts_to c3 vrr);
  A.pts_to_len c3;

  hash3 c1 c3 pub msg mlen;
  Scalar.reduce_op a2 a5 a6 c1;
  with vk. assert (A.pts_to a2 vk);
  scalar_reduce32 a3 a5 a6 sk;
  with vsa. assert (A.pts_to a3 vsa);
  Scalar.qmul_op a4 a2 a3 a5 a6 a7;
  with vr. assert (A.pts_to a1 vr);
  with vmm. assert (A.pts_to a4 vmm);
  Scalar.qadd_op a1 a4 a5 a6;
  Sc.qadd_ok (vals vr) (vals vmm);
  Math.lemma_mod_add_distr (eval (vals vr))
    (eval (vals vk) * eval (vals vsa)) Sc.q;
  store c4 a1;
  with vss. assert (A.pts_to c4 vss);
  A.pts_to_len c4;

  let s0 = Sub.sub sg 0sz 32sz;
  Hacl.Impl.Copy.copy_prefix s0 c3 32sz;
  with w0. assert (A.pts_to s0 w0);
  assert (pure (Seq.equal w0 vrr));
  Sub.unsub sg 0 32 s0;
  with o1. assert (A.pts_to sg o1);
  A.pts_to_len sg;
  assert (pure (Seq.equal (Seq.slice o1 0 32) vrr));

  let s1 = Sub.sub sg 32sz 64sz;
  Hacl.Impl.Copy.copy_prefix s1 c4 32sz;
  with w1. assert (A.pts_to s1 w1);
  assert (pure (Seq.equal w1 vss));
  Sub.unsub sg 32 64 s1;
  with o2. assert (A.pts_to sg o2);
  A.pts_to_len sg;
  assert (pure (Seq.equal (Seq.slice o2 0 32) vrr));
  assert (pure (Seq.equal (Seq.slice o2 32 64) vss));
  join32 o2 vrr vss;

  assert (pure (Seq.equal o2 (Seq.append vrr vss)));
}

#pop-options

fn sign (sg: A.array S8.t) (secret: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
        (#vsg: erased (Seq.seq S8.t))
        (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
        (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires A.pts_to sg vsg ** A.pts_to secret #ps vs ** A.pts_to msg #pm vm **
  pure (Seq.length vsg == 64 /\ SZ.fits (64 + Seq.length vm) /\
        SZ.v mlen == Seq.length vm)
returns _: unit
ensures exists* (vsg': Seq.seq S8.t).
  A.pts_to sg vsg' ** A.pts_to secret #ps vs ** A.pts_to msg #pm vm **
  pure (vsg' == E.sign vs vm)
{
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut c1 = [| z8; 32sz |]; A.pts_to_len c1; let mut c2 = [| z8; 32sz |]; A.pts_to_len c2; let mut c3 = [| z8; 32sz |]; A.pts_to_len c3; let mut a1 = [| zz; 8sz |]; A.pts_to_len a1; let mut a2 = [| zz; 8sz |]; A.pts_to_len a2; let mut a3 = [| zz; 8sz |]; A.pts_to_len a3; let mut a4 = [| zz; 8sz |]; A.pts_to_len a4; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3;
  A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3; A.pts_to_len a4;

  secret_expand c2 c3 secret;
  point_mul_g a1 a2 a3 a4 c2;
  point_compress c1 a1 a2 a3 a4;
  sign_expanded sg c1 c2 c3 msg mlen;

  ()
}

#pop-options

#push-options "--fuel 0 --ifuel 2 --z3rlimit 300"

(** What verification decides, stated once so that the Pulse function does
    not have to unfold the specification inside its own proof. *)

(** [a] is already reduced exactly when it is small. *)
let lt_char (a: nat) (n: pos) (oks: bool)
  : Lemma (requires oks == (a = a % n)) (ensures oks == (a < n))
  = Math.lemma_mod_lt a n;
    if a < n then Math.modulo_lemma a n

let verify_char (pub: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { E.msg_ok msg })
                (sg: Seq.lseq S8.t 64) (aa rp: E.ext_point)
                (s: nat { s < E.q }) (k: nat { k < E.q }) (res: bool)
  : Lemma (requires
             E.point_decompress pub == Some aa /\
             E.point_decompress (Seq.slice sg 0 32) == Some rp /\
             s == le_nat (Seq.slice sg 32 64) /\
             k == E.sig_k (Seq.slice sg 0 32) pub msg /\
             res == E.point_equal (E.point_mul_g (E.scalar_bytes s))
                      (E.point_add rp (E.point_mul (E.scalar_bytes k) aa)))
          (ensures E.verify pub msg sg == res)
  = ()

let verify_false (pub: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { E.msg_ok msg })
                 (sg: Seq.lseq S8.t 64)
  : Lemma (requires E.point_decompress pub == None \/
                    E.point_decompress (Seq.slice sg 0 32) == None \/
                    le_nat (Seq.slice sg 32 64) >= E.q)
          (ensures E.verify pub msg sg == false)
  = ()

(** {2 Verification}

    [[S]B = R + [k]A].  The three ways to fail -- an undecompressable
    public key, an undecompressable [R], and an [S] at or above the group
    order -- are all public, so they are ordinary booleans.  The last of
    the three is what makes Ed25519 signatures non-malleable, and RFC 8032
    requires it. *)

fn verify (pub: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t) (sg: A.array S8.t)
          (#ppub: perm) (#vpub: erased (Seq.lseq S8.t 32))
          (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
          (#psg: perm) (#vsg: erased (Seq.lseq S8.t 64))
requires A.pts_to pub #ppub vpub ** A.pts_to msg #pm vm ** A.pts_to sg #psg vsg **
  pure (SZ.fits (64 + Seq.length vm) /\ SZ.v mlen == Seq.length vm)
returns r: bool
ensures A.pts_to pub #ppub vpub ** A.pts_to msg #pm vm ** A.pts_to sg #psg vsg **
  pure (r == E.verify vpub vm vsg)
{
  A.pts_to_len pub; A.pts_to_len sg;
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut c1 = [| z8; 32sz |]; A.pts_to_len c1; let mut c2 = [| z8; 32sz |]; A.pts_to_len c2; let mut c3 = [| z8; 32sz |]; A.pts_to_len c3; let mut c4 = [| z8; 32sz |]; A.pts_to_len c4; let mut c5 = [| z8; 64sz |]; A.pts_to_len c5; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3;
  A.pts_to_len c4; A.pts_to_len c5;

  let mut d1 = [| zz; 8sz |]; A.pts_to_len d1; let mut d2 = [| zz; 8sz |]; A.pts_to_len d2; let mut d3 = [| zz; 8sz |]; A.pts_to_len d3; let mut d4 = [| zz; 8sz |]; A.pts_to_len d4; let mut d5 = [| zz; 8sz |]; A.pts_to_len d5; let mut d6 = [| zz; 8sz |]; A.pts_to_len d6; let mut d7 = [| zz; 8sz |]; A.pts_to_len d7; let mut d8 = [| zz; 8sz |]; A.pts_to_len d8; let mut d9 = [| zz; 8sz |]; A.pts_to_len d9; let mut e1 = [| zz; 8sz |]; A.pts_to_len e1; let mut e2 = [| zz; 8sz |]; A.pts_to_len e2; let mut e3 = [| zz; 8sz |]; A.pts_to_len e3; let mut e4 = [| zz; 8sz |]; A.pts_to_len e4; let mut e5 = [| zz; 8sz |]; A.pts_to_len e5; let mut e6 = [| zz; 8sz |]; A.pts_to_len e6; let mut e7 = [| zz; 8sz |]; A.pts_to_len e7; let mut e8 = [| zz; 8sz |]; A.pts_to_len e8; let mut e9 = [| zz; 8sz |]; A.pts_to_len e9; let mut f1 = [| zz; 8sz |]; A.pts_to_len f1; let mut f2 = [| zz; 8sz |]; A.pts_to_len f2; let mut f3 = [| zz; 8sz |]; A.pts_to_len f3; let mut f4 = [| zz; 8sz |]; A.pts_to_len f4; let mut f5 = [| zz; 8sz |]; A.pts_to_len f5; let mut f6 = [| zz; 8sz |]; A.pts_to_len f6; let mut f7 = [| zz; 8sz |]; A.pts_to_len f7; A.pts_to_len d1; A.pts_to_len d2; A.pts_to_len d3; A.pts_to_len d4;
  A.pts_to_len d5; A.pts_to_len d6; A.pts_to_len d7; A.pts_to_len d8;
  A.pts_to_len d9; A.pts_to_len e1; A.pts_to_len e2; A.pts_to_len e3;
  A.pts_to_len e4; A.pts_to_len e5; A.pts_to_len e6; A.pts_to_len e7;
  A.pts_to_len e8; A.pts_to_len e9; A.pts_to_len f1; A.pts_to_len f2;
  A.pts_to_len f3; A.pts_to_len f4; A.pts_to_len f5;
  A.pts_to_len f6; A.pts_to_len f7;

  (* The two halves of the signature, in their own buffers. *)
  let g0 = Sub.sub sg 0sz 32sz;
  Hacl.Impl.Copy.copy_prefix c1 g0 32sz;
  with vr0. assert (A.pts_to c1 vr0);
  assert (pure (Seq.equal vr0 (Seq.slice (reveal vsg) 0 32)));
  Sub.unsub sg 0 32 g0;
  with sg1. assert (A.pts_to sg #psg sg1);
  A.pts_to_len sg;
  assert (pure (Seq.equal sg1 vsg));

  let g1 = Sub.sub sg 32sz 64sz;
  Hacl.Impl.Copy.copy_prefix c2 g1 32sz;
  with vs0. assert (A.pts_to c2 vs0);
  assert (pure (Seq.equal vs0 (Seq.slice (reveal vsg) 32 64)));
  Sub.unsub sg 32 64 g1;
  with sg2. assert (A.pts_to sg #psg sg2);
  A.pts_to_len sg;
  assert (pure (Seq.equal sg2 vsg));

  let oka = point_decompress d1 d2 d3 d4 pub;
  let okr = point_decompress d5 d6 d7 d8 c1;

  (* [S] must be below the group order: reducing it has to be the
     identity, which is exactly what comparing against the reduction
     decides. *)
  load f3 c2;
  scalar_reduce32 f4 f6 f7 c2;
  with vsl. assert (A.pts_to f3 vsl);
  with vsr. assert (A.pts_to f4 vsr);
  let oks = limbs_eq f3 f4;
  lt_char (le_nat vs0) Sc.q oks;
  assert (pure (oks == (le_nat vs0 < Sc.q)));

  assert (pure (Sc.q == E.q));

  if ((oka && okr) && oks) {
    with vax. assert (A.pts_to d1 vax);
    with vay. assert (A.pts_to d2 vay);
    with vaz. assert (A.pts_to d3 vaz);
    with vat. assert (A.pts_to d4 vat);
    with vrx. assert (A.pts_to d5 vrx);
    with vry. assert (A.pts_to d6 vry);
    with vrz. assert (A.pts_to d7 vrz);
    with vrt. assert (A.pts_to d8 vrt);
    store c3 f3;
    hash3 c5 c1 pub msg mlen;
    Scalar.reduce_op f5 f6 f7 c5;
    store c4 f5;
    point_mul_g e4 e5 e6 e7 c3;
    P.point_mul d9 e1 e2 e3 d1 d2 d3 d4 c4;
    P.point_add e8 e9 f1 f2 d5 d6 d7 d8 d9 e1 e2 e3;
    with vacc. assert (A.pts_to f5 vacc);
    let r = point_equal e4 e5 e6 e7 e8 e9 f1 f2;
    verify_char vpub vm vsg (P.pt vax vay vaz vat) (P.pt vrx vry vrz vrt)
                (le_nat vs0) (eval (vals vacc)) r;
    r
  } else {
    verify_false vpub vm vsg;
    false
  }
}

#pop-options
