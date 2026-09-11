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

(** {2 Hashing a concatenation}

    [H(a | msg)] and [H(a | b | msg)] without ever materialising the
    concatenation: the streaming state absorbs the pieces in order. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"

fn hash2 (out a msg: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t))
         (#pa: perm) (#va: erased (Seq.lseq S8.t 32))
         (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires S.pts_to out vout ** S.pts_to a #pa va ** S.pts_to msg #pm vm **
  pure (Seq.length vout == 64 /\ SZ.fits (64 + Seq.length vm))
returns _: unit
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to a #pa va ** S.pts_to msg #pm vm **
  pure (vout' == E.sha512 (Seq.append va vm))
{
  S.pts_to_len out; S.pts_to_len a; S.pts_to_len msg;
  let z64 = S64.zero;
  let z8 = S8.zero;
  let mut c1 = [| z64; 8sz |]; A.pts_to_len c1; let acc = S.from_array c1 8sz;
  let mut c2 = [| z8; 128sz |]; A.pts_to_len c2; let buf = S.from_array c2 128sz;
  let mut c3 = [| 0sz; 1sz |]; A.pts_to_len c3; let tot = S.from_array c3 1sz;
  S.pts_to_len acc; S.pts_to_len buf; S.pts_to_len tot;
  assert_norm (E.max_msg == pow2 32);
  assert_norm (pow2 32 + 64 < pow2 61);
  Stream.sha512_init acc buf tot;
  Stream.sha512_update acc buf tot a (Seq.empty #S8.t);
  Stream.sha512_update acc buf tot msg (Seq.append (Seq.empty #S8.t) va);
  Stream.sha512_digest acc buf tot out
    (Seq.append (Seq.append (Seq.empty #S8.t) va) vm);
  assert (pure (Seq.equal (Seq.append (Seq.append (Seq.empty #S8.t) va) vm)
                          (Seq.append va vm)));
  S.to_array acc; S.to_array buf; S.to_array tot;
}

fn hash3 (out a b msg: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t))
         (#pa: perm) (#va: erased (Seq.lseq S8.t 32))
         (#pb: perm) (#vb: erased (Seq.lseq S8.t 32))
         (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires S.pts_to out vout ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to msg #pm vm **
  pure (Seq.length vout == 64 /\ SZ.fits (64 + Seq.length vm))
returns _: unit
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to msg #pm vm **
  pure (vout' == E.sha512 (Seq.append va (Seq.append vb vm)))
{
  S.pts_to_len out; S.pts_to_len a; S.pts_to_len b; S.pts_to_len msg;
  let z64 = S64.zero;
  let z8 = S8.zero;
  let mut c1 = [| z64; 8sz |]; A.pts_to_len c1; let acc = S.from_array c1 8sz;
  let mut c2 = [| z8; 128sz |]; A.pts_to_len c2; let buf = S.from_array c2 128sz;
  let mut c3 = [| 0sz; 1sz |]; A.pts_to_len c3; let tot = S.from_array c3 1sz;
  S.pts_to_len acc; S.pts_to_len buf; S.pts_to_len tot;
  assert_norm (E.max_msg == pow2 32);
  assert_norm (pow2 32 + 64 < pow2 61);
  Stream.sha512_init acc buf tot;
  Stream.sha512_update acc buf tot a (Seq.empty #S8.t);
  Stream.sha512_update acc buf tot b (Seq.append (Seq.empty #S8.t) va);
  Stream.sha512_update acc buf tot msg
    (Seq.append (Seq.append (Seq.empty #S8.t) va) vb);
  Stream.sha512_digest acc buf tot out
    (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) va) vb) vm);
  assert (pure (Seq.equal
                  (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) va) vb) vm)
                  (Seq.append va (Seq.append vb vm))));
  S.to_array acc; S.to_array buf; S.to_array tot;
}

(** {2 A thirty-two byte scalar, reduced}

    The secret scalar is stored as thirty-two bytes but is used modulo the
    group order.  Zero-extending to sixty-four bytes lets the same
    reduction serve, and costs only the extra doublings. *)

fn scalar_reduce32 (acc t1 t2: S.slice S64.t) (sb: S.slice S8.t)
                   (#vacc: erased (Seq.seq S64.t))
                   (#v1: erased (Seq.seq S64.t)) (#v2: erased (Seq.seq S64.t))
                   (#psb: perm) (#vsb: erased (Seq.lseq S8.t 32))
requires S.pts_to acc vacc ** S.pts_to t1 v1 ** S.pts_to t2 v2 **
  S.pts_to sb #psb vsb **
  pure (Seq.length vacc == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl)
ensures exists* (w: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t).
  S.pts_to acc w ** S.pts_to t1 w1 ** S.pts_to t2 w2 ** S.pts_to sb #psb vsb **
  pure (Seq.length w == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
        bnd (vals w) base /\ eval (vals w) < Sc.q /\
        eval (vals w) == le_nat vsb % Sc.q)
{
  S.pts_to_len sb;
  let z8 = S8.zero;
  let mut c1 = [| z8; 64sz |]; A.pts_to_len c1; let h = S.from_array c1 64sz;
  S.pts_to_len h;
  Hacl.Impl.Copy.copy_prefix h sb 32sz;
  with vh. assert (S.pts_to h vh);
  S.pts_to_len h;
  le_nat_split vh 32;
  assert (pure (forall (i: nat). i < 32 ==>
                  S8.v (Seq.index (Seq.slice vh 32 64) i) == 0));
  le_nat_zeros (Seq.slice vh 32 64);
  assert (pure (Seq.equal (Seq.slice vh 0 32) vsb));
  Scalar.reduce_op acc t1 t2 h;
  S.to_array h;
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

fn sign_expanded (sg: S.slice S8.t) (pub sk prefix: S.slice S8.t)
                 (msg: S.slice S8.t)
                 (#vsg: erased (Seq.seq S8.t))
                 (#ppub: perm) (#vpub: erased (Seq.lseq S8.t 32))
                 (#psk: perm) (#vsk: erased (Seq.lseq S8.t 32))
                 (#ppre: perm) (#vpre: erased (Seq.lseq S8.t 32))
                 (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires S.pts_to sg vsg ** S.pts_to pub #ppub vpub ** S.pts_to sk #psk vsk **
  S.pts_to prefix #ppre vpre ** S.pts_to msg #pm vm **
  pure (Seq.length vsg == 64 /\ SZ.fits (64 + Seq.length vm))
returns _: unit
ensures exists* (vsg': Seq.seq S8.t).
  S.pts_to sg vsg' ** S.pts_to pub #ppub vpub ** S.pts_to sk #psk vsk **
  S.pts_to prefix #ppre vpre ** S.pts_to msg #pm vm **
  pure (vsg' == E.sign_expanded vpub vsk vpre vm)
{
  S.pts_to_len sg;
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut c1 = [| z8; 64sz |]; A.pts_to_len c1; let h = S.from_array c1 64sz;
  let mut c2 = [| z8; 32sz |]; A.pts_to_len c2; let rb = S.from_array c2 32sz;
  let mut c3 = [| z8; 32sz |]; A.pts_to_len c3; let rrb = S.from_array c3 32sz;
  let mut c4 = [| z8; 32sz |]; A.pts_to_len c4; let ssb = S.from_array c4 32sz;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let racc = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let kacc = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let sacc = S.from_array a3 16sz;
  let mut a4 = [| zz; 16sz |]; A.pts_to_len a4; let mac = S.from_array a4 16sz;
  let mut a5 = [| zz; 16sz |]; A.pts_to_len a5; let t1 = S.from_array a5 16sz;
  let mut a6 = [| zz; 16sz |]; A.pts_to_len a6; let t2 = S.from_array a6 16sz;
  let mut a7 = [| zz; 16sz |]; A.pts_to_len a7; let t3 = S.from_array a7 16sz;
  let mut a8 = [| zz; 16sz |]; A.pts_to_len a8; let px = S.from_array a8 16sz;
  let mut a9 = [| zz; 16sz |]; A.pts_to_len a9; let py = S.from_array a9 16sz;
  let mut aa = [| zz; 16sz |]; A.pts_to_len aa; let pz = S.from_array aa 16sz;
  let mut ab = [| zz; 16sz |]; A.pts_to_len ab; let ptt = S.from_array ab 16sz;
  S.pts_to_len h; S.pts_to_len rb; S.pts_to_len rrb; S.pts_to_len ssb;
  S.pts_to_len racc; S.pts_to_len kacc; S.pts_to_len sacc; S.pts_to_len mac;
  S.pts_to_len t1; S.pts_to_len t2; S.pts_to_len t3;
  S.pts_to_len px; S.pts_to_len py; S.pts_to_len pz; S.pts_to_len ptt;

  hash2 h prefix msg;
  Scalar.reduce_op racc t1 t2 h;
  store rb racc;
  point_mul_g px py pz ptt rb;
  point_compress rrb px py pz ptt;
  with vrr. assert (S.pts_to rrb vrr);
  S.pts_to_len rrb;

  hash3 h rrb pub msg;
  Scalar.reduce_op kacc t1 t2 h;
  with vk. assert (S.pts_to kacc vk);
  scalar_reduce32 sacc t1 t2 sk;
  with vsa. assert (S.pts_to sacc vsa);
  Scalar.qmul_op mac kacc sacc t1 t2 t3;
  with vr. assert (S.pts_to racc vr);
  with vmm. assert (S.pts_to mac vmm);
  Scalar.qadd_op racc mac t1 t2;
  Sc.qadd_ok (vals vr) (vals vmm);
  Math.lemma_mod_add_distr (eval (vals vr))
    (eval (vals vk) * eval (vals vsa)) Sc.q;
  store ssb racc;
  with vss. assert (S.pts_to ssb vss);
  S.pts_to_len ssb;

  let s0 = S.subslice sg 0sz 32sz;
  Hacl.Impl.Copy.copy_prefix s0 rrb 32sz;
  with w0. assert (S.pts_to s0 w0);
  assert (pure (Seq.equal w0 vrr));
  unfold S.subslice_rest;
  S.join s0 _ _;
  S.join _ _ sg;
  with o1. assert (S.pts_to sg o1);
  S.pts_to_len sg;
  assert (pure (Seq.equal (Seq.slice o1 0 32) vrr));

  let s1 = S.subslice sg 32sz 64sz;
  Hacl.Impl.Copy.copy_prefix s1 ssb 32sz;
  with w1. assert (S.pts_to s1 w1);
  assert (pure (Seq.equal w1 vss));
  unfold S.subslice_rest;
  S.join s1 _ _;
  S.join _ _ sg;
  with o2. assert (S.pts_to sg o2);
  S.pts_to_len sg;
  assert (pure (Seq.equal (Seq.slice o2 0 32) vrr));
  assert (pure (Seq.equal (Seq.slice o2 32 64) vss));
  join32 o2 vrr vss;

  S.to_array h; S.to_array rb; S.to_array rrb; S.to_array ssb;
  S.to_array racc; S.to_array kacc; S.to_array sacc; S.to_array mac;
  S.to_array t1; S.to_array t2; S.to_array t3;
  S.to_array px; S.to_array py; S.to_array pz; S.to_array ptt;
  assert (pure (Seq.equal o2 (Seq.append vrr vss)));
}

#pop-options

fn sign (sg: S.slice S8.t) (secret: S.slice S8.t) (msg: S.slice S8.t)
        (#vsg: erased (Seq.seq S8.t))
        (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
        (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires S.pts_to sg vsg ** S.pts_to secret #ps vs ** S.pts_to msg #pm vm **
  pure (Seq.length vsg == 64 /\ SZ.fits (64 + Seq.length vm))
returns _: unit
ensures exists* (vsg': Seq.seq S8.t).
  S.pts_to sg vsg' ** S.pts_to secret #ps vs ** S.pts_to msg #pm vm **
  pure (vsg' == E.sign vs vm)
{
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut c1 = [| z8; 32sz |]; A.pts_to_len c1; let pub = S.from_array c1 32sz;
  let mut c2 = [| z8; 32sz |]; A.pts_to_len c2; let low = S.from_array c2 32sz;
  let mut c3 = [| z8; 32sz |]; A.pts_to_len c3; let pre = S.from_array c3 32sz;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let px = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let py = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let pz = S.from_array a3 16sz;
  let mut a4 = [| zz; 16sz |]; A.pts_to_len a4; let ptt = S.from_array a4 16sz;
  S.pts_to_len pub; S.pts_to_len low; S.pts_to_len pre;
  S.pts_to_len px; S.pts_to_len py; S.pts_to_len pz; S.pts_to_len ptt;

  secret_expand low pre secret;
  point_mul_g px py pz ptt low;
  point_compress pub px py pz ptt;
  sign_expanded sg pub low pre msg;

  S.to_array pub; S.to_array low; S.to_array pre;
  S.to_array px; S.to_array py; S.to_array pz; S.to_array ptt;
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

fn verify (pub: S.slice S8.t) (msg: S.slice S8.t) (sg: S.slice S8.t)
          (#ppub: perm) (#vpub: erased (Seq.lseq S8.t 32))
          (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
          (#psg: perm) (#vsg: erased (Seq.lseq S8.t 64))
requires S.pts_to pub #ppub vpub ** S.pts_to msg #pm vm ** S.pts_to sg #psg vsg **
  pure (SZ.fits (64 + Seq.length vm))
returns r: bool
ensures S.pts_to pub #ppub vpub ** S.pts_to msg #pm vm ** S.pts_to sg #psg vsg **
  pure (r == E.verify vpub vm vsg)
{
  S.pts_to_len pub; S.pts_to_len sg;
  let z8 = S8.zero;
  let zz = S64.zero;
  let mut c1 = [| z8; 32sz |]; A.pts_to_len c1; let rrb = S.from_array c1 32sz;
  let mut c2 = [| z8; 32sz |]; A.pts_to_len c2; let sbb = S.from_array c2 32sz;
  let mut c3 = [| z8; 32sz |]; A.pts_to_len c3; let sby = S.from_array c3 32sz;
  let mut c4 = [| z8; 32sz |]; A.pts_to_len c4; let kb = S.from_array c4 32sz;
  let mut c5 = [| z8; 64sz |]; A.pts_to_len c5; let h = S.from_array c5 64sz;
  S.pts_to_len rrb; S.pts_to_len sbb; S.pts_to_len sby;
  S.pts_to_len kb; S.pts_to_len h;

  let mut d1 = [| zz; 16sz |]; A.pts_to_len d1; let ax = S.from_array d1 16sz;
  let mut d2 = [| zz; 16sz |]; A.pts_to_len d2; let ay = S.from_array d2 16sz;
  let mut d3 = [| zz; 16sz |]; A.pts_to_len d3; let az = S.from_array d3 16sz;
  let mut d4 = [| zz; 16sz |]; A.pts_to_len d4; let at = S.from_array d4 16sz;
  let mut d5 = [| zz; 16sz |]; A.pts_to_len d5; let rx = S.from_array d5 16sz;
  let mut d6 = [| zz; 16sz |]; A.pts_to_len d6; let ry = S.from_array d6 16sz;
  let mut d7 = [| zz; 16sz |]; A.pts_to_len d7; let rz = S.from_array d7 16sz;
  let mut d8 = [| zz; 16sz |]; A.pts_to_len d8; let rt = S.from_array d8 16sz;
  let mut d9 = [| zz; 16sz |]; A.pts_to_len d9; let kx = S.from_array d9 16sz;
  let mut e1 = [| zz; 16sz |]; A.pts_to_len e1; let ky = S.from_array e1 16sz;
  let mut e2 = [| zz; 16sz |]; A.pts_to_len e2; let kz = S.from_array e2 16sz;
  let mut e3 = [| zz; 16sz |]; A.pts_to_len e3; let kt = S.from_array e3 16sz;
  let mut e4 = [| zz; 16sz |]; A.pts_to_len e4; let ux = S.from_array e4 16sz;
  let mut e5 = [| zz; 16sz |]; A.pts_to_len e5; let uy = S.from_array e5 16sz;
  let mut e6 = [| zz; 16sz |]; A.pts_to_len e6; let uz = S.from_array e6 16sz;
  let mut e7 = [| zz; 16sz |]; A.pts_to_len e7; let ut = S.from_array e7 16sz;
  let mut e8 = [| zz; 16sz |]; A.pts_to_len e8; let vx = S.from_array e8 16sz;
  let mut e9 = [| zz; 16sz |]; A.pts_to_len e9; let vy = S.from_array e9 16sz;
  let mut f1 = [| zz; 16sz |]; A.pts_to_len f1; let vz = S.from_array f1 16sz;
  let mut f2 = [| zz; 16sz |]; A.pts_to_len f2; let vt = S.from_array f2 16sz;
  let mut f3 = [| zz; 16sz |]; A.pts_to_len f3; let sl = S.from_array f3 16sz;
  let mut f4 = [| zz; 16sz |]; A.pts_to_len f4; let sr = S.from_array f4 16sz;
  let mut f5 = [| zz; 16sz |]; A.pts_to_len f5; let acc = S.from_array f5 16sz;
  let mut f6 = [| zz; 16sz |]; A.pts_to_len f6; let t1 = S.from_array f6 16sz;
  let mut f7 = [| zz; 16sz |]; A.pts_to_len f7; let t2 = S.from_array f7 16sz;
  S.pts_to_len ax; S.pts_to_len ay; S.pts_to_len az; S.pts_to_len at;
  S.pts_to_len rx; S.pts_to_len ry; S.pts_to_len rz; S.pts_to_len rt;
  S.pts_to_len kx; S.pts_to_len ky; S.pts_to_len kz; S.pts_to_len kt;
  S.pts_to_len ux; S.pts_to_len uy; S.pts_to_len uz; S.pts_to_len ut;
  S.pts_to_len vx; S.pts_to_len vy; S.pts_to_len vz; S.pts_to_len vt;
  S.pts_to_len sl; S.pts_to_len sr; S.pts_to_len acc;
  S.pts_to_len t1; S.pts_to_len t2;

  (* The two halves of the signature, in their own buffers. *)
  let g0 = S.subslice sg 0sz 32sz;
  Hacl.Impl.Copy.copy_prefix rrb g0 32sz;
  with vr0. assert (S.pts_to rrb vr0);
  assert (pure (Seq.equal vr0 (Seq.slice (reveal vsg) 0 32)));
  unfold S.subslice_rest;
  S.join g0 _ _;
  S.join _ _ sg;
  with sg1. assert (S.pts_to sg #psg sg1);
  S.pts_to_len sg;
  assert (pure (Seq.equal sg1 vsg));

  let g1 = S.subslice sg 32sz 64sz;
  Hacl.Impl.Copy.copy_prefix sbb g1 32sz;
  with vs0. assert (S.pts_to sbb vs0);
  assert (pure (Seq.equal vs0 (Seq.slice (reveal vsg) 32 64)));
  unfold S.subslice_rest;
  S.join g1 _ _;
  S.join _ _ sg;
  with sg2. assert (S.pts_to sg #psg sg2);
  S.pts_to_len sg;
  assert (pure (Seq.equal sg2 vsg));

  let oka = point_decompress ax ay az at pub;
  let okr = point_decompress rx ry rz rt rrb;

  (* [S] must be below the group order: reducing it has to be the
     identity, which is exactly what comparing against the reduction
     decides. *)
  load sl sbb;
  scalar_reduce32 sr t1 t2 sbb;
  with vsl. assert (S.pts_to sl vsl);
  with vsr. assert (S.pts_to sr vsr);
  let oks = limbs_eq sl sr;
  lt_char (le_nat vs0) Sc.q oks;
  assert (pure (oks == (le_nat vs0 < Sc.q)));

  assert (pure (Sc.q == E.q));

  if ((oka && okr) && oks) {
    with vax. assert (S.pts_to ax vax);
    with vay. assert (S.pts_to ay vay);
    with vaz. assert (S.pts_to az vaz);
    with vat. assert (S.pts_to at vat);
    with vrx. assert (S.pts_to rx vrx);
    with vry. assert (S.pts_to ry vry);
    with vrz. assert (S.pts_to rz vrz);
    with vrt. assert (S.pts_to rt vrt);
    store sby sl;
    hash3 h rrb pub msg;
    Scalar.reduce_op acc t1 t2 h;
    store kb acc;
    point_mul_g ux uy uz ut sby;
    P.point_mul kx ky kz kt ax ay az at kb;
    P.point_add vx vy vz vt rx ry rz rt kx ky kz kt;
    with vacc. assert (S.pts_to acc vacc);
    let r = point_equal ux uy uz ut vx vy vz vt;
    verify_char vpub vm vsg (P.pt vax vay vaz vat) (P.pt vrx vry vrz vrt)
                (le_nat vs0) (eval (vals vacc)) r;
    S.to_array rrb;
    S.to_array sbb;
    S.to_array sby;
    S.to_array kb;
    S.to_array h;
    S.to_array ax;
    S.to_array ay;
    S.to_array az;
    S.to_array at;
    S.to_array rx;
    S.to_array ry;
    S.to_array rz;
    S.to_array rt;
    S.to_array kx;
    S.to_array ky;
    S.to_array kz;
    S.to_array kt;
    S.to_array ux;
    S.to_array uy;
    S.to_array uz;
    S.to_array ut;
    S.to_array vx;
    S.to_array vy;
    S.to_array vz;
    S.to_array vt;
    S.to_array sl;
    S.to_array sr;
    S.to_array acc;
    S.to_array t1;
    S.to_array t2;
    r
  } else {
    verify_false vpub vm vsg;
    S.to_array rrb;
    S.to_array sbb;
    S.to_array sby;
    S.to_array kb;
    S.to_array h;
    S.to_array ax;
    S.to_array ay;
    S.to_array az;
    S.to_array at;
    S.to_array rx;
    S.to_array ry;
    S.to_array rz;
    S.to_array rt;
    S.to_array kx;
    S.to_array ky;
    S.to_array kz;
    S.to_array kt;
    S.to_array ux;
    S.to_array uy;
    S.to_array uz;
    S.to_array ut;
    S.to_array vx;
    S.to_array vy;
    S.to_array vz;
    S.to_array vt;
    S.to_array sl;
    S.to_array sr;
    S.to_array acc;
    S.to_array t1;
    S.to_array t2;
    false
  }
}

#pop-options
