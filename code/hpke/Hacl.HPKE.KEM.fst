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

(** DHKEM, RFC 9180 section 4.1.

    A Diffie-Hellman key encapsulation: the sender multiplies an ephemeral
    private key by the recipient's public key, and both sides run the result
    and a transcript of the public keys involved through HKDF-SHA-256.

    The KEM's KDF is HKDF-SHA-256 for both of the curves here -- that is what
    RFC 9180 registers for [DHKEM(X25519, HKDF-SHA256)] and [DHKEM(P-256,
    HKDF-SHA256)] alike -- so nothing in this module is generic over a hash.
    What it is generic over is the curve, and that is a [monomorphize]
    parameter: a program that uses X25519 and nothing else gets no P-256.

    Public keys are on the wire in the format RFC 9180 asks for: a bare
    u-coordinate for X25519, and SEC1 {i uncompressed} -- the [0x04] tag byte
    and both coordinates -- for P-256.  The shared coordinate that comes out
    of P-256 is the x coordinate alone. *)
module Hacl.HPKE.KEM

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HPKE
open Hacl.Hash.SHA2.Tables
open Hacl.HPKE.Tables
open Hacl.HPKE.Labeled
open Hacl.Impl.Copy
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module C = Hacl.Curve25519
module PE = Hacl.P256.Ecdh
module PS = Hacl.P256.Sec1
module B = Hacl.Spec.Bytes
module Mem = Hacl.Mem
module D = Hacl.Hash.SHA2.Dispatch

(** The wire length of a public key, as a machine value. *)
let pk_len ([@@@FStar.Attributes.monomorphize] k: kem_alg)
  : n: SZ.t { SZ.v n == size_dh_public k }
  = match k with DH_X25519 -> 32sz | DH_P256 -> 65sz

(** {2 The KEM's suite identifier}

    Five bytes: [KEM] and the algorithm number.  Short enough that writing it
    out is cheaper than deriving it. *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn kem_sid ([@@@FStar.Attributes.monomorphize] k: kem_alg) (out: A.array S8.t)
           (#vo: erased (Seq.seq S8.t))
requires A.pts_to out vo ** pure (Seq.length vo == 5)
ensures exists* wo. A.pts_to out wo **
        pure (Seq.length wo == 5 /\ wo == kem_suite_id k)
{
  A.pts_to_len out;
  let kp = table kem_prefix_arr 3sz;
  A.pts_to_len kp;
  copy_at out 0sz kp 3sz;
  A.((out.(3sz) <- S8.zero));
  let lo = if DH_P256? k { S8.classify 0x10uy } else { S8.classify 0x20uy };
  A.((out.(4sz) <- lo));
  with wo. assert (A.pts_to out wo);
  A.pts_to_len out;
  B.nat_to_be_index 2 (kem_id k) 0;
  B.nat_to_be_index 2 (kem_id k) 1;
  assert_norm (pow2 8 == 256);
  cat2_pointwise wo kem_prefix (two_bytes (kem_id k));
  drop_table kp;
}

#pop-options

(** {2 The curve operations} *)

(** [DH]: [false] is RFC 9180's "invalid input" -- a small-order X25519 peer
    point, or a P-256 input that is not a point on the curve. *)
fn dh_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
           (out: A.array S8.t) (sk: A.array S8.t) (pk: A.array S8.t)
           (#vo: erased (Seq.seq S8.t))
           (#ps: perm) (#vs: erased (Seq.seq S8.t))
           (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to sk #ps vs ** A.pts_to pk #pp vp **
         pure (Seq.length vo == 32 /\ Seq.length vs == 32 /\
               Seq.length vp == size_dh_public k)
returns r: bool
ensures exists* wo. A.pts_to out wo ** A.pts_to sk #ps vs ** A.pts_to pk #pp vp **
        pure (Seq.length wo == 32 /\ Seq.length vs == 32 /\
              Seq.length vp == size_dh_public k /\
              r == Some? (dh k vs vp) /\ (r ==> wo == Some?.v (dh k vs vp)))
{
  A.pts_to_len out;
  A.pts_to_len sk;
  A.pts_to_len pk;
  if (DH_P256? k) {
    let z8 = S8.zero;
    let mut raw = [| z8; 64sz |];
    Mem.track raw;
    A.pts_to_len raw;
    let ok1 = PS.uncompressed_to_raw raw pk;
    if ok1 {
      let mut sh = [| z8; 64sz |];
      Mem.track sh;
      A.pts_to_len sh;
      let ok2 = PE.dh_responder sh raw sk;
      if ok2 {
        copy_prefix out sh 32sz;
        with wo. assert (A.pts_to out wo);
        with vsh. assert (A.pts_to sh vsh);
        A.pts_to_len out;
        Seq.lemma_eq_elim (reveal wo) (Seq.slice (reveal vsh) 0 32);
        Mem.wipe sh 64sz;
        Mem.wipe raw 64sz;
        true
      } else { Mem.wipe sh 64sz;
      Mem.wipe raw 64sz;
      false }
    } else { Mem.wipe raw 64sz;
    false }
  } else {
    let ok = C.ecdh out sk pk;
    ok
  }
}

(** The public key belonging to a private one, in the wire format. *)
fn stp_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
            (out: A.array S8.t) (sk: A.array S8.t)
            (#vo: erased (Seq.seq S8.t))
            (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to sk #ps vs **
         pure (Seq.length vo == size_dh_public k /\ Seq.length vs == 32)
returns r: bool
ensures exists* wo. A.pts_to out wo ** A.pts_to sk #ps vs **
        pure (Seq.length wo == size_dh_public k /\ Seq.length vs == 32 /\
              r == Some? (secret_to_public k vs) /\
              (r ==> wo == Some?.v (secret_to_public k vs)))
{
  A.pts_to_len out;
  A.pts_to_len sk;
  if (DH_P256? k) {
    let z8 = S8.zero;
    let mut raw = [| z8; 64sz |];
    Mem.track raw;
    A.pts_to_len raw;
    let ok = PE.dh_initiator raw sk;
    if ok {
      PS.raw_to_uncompressed out raw;
      Mem.wipe raw 64sz;
      true
    } else { Mem.wipe raw 64sz;
    false }
  } else {
    C.secret_to_public out sk;
    true
  }
}

(** {2 ExtractAndExpand} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn extract_and_expand_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
                           (out: A.array S8.t) (dho: A.array S8.t) (dho_len: SZ.t)
                           (ctx: A.array S8.t) (ctx_len: SZ.t)
                           (#vo: erased (Seq.seq S8.t))
                           (#pd: perm) (#vdho: erased (Seq.seq S8.t))
                           (#pc: perm) (#vctx: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to dho #pd vdho ** A.pts_to ctx #pc vctx **
         pure (Seq.length vo == 32 /\ Seq.length vdho <= 64 /\
               Seq.length vctx <= 256)
         ** pure (SZ.v dho_len == Seq.length vdho)
         ** pure (SZ.v ctx_len == Seq.length vctx)
ensures exists* wo. A.pts_to out wo ** A.pts_to dho #pd vdho ** A.pts_to ctx #pc vctx **
        pure (Seq.length wo == 32 /\ Seq.length vdho <= 64 /\ Seq.length vctx <= 256 /\
              wo == extract_and_expand k vdho vctx)
{
  A.pts_to_len out;
  A.pts_to_len dho;
  A.pts_to_len ctx;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (64 + 7 + 5 + 7 + Seq.length vdho);
  SZ.fits_u32_implies_fits (64 + 32 + 9 + 5 + 13 + Seq.length vctx + 1);

  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let z8 = S8.zero;

  let mut sid = [| z8; 5sz |];
  Mem.track sid;
  A.pts_to_len sid;
  kem_sid k sid;

  let mut prk = [| z8; 32sz |];
  Mem.track prk;
  A.pts_to_len prk;

  let lab1 = table label_eae_prk_arr 7sz;
  A.pts_to_len lab1;
  Hacl.Hash.SHA2.sha2_256_facts ();
  labeled_extract_nosalt sha2_256 (D.blocks_dispatch32 sha2_256) kt ivt prk sid 5sz lab1 7sz dho dho_len;
  drop_table lab1;

  let lab2 = table label_shared_secret_arr 13sz;
  A.pts_to_len lab2;
  Hacl.Hash.SHA2.sha2_256_facts ();
  labeled_expand_impl sha2_256 (D.blocks_dispatch32 sha2_256) kt ivt out 32sz prk 32sz sid 5sz lab2 13sz ctx ctx_len;
  drop_table lab2;

  drop_table ivt;
  drop_table kt;
  Mem.wipe prk 32sz;
  Mem.wipe sid 5sz;
}

#pop-options

(** {2 Encapsulation and decapsulation}

    The ephemeral private key is the caller's, here as everywhere else in
    this library: nothing samples randomness behind a caller's back.  A
    [false] answer means some Diffie-Hellman refused its input; the output
    buffers hold nothing meaningful then, and the caller must not use them. *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

fn encap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
              (shared: A.array S8.t) (enc: A.array S8.t)
              (skE: A.array S8.t) (pkR: A.array S8.t)
              (#vsh: erased (Seq.seq S8.t)) (#ve: erased (Seq.seq S8.t))
              (#pe: perm) (#vskE: erased (Seq.seq S8.t))
              (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
requires A.pts_to shared vsh ** A.pts_to enc ve **
         A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
               Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public k)
returns r: bool
ensures exists* wsh we.
  A.pts_to shared wsh ** A.pts_to enc we **
  A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  pure (Seq.length wsh == 32 /\ Seq.length we == size_dh_public k /\
        Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public k /\
        r == Some? (encap k vskE vpkR) /\
        (r ==> (wsh, we) == Some?.v (encap k vskE vpkR)))
{
  A.pts_to_len shared;
  A.pts_to_len enc;
  A.pts_to_len skE;
  A.pts_to_len pkR;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (2 * size_dh_public k);
  let pl = pk_len k;
  let z8 = S8.zero;

  let mut dho = [| z8; 32sz |];
  Mem.track dho;
  A.pts_to_len dho;
  let ok1 = dh_impl k dho skE pkR;
  if ok1 {
    let ok2 = stp_impl k enc skE;
    if ok2 {
      let mut ctx = [| z8; SZ.add pl pl |];
      Mem.track ctx;
      A.pts_to_len ctx;
      copy_at ctx 0sz enc pl;
      copy_at ctx pl pkR pl;
      with vctx. assert (A.pts_to ctx vctx);
      with we. assert (A.pts_to enc we);
      A.pts_to_len ctx;
      cat2_pointwise vctx we vpkR;
      extract_and_expand_impl k shared dho 32sz ctx (SZ.add pl pl);
      Mem.wipe ctx (SZ.add pl pl);
      Mem.wipe dho 32sz;
      true
    } else { Mem.wipe dho 32sz;
    false }
  } else { Mem.wipe dho 32sz;
  false }
}

fn decap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
              (shared: A.array S8.t) (enc: A.array S8.t) (skR: A.array S8.t)
              (#vsh: erased (Seq.seq S8.t))
              (#pn: perm) (#ve: erased (Seq.seq S8.t))
              (#pr: perm) (#vskR: erased (Seq.seq S8.t))
requires A.pts_to shared vsh ** A.pts_to enc #pn ve ** A.pts_to skR #pr vskR **
         pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
               Seq.length vskR == 32)
returns r: bool
ensures exists* wsh.
  A.pts_to shared wsh ** A.pts_to enc #pn ve ** A.pts_to skR #pr vskR **
  pure (Seq.length wsh == 32 /\ Seq.length ve == size_dh_public k /\
        Seq.length vskR == 32 /\
        r == Some? (decap k ve vskR) /\
        (r ==> wsh == Some?.v (decap k ve vskR)))
{
  A.pts_to_len shared;
  A.pts_to_len enc;
  A.pts_to_len skR;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (2 * size_dh_public k);
  let pl = pk_len k;
  let z8 = S8.zero;

  let mut dho = [| z8; 32sz |];
  Mem.track dho;
  A.pts_to_len dho;
  let ok1 = dh_impl k dho skR enc;
  if ok1 {
    let mut pkRm = [| z8; pl |];
    Mem.track pkRm;
    A.pts_to_len pkRm;
    let ok2 = stp_impl k pkRm skR;
    if ok2 {
      let mut ctx = [| z8; SZ.add pl pl |];
      Mem.track ctx;
      A.pts_to_len ctx;
      copy_at ctx 0sz enc pl;
      copy_at ctx pl pkRm pl;
      with vctx. assert (A.pts_to ctx vctx);
      with wp. assert (A.pts_to pkRm wp);
      A.pts_to_len ctx;
      cat2_pointwise vctx ve wp;
      extract_and_expand_impl k shared dho 32sz ctx (SZ.add pl pl);
      Mem.wipe ctx (SZ.add pl pl);
      Mem.wipe pkRm pl;
      Mem.wipe dho 32sz;
      true
    } else { Mem.wipe pkRm pl;
    Mem.wipe dho 32sz;
    false }
  } else { Mem.wipe dho 32sz;
  false }
}

(** {2 The authenticated variants}

    Two Diffie-Hellmans instead of one -- the ephemeral key and a static
    sender key, both against the recipient -- and the sender's public key at
    the end of the transcript.  A recipient that decapsulates successfully
    knows the message came from the holder of that key. *)

fn auth_encap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
                   (shared: A.array S8.t) (enc: A.array S8.t)
                   (skE: A.array S8.t) (skS: A.array S8.t) (pkR: A.array S8.t)
                   (#vsh: erased (Seq.seq S8.t)) (#ve: erased (Seq.seq S8.t))
                   (#pe: perm) (#vskE: erased (Seq.seq S8.t))
                   (#pss: perm) (#vskS: erased (Seq.seq S8.t))
                   (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
requires A.pts_to shared vsh ** A.pts_to enc ve **
         A.pts_to skE #pe vskE ** A.pts_to skS #pss vskS ** A.pts_to pkR #pr vpkR **
         pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
               Seq.length vskE == 32 /\ Seq.length vskS == 32 /\
               Seq.length vpkR == size_dh_public k)
returns r: bool
ensures exists* wsh we.
  A.pts_to shared wsh ** A.pts_to enc we **
  A.pts_to skE #pe vskE ** A.pts_to skS #pss vskS ** A.pts_to pkR #pr vpkR **
  pure (Seq.length wsh == 32 /\ Seq.length we == size_dh_public k /\
        Seq.length vskE == 32 /\ Seq.length vskS == 32 /\
        Seq.length vpkR == size_dh_public k /\
        r == Some? (auth_encap k vskE vskS vpkR) /\
        (r ==> (wsh, we) == Some?.v (auth_encap k vskE vskS vpkR)))
{
  A.pts_to_len shared;
  A.pts_to_len enc;
  A.pts_to_len skE;
  A.pts_to_len skS;
  A.pts_to_len pkR;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (3 * size_dh_public k);
  let pl = pk_len k;
  let z8 = S8.zero;

  let mut dho = [| z8; 64sz |];
  Mem.track dho;
  A.pts_to_len dho;
  let mut tmp = [| z8; 32sz |];
  Mem.track tmp;
  A.pts_to_len tmp;

  let ok1 = dh_impl k tmp skE pkR;
  if ok1 {
    copy_at dho 0sz tmp 32sz;
    with d1. assert (A.pts_to tmp d1);
    let ok2 = dh_impl k tmp skS pkR;
    if ok2 {
      copy_at dho 32sz tmp 32sz;
      with d2. assert (A.pts_to tmp d2);
      with vdho. assert (A.pts_to dho vdho);
      A.pts_to_len dho;
      cat2_pointwise vdho d1 d2;
      let ok3 = stp_impl k enc skE;
      if ok3 {
        let mut pkS = [| z8; pl |];
        Mem.track pkS;
        A.pts_to_len pkS;
        let ok4 = stp_impl k pkS skS;
        if ok4 {
          let mut ctx = [| z8; SZ.add (SZ.add pl pl) pl |];
          Mem.track ctx;
          A.pts_to_len ctx;
          copy_at ctx 0sz enc pl;
          copy_at ctx pl pkR pl;
          copy_at ctx (SZ.add pl pl) pkS pl;
          with vctx. assert (A.pts_to ctx vctx);
          with we. assert (A.pts_to enc we);
          with wps. assert (A.pts_to pkS wps);
          A.pts_to_len ctx;
          cat3_pointwise vctx we vpkR wps;
          extract_and_expand_impl k shared dho 64sz ctx (SZ.add (SZ.add pl pl) pl);
          Mem.wipe ctx (SZ.add (SZ.add pl pl) pl);
          Mem.wipe pkS pl;
          Mem.wipe tmp 32sz;
          Mem.wipe dho 64sz;
          true
        } else { Mem.wipe pkS pl;
        Mem.wipe tmp 32sz;
        Mem.wipe dho 64sz;
        false }
      } else { Mem.wipe tmp 32sz;
      Mem.wipe dho 64sz;
      false }
    } else { Mem.wipe tmp 32sz;
    Mem.wipe dho 64sz;
    false }
  } else { Mem.wipe tmp 32sz;
  Mem.wipe dho 64sz;
  false }
}

fn auth_decap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
                   (shared: A.array S8.t) (enc: A.array S8.t)
                   (skR: A.array S8.t) (pkS: A.array S8.t)
                   (#vsh: erased (Seq.seq S8.t))
                   (#pn: perm) (#ve: erased (Seq.seq S8.t))
                   (#pr: perm) (#vskR: erased (Seq.seq S8.t))
                   (#pS: perm) (#vpkS: erased (Seq.seq S8.t))
requires A.pts_to shared vsh ** A.pts_to enc #pn ve **
         A.pts_to skR #pr vskR ** A.pts_to pkS #pS vpkS **
         pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
               Seq.length vskR == 32 /\ Seq.length vpkS == size_dh_public k)
returns r: bool
ensures exists* wsh.
  A.pts_to shared wsh ** A.pts_to enc #pn ve **
  A.pts_to skR #pr vskR ** A.pts_to pkS #pS vpkS **
  pure (Seq.length wsh == 32 /\ Seq.length ve == size_dh_public k /\
        Seq.length vskR == 32 /\ Seq.length vpkS == size_dh_public k /\
        r == Some? (auth_decap k ve vskR vpkS) /\
        (r ==> wsh == Some?.v (auth_decap k ve vskR vpkS)))
{
  A.pts_to_len shared;
  A.pts_to_len enc;
  A.pts_to_len skR;
  A.pts_to_len pkS;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (3 * size_dh_public k);
  let pl = pk_len k;
  let z8 = S8.zero;

  let mut dho = [| z8; 64sz |];
  Mem.track dho;
  A.pts_to_len dho;
  let mut tmp = [| z8; 32sz |];
  Mem.track tmp;
  A.pts_to_len tmp;

  let ok1 = dh_impl k tmp skR enc;
  if ok1 {
    copy_at dho 0sz tmp 32sz;
    with d1. assert (A.pts_to tmp d1);
    let ok2 = dh_impl k tmp skR pkS;
    if ok2 {
      copy_at dho 32sz tmp 32sz;
      with d2. assert (A.pts_to tmp d2);
      with vdho. assert (A.pts_to dho vdho);
      A.pts_to_len dho;
      cat2_pointwise vdho d1 d2;
      let mut pkRm = [| z8; pl |];
      Mem.track pkRm;
      A.pts_to_len pkRm;
      let ok3 = stp_impl k pkRm skR;
      if ok3 {
        let mut ctx = [| z8; SZ.add (SZ.add pl pl) pl |];
        Mem.track ctx;
        A.pts_to_len ctx;
        copy_at ctx 0sz enc pl;
        copy_at ctx pl pkRm pl;
        copy_at ctx (SZ.add pl pl) pkS pl;
        with vctx. assert (A.pts_to ctx vctx);
        with wp. assert (A.pts_to pkRm wp);
        A.pts_to_len ctx;
        cat3_pointwise vctx ve wp vpkS;
        extract_and_expand_impl k shared dho 64sz ctx (SZ.add (SZ.add pl pl) pl);
        Mem.wipe ctx (SZ.add (SZ.add pl pl) pl);
        Mem.wipe pkRm pl;
        Mem.wipe tmp 32sz;
        Mem.wipe dho 64sz;
        true
      } else { Mem.wipe pkRm pl;
      Mem.wipe tmp 32sz;
      Mem.wipe dho 64sz;
      false }
    } else { Mem.wipe tmp 32sz;
    Mem.wipe dho 64sz;
    false }
  } else { Mem.wipe tmp 32sz;
  Mem.wipe dho 64sz;
  false }
}

#pop-options
