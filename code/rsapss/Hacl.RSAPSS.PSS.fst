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

(** EMSA-PSS encoding, RFC 8017 section 9.1.

    The encoding is built in place in the output.  [H] is written where it
    belongs, two thirds of the way along, and then used as the MGF1 seed
    directly out of the output array; [DB] is written over the front and
    masked in place.  Nothing is assembled in a scratch buffer and copied.

    The two scratch arrays are [M'], which has to be contiguous because it is
    hashed, and the mask, which has to exist because the exclusive-or reads it
    while writing over [DB]. *)
module Hacl.RSAPSS.PSS

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.RSAPSS
open Hacl.Spec.Bytes
open Hacl.Hash.SHA2.Core
open Hacl.Impl.Copy
open Hacl.RSAPSS.MGF

module Sub = Hacl.Impl.Sub
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Declassify = Hacl.Secret.Declassify

(** {2 Two small helpers} *)

(** [dst[base .. base+n) <- x].  [Hacl.Impl.Copy.fill] writes a whole array;
    the padding string is a prefix of one. *)
fn fill_range (dst: A.array S8.t) (base: SZ.t) (n: SZ.t) (x: S8.t)
              (#vd: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** pure (SZ.v base + SZ.v n <= Seq.length vd)
ensures exists* vd'. A.pts_to dst vd' **
        pure (Seq.length vd' == Seq.length vd /\
              SZ.v base + SZ.v n <= Seq.length vd' /\
              (forall (k: nat). k < SZ.v n ==> Seq.index vd' (SZ.v base + k) == x) /\
              (forall (k: nat). k < Seq.length vd ==>
                 k < SZ.v base \/ k >= SZ.v base + SZ.v n ==> Seq.index vd' k == Seq.index vd k))
{
  A.pts_to_len dst;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S8.t).
    pts_to i vi ** A.pts_to dst vd' **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vd' == Seq.length vd /\
          SZ.v base + SZ.v n <= Seq.length vd' /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' (SZ.v base + k) == x) /\
          (forall (k: nat). k < Seq.length vd ==>
             k < SZ.v base \/ k >= SZ.v base + SZ.v vi ==> Seq.index vd' k == Seq.index vd k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    A.((dst.(SZ.add base vi) <- x));
    i := SZ.add vi 1sz;
  }
}

(** The mask that keeps the bits of the top byte belonging to the number.
    [emBits] is public -- it is the modulus size -- so the shift may be. *)
fn top_mask_of (emBits: U32.t)
requires pure (0 < U32.v emBits /\ U32.v emBits + 7 < pow2 32)
returns r: S8.t
ensures pure (0 < U32.v emBits /\ r == top_mask (U32.v emBits))
{
  em_len_ok (U32.v emBits);
  let spare = U32.sub (U32.mul 8ul (U32.div (U32.add emBits 7ul) 8ul)) emBits;
  let r = S8.classify (U8.shift_right 255uy spare);
  r
}

(** {2 The encoding} *)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

(** [dst[0..n) ^= src[0..n)]. *)
fn xor_range (dst: A.array S8.t) (n: SZ.t) (src: A.array S8.t)
             (#vd: erased (Seq.seq S8.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (SZ.v n <= Seq.length vd /\ SZ.v n <= Seq.length vs)
ensures exists* vd'. A.pts_to dst vd' ** A.pts_to src #ps vs **
        pure (Seq.length vd' == Seq.length vd /\ SZ.v n <= Seq.length vd' /\
              SZ.v n <= Seq.length vs /\
              (forall (k: nat). k < SZ.v n ==>
                 Seq.index vd' k == S8.logxor (Seq.index vd k) (Seq.index vs k)) /\
              (forall (k: nat). SZ.v n <= k /\ k < Seq.length vd' ==>
                 Seq.index vd' k == Seq.index vd k))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S8.t).
    pts_to i vi ** A.pts_to dst vd' ** A.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vd' == Seq.length vd /\
          SZ.v n <= Seq.length vd' /\ SZ.v n <= Seq.length vs /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index vd' k == S8.logxor (Seq.index vd k) (Seq.index vs k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < Seq.length vd' ==>
             Seq.index vd' k == Seq.index vd k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(dst.(vi));
    let b = A.(src.(vi));
    A.((dst.(vi) <- S8.logxor a b));
    i := SZ.add vi 1sz;
  }
}

(** [out] receives [Hash(0^8 | Hash(msg) | salt)], the [H] of EMSA-PSS. *)
fn hash_m_prime (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                (kt: A.array t) (ivt: A.array t)
                (out: A.array S8.t)
                (salt: A.array S8.t) (sLen: SZ.t)
                (msg: A.array S8.t) (mLen: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vout: erased (Seq.seq S8.t))
                (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #t }))
                (#psa: perm)
                (#vsalt: erased (s: Seq.seq S8.t { 8 + (hash_bytes p) + Seq.length s < max_input #t }))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               SZ.v sLen == Seq.length vsalt /\ SZ.v mLen == Seq.length vmsg /\
               Seq.length vmsg < pow2 61 /\
               SZ.fits (8 + (hash_bytes p) + Seq.length vsalt) /\
               8 + (hash_bytes p) + Seq.length vsalt < pow2 61)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg **
  pure (Seq.length vout' == (hash_bytes p) /\
        vout' == hash p (m_prime p (hash p vmsg) vsalt))
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len salt;
  A.pts_to_len msg;
  let hLen = p.nhash_bytes;
  let z8 = S8.classify 0uy;
  let mpLen = SZ.add (SZ.add 8sz hLen) sLen;
  let mut mp = [| z8; mpLen |];
  A.pts_to_len mp;

  (* [mp = 0^8 | Hash(msg) | salt].  The eight zeroes are the initial value. *)
  let mw = Sub.sub mp 8sz (SZ.add 8sz hLen);
  hash_impl p kt ivt mw msg mLen;
  Sub.unsub mp 8 (SZ.v (SZ.add 8sz hLen)) mw;
  copy_at mp (SZ.add 8sz hLen) salt sLen;
  with vmp. assert (A.pts_to mp vmp);
  assert (pure (S8.v z8 == 0 /\ z8 == S8.zero));
  assert (pure (forall (k: nat). k < 8 ==> Seq.index vmp k == S8.zero));
  assert (pure (forall (k: nat). k < (hash_bytes p) ==>
                  Seq.index vmp (8 + k) == Seq.index (hash p vmsg) k));
  assert (pure (forall (k: nat). k < Seq.length vsalt ==>
                  Seq.index vmp (8 + (hash_bytes p) + k) == Seq.index vsalt k));
  m_prime_index p (hash p vmsg) (reveal vsalt) (reveal vmp);
  hash_impl p kt ivt out mp mpLen;
}

(** [em] receives [EMSA-PSS-ENCODE(msg, emBits)] with the given salt.

    [emLen] is passed as well as [emBits] because the caller has both -- it
    sized [em] with it -- and because deriving one from the other in two
    different integer types inside the proof is pure cost. *)
fn pss_encode_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                   (kt: A.array t) (ivt: A.array t)
                   (em: A.array S8.t) (emBits: (e: U32.t { 0 < U32.v e })) (emLen: SZ.t)
                   (salt: A.array S8.t) (sLen: SZ.t)
                   (msg: A.array S8.t) (mLen: SZ.t)
                   (#pk: perm) (#vk: erased (Seq.seq t))
                   (#pi: perm) (#vi: erased (Seq.seq t))
                   (#vem: erased (Seq.seq S8.t))
                   (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #t }))
                   (#psa: perm)
                   (#vsalt: erased (s: Seq.seq S8.t { pss_ok p (Seq.length s) (U32.v emBits) }))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to em vem **
         A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               U32.v emBits + 7 < pow2 32 /\
               SZ.v emLen == em_len (U32.v emBits) /\ Seq.length vem == SZ.v emLen /\
               SZ.v emLen <= 65536 /\
               SZ.v sLen == Seq.length vsalt /\ SZ.v mLen == Seq.length vmsg /\
               Seq.length vmsg < pow2 61 /\
               SZ.fits (8 + (hash_bytes p) + Seq.length vsalt) /\
               8 + (hash_bytes p) + Seq.length vsalt < pow2 61)
ensures exists* vem'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to em vem' **
  A.pts_to salt #psa vsalt ** A.pts_to msg #pm vmsg **
  pure (Seq.length vem' == SZ.v emLen /\
        vem' == pss_encode p (Seq.length vsalt) (U32.v emBits) vsalt vmsg)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len em;
  A.pts_to_len salt;
  A.pts_to_len msg;
  let hLen = p.nhash_bytes;
  SZ.fits_lte (SZ.v hLen + SZ.v sLen + 2) (8 + (hash_bytes p) + Seq.length vsalt);
  (* Neither disjunct can happen: [pss_ok] rules out the first and the
     caller's bound on [emLen] the second.  They are tested anyway so that
     the C compiler, which sees neither, can bound the buffer below. *)
  if (SZ.lt emLen (SZ.add (SZ.add hLen sLen) 2sz) ||
      SZ.lt (Hacl.SizeT.big 65536) emLen) {
    ()
  } else {
  let dbLen = SZ.sub (SZ.sub emLen hLen) 1sz;
  let z8 = S8.classify 0uy;

  let mut mask = [| z8; dbLen |];
  A.pts_to_len mask;

  (* [H] goes straight into its place in the output and is the MGF1 seed
     from there. *)
  let hw = Sub.sub em dbLen (SZ.add dbLen hLen);
  hash_m_prime p kt ivt hw salt sLen msg mLen
               #pk #vk #pi #vi #_ #pm #vmsg #psa #(hide (as_mp_salt p (reveal vsalt)));
  with vh. assert (A.pts_to hw vh);
  seed_ok_hash p (reveal vh);
  mgf_impl p kt ivt mask dbLen hw hLen #pk #vk #pi #vi #_ #_ #(hide (as_seed #t (reveal vh)));
  Sub.unsub em (SZ.v dbLen) (SZ.v (SZ.add dbLen hLen)) hw;
  with vem1. assert (A.pts_to em vem1);
  with vmask. assert (A.pts_to mask vmask);

  (* [DB = 0^k | 0x01 | salt] over the front of the output. *)
  let padLen = SZ.sub (SZ.sub dbLen sLen) 1sz;
  fill_range em 0sz padLen z8;
  A.((em.(padLen) <- S8.classify 1uy));
  copy_at em (SZ.sub dbLen sLen) salt sLen;
  with vem2. assert (A.pts_to em vem2);

  (* Mask it. *)
  xor_range em dbLen mask;

  (* Clear the spare bits, and stamp the trailer. *)
  let tm = top_mask_of emBits;
  let e0 = A.(em.(0sz));
  A.((em.(0sz) <- S8.logand e0 tm));
  A.((em.(SZ.sub emLen 1sz) <- S8.classify 0xbcuy));

  with vem4. assert (A.pts_to em vem4);
  pss_encode_pointwise p (Seq.length vsalt) (U32.v emBits) (reveal vsalt) (reveal vmsg)
                       (reveal vh) (reveal vmask) (reveal vem2) (reveal vem4);
  ()
  }
}

#pop-options

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

(** {2 Verification} *)

(** Everything an EMSA-PSS verifier looks at is public: the encoded message
    was transmitted in the clear and the answer is a single bit the caller
    asked for.  So the checks below declassify and return a plain [bool]
    rather than accumulating a constant-time mask. *)

(** [forall k < n. a[k] == 0]. *)
fn all_zero (a: A.array S8.t) (n: SZ.t) (#pa: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to a #pa va ** pure (SZ.v n <= Seq.length va)
returns ok: bool
ensures A.pts_to a #pa va **
        pure (SZ.v n <= Seq.length va /\
              (ok <==> (forall (k: nat). k < SZ.v n ==> S8.v (Seq.index va k) == 0)))
{
  A.pts_to_len a;
  let mut acc = true;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vacc: bool).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va **
    pure (SZ.v vi <= SZ.v n /\ SZ.v n <= Seq.length va /\
          (vacc <==> (forall (k: nat). k < SZ.v vi ==> S8.v (Seq.index va k) == 0)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = Declassify.u8 (A.(a.(vi)));
    let vacc = !acc;
    acc := vacc && (x = 0uy);
    i := SZ.add vi 1sz;
  };
  !acc
}

(** [a[0..n) == b[base .. base+n)]. *)
fn eq_range (a: A.array S8.t) (b: A.array S8.t) (base: SZ.t) (n: SZ.t)
            (#pa: perm) (#va: erased (Seq.seq S8.t))
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (SZ.v n <= Seq.length va /\ SZ.v base + SZ.v n <= Seq.length vb)
returns ok: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (SZ.v n <= Seq.length va /\ SZ.v base + SZ.v n <= Seq.length vb /\
              (ok <==> (forall (k: nat). k < SZ.v n ==>
                         S8.v (Seq.index va k) == S8.v (Seq.index vb (SZ.v base + k)))))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut acc = true;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vacc: bool).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ SZ.v n <= Seq.length va /\
          SZ.v base + SZ.v n <= Seq.length vb /\
          (vacc <==> (forall (k: nat). k < SZ.v vi ==>
                        S8.v (Seq.index va k) == S8.v (Seq.index vb (SZ.v base + k)))))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = Declassify.u8 (A.(a.(vi)));
    let y = Declassify.u8 (A.(b.(SZ.add base vi)));
    let vacc = !acc;
    acc := vacc && (x = y);
    i := SZ.add vi 1sz;
  };
  !acc
}

(** EMSA-PSS-VERIFY, RFC 8017 section 9.1.2.

    This is not the encoder run backwards and compared: a verifier has to
    reject encodings an encoder would never produce, so the two directions
    are separate spec functions and this one proves itself equivalent to
    [Spec.RSAPSS.pss_valid]. *)
fn pss_verify_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                   (kt: A.array t) (ivt: A.array t)
                   (em: A.array S8.t) (emBits: (e: U32.t { 0 < U32.v e })) (emLen: SZ.t)
                   (sLen: (n: SZ.t { pss_ok p (SZ.v n) (U32.v emBits) }))
                   (msg: A.array S8.t) (mLen: SZ.t)
                   (#pk: perm) (#vk: erased (Seq.seq t))
                   (#pi: perm) (#vi: erased (Seq.seq t))
                   (#pe: perm) (#vem: erased (Seq.lseq S8.t (em_len (U32.v emBits))))
                   (#pm: perm) (#vmsg: erased (m: Seq.seq S8.t { Seq.length m < max_input #t }))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to em #pe vem **
         A.pts_to msg #pm vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               U32.v emBits + 7 < pow2 32 /\
               SZ.v emLen == em_len (U32.v emBits) /\
               SZ.v mLen == Seq.length vmsg /\ Seq.length vmsg < pow2 61 /\
               SZ.fits (8 + (hash_bytes p) + SZ.v sLen) /\
               8 + (hash_bytes p) + SZ.v sLen < pow2 61)
returns ok: bool
ensures A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to em #pe vem **
        A.pts_to msg #pm vmsg **
        pure (ok <==> pss_valid p (SZ.v sLen) (U32.v emBits) vmsg vem)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len em;
  A.pts_to_len msg;
  let hLen = p.nhash_bytes;
  let dbLen = SZ.sub (SZ.sub emLen hLen) 1sz;
  let z8 = S8.classify 0uy;
  let tm = top_mask_of emBits;

  (* The trailer and the bits above the modulus. *)
  let trailer = Declassify.u8 (A.(em.(SZ.sub emLen 1sz)));
  let e0 = A.(em.(0sz));
  let topbits = Declassify.u8 (S8.logand e0 (S8.lognot tm));

  (* Unmask the data block into scratch. *)
  let mut db = [| z8; dbLen |];
  A.pts_to_len db;
  copy_at db 0sz em dbLen;
  with vdb0. assert (A.pts_to db vdb0);
  assert (pure (Seq.length vdb0 == SZ.v dbLen /\
                (forall (k: nat). k < SZ.v dbLen ==>
                   Seq.index vdb0 k == Seq.index (Seq.slice (reveal vem) 0 (SZ.v dbLen)) k)));
  let mut mask = [| z8; dbLen |];
  A.pts_to_len mask;

  let hw = Sub.sub em dbLen (SZ.add dbLen hLen);
  with vh. assert (A.pts_to hw #pe vh);
  seed_ok_hash p (reveal vh);
  mgf_impl p kt ivt mask dbLen hw hLen
           #pk #vk #pi #vi #_ #pe #(hide (as_seed #t (reveal vh)));
  Sub.unsub_id em (SZ.v dbLen) (SZ.v (SZ.add dbLen hLen)) hw;

  with vmask. assert (A.pts_to mask vmask);
  xor_range db dbLen mask;
  with vdb1. assert (A.pts_to db vdb1);
  assert (pure (Seq.length vdb1 == SZ.v dbLen /\
                (forall (k: nat). k < SZ.v dbLen ==>
                   Seq.index vdb1 k ==
                     S8.logxor (Seq.index (Seq.slice (reveal vem) 0 (SZ.v dbLen)) k)
                               (Seq.index vmask k))));
  let d0 = A.(db.(0sz));
  A.((db.(0sz) <- S8.logand d0 tm));
  with vdb. assert (A.pts_to db vdb);
  assert (pure (Seq.length vdb == SZ.v dbLen /\
                Seq.index vdb 0 == S8.logand (Seq.index vdb1 0) tm /\
                (forall (k: nat). 0 < k /\ k < SZ.v dbLen ==>
                   Seq.index vdb k == Seq.index vdb1 k)));
  clear_top_xor_index (U32.v emBits) (SZ.v dbLen)
                      (as_lseq (SZ.v dbLen) (Seq.slice (reveal vem) 0 (SZ.v dbLen)))
                      (as_lseq (SZ.v dbLen) (reveal vmask))
                      (as_lseq (SZ.v dbLen) (reveal vdb));

  (* The padding string, the 0x01 separator, and the salt. *)
  let zeros = all_zero db (SZ.sub (SZ.sub dbLen sLen) 1sz);
  let sep = Declassify.u8 (A.(db.(SZ.sub (SZ.sub dbLen sLen) 1sz)));

  let mut hp = [| z8; hLen |];
  A.pts_to_len hp;
  let sw = Sub.sub db (SZ.sub dbLen sLen) dbLen;
  hash_m_prime p kt ivt hp sw sLen msg mLen
               #pk #vk #pi #vi #_ #pm #vmsg #1.0R
               #(hide (as_mp_salt p (Seq.slice (reveal vdb) (SZ.v dbLen - SZ.v sLen) (SZ.v dbLen))));
  Sub.unsub_id db (SZ.v (SZ.sub dbLen sLen)) (SZ.v dbLen) sw;

  let heq = eq_range hp em dbLen hLen;
  with vhp. assert (A.pts_to hp vhp);
  pss_valid_intro p (SZ.v sLen) (U32.v emBits) (reveal vmsg) (reveal vem)
                  (as_lseq (SZ.v dbLen) (reveal vdb)) (as_lseq (SZ.v hLen) (reveal vhp));

  (trailer = 0xbcuy) && (topbits = 0uy) && zeros && (sep = 1uy) && heq
}

#pop-options
