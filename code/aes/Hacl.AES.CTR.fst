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

(** Counter mode: the standard incrementing function of NIST SP 800-38A on
    the last four bytes, and the keystream it drives.

    [inc32] is written as a carry chain over the four bytes with the carry
    itself a mask, so that a counter which happens to be secret leaks nothing
    through a branch.  The alternative -- loading the four bytes into a
    thirty-two bit word -- would need a secret-integer cast for no gain.

    Encryption is in place, one block of keystream at a time, and the final
    partial block is handled by the same inner loop rather than by a separate
    path: [Spec.AES.ctr_keystream] is stated pointwise for exactly that
    reason. *)
module Hacl.AES.CTR

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core
open Hacl.AES.Cipher

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Copy = Hacl.Impl.Copy

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side of [inc32]} *)

(** Four bytes, most significant first, are recovered from the number they
    make: the standard digit extraction, spelled out because the numbers are
    the only place division appears in this file. *)
let byte_at_digits (a b c d: elem)
  : Lemma (let x = a * 16777216 + b * 65536 + c * 256 + d in
           x < 4294967296 /\
           byte_at x 0 == d /\ byte_at x 8 == c /\
           byte_at x 16 == b /\ byte_at x 24 == a)
  = assert_norm (pow2 0 == 1);
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 16 == 65536);
    assert_norm (pow2 24 == 16777216);
    let x = a * 16777216 + b * 65536 + c * 256 + d in
    let y = a * 65536 + b * 256 + c in
    let z = a * 256 + b in
    assert (x == d + y * 256);
    Math.lemma_div_plus d y 256; Math.small_div d 256;
    Math.lemma_mod_plus d y 256; Math.small_mod d 256;
    assert (y == c + z * 256);
    Math.lemma_div_plus c z 256; Math.small_div c 256;
    Math.lemma_mod_plus c z 256; Math.small_mod c 256;
    Math.lemma_div_plus b a 256; Math.small_div b 256;
    Math.lemma_mod_plus b a 256; Math.small_mod b 256;
    Math.division_multiplication_lemma x 256 256;
    Math.division_multiplication_lemma x 65536 256;
    Math.small_mod a 256

#push-options "--z3rlimit 400"

(** The carry chain is the increment.  [c15] is the carry out of the last
    byte, [c14] out of the last two, and so on: each is the previous carry
    kept only where the byte was already all ones. *)
let inc32_bytes (b: block) (r12 r13 r14 r15: elem)
  : Lemma (requires
      (let x12 = Seq.index b 12 in let x13 = Seq.index b 13 in
       let x14 = Seq.index b 14 in let x15 = Seq.index b 15 in
       let c15 = (if x15 = 255 then 1 else 0) in
       let c14 = (if x14 = 255 then c15 else 0) in
       let c13 = (if x13 = 255 then c14 else 0) in
       r15 == (x15 + 1) % 256 /\ r14 == (x14 + c15) % 256 /\
       r13 == (x13 + c14) % 256 /\ r12 == (x12 + c13) % 256))
    (ensures
      (forall (j: nat). j < 12 ==> Seq.index (inc32 b) j == Seq.index b j) /\
      Seq.index (inc32 b) 12 == r12 /\ Seq.index (inc32 b) 13 == r13 /\
      Seq.index (inc32 b) 14 == r14 /\ Seq.index (inc32 b) 15 == r15)
  = assert_norm (pow2 32 == 4294967296);
    let x12 = Seq.index b 12 in let x13 = Seq.index b 13 in
    let x14 = Seq.index b 14 in let x15 = Seq.index b 15 in
    byte_at_digits x12 x13 x14 x15;
    let n = be32 b in
    assert (n == x12 * 16777216 + x13 * 65536 + x14 * 256 + x15);
    if x15 < 255 then begin
      byte_at_digits x12 x13 x14 (x15 + 1);
      Math.small_mod (n + 1) 4294967296
    end else if x14 < 255 then begin
      byte_at_digits x12 x13 (x14 + 1) 0;
      Math.small_mod (n + 1) 4294967296
    end else if x13 < 255 then begin
      byte_at_digits x12 (x13 + 1) 0 0;
      Math.small_mod (n + 1) 4294967296
    end else if x12 < 255 then begin
      byte_at_digits (x12 + 1) 0 0 0;
      Math.small_mod (n + 1) 4294967296
    end else begin
      byte_at_digits 0 0 0 0;
      Math.lemma_mod_plus 0 1 4294967296
    end

#pop-options

(** {2 The pure side of the keystream} *)

#push-options "--fuel 1 --ifuel 1"
let counter_block_zero (b: block) : Lemma (counter_block b 0 == b) = ()

let counter_block_step (b: block) (j: nat)
  : Lemma (counter_block b (j + 1) == inc32 (counter_block b j)) = ()
#pop-options

let ks_index (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
             (n: nat) (j: nat) (bi: nat) (t: nat)
  : Lemma (requires j == 16 * bi /\ t < 16 /\ j + t < n)
          (ensures ctr_keystream v w b n (j + t) ==
                   Seq.index (cipher v w (counter_block b bi)) t)
  = Math.lemma_div_plus t bi 16; Math.small_div t 16;
    Math.lemma_mod_plus t bi 16; Math.small_mod t 16

let ctr_done (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
             (m m': Seq.seq elem) (n: nat)
  : Lemma (requires Seq.length m == n /\ Seq.length m' == n /\
             (forall (k: nat). k < n ==>
                Seq.index m' k == Seq.index m k ^^ ctr_keystream v w b n k))
          (ensures m' == ctr_encrypt v w b m)
  = Seq.lemma_eq_intro m' (ctr_encrypt v w b m)

(** {2 The increment} *)

fn inc32_impl (ctr: S.slice S8.t) (#v0: erased (Seq.seq S8.t))
requires S.pts_to ctr v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). S.pts_to ctr v1 ** pure (
  Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\
  vals v1 == inc32 (vals v0))
{
  S.pts_to_len ctr;
  let one = S8.classify 1uy;
  let ff = S8.classify 255uy;
  let x12 = S.(ctr.(12sz));
  let x13 = S.(ctr.(13sz));
  let x14 = S.(ctr.(14sz));
  let x15 = S.(ctr.(15sz));
  let r15 = S8.add_mod x15 one;
  let c15 = S8.select (S8.eq_mask x15 ff) one S8.zero;
  let r14 = S8.add_mod x14 c15;
  let c14 = S8.select (S8.eq_mask x14 ff) c15 S8.zero;
  let r13 = S8.add_mod x13 c14;
  let c13 = S8.select (S8.eq_mask x13 ff) c14 S8.zero;
  let r12 = S8.add_mod x12 c13;
  S.((ctr.(12sz) <- r12));
  S.((ctr.(13sz) <- r13));
  S.((ctr.(14sz) <- r14));
  S.((ctr.(15sz) <- r15));
  with v1. assert S.pts_to ctr v1;
  assert_norm (pow2 8 == 256);
  inc32_bytes (vals v0) (S8.v r12) (S8.v r13) (S8.v r14) (S8.v r15);
  Seq.lemma_eq_intro (vals v1) (inc32 (vals v0));
  S.pts_to_len ctr;
}

(** {2 Counter mode}

    [ctr] holds the initial counter block and is advanced as the loop runs;
    its final value is left unspecified, since every caller either discards
    it or, in GCM's case, has already saved what it needs. *)

fn ctr_encrypt_impl ([@@@FStar.Attributes.monomorphize] p: params)
                    (msg: S.slice S8.t) (w: S.slice S8.t) (ctr: S.slice S8.t)
                    (#vm0 #vw #vc0: erased (Seq.seq S8.t))
requires S.pts_to msg vm0 ** S.pts_to w vw ** S.pts_to ctr vc0 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
  SZ.fits (Seq.length vm0 + blocklen))
ensures exists* (vm1 vc1: Seq.seq S8.t).
  S.pts_to msg vm1 ** S.pts_to w vw ** S.pts_to ctr vc1 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
  Seq.length vc1 == blocklen /\ Seq.length vm1 == Seq.length vm0 /\
  vals vm1 == ctr_encrypt p.pv (vals vw) (vals vc0) (vals vm0))
{
  S.pts_to_len msg;
  S.pts_to_len w;
  S.pts_to_len ctr;
  let n = S.len msg;
  let z = S8.zero;
  let mut ka = [| z; 16sz |];
  A.pts_to_len ka;
  let ks = S.from_array ka 16sz;
  S.pts_to_len ks;

  counter_block_zero (vals vc0);
  let mut j = 0sz;
  let mut bi = 0sz;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (vbi: SZ.t) (vm: Seq.seq S8.t)
                    (vc: Seq.seq S8.t) (vk: Seq.seq S8.t).
    pts_to j vj ** pts_to bi vbi ** S.pts_to msg vm ** S.pts_to w vw **
    S.pts_to ctr vc ** S.pts_to ks vk **
    pure (SZ.v vj == 16 * SZ.v vbi /\ Seq.length vk == blocklen /\
          Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
          Seq.length vc == blocklen /\
          Seq.length vm == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
          SZ.fits (SZ.v n + blocklen) /\ SZ.v vj <= SZ.v n + blocklen /\
          vals vc == counter_block (vals vc0) (SZ.v vbi) /\
          (forall (k: nat). k < SZ.v n ==>
             Seq.index (vals vm) k ==
               (if k < SZ.v vj
                then Seq.index (vals vm0) k ^^
                     ctr_keystream p.pv (vals vw) (vals vc0) (SZ.v n) k
                else Seq.index (vals vm0) k)))
  decreases (SZ.v n + blocklen - SZ.v (!j))
  {
    let vj = !j;
    let vbi = !bi;
    Copy.copy_exact ks ctr 16sz;
    cipher_impl p ks w;
    with vk. assert S.pts_to ks vk;

    let rem = SZ.sub n vj;
    let mut t = 0sz;
    while (let vt = !t; SZ.lt vt 16sz && SZ.lt vt rem)
    invariant exists* (vt: SZ.t) (vm: Seq.seq S8.t).
      pts_to t vt ** S.pts_to msg vm ** S.pts_to w vw ** S.pts_to ks vk **
      pure (SZ.v vt <= blocklen /\ SZ.v vj == 16 * SZ.v vbi /\
            SZ.v vj < SZ.v n /\ SZ.v rem == SZ.v n - SZ.v vj /\
            SZ.fits (SZ.v n + blocklen) /\ Seq.length vk == blocklen /\
            Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
            Seq.length vm == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
            vals vk == cipher p.pv (vals vw) (counter_block (vals vc0) (SZ.v vbi)) /\
            (forall (k: nat). k < SZ.v n ==>
               Seq.index (vals vm) k ==
                 (if k < SZ.v vj + SZ.v vt
                  then Seq.index (vals vm0) k ^^
                       ctr_keystream p.pv (vals vw) (vals vc0) (SZ.v n) k
                  else Seq.index (vals vm0) k)))
    decreases (blocklen - SZ.v (!t))
    {
      let vt = !t;
      SZ.fits_lte (SZ.v vj + SZ.v vt) (SZ.v n + blocklen);
      let idx = SZ.add vj vt;
      let a = S.(msg.(idx));
      let b = S.(ks.(vt));
      let y = bxor a b;
      with vm. assert S.pts_to msg vm;
      ks_index p.pv (vals vw) (vals vc0) (SZ.v n) (SZ.v vj) (SZ.v vbi) (SZ.v vt);
      vals_upd vm (SZ.v idx) y;
      S.((msg.(idx) <- y));
      t := SZ.add vt 1sz;
    };

    with vc. assert S.pts_to ctr vc;
    counter_block_step (vals vc0) (SZ.v vbi);
    inc32_impl ctr;
    j := SZ.add vj 16sz;
    bi := SZ.add vbi 1sz;
  };
  with vm. assert S.pts_to msg vm;
  ctr_done p.pv (vals vw) (vals vc0) (vals vm0) (vals vm) (SZ.v n);
  S.to_array ks;
}

#pop-options
