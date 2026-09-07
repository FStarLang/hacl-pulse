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

(** The four SHA-2 algorithms, as C functions.

    This is the only module of the hash that is not generic: it names the
    [Spec.SHA2.params] value for each algorithm, which is what makes Custard
    emit four specialized copies of everything in [Hacl.Hash.SHA2.Core].

    It is also where the round constants and the initial state are put in
    memory.  The direct-to-C backend has no way to write a compile-time array,
    so each entry point allocates the tables on the stack and stores the
    literals into them; the sequence that results is the one
    [Spec.SHA2.Constants] defines, by construction rather than by proof.  That
    costs sixty-four (eighty) stores per call, which is a few percent of the
    work of hashing a single block and nothing at all on a long message; a
    later revision that teaches the backend about constant globals can delete
    these functions without touching anything else. *)
module Hacl.Hash.SHA2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Hacl.Hash.SHA2.Core

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** [Spec.SHA2.max_input] is [2^61] for the thirty-two bit family and [2^125]
    for the sixty-four bit one, so the [2^61] the callers promise is enough for
    both. *)
let max_input_bound (_: unit)
  : Lemma (pow2 61 <= max_input #S32.t /\ pow2 61 <= max_input #S64.t)
  = assert_norm (bits #S32.t == 32);
    assert_norm (bits #S64.t == 64);
    Math.pow2_le_compat 125 61


(** The SHA-224/256 round constants. *)
fn fill_k256 (b: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 64 (S32.classify 0ul))
ensures S.pts_to b k256
{
  S.pts_to_len b;
  S.((b.(0sz) <- S32.classify 0x428a2f98ul)); S.pts_to_len b;
  S.((b.(1sz) <- S32.classify 0x71374491ul)); S.pts_to_len b;
  S.((b.(2sz) <- S32.classify 0xb5c0fbcful)); S.pts_to_len b;
  S.((b.(3sz) <- S32.classify 0xe9b5dba5ul)); S.pts_to_len b;
  S.((b.(4sz) <- S32.classify 0x3956c25bul)); S.pts_to_len b;
  S.((b.(5sz) <- S32.classify 0x59f111f1ul)); S.pts_to_len b;
  S.((b.(6sz) <- S32.classify 0x923f82a4ul)); S.pts_to_len b;
  S.((b.(7sz) <- S32.classify 0xab1c5ed5ul)); S.pts_to_len b;
  S.((b.(8sz) <- S32.classify 0xd807aa98ul)); S.pts_to_len b;
  S.((b.(9sz) <- S32.classify 0x12835b01ul)); S.pts_to_len b;
  S.((b.(10sz) <- S32.classify 0x243185beul)); S.pts_to_len b;
  S.((b.(11sz) <- S32.classify 0x550c7dc3ul)); S.pts_to_len b;
  S.((b.(12sz) <- S32.classify 0x72be5d74ul)); S.pts_to_len b;
  S.((b.(13sz) <- S32.classify 0x80deb1feul)); S.pts_to_len b;
  S.((b.(14sz) <- S32.classify 0x9bdc06a7ul)); S.pts_to_len b;
  S.((b.(15sz) <- S32.classify 0xc19bf174ul)); S.pts_to_len b;
  S.((b.(16sz) <- S32.classify 0xe49b69c1ul)); S.pts_to_len b;
  S.((b.(17sz) <- S32.classify 0xefbe4786ul)); S.pts_to_len b;
  S.((b.(18sz) <- S32.classify 0x0fc19dc6ul)); S.pts_to_len b;
  S.((b.(19sz) <- S32.classify 0x240ca1ccul)); S.pts_to_len b;
  S.((b.(20sz) <- S32.classify 0x2de92c6ful)); S.pts_to_len b;
  S.((b.(21sz) <- S32.classify 0x4a7484aaul)); S.pts_to_len b;
  S.((b.(22sz) <- S32.classify 0x5cb0a9dcul)); S.pts_to_len b;
  S.((b.(23sz) <- S32.classify 0x76f988daul)); S.pts_to_len b;
  S.((b.(24sz) <- S32.classify 0x983e5152ul)); S.pts_to_len b;
  S.((b.(25sz) <- S32.classify 0xa831c66dul)); S.pts_to_len b;
  S.((b.(26sz) <- S32.classify 0xb00327c8ul)); S.pts_to_len b;
  S.((b.(27sz) <- S32.classify 0xbf597fc7ul)); S.pts_to_len b;
  S.((b.(28sz) <- S32.classify 0xc6e00bf3ul)); S.pts_to_len b;
  S.((b.(29sz) <- S32.classify 0xd5a79147ul)); S.pts_to_len b;
  S.((b.(30sz) <- S32.classify 0x06ca6351ul)); S.pts_to_len b;
  S.((b.(31sz) <- S32.classify 0x14292967ul)); S.pts_to_len b;
  S.((b.(32sz) <- S32.classify 0x27b70a85ul)); S.pts_to_len b;
  S.((b.(33sz) <- S32.classify 0x2e1b2138ul)); S.pts_to_len b;
  S.((b.(34sz) <- S32.classify 0x4d2c6dfcul)); S.pts_to_len b;
  S.((b.(35sz) <- S32.classify 0x53380d13ul)); S.pts_to_len b;
  S.((b.(36sz) <- S32.classify 0x650a7354ul)); S.pts_to_len b;
  S.((b.(37sz) <- S32.classify 0x766a0abbul)); S.pts_to_len b;
  S.((b.(38sz) <- S32.classify 0x81c2c92eul)); S.pts_to_len b;
  S.((b.(39sz) <- S32.classify 0x92722c85ul)); S.pts_to_len b;
  S.((b.(40sz) <- S32.classify 0xa2bfe8a1ul)); S.pts_to_len b;
  S.((b.(41sz) <- S32.classify 0xa81a664bul)); S.pts_to_len b;
  S.((b.(42sz) <- S32.classify 0xc24b8b70ul)); S.pts_to_len b;
  S.((b.(43sz) <- S32.classify 0xc76c51a3ul)); S.pts_to_len b;
  S.((b.(44sz) <- S32.classify 0xd192e819ul)); S.pts_to_len b;
  S.((b.(45sz) <- S32.classify 0xd6990624ul)); S.pts_to_len b;
  S.((b.(46sz) <- S32.classify 0xf40e3585ul)); S.pts_to_len b;
  S.((b.(47sz) <- S32.classify 0x106aa070ul)); S.pts_to_len b;
  S.((b.(48sz) <- S32.classify 0x19a4c116ul)); S.pts_to_len b;
  S.((b.(49sz) <- S32.classify 0x1e376c08ul)); S.pts_to_len b;
  S.((b.(50sz) <- S32.classify 0x2748774cul)); S.pts_to_len b;
  S.((b.(51sz) <- S32.classify 0x34b0bcb5ul)); S.pts_to_len b;
  S.((b.(52sz) <- S32.classify 0x391c0cb3ul)); S.pts_to_len b;
  S.((b.(53sz) <- S32.classify 0x4ed8aa4aul)); S.pts_to_len b;
  S.((b.(54sz) <- S32.classify 0x5b9cca4ful)); S.pts_to_len b;
  S.((b.(55sz) <- S32.classify 0x682e6ff3ul)); S.pts_to_len b;
  S.((b.(56sz) <- S32.classify 0x748f82eeul)); S.pts_to_len b;
  S.((b.(57sz) <- S32.classify 0x78a5636ful)); S.pts_to_len b;
  S.((b.(58sz) <- S32.classify 0x84c87814ul)); S.pts_to_len b;
  S.((b.(59sz) <- S32.classify 0x8cc70208ul)); S.pts_to_len b;
  S.((b.(60sz) <- S32.classify 0x90befffaul)); S.pts_to_len b;
  S.((b.(61sz) <- S32.classify 0xa4506cebul)); S.pts_to_len b;
  S.((b.(62sz) <- S32.classify 0xbef9a3f7ul)); S.pts_to_len b;
  S.((b.(63sz) <- S32.classify 0xc67178f2ul)); S.pts_to_len b;
}


(** The SHA-256 initial state. *)
fn fill_iv256 (b: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 8 (S32.classify 0ul))
ensures S.pts_to b iv256
{
  S.pts_to_len b;
  S.((b.(0sz) <- S32.classify 0x6a09e667ul)); S.pts_to_len b;
  S.((b.(1sz) <- S32.classify 0xbb67ae85ul)); S.pts_to_len b;
  S.((b.(2sz) <- S32.classify 0x3c6ef372ul)); S.pts_to_len b;
  S.((b.(3sz) <- S32.classify 0xa54ff53aul)); S.pts_to_len b;
  S.((b.(4sz) <- S32.classify 0x510e527ful)); S.pts_to_len b;
  S.((b.(5sz) <- S32.classify 0x9b05688cul)); S.pts_to_len b;
  S.((b.(6sz) <- S32.classify 0x1f83d9abul)); S.pts_to_len b;
  S.((b.(7sz) <- S32.classify 0x5be0cd19ul)); S.pts_to_len b;
}


(** The SHA-224 initial state. *)
fn fill_iv224 (b: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 8 (S32.classify 0ul))
ensures S.pts_to b iv224
{
  S.pts_to_len b;
  S.((b.(0sz) <- S32.classify 0xc1059ed8ul)); S.pts_to_len b;
  S.((b.(1sz) <- S32.classify 0x367cd507ul)); S.pts_to_len b;
  S.((b.(2sz) <- S32.classify 0x3070dd17ul)); S.pts_to_len b;
  S.((b.(3sz) <- S32.classify 0xf70e5939ul)); S.pts_to_len b;
  S.((b.(4sz) <- S32.classify 0xffc00b31ul)); S.pts_to_len b;
  S.((b.(5sz) <- S32.classify 0x68581511ul)); S.pts_to_len b;
  S.((b.(6sz) <- S32.classify 0x64f98fa7ul)); S.pts_to_len b;
  S.((b.(7sz) <- S32.classify 0xbefa4fa4ul)); S.pts_to_len b;
}


(** The SHA-384/512 round constants. *)
fn fill_k512 (b: S.slice S64.t) (#v0: erased (Seq.seq S64.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 80 (S64.classify 0uL))
ensures S.pts_to b k512
{
  S.pts_to_len b;
  S.((b.(0sz) <- S64.classify 0x428a2f98d728ae22uL)); S.pts_to_len b;
  S.((b.(1sz) <- S64.classify 0x7137449123ef65cduL)); S.pts_to_len b;
  S.((b.(2sz) <- S64.classify 0xb5c0fbcfec4d3b2fuL)); S.pts_to_len b;
  S.((b.(3sz) <- S64.classify 0xe9b5dba58189dbbcuL)); S.pts_to_len b;
  S.((b.(4sz) <- S64.classify 0x3956c25bf348b538uL)); S.pts_to_len b;
  S.((b.(5sz) <- S64.classify 0x59f111f1b605d019uL)); S.pts_to_len b;
  S.((b.(6sz) <- S64.classify 0x923f82a4af194f9buL)); S.pts_to_len b;
  S.((b.(7sz) <- S64.classify 0xab1c5ed5da6d8118uL)); S.pts_to_len b;
  S.((b.(8sz) <- S64.classify 0xd807aa98a3030242uL)); S.pts_to_len b;
  S.((b.(9sz) <- S64.classify 0x12835b0145706fbeuL)); S.pts_to_len b;
  S.((b.(10sz) <- S64.classify 0x243185be4ee4b28cuL)); S.pts_to_len b;
  S.((b.(11sz) <- S64.classify 0x550c7dc3d5ffb4e2uL)); S.pts_to_len b;
  S.((b.(12sz) <- S64.classify 0x72be5d74f27b896fuL)); S.pts_to_len b;
  S.((b.(13sz) <- S64.classify 0x80deb1fe3b1696b1uL)); S.pts_to_len b;
  S.((b.(14sz) <- S64.classify 0x9bdc06a725c71235uL)); S.pts_to_len b;
  S.((b.(15sz) <- S64.classify 0xc19bf174cf692694uL)); S.pts_to_len b;
  S.((b.(16sz) <- S64.classify 0xe49b69c19ef14ad2uL)); S.pts_to_len b;
  S.((b.(17sz) <- S64.classify 0xefbe4786384f25e3uL)); S.pts_to_len b;
  S.((b.(18sz) <- S64.classify 0x0fc19dc68b8cd5b5uL)); S.pts_to_len b;
  S.((b.(19sz) <- S64.classify 0x240ca1cc77ac9c65uL)); S.pts_to_len b;
  S.((b.(20sz) <- S64.classify 0x2de92c6f592b0275uL)); S.pts_to_len b;
  S.((b.(21sz) <- S64.classify 0x4a7484aa6ea6e483uL)); S.pts_to_len b;
  S.((b.(22sz) <- S64.classify 0x5cb0a9dcbd41fbd4uL)); S.pts_to_len b;
  S.((b.(23sz) <- S64.classify 0x76f988da831153b5uL)); S.pts_to_len b;
  S.((b.(24sz) <- S64.classify 0x983e5152ee66dfabuL)); S.pts_to_len b;
  S.((b.(25sz) <- S64.classify 0xa831c66d2db43210uL)); S.pts_to_len b;
  S.((b.(26sz) <- S64.classify 0xb00327c898fb213fuL)); S.pts_to_len b;
  S.((b.(27sz) <- S64.classify 0xbf597fc7beef0ee4uL)); S.pts_to_len b;
  S.((b.(28sz) <- S64.classify 0xc6e00bf33da88fc2uL)); S.pts_to_len b;
  S.((b.(29sz) <- S64.classify 0xd5a79147930aa725uL)); S.pts_to_len b;
  S.((b.(30sz) <- S64.classify 0x06ca6351e003826fuL)); S.pts_to_len b;
  S.((b.(31sz) <- S64.classify 0x142929670a0e6e70uL)); S.pts_to_len b;
  S.((b.(32sz) <- S64.classify 0x27b70a8546d22ffcuL)); S.pts_to_len b;
  S.((b.(33sz) <- S64.classify 0x2e1b21385c26c926uL)); S.pts_to_len b;
  S.((b.(34sz) <- S64.classify 0x4d2c6dfc5ac42aeduL)); S.pts_to_len b;
  S.((b.(35sz) <- S64.classify 0x53380d139d95b3dfuL)); S.pts_to_len b;
  S.((b.(36sz) <- S64.classify 0x650a73548baf63deuL)); S.pts_to_len b;
  S.((b.(37sz) <- S64.classify 0x766a0abb3c77b2a8uL)); S.pts_to_len b;
  S.((b.(38sz) <- S64.classify 0x81c2c92e47edaee6uL)); S.pts_to_len b;
  S.((b.(39sz) <- S64.classify 0x92722c851482353buL)); S.pts_to_len b;
  S.((b.(40sz) <- S64.classify 0xa2bfe8a14cf10364uL)); S.pts_to_len b;
  S.((b.(41sz) <- S64.classify 0xa81a664bbc423001uL)); S.pts_to_len b;
  S.((b.(42sz) <- S64.classify 0xc24b8b70d0f89791uL)); S.pts_to_len b;
  S.((b.(43sz) <- S64.classify 0xc76c51a30654be30uL)); S.pts_to_len b;
  S.((b.(44sz) <- S64.classify 0xd192e819d6ef5218uL)); S.pts_to_len b;
  S.((b.(45sz) <- S64.classify 0xd69906245565a910uL)); S.pts_to_len b;
  S.((b.(46sz) <- S64.classify 0xf40e35855771202auL)); S.pts_to_len b;
  S.((b.(47sz) <- S64.classify 0x106aa07032bbd1b8uL)); S.pts_to_len b;
  S.((b.(48sz) <- S64.classify 0x19a4c116b8d2d0c8uL)); S.pts_to_len b;
  S.((b.(49sz) <- S64.classify 0x1e376c085141ab53uL)); S.pts_to_len b;
  S.((b.(50sz) <- S64.classify 0x2748774cdf8eeb99uL)); S.pts_to_len b;
  S.((b.(51sz) <- S64.classify 0x34b0bcb5e19b48a8uL)); S.pts_to_len b;
  S.((b.(52sz) <- S64.classify 0x391c0cb3c5c95a63uL)); S.pts_to_len b;
  S.((b.(53sz) <- S64.classify 0x4ed8aa4ae3418acbuL)); S.pts_to_len b;
  S.((b.(54sz) <- S64.classify 0x5b9cca4f7763e373uL)); S.pts_to_len b;
  S.((b.(55sz) <- S64.classify 0x682e6ff3d6b2b8a3uL)); S.pts_to_len b;
  S.((b.(56sz) <- S64.classify 0x748f82ee5defb2fcuL)); S.pts_to_len b;
  S.((b.(57sz) <- S64.classify 0x78a5636f43172f60uL)); S.pts_to_len b;
  S.((b.(58sz) <- S64.classify 0x84c87814a1f0ab72uL)); S.pts_to_len b;
  S.((b.(59sz) <- S64.classify 0x8cc702081a6439ecuL)); S.pts_to_len b;
  S.((b.(60sz) <- S64.classify 0x90befffa23631e28uL)); S.pts_to_len b;
  S.((b.(61sz) <- S64.classify 0xa4506cebde82bde9uL)); S.pts_to_len b;
  S.((b.(62sz) <- S64.classify 0xbef9a3f7b2c67915uL)); S.pts_to_len b;
  S.((b.(63sz) <- S64.classify 0xc67178f2e372532buL)); S.pts_to_len b;
  S.((b.(64sz) <- S64.classify 0xca273eceea26619cuL)); S.pts_to_len b;
  S.((b.(65sz) <- S64.classify 0xd186b8c721c0c207uL)); S.pts_to_len b;
  S.((b.(66sz) <- S64.classify 0xeada7dd6cde0eb1euL)); S.pts_to_len b;
  S.((b.(67sz) <- S64.classify 0xf57d4f7fee6ed178uL)); S.pts_to_len b;
  S.((b.(68sz) <- S64.classify 0x06f067aa72176fbauL)); S.pts_to_len b;
  S.((b.(69sz) <- S64.classify 0x0a637dc5a2c898a6uL)); S.pts_to_len b;
  S.((b.(70sz) <- S64.classify 0x113f9804bef90daeuL)); S.pts_to_len b;
  S.((b.(71sz) <- S64.classify 0x1b710b35131c471buL)); S.pts_to_len b;
  S.((b.(72sz) <- S64.classify 0x28db77f523047d84uL)); S.pts_to_len b;
  S.((b.(73sz) <- S64.classify 0x32caab7b40c72493uL)); S.pts_to_len b;
  S.((b.(74sz) <- S64.classify 0x3c9ebe0a15c9bebcuL)); S.pts_to_len b;
  S.((b.(75sz) <- S64.classify 0x431d67c49c100d4cuL)); S.pts_to_len b;
  S.((b.(76sz) <- S64.classify 0x4cc5d4becb3e42b6uL)); S.pts_to_len b;
  S.((b.(77sz) <- S64.classify 0x597f299cfc657e2auL)); S.pts_to_len b;
  S.((b.(78sz) <- S64.classify 0x5fcb6fab3ad6faecuL)); S.pts_to_len b;
  S.((b.(79sz) <- S64.classify 0x6c44198c4a475817uL)); S.pts_to_len b;
}


(** The SHA-512 initial state. *)
fn fill_iv512 (b: S.slice S64.t) (#v0: erased (Seq.seq S64.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 8 (S64.classify 0uL))
ensures S.pts_to b iv512
{
  S.pts_to_len b;
  S.((b.(0sz) <- S64.classify 0x6a09e667f3bcc908uL)); S.pts_to_len b;
  S.((b.(1sz) <- S64.classify 0xbb67ae8584caa73buL)); S.pts_to_len b;
  S.((b.(2sz) <- S64.classify 0x3c6ef372fe94f82buL)); S.pts_to_len b;
  S.((b.(3sz) <- S64.classify 0xa54ff53a5f1d36f1uL)); S.pts_to_len b;
  S.((b.(4sz) <- S64.classify 0x510e527fade682d1uL)); S.pts_to_len b;
  S.((b.(5sz) <- S64.classify 0x9b05688c2b3e6c1fuL)); S.pts_to_len b;
  S.((b.(6sz) <- S64.classify 0x1f83d9abfb41bd6buL)); S.pts_to_len b;
  S.((b.(7sz) <- S64.classify 0x5be0cd19137e2179uL)); S.pts_to_len b;
}


(** The SHA-384 initial state. *)
fn fill_iv384 (b: S.slice S64.t) (#v0: erased (Seq.seq S64.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 8 (S64.classify 0uL))
ensures S.pts_to b iv384
{
  S.pts_to_len b;
  S.((b.(0sz) <- S64.classify 0xcbbb9d5dc1059ed8uL)); S.pts_to_len b;
  S.((b.(1sz) <- S64.classify 0x629a292a367cd507uL)); S.pts_to_len b;
  S.((b.(2sz) <- S64.classify 0x9159015a3070dd17uL)); S.pts_to_len b;
  S.((b.(3sz) <- S64.classify 0x152fecd8f70e5939uL)); S.pts_to_len b;
  S.((b.(4sz) <- S64.classify 0x67332667ffc00b31uL)); S.pts_to_len b;
  S.((b.(5sz) <- S64.classify 0x8eb44a8768581511uL)); S.pts_to_len b;
  S.((b.(6sz) <- S64.classify 0xdb0c2e0d64f98fa7uL)); S.pts_to_len b;
  S.((b.(7sz) <- S64.classify 0x47b5481dbefa4fa4uL)); S.pts_to_len b;
}


(** {2 The four algorithms}

    Each takes the digest buffer first, as HACL* does, and a slice rather than
    a pointer and a length; [Hacl.Hash.SHA2.Ptr] is the flat C interface. *)


(** SHA-224. *)
fn sha224 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 28 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_224 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv224 ivt;
  max_input_bound ();
  hash_impl sha2_224 kt ivt out input;
  S.to_array ivt;
  S.to_array kt;
}


(** SHA-256. *)
fn sha256 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 32 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_256 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv256 ivt;
  max_input_bound ();
  hash_impl sha2_256 kt ivt out input;
  S.to_array ivt;
  S.to_array kt;
}


(** SHA-384. *)
fn sha384 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 48 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_384 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv384 ivt;
  max_input_bound ();
  hash_impl sha2_384 kt ivt out input;
  S.to_array ivt;
  S.to_array kt;
}


(** SHA-512. *)
fn sha512 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 64 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_512 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv512 ivt;
  max_input_bound ();
  hash_impl sha2_512 kt ivt out input;
  S.to_array ivt;
  S.to_array kt;
}
