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

(** SHA-1's padding is SHA-2's padding at 32 bits.

    Everything outside the compression function -- the [0x80] byte, the zeros,
    the 64-bit big-endian bit length, how blocks are cut out of the padded
    message -- is byte for byte what [Spec.SHA2] does when its word type is
    [S32.t]: sixty-four byte blocks, an eight byte length field, a [2^61]
    bound.  [Spec.SHA1] states those definitions again rather than
    instantiating SHA-2's, because SHA-1 is not an instance of
    [Spec.SHA2.params] for the parts that matter; but the two {i are} equal,
    and this module proves it.

    The point is reuse.  With these four lemmas the SHA-1 implementation
    inherits the whole of [Spec.SHA2.Lemmas] -- [padded_index],
    [padded_shape], [pad_zeros_alt], [padded_index_block], [tail_bytes] --
    and the whole of the padding code, [write_len_be] and [build_tail],
    without a line of it being written twice.  What is left genuinely specific
    to SHA-1 is the compression function and the five-word digest. *)
module Spec.SHA1.Lemmas

open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module SHA2 = Spec.SHA2

(** The two sets of sizes agree.  Both are [unfold], so this is by
    computation; it is stated to give the agreement a name. *)
let sizes ()
  : Lemma (SHA2.block_len #S32.t == Spec.SHA1.block_len /\
           SHA2.len_len #S32.t == Spec.SHA1.len_len /\
           SHA2.max_input #S32.t == Spec.SHA1.max_input)
  = ()

let pad_zeros_eq (len: nat)
  : Lemma (SHA2.pad_zeros #S32.t len == Spec.SHA1.pad_zeros len)
          [SMTPat (Spec.SHA1.pad_zeros len)]
  = ()

let padding_eq (len: nat { len < Spec.SHA1.max_input })
  : Lemma (SHA2.padding #S32.t len == Spec.SHA1.padding len)
          [SMTPat (Spec.SHA1.padding len)]
  = ()

let padded_eq (msg: Seq.seq S8.t { Seq.length msg < Spec.SHA1.max_input })
  : Lemma (SHA2.padded #S32.t msg == Spec.SHA1.padded msg)
          [SMTPat (Spec.SHA1.padded msg)]
  = ()

let block_at_eq (s: Seq.seq S8.t) (off: nat)
  : Lemma (SHA2.block_at #S32.t s off == Spec.SHA1.block_at s off)
          [SMTPat (Spec.SHA1.block_at s off)]
  = ()
