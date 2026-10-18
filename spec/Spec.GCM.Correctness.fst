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

(** Decryption inverts encryption for {!Spec.GCM}, for both key sizes.

    Two forms, matching the two layers of the implementation: on an expanded
    key schedule ([gcm_encrypt_w] / [gcm_decrypt_w], what [encrypt_w] and
    [decrypt_w] are verified against) and on the raw key ([gcm_encrypt] /
    [gcm_decrypt]).  In both, decrypting the ciphertext and tag that
    encryption produced, under the same key, nonce and associated data,
    returns [Some m].  The hypotheses are exactly the refinements the two
    functions carry: a non-empty nonce and the SP 800-38D length limits.

    The tag check succeeds because the tag is recomputed from the same
    inputs.  Recovery is the stream-cipher argument: counter mode xors the
    message with a keystream that depends on the key schedule, the starting
    counter block and the byte index only, so applying it twice from the same
    block xors the same byte in twice and cancels. *)
module Spec.GCM.Correctness

open Spec.Byte
open Spec.AES
open Spec.GCM

module Seq = FStar.Seq
module UInt = FStar.UInt

#push-options "--fuel 0 --ifuel 0"

(** {2 Counter mode is an involution} *)

let xor_twice (a b: elem) : Lemma ((a ^^ b) ^^ b == a)
  = UInt.logxor_associative #8 a b b;
    UInt.logxor_self #8 b;
    UInt.logxor_lemma_1 #8 a

let ctr_encrypt_length (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                       (m: Seq.seq elem)
  : Lemma (Seq.length (ctr_encrypt v w b m) == Seq.length m)
  = ()

let ctr_encrypt_involutive (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                           (m: Seq.seq elem)
  : Lemma (ctr_encrypt v w b (ctr_encrypt v w b m) == m)
  = let c = ctr_encrypt v w b m in
    let aux (i: nat { i < Seq.length m })
      : Lemma (Seq.index (ctr_encrypt v w b c) i == Seq.index m i)
      = xor_twice (Seq.index m i) (ctr_keystream v w b (Seq.length m) i)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (ctr_encrypt v w b c) m;
    Seq.lemma_eq_elim (ctr_encrypt v w b c) m

(** {2 The round trip} *)

(** The ciphertext has the message's length, so it is again an admissible
    input to decryption; the first conjunct is what makes the second
    well-typed. *)
let decrypt_encrypt_w (v: variant) (w: Seq.lseq elem (xkeylen v))
                      (iv: Seq.seq elem { iv_ok iv })
                      (a: Seq.seq elem { aad_ok a })
                      (m: Seq.seq elem { msg_ok m })
  : Lemma (let c = fst (gcm_encrypt_w v w iv a m) in
           let t = snd (gcm_encrypt_w v w iv a m) in
           Seq.length c == Seq.length m /\
           gcm_decrypt_w v w iv a c t == Some m)
  = let jj = j0 v w iv in
    let c = fst (gcm_encrypt_w v w iv a m) in
    ctr_encrypt_length v w (inc32 jj) m;
    ctr_encrypt_involutive v w (inc32 jj) m;
    Seq.lemma_eq_intro (gtag v w jj a c) (gtag v w jj a c)

let decrypt_encrypt (v: variant) (key: Seq.lseq elem (keylen v))
                    (iv: Seq.seq elem { iv_ok iv })
                    (a: Seq.seq elem { aad_ok a })
                    (m: Seq.seq elem { msg_ok m })
  : Lemma (let c = fst (gcm_encrypt v key iv a m) in
           let t = snd (gcm_encrypt v key iv a m) in
           Seq.length c == Seq.length m /\
           gcm_decrypt v key iv a c t == Some m)
  = decrypt_encrypt_w v (key_expansion v key) iv a m

#pop-options
