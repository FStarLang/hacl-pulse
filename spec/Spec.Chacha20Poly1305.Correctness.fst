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

(** Decryption inverts encryption for {!Spec.Chacha20Poly1305}.

    The statement is in terms of the two halves the specification splits
    decryption into, because those are what the implementation's [decrypt]
    reports: the tag of [encrypt k n aad m] is accepted by [decrypt_ok], and
    [decrypted] gives back [m].  There is no side condition beyond the one
    [encrypt] itself imposes on the message length.

    Acceptance holds by definition -- the tag is recomputed from the same
    inputs.  Recovery is the usual stream-cipher argument: the ciphertext is
    the message xored with the keystream from counter one, and xoring the
    same keystream a second time cancels it, byte by byte.  {!logxor_twice}
    is that one byte; it is stated for any two secret bytes so that the other
    stream-cipher constructions can use it too. *)
module Spec.Chacha20Poly1305.Correctness

open Spec.Chacha20Poly1305

module Seq = FStar.Seq
module UInt = FStar.UInt
module S8 = Hacl.Secret.UInt8
module C = Spec.Chacha20

#push-options "--fuel 0 --ifuel 0"

(** {2 Xor twice} *)

let logxor_twice (x y: S8.t)
  : Lemma (S8.logxor (S8.logxor x y) y == x)
  = UInt.logxor_associative #8 (S8.v x) (S8.v y) (S8.v y);
    UInt.logxor_self #8 (S8.v y);
    UInt.logxor_lemma_1 #8 (S8.v x);
    S8.v_extensional (S8.logxor (S8.logxor x y) y) x

(** ChaCha20 from a fixed counter is an involution. *)
let chacha20_involutive (k: C.key) (n: C.nonce) (ctr0: FStar.UInt32.t)
                        (m: Seq.seq S8.t { Seq.length m <= C.max_len ctr0 })
  : Lemma (C.chacha20 k n ctr0 (C.chacha20 k n ctr0 m) == m)
  = let c = C.chacha20 k n ctr0 m in
    let aux (i: nat { i < Seq.length m })
      : Lemma (Seq.index (C.chacha20 k n ctr0 c) i == Seq.index m i)
      = C.div_lt C.size_block i (pow2 32 - FStar.UInt32.v ctr0);
        logxor_twice (Seq.index m i) (C.ks_byte (C.init k n ctr0) ctr0 i)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (C.chacha20 k n ctr0 c) m;
    Seq.lemma_eq_elim (C.chacha20 k n ctr0 c) m

(** {2 The round trip} *)

let decrypt_encrypt (k: C.key) (n: C.nonce) (aad: Seq.seq S8.t)
                    (m: Seq.seq S8.t { Seq.length m <= C.max_len 1ul })
  : Lemma (let ct = fst (encrypt k n aad m) in
           let tag = snd (encrypt k n aad m) in
           decrypt_ok k n aad ct tag /\ decrypted k n ct == m)
  = chacha20_involutive k n 1ul m

#pop-options
