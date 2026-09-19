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


(** The pure obligations of ML-KEM proper.

    The same two kinds as {!Hacl.Impl.MLKEM.KPKELemmas}, which this module
    extends: reading a concatenation back, and one spelled-out lemma per
    algorithm.  Decapsulation's is the interesting one -- it takes the
    mask the comparison produced and the pointwise result of the
    branch-free selection, and concludes the [if] the specification
    writes. *)
module Hacl.Impl.MLKEM.KEMLemmas

open Spec.MLKEM
open Spec.MLKEM.Params
open Hacl.Impl.MLKEM.KPKELemmas

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

let append4_eq (a b c d res: Seq.seq S8.t)
  : Lemma (requires Seq.length res == Seq.length a + Seq.length b + Seq.length c + Seq.length d /\
                    (forall (t: nat). t < Seq.length a ==> Seq.index res t == Seq.index a t) /\
                    (forall (t: nat). t < Seq.length b ==>
                       Seq.index res (Seq.length a + t) == Seq.index b t) /\
                    (forall (t: nat). t < Seq.length c ==>
                       Seq.index res (Seq.length a + Seq.length b + t) == Seq.index c t) /\
                    (forall (t: nat). t < Seq.length d ==>
                       Seq.index res (Seq.length a + Seq.length b + Seq.length c + t) ==
                         Seq.index d t))
          (ensures res == Seq.append a (Seq.append b (Seq.append c d)))
  = Seq.lemma_eq_intro res (Seq.append a (Seq.append b (Seq.append c d)))

(** Algorithm 16. *)
let kem_keygen_eq (p: params) (d z: Seq.lseq S8.t 32)
                  (vek: Seq.lseq S8.t (ek_len p)) (vdk: Seq.lseq S8.t (dk_len p))
  : Lemma
      (requires
        (let ek, dk_pke = kpke_keygen p d in
         vek == ek /\
         vdk == Seq.append dk_pke (Seq.append ek (Seq.append (hash_h ek) z))))
      (ensures vek == fst (keygen p d z) /\ vdk == snd (keygen p d z))
  = ()

(** Algorithm 17. *)
let encaps_eq (p: params) (ek: Seq.lseq S8.t (ek_len p)) (m: Seq.lseq S8.t 32)
              (vss: Seq.lseq S8.t 32) (vct: Seq.lseq S8.t (ct_len p))
  : Lemma
      (requires
        (let g = hash_g (Seq.append m (hash_h ek)) in
         vss == Seq.slice g 0 32 /\
         vct == kpke_encrypt p ek m (Seq.slice g 32 64)))
      (ensures vss == fst (encaps p ek m) /\ vct == snd (encaps p ek m))
  = ()

(** Algorithm 18.  [kk] is the real key stream, [jj] the rejection value,
    and [mask] the comparison; the implementation only ever has the mask,
    so the selection is stated pointwise. *)
let decaps_eq (p: params) (dk: Seq.lseq S8.t (dk_len p)) (c: Seq.lseq S8.t (ct_len p))
              (mask: S8.t) (kk jj vout: Seq.lseq S8.t 32)
              (c': Seq.lseq S8.t (ct_len p))
  : Lemma
      (requires
        (let dk_pke = Seq.slice dk 0 (dk_pke_len p) in
         let ek = Seq.slice dk (dk_pke_len p) (dk_pke_len p + ek_len p) in
         let h = Seq.slice dk (dk_pke_len p + ek_len p) (dk_pke_len p + ek_len p + 32) in
         let z = Seq.slice dk (dk_pke_len p + ek_len p + 32) (dk_len p) in
         let m = kpke_decrypt p dk_pke c in
         let g = hash_g (Seq.append m h) in
         kk == Seq.slice g 0 32 /\
         c' == kpke_encrypt p ek m (Seq.slice g 32 64) /\
         jj == hash_j (Seq.append z c) /\
         (S8.v mask == 0 \/ S8.v mask == pow2 8 - 1) /\
         (S8.v mask == pow2 8 - 1 <==> c == c') /\
         (forall (t: nat). t < 32 ==>
            Seq.index vout t == (if S8.v mask = 0 then Seq.index jj t else Seq.index kk t))))
      (ensures vout == decaps p dk c)
  = assert_norm (pow2 8 - 1 == 255);
    if S8.v mask = 0
    then begin
      Seq.lemma_eq_intro vout jj;
      assert (~ (Seq.equal c c'))
    end
    else begin
      Seq.lemma_eq_intro vout kk;
      Seq.lemma_eq_elim c c'
    end

#pop-options
