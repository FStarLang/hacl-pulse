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

(** P-384 Diffie--Hellman agrees.

    For private keys [a] and [b] accepted by [validate_private_key], each
    party's [dh_initiator] produces a public key that [validate_public_key]
    accepts ({!dh_initiator_valid}), and each party's [dh_responder] on the
    other's public key returns the encoding of [(a b mod n) G]
    ({!dh_shared_secret}); in particular the two agree and neither is
    [None] ({!dh_agree}).

    The proof is the chain

    [point_mul a Q ~ a Q ~ a (b G) ~ (a b) G ~ (a b mod n) G ~ point_mul_g (a b mod n)]

    of projective equivalences, where [Q] is what [load_point] makes of the
    other party's encoded key ({!Spec.P384.Order.store_load}),
    {!Spec.Group.ECDSA.smul_mul} and {!Spec.Group.ECDSA.smul_mod} are the
    middle steps, and the ends are {!Spec.P384.Smul.point_mul_is_smul}.
    [a b mod n] is not zero because [n] is prime, so the result is not at
    infinity and the responder does not reject it; equivalent finite points
    have the same affine coordinates and hence the same encoding. *)
module Spec.P384.ECDH.Correctness

open Hacl.Spec.Bytes
open Spec.P384
open Spec.P384.Group

module GE = Spec.Group.ECDSA
module SM = Spec.P384.Smul
module O = Spec.P384.Order
module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** An honestly generated public key is valid. *)
let dh_initiator_valid (sk: Seq.lseq S8.t 48)
  : Lemma (requires validate_private_key sk)
          (ensures Some? (dh_initiator sk) /\ validate_public_key (Some?.v (dh_initiator sk)))
  = let k = be_nat sk in
    O.bounds ();
    M.small_mod k order;
    O.point_mul_g_nonzero k;
    O.store_load (point_mul_g k)

(** [a b mod n] is not zero. *)
let prod_nonzero (a b: nat)
  : Lemma (requires 0 < a /\ a < order /\ 0 < b /\ b < order)
          (ensures (a * b) % order <> 0)
  = O.order_is_prime ();
    M.small_mod a order;
    M.small_mod b order;
    if (a * b) % order = 0 then E.euclid_prime order a b

(** The responder's multiple of a loaded point is the multiple of [G] by the
    product, up to [peq]. *)
let responder_peq (a b: nat) (q: proj_point)
  : Lemma (requires 0 < a /\ a < order /\ 0 < b /\ b < order /\
                    on_curve q /\ peq q (point_mul_g b))
          (ensures on_curve (point_mul a q) /\
                   peq (point_mul a q) (point_mul_g ((a * b) % order)))
  = let c = (a * b) % order in
    let pb = point_mul_g b in
    O.bounds ();
    M.small_mod b order;
    prod_nonzero a b;
    M.lemma_mod_twice (a * b) order;
    O.point_mul_g_nonzero b;
    O.point_mul_g_nonzero c;
    g_on_curve ();
    O.g_has_order ();
    SM.point_mul_is_smul a q;
    SM.smul_ok b g;
    SM.smul_ok a q;
    SM.smul_ok a pb;
    SM.smul_ok a (SM.smul b g);
    SM.smul_ok (a * b) g;
    SM.smul_ok c g;
    peq_trans q pb (SM.smul b g);
    SM.smul_congr a q (SM.smul b g);
    GE.smul_mul SM.pg a b g;
    peq_sym (SM.smul (a * b) g) (SM.smul a (SM.smul b g));
    GE.smul_mod SM.pg order (a * b) g;
    peq_trans (point_mul a q) (SM.smul a q) (SM.smul a (SM.smul b g));
    peq_trans (point_mul a q) (SM.smul a (SM.smul b g)) (SM.smul (a * b) g);
    peq_trans (point_mul a q) (SM.smul (a * b) g) (SM.smul c g);
    peq_sym (point_mul_g c) (SM.smul c g);
    peq_trans (point_mul a q) (SM.smul c g) (point_mul_g c)

#push-options "--ifuel 1"

(** The shared secret: the responder's answer to an honestly generated key
    is the encoding of [(a b mod n) G]. *)
let dh_shared_secret (a b: Seq.lseq S8.t 48)
  : Lemma (requires validate_private_key a /\ validate_private_key b)
          (ensures (match dh_initiator b with
                    | Some pb ->
                      dh_responder pb a ==
                      Some (store_point (point_mul_g ((be_nat a * be_nat b) % order)))
                    | None -> False))
  = let ka = be_nat a in
    let kb = be_nat b in
    let c = (ka * kb) % order in
    let p = point_mul_g kb in
    O.bounds ();
    M.small_mod kb order;
    O.point_mul_g_nonzero kb;
    O.store_load p;
    let (x, y) = to_aff_point p in
    let q : proj_point = (x, y, fone) in
    responder_peq ka kb q;
    prod_nonzero ka kb;
    M.lemma_mod_twice (ka * kb) order;
    O.point_mul_g_nonzero c;
    O.smul_g_nonzero c;
    peq_trans (point_mul ka q) (point_mul_g c) (SM.smul c g);
    O.not_inf_of_peq (point_mul ka q) (SM.smul c g);
    peq_to_aff_point (point_mul ka q) (point_mul_g c)

(** ECDH agreement: both parties compute the same shared secret, and
    neither rejects. *)
let dh_agree (a b: Seq.lseq S8.t 48)
  : Lemma (requires validate_private_key a /\ validate_private_key b)
          (ensures (match dh_initiator a, dh_initiator b with
                    | Some pa, Some pb ->
                      Some? (dh_responder pb a) /\ dh_responder pb a == dh_responder pa b
                    | _ -> False))
  = dh_shared_secret a b;
    dh_shared_secret b a;
    M.swap_mul (be_nat a) (be_nat b)

#pop-options
#pop-options
