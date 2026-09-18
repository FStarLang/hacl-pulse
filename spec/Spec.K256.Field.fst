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

(** secp256k1's field prime and group order as two instances of
    {!Spec.Field256}.

    Exactly the shape of {!Spec.P256.Field}, and for the same reason: the
    limb arithmetic does not know or care which 256-bit odd modulus it is
    working over, so a curve contributes two numbers and two [assert_norm]s
    and nothing else.  [mu] is [-m^-1 mod 2^16] and [ri] is [R^-1 mod m];
    neither of K-256's moduli has a [mu] as convenient as P-256's prime. *)
module Spec.K256.Field

include Spec.Field256

open Spec.Bignum256
open Spec.Montgomery256

module K = Spec.K256

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let fmod : modulus =
  assert_norm (K.prime < pow2 256);
  mk K.prime 3525653809
     0xc9bd1905155383999c46c2c295f2b761bcb223fedc24a059d838091d0868192a

let fmod_ok (_: unit) : Lemma (modulus_ok fmod) =
  assert_norm (K.prime < pow2 256);
  assert_norm (1 < K.prime);
  assert_norm (3525653809 < pow2 rad);
  assert_norm (((K.prime % pow2 rad) * 3525653809 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0xc9bd1905155383999c46c2c295f2b761bcb223fedc24a059d838091d0868192a
    % K.prime == 1);
  mk_ok K.prime 3525653809
    0xc9bd1905155383999c46c2c295f2b761bcb223fedc24a059d838091d0868192a

let qmod : modulus =
  assert_norm (K.order < pow2 256);
  mk K.order 1435021631
     0xd9e8890d6494ef93897f30c127cfab5d3bbbd4567fa50c3c80fd22938097c016

let qmod_ok (_: unit) : Lemma (modulus_ok qmod) =
  assert_norm (K.order < pow2 256);
  assert_norm (1 < K.order);
  assert_norm (1435021631 < pow2 rad);
  assert_norm (((K.order % pow2 rad) * 1435021631 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0xd9e8890d6494ef93897f30c127cfab5d3bbbd4567fa50c3c80fd22938097c016
    % K.order == 1);
  mk_ok K.order 1435021631
    0xd9e8890d6494ef93897f30c127cfab5d3bbbd4567fa50c3c80fd22938097c016

#pop-options
