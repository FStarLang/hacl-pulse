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

(** SHA-3 and SHAKE (FIPS 202).

    Keccak is a sponge, and this specification says so directly: a state is
    twenty-five sixty-four bit lanes, [permute] is Keccak-f[1600], [absorb]
    exclusive-ors the padded message into the state a rate at a time, and
    [squeeze] reads bytes back out, permuting between blocks.

    Two things make this much shorter than [Spec.SHA2]:

    - the lane width is fixed at sixty-four bits, so there is no type class and
      no [params] record -- an algorithm is just a rate and a domain-separation
      byte;
    - there is no length encoding in the padding, so there is no bound on the
      message length and no [max_input] to carry around.

    The state is a sequence of [Hacl.Secret.UInt64.t].  Unlike [Spec.SHA2],
    which speaks in [nat] and is bridged to the implementation by [v], Keccak
    is purely bitwise: every step is an exclusive-or, an and-not or a rotation,
    with no carries, so there is nothing for [nat] arithmetic to say that the
    secret-integer operations do not already say.  Writing the specification
    over the same abstract type the implementation uses therefore loses no
    precision and makes the refinement proof a matter of showing the loops
    build the sequences the specification names. *)
module Spec.SHA3

open Spec.SHA3.Constants

module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Loops = Hacl.Spec.Loops
module Math = FStar.Math.Lemmas


(** {2 The state} *)

(** Twenty-five lanes, indexed [x + 5 * y]: [x] is the column, [y] the row. *)
type state = s: Seq.seq S64.t { Seq.length s == 25 }

let idx (x: nat { x < 5 }) (y: nat { y < 5 }) : n: nat { n < 25 } = x + 5 * y

let get (s: state) (x: nat { x < 5 }) (y: nat { y < 5 }) : S64.t = Seq.index s (idx x y)

let zero_state : state = Seq.create 25 S64.zero


(** {2 Bit plumbing}

    [rotl] and the shifts take the offset as a [nat] and fall back to the
    identity at zero, because [Hacl.Secret.UInt64.rotate_left] insists on a
    nonzero offset and [rho] has one zero offset. *)

let rotl (x: S64.t) (k: nat { k < 64 }) : S64.t =
  if k = 0 then x else S64.rotate_left x (U32.uint_to_t k)

let shiftl (x: S64.t) (k: nat { k < 64 }) : S64.t =
  if k = 0 then x else S64.shift_left x (U32.uint_to_t k)

let shiftr (x: S64.t) (k: nat { k < 64 }) : S64.t =
  if k = 0 then x else S64.shift_right x (U32.uint_to_t k)


(** {2 Keccak-f[1600]} *)

(** theta.  [c x] is the parity of column [x]; [d x] is what gets folded back
    into every lane of that column. *)

[@@"opaque_to_smt"]
let theta_c (s: state) (x: nat { x < 5 }) : S64.t =
  S64.logxor (S64.logxor (S64.logxor (S64.logxor (get s x 0) (get s x 1)) (get s x 2))
                         (get s x 3))
             (get s x 4)

let theta_d (s: state) (x: nat { x < 5 }) : S64.t =
  S64.logxor (theta_c s ((x + 4) % 5)) (rotl (theta_c s ((x + 1) % 5)) 1)

[@@"opaque_to_smt"]
let theta (s: state) : state =
  Seq.init 25 (fun i -> S64.logxor (Seq.index s i) (theta_d s (i % 5)))

(** rho and pi together.  pi sends lane [(x, y)] to lane [(y, (2x + 3y) mod
    5)]; read backwards, the lane that ends up at [(x', y')] started at
    [x = (x' + 3 y') mod 5], [y = x']. *)

let rho_pi_src (i: nat { i < 25 }) : n: nat { n < 25 } =
  let x' = i % 5 in
  let y' = i / 5 in
  idx ((x' + 3 * y') % 5) x'

[@@"opaque_to_smt"]
let rho_pi (s: state) : state =
  Seq.init 25 (fun i ->
    let j = rho_pi_src i in
    rotl (Seq.index s j) (rotc j))

(** chi, the only nonlinear step. *)

[@@"opaque_to_smt"]
let chi (s: state) : state =
  Seq.init 25 (fun i ->
    let x = i % 5 in
    let y = i / 5 in
    assert_norm (pow2 5 == 32);
    Math.lemma_div_lt_nat i 5 1;
    S64.logxor (get s x y)
               (S64.logand (S64.lognot (get s ((x + 1) % 5) y))
                           (get s ((x + 2) % 5) y)))

(** iota, which breaks the symmetry between the rounds. *)

let iota (i: nat { i < 24 }) (s: state) : state =
  Seq.upd s 0 (S64.logxor (Seq.index s 0) (Seq.index rc i))

let round (i: nat) (s: state) : state =
  if i < 24 then iota i (chi (rho_pi (theta s))) else s

let permute (s: state) : state = Loops.repeati 24 round s


(** {2 Lanes and bytes}

    Keccak is little-endian, so lane [j] of the state is bytes [8j] through
    [8j + 7] of the block, least significant first. *)

let lane_of_step (b: Seq.seq S8.t) (j: nat) (acc: S64.t) : S64.t =
  if j < 8 && j < Seq.length b
  then S64.logor acc (shiftl (Cast.u8_to_u64 (Seq.index b j)) (8 * j))
  else acc

let lane_of (b: Seq.lseq S8.t 8) : S64.t = Loops.repeati 8 (lane_of_step b) S64.zero

let lane_byte (x: S64.t) (k: nat { k < 8 }) : S8.t = Cast.u64_to_u8 (shiftr x (8 * k))


(** {2 The sponge}

    A rate is a whole number of lanes and leaves at least one lane of capacity;
    that covers every rate FIPS 202 defines (72, 104, 136, 144 and 168). *)

let rate_t = r: nat { r % 8 == 0 /\ 0 < r /\ r < 200 }

let rate_lanes (r: rate_t) : n: nat { 0 < n /\ n < 25 } = r / 8

(** The [i]th byte of [s], read out at rate [r]. *)
let state_byte (s: state) (i: nat { i < 200 }) : S8.t =
  assert_norm (pow2 8 == 256);
  Math.pow2_le_compat 200 8;
  Math.lemma_div_lt_nat i 200 3;
  lane_byte (Seq.index s (i / 8)) (i % 8)

(** Exclusive-or one rate-sized block into the state, then permute. *)

let xor_block (r: rate_t) (block: Seq.lseq S8.t r) (s: state) : state =
  Seq.init 25 (fun i ->
    if i < rate_lanes r
    then S64.logxor (Seq.index s i) (lane_of (Seq.slice block (8 * i) (8 * i + 8)))
    else Seq.index s i)

let absorb_block (r: rate_t) (block: Seq.lseq S8.t r) (s: state) : state =
  permute (xor_block r block s)


(** {2 Padding}

    pad10*1, with the domain-separation bits of FIPS 202 §6.1 folded into the
    first byte: [0x06] for SHA-3 and [0x1f] for SHAKE.  The two bits can land
    in the same byte when only one byte of room is left, which is why the byte
    is built as an [or] of two independent contributions rather than by cases. *)

let pad_len (r: rate_t) (n: nat) : k: pos { (n + k) % r == 0 } =
  Math.lemma_mod_lt n r;
  Math.euclidean_division_definition n r;
  Math.distributivity_add_left (n / r) 1 r;
  Math.multiple_modulo_lemma (n / r + 1) r;
  r - n % r

let pad_byte (suffix: U8.t) (k: pos) (i: nat { i < k }) : S8.t =
  let a = if i = 0 then suffix else 0uy in
  let b = if i = k - 1 then 0x80uy else 0uy in
  S8.classify (U8.logor a b)

let padding (r: rate_t) (suffix: U8.t) (n: nat) : Seq.lseq S8.t (pad_len r n) =
  Seq.init (pad_len r n) (pad_byte suffix (pad_len r n))

let padded (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t) : Seq.seq S8.t =
  Seq.append msg (padding r suffix (Seq.length msg))

let padded_len (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t)
  : Lemma (Seq.length (padded r suffix msg) ==
           Seq.length msg + pad_len r (Seq.length msg) /\
           Seq.length (padded r suffix msg) % r == 0)
  = Seq.lemma_len_append msg (padding r suffix (Seq.length msg))

let nblocks (r: rate_t) (msg: Seq.seq S8.t) : pos =
  padded_len r 0uy msg;
  (Seq.length msg + pad_len r (Seq.length msg)) / r


(** {2 Absorbing} *)

(** Block [i] of a byte sequence at rate [r].  Outside the sequence the block
    is zero, which never happens for [i < nblocks]. *)
let block_at (r: rate_t) (s: Seq.seq S8.t) (i: nat) : Seq.lseq S8.t r =
  Seq.init r (fun k -> if i * r + k < Seq.length s
                    then Seq.index s (i * r + k)
                    else S8.classify 0uy)

let absorb_step (r: rate_t) (s: Seq.seq S8.t) (i: nat) (st: state) : state =
  absorb_block r (block_at r s i) st

let absorb (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t) : state =
  Loops.repeati (nblocks r msg) (absorb_step r (padded r suffix msg)) zero_state


(** {2 Squeezing}

    Byte [i] of the output comes from block [i / r] of the squeeze, which is
    the state permuted [i / r] more times. *)

let squeeze_state (j: nat) (s: state) : state =
  Loops.repeati j (fun _ st -> permute st) s

let squeeze (r: rate_t) (s: state) (outlen: nat) : Seq.lseq S8.t outlen =
  Seq.init outlen (fun i ->
    Math.lemma_mod_lt i r;
    state_byte (squeeze_state (i / r) s) (i % r))


(** {2 The named algorithms} *)

let keccak (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t) (outlen: nat)
  : Seq.lseq S8.t outlen
  = squeeze r (absorb r suffix msg) outlen

unfold let sha3_suffix : U8.t = 0x06uy
unfold let shake_suffix : U8.t = 0x1fuy

let sha3_224 (msg: Seq.seq S8.t) : Seq.lseq S8.t 28 = keccak 144 sha3_suffix msg 28
let sha3_256 (msg: Seq.seq S8.t) : Seq.lseq S8.t 32 = keccak 136 sha3_suffix msg 32
let sha3_384 (msg: Seq.seq S8.t) : Seq.lseq S8.t 48 = keccak 104 sha3_suffix msg 48
let sha3_512 (msg: Seq.seq S8.t) : Seq.lseq S8.t 64 = keccak  72 sha3_suffix msg 64

let shake128 (msg: Seq.seq S8.t) (outlen: nat) : Seq.lseq S8.t outlen =
  keccak 168 shake_suffix msg outlen
let shake256 (msg: Seq.seq S8.t) (outlen: nat) : Seq.lseq S8.t outlen =
  keccak 136 shake_suffix msg outlen


(** {2 Index lemmas}

    Everything above is defined with [Seq.init], and [Seq.init_index_] needs
    the contents function written out.  These lemmas do that once, so that the
    implementation can talk about one entry at a time. *)

let theta_index (s: state) (i: nat { i < 25 })
  : Lemma (Seq.index (theta s) i == S64.logxor (Seq.index s i) (theta_d s (i % 5)))
  = reveal_opaque (`%theta) theta;
    Seq.init_index_ 25 (fun j -> S64.logxor (Seq.index s j) (theta_d s (j % 5))) i

(** [theta_c] spelled out with flat indices. *)
let theta_c_eq (s: state) (x: nat { x < 5 })
  : Lemma (theta_c s x ==
           S64.logxor (S64.logxor (S64.logxor (S64.logxor
             (Seq.index s x) (Seq.index s (x + 5))) (Seq.index s (x + 10)))
             (Seq.index s (x + 15))) (Seq.index s (x + 20)))
  = reveal_opaque (`%theta_c) theta_c

(** The whole of one theta lane in terms of the parity buffer, so that the
    implementation never has to unfold [theta_c] inside a Pulse context. *)
let theta_step (s: state) (cs: Seq.seq S64.t) (i: nat { i < 25 })
  : Lemma (requires Seq.length cs == 5 /\
                    (forall (x: nat). x < 5 ==> Seq.index cs x == theta_c s x))
          (ensures Seq.index (theta s) i ==
                   S64.logxor (Seq.index s i)
                     (S64.logxor (Seq.index cs ((i % 5 + 4) % 5))
                                 (rotl (Seq.index cs ((i % 5 + 1) % 5)) 1)))
  = reveal_opaque (`%theta_c) theta_c;
    theta_index s i

let rho_pi_index (s: state) (i: nat { i < 25 })
  : Lemma (Seq.index (rho_pi s) i ==
           rotl (Seq.index s (rho_pi_src i)) (rotc (rho_pi_src i)))
  = reveal_opaque (`%rho_pi) rho_pi;
    Seq.init_index_ 25 (fun j ->
      let k = rho_pi_src j in
      rotl (Seq.index s k) (rotc k)) i

let chi_index (s: state) (i: nat { i < 25 })
  : Lemma (Seq.index (chi s) i ==
           S64.logxor (Seq.index s i)
             (S64.logand (S64.lognot (Seq.index s (idx ((i % 5 + 1) % 5) (i / 5))))
                         (Seq.index s (idx ((i % 5 + 2) % 5) (i / 5)))))
  = reveal_opaque (`%chi) chi;
    assert_norm (pow2 5 == 32);
    Math.lemma_div_lt_nat i 5 1;
    Math.euclidean_division_definition i 5;
    assert (idx (i % 5) (i / 5) == i);
    Seq.init_index_ 25 (fun j ->
      let x = j % 5 in
      let y = j / 5 in
      assert_norm (pow2 5 == 32);
      Math.lemma_div_lt_nat j 5 1;
      S64.logxor (get s x y)
                 (S64.logand (S64.lognot (get s ((x + 1) % 5) y))
                             (get s ((x + 2) % 5) y))) i

let xor_block_index (r: rate_t) (block: Seq.lseq S8.t r) (s: state) (i: nat { i < 25 })
  : Lemma (Seq.index (xor_block r block s) i ==
           (if i < rate_lanes r
            then S64.logxor (Seq.index s i) (lane_of (Seq.slice block (8 * i) (8 * i + 8)))
            else Seq.index s i))
  = Seq.init_index_ 25 (fun j ->
      if j < rate_lanes r
      then S64.logxor (Seq.index s j) (lane_of (Seq.slice block (8 * j) (8 * j + 8)))
      else Seq.index s j) i

let block_at_index (r: rate_t) (s: Seq.seq S8.t) (i: nat) (k: nat { k < r })
  : Lemma (Seq.index (block_at r s i) k ==
           (if i * r + k < Seq.length s then Seq.index s (i * r + k) else S8.classify 0uy))
  = Seq.init_index_ r (fun j -> if i * r + j < Seq.length s
                             then Seq.index s (i * r + j)
                             else S8.classify 0uy) k

let padding_index (r: rate_t) (suffix: U8.t) (n: nat) (i: nat { i < pad_len r n })
  : Lemma (Seq.index (padding r suffix n) i == pad_byte suffix (pad_len r n) i)
  = Seq.init_index_ (pad_len r n) (pad_byte suffix (pad_len r n)) i

let squeeze_index (r: rate_t) (s: state) (outlen: nat) (i: nat { i < outlen })
  : Lemma (Seq.index (squeeze r s outlen) i ==
           state_byte (squeeze_state (i / r) s) (i % r))
  = Seq.init_index_ outlen (fun j ->
      Math.lemma_mod_lt j r;
      state_byte (squeeze_state (j / r) s) (j % r)) i

(** [padded] is [msg] then the padding, spelled out one byte at a time. *)
let padded_index (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t)
                 (i: nat { i < Seq.length msg + pad_len r (Seq.length msg) })
  : Lemma (padded_len r suffix msg;
           Seq.index (padded r suffix msg) i ==
           (if i < Seq.length msg then Seq.index msg i
            else pad_byte suffix (pad_len r (Seq.length msg)) (i - Seq.length msg)))
  = padded_len r suffix msg;
    let p = padding r suffix (Seq.length msg) in
    if i < Seq.length msg
    then Seq.lemma_index_app1 msg p i
    else (Seq.lemma_index_app2 msg p i;
          padding_index r suffix (Seq.length msg) (i - Seq.length msg))

(** The number of blocks is one more than the number of whole message blocks:
    the padding is never empty, and never spills into a second block. *)
let nblocks_eq (r: rate_t) (msg: Seq.seq S8.t)
  : Lemma (nblocks r msg == Seq.length msg / r + 1)
  = let n = Seq.length msg in
    Math.lemma_mod_lt n r;
    Math.euclidean_division_definition n r;
    Math.distributivity_add_left (n / r) 1 r;
    Math.multiple_division_lemma (n / r + 1) r

(** {2 Blocks of the padded message}

    The implementation absorbs whole message blocks straight out of the
    caller's buffer and builds only the last block, so it needs to know that
    block [i] of [padded] is a slice of [msg] for every [i] but the last, and
    what the last one contains. *)

let block_at_full (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires i * r + r <= Seq.length msg)
          (ensures block_at r (padded r suffix msg) i ==
                   Seq.slice msg (i * r) (i * r + r))
  = padded_len r suffix msg;
    let p = padded r suffix msg in
    let aux (k: nat { k < r }) : Lemma
      (Seq.index (block_at r p i) k == Seq.index (Seq.slice msg (i * r) (i * r + r)) k)
      = block_at_index r p i k;
        padded_index r suffix msg (i * r + k)
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (block_at r p i) (Seq.slice msg (i * r) (i * r + r))

let block_at_last_byte (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t) (blk: Seq.seq S8.t)
                       (k: nat { k < r })
  : Lemma (requires (let n = Seq.length msg in
                     Seq.length blk == r /\
                     (k < n % r ==> Seq.index blk k == Seq.index msg (n - n % r + k)) /\
                     (n % r <= k ==> Seq.index blk k == pad_byte suffix (r - n % r) (k - n % r))))
          (ensures (Math.nat_over_pos_is_nat (Seq.length msg) r;
                    Seq.index (block_at r (padded r suffix msg) (Seq.length msg / r)) k ==
                    Seq.index blk k))
  = padded_len r suffix msg;
    let n = Seq.length msg in
    Math.nat_over_pos_is_nat n r;
    let q = n / r in
    let m = n % r in
    Math.euclidean_division_definition n r;
    assert (pad_len r n == r - m);
    assert (q * r + k - n == k - m);
    block_at_index r (padded r suffix msg) q k;
    padded_index r suffix msg (q * r + k)

let block_at_last (r: rate_t) (suffix: U8.t) (msg: Seq.seq S8.t) (blk: Seq.seq S8.t)
  : Lemma (requires (let n = Seq.length msg in
                     Seq.length blk == r /\
                     (forall (k: nat). k < n % r ==>
                        Seq.index blk k == Seq.index msg (n - n % r + k)) /\
                     (forall (k: nat). n % r <= k /\ k < r ==>
                        Seq.index blk k == pad_byte suffix (r - n % r) (k - n % r))))
          (ensures (Math.nat_over_pos_is_nat (Seq.length msg) r;
                    block_at r (padded r suffix msg) (Seq.length msg / r) == blk))
  = padded_len r suffix msg;
    let n = Seq.length msg in
    Math.nat_over_pos_is_nat n r;
    let q = n / r in
    let m = n % r in
    Math.euclidean_division_definition n r;
    let p = padded r suffix msg in
    let aux (k: nat { k < r }) : Lemma (Seq.index (block_at r p q) k == Seq.index blk k)
      = block_at_last_byte r suffix msg blk k
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (block_at r p q) blk

(** {2 Squeezing one block at a time} *)

let squeeze_byte_eq (r: rate_t) (s: state) (outlen: nat) (j: nat) (u: nat)
  : Lemma (requires u < r /\ j * r + u < outlen)
          (ensures Seq.index (squeeze r s outlen) (j * r + u) ==
                   state_byte (squeeze_state j s) u)
  = Math.lemma_div_plus u j r;
    Math.lemma_mod_plus u j r;
    Math.small_div u r;
    Math.small_mod u r;
    squeeze_index r s outlen (j * r + u)

let squeeze_bytes_eq (r: rate_t) (s: state) (outlen: nat) (j: nat) (cnt: nat)
  : Lemma (requires cnt <= r /\ j * r + cnt <= outlen)
          (ensures forall (u: nat). u < cnt ==>
                     Seq.index (squeeze r s outlen) (j * r + u) ==
                     state_byte (squeeze_state j s) u)
  = let aux (u: nat { u < cnt }) : Lemma
      (Seq.index (squeeze r s outlen) (j * r + u) == state_byte (squeeze_state j s) u)
      = squeeze_byte_eq r s outlen j u
    in
    Classical.forall_intro aux

let squeeze_byte_eq_abs (r: rate_t) (s: state) (outlen: nat) (j: nat) (base: nat) (k: nat)
  : Lemma (requires j * r == base /\ base <= k /\ k < base + r /\ k < outlen)
          (ensures Seq.index (squeeze r s outlen) k ==
                   state_byte (squeeze_state j s) (k - base))
  = assert (j * r + (k - base) == k);
    squeeze_byte_eq r s outlen j (k - base)

(** The same, indexed absolutely, which is the shape the implementation's
    output buffer invariant has. *)
let squeeze_range_eq (r: rate_t) (s: state) (outlen: nat) (base: nat) (cnt: nat)
  : Lemma (requires base % r == 0 /\ cnt <= r /\ base + cnt <= outlen)
          (ensures forall (k: nat). base <= k /\ k < base + cnt ==>
                     Seq.index (squeeze r s outlen) k ==
                     state_byte (squeeze_state (base / r) s) (k - base))
  = Math.euclidean_division_definition base r;
    let j = base / r in
    let aux (k: nat { base <= k /\ k < base + cnt })
      : Lemma (Seq.index (squeeze r s outlen) k ==
               state_byte (squeeze_state j s) (k - base))
      = squeeze_byte_eq_abs r s outlen j base k
    in
    Classical.forall_intro aux
