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

(** The number-theoretic transform.

    FIPS 203 writes the transform as the textbook in-place butterfly
    network: two nested loops, the outer one walking blocks and the inner
    one walking a block's butterflies, each iteration writing the two
    coefficients it has just read.  That is not what happens here.

    The specification's layers are {i pointwise}: [ntt_layer_at e f t]
    says what coefficient [t] of the output is as a function of the whole
    input, with no reference to the order the coefficients are produced in.
    Implementing that shape directly -- one flat loop over [t], reading the
    previous layer and writing the next -- turns the loop invariant into
    "the first [t] coefficients are already right", which is the invariant
    a pointwise specification wants and nothing more.  The price is a
    second 512-byte buffer, and the two are used alternately so that no
    layer ever copies: seven layers is an odd number, so the result lands
    in the scratch buffer and one copy at the end puts it back.

    Within a layer the loop still has to know which butterfly coefficient
    [t] belongs to, and the standard's [t / 2len] and [(t / len) mod 2] are
    divisions by a quantity that is not a compile-time constant.  Rather
    than emit them, the loop carries the block index [b] and the offset [c]
    within the block and steps them, which is a comparison and an
    increment; {!layer_split} is what says that this is the same thing. *)
module Hacl.Impl.MLKEM.NTT

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq
open Hacl.MLKEM.Tables

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S16 = Hacl.Secret.UInt16
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module T = Hacl.Impl.Table
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** Carrying [(b, c)] with [t = b * 2len + c] is the same as dividing:
    [b] is the block [t] falls in, and [c < len] is exactly the test for
    being in the lower half of the butterfly. *)
let layer_split (e: nat { 1 <= e /\ e <= 7 }) (b c: nat)
  : Lemma (requires c < pow2 (e + 1) /\ b * pow2 (e + 1) + c < n)
          (ensures (let t = b * pow2 (e + 1) + c in
                    b < pow2 (7 - e) /\
                    zidx e t == pow2 (7 - e) + b /\
                    zidx_inv e t == 2 * pow2 (7 - e) - 1 - b /\
                    (((t / pow2 e) % 2 == 0) <==> c < pow2 e)))
  = let p = pow2 e in
    let d = pow2 (e + 1) in
    let t = b * d + c in
    Math.pow2_plus 1 e;
    assert_norm (pow2 1 == 2);
    assert (d == 2 * p);
    Math.lemma_div_plus c b d;
    Math.small_div c d;
    assert (t / d == b);
    assert_norm (n == pow2 8);
    Math.pow2_plus (7 - e) (e + 1);
    div_lt t (pow2 (7 - e)) d;
    Math.pow2_plus 1 (7 - e);
    Math.lemma_div_plus c (2 * b) p;
    assert (t / p == c / p + 2 * b);
    Math.lemma_mod_plus (c / p) b 2;
    assert ((t / p) % 2 == (c / p) % 2);
    if c < p then Math.small_div c p
    else begin
      Math.lemma_div_le p c p;
      Math.lemma_div_lt_nat c (e + 1) e;
      Math.small_div (c / p) 2
    end

(** {2 One layer}

    [dst <- ntt_layer e src].  [len] is [2^e] and [half] is [2^(7-e)], the
    number of roots the earlier layers have consumed; both are constants at
    every call site. *)

(** One butterfly.

    It is a function of its own rather than the body of the loop because
    the two arms write different things, and an [if] whose arms leave the
    heap in differently-shaped states is not something Pulse can join on
    its own; giving the [if] a name gives it a postcondition to be joined
    against.  [lower] says which arm of the butterfly [i] is, which the
    caller knows without dividing. *)
inline_for_extraction
fn ntt_butterfly (dst src zt: A.array zqt) (i len zi: SZ.t) (lower: bool)
                 (#e: erased nat) (#p #pz: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs ** A.pts_to zt #pz zeta_table **
         pure (1 <= reveal e /\ reveal e <= 7 /\ SZ.v len == pow2 (reveal e) /\
               SZ.v i < n /\ SZ.v zi == zidx (reveal e) (SZ.v i) /\
               (lower <==> (SZ.v i / pow2 (reveal e)) % 2 == 0) /\
               Seq.length vd == n /\ Seq.length vs == n /\
               (forall (k: nat). k < SZ.v i ==>
                  S16.v (Seq.index vd k) ==
                    Seq.index (ntt_layer (reveal e) (as_poly vs)) k))
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs ** A.pts_to zt #pz zeta_table **
        pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\
              SZ.v i < n /\ Seq.length v == n /\
              (forall (k: nat). k < SZ.v i + 1 ==>
                 S16.v (Seq.index v k) ==
                   Seq.index (ntt_layer (reveal e) (as_poly vs)) k))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  ntt_layer_index (reveal e) (as_poly vs) (SZ.v i);
  let z = A.(zt.(zi));
  if lower {
    even_step (reveal e) (SZ.v i);
    SZ.fits_u32_implies_fits (SZ.v i + SZ.v len);
    let x = A.(src.(i));
    let y = A.(src.(SZ.add i len));
    A.((dst.(i) <- zq_add x (zq_mul z y)));
  } else {
    odd_step (reveal e) (SZ.v i);
    let x = A.(src.(SZ.sub i len));
    let y = A.(src.(i));
    A.((dst.(i) <- zq_sub x (zq_mul z y)));
  }
}

(** The Gentleman-Sande butterfly: the root multiplies after the
    subtraction rather than before it, which is what makes the two layers
    mutually inverse rather than merely similar. *)
inline_for_extraction
fn intt_butterfly (dst src zt: A.array zqt) (i len zi: SZ.t) (lower: bool)
                  (#e: erased nat) (#p #pz: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs ** A.pts_to zt #pz zeta_table **
         pure (1 <= reveal e /\ reveal e <= 7 /\ SZ.v len == pow2 (reveal e) /\
               SZ.v i < n /\ SZ.v zi == zidx_inv (reveal e) (SZ.v i) /\
               (lower <==> (SZ.v i / pow2 (reveal e)) % 2 == 0) /\
               Seq.length vd == n /\ Seq.length vs == n /\
               (forall (k: nat). k < SZ.v i ==>
                  S16.v (Seq.index vd k) ==
                    Seq.index (intt_layer (reveal e) (as_poly vs)) k))
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs ** A.pts_to zt #pz zeta_table **
        pure (1 <= reveal e /\ reveal e <= 7 /\ Seq.length vs == n /\
              SZ.v i < n /\ Seq.length v == n /\
              (forall (k: nat). k < SZ.v i + 1 ==>
                 S16.v (Seq.index v k) ==
                   Seq.index (intt_layer (reveal e) (as_poly vs)) k))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  intt_layer_index (reveal e) (as_poly vs) (SZ.v i);
  let z = A.(zt.(zi));
  if lower {
    even_step (reveal e) (SZ.v i);
    SZ.fits_u32_implies_fits (SZ.v i + SZ.v len);
    let x = A.(src.(i));
    let y = A.(src.(SZ.add i len));
    A.((dst.(i) <- zq_add x y));
  } else {
    odd_step (reveal e) (SZ.v i);
    let x = A.(src.(SZ.sub i len));
    let y = A.(src.(i));
    A.((dst.(i) <- zq_mul z (zq_sub y x)));
  }
}

inline_for_extraction
fn ntt_layer_impl (dst src: A.array zqt) (len half: SZ.t)
         (#e: erased nat) (#p: perm)
         (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (1 <= reveal e /\ reveal e <= 7 /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vd == n /\ Seq.length vs == n)
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs **
        pure (1 <= reveal e /\ reveal e <= 7 /\
              Seq.length v == n /\ Seq.length vs == n /\
              as_poly v == ntt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let zt = T.table zeta_arr 128sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  HSZ.fits32 ();
  Math.pow2_le_compat 7 (reveal e);
  Math.pow2_le_compat 7 (7 - reveal e);
  assert_norm (pow2 7 == 128);
  SZ.fits_u32_implies_fits (SZ.v len + SZ.v len);
  let dbl = SZ.add len len;
  Math.pow2_double_sum (reveal e);
  assert (pure (SZ.v dbl == pow2 (reveal e + 1)));
  let mut i = 0sz;
  let mut b = 0sz;
  let mut c = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi vb vc: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** pts_to b vb ** pts_to c vc **
    A.pts_to dst v ** A.pts_to src #p vs ** A.pts_to zt #pz zeta_table **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          SZ.v vi == SZ.v vb * pow2 (reveal e + 1) + SZ.v vc /\
          SZ.v vc < pow2 (reveal e + 1) /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) ==
               Seq.index (ntt_layer (reveal e) (as_poly vs)) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let vb = !b;
    let vc = !c;
    layer_split (reveal e) (SZ.v vb) (SZ.v vc);
    ntt_butterfly dst src zt vi len (SZ.add half vb) (SZ.lt vc len) #e;
    Math.pow2_le_compat 8 (reveal e + 1);
    Math.pow2_plus 1 (reveal e);
    assert_norm (pow2 1 == 2);
    Math.distributivity_add_left (SZ.v vb) 1 (pow2 (reveal e + 1));
    assert_norm (pow2 8 == 256);
    assert_norm (256 < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v vc + 1);
    SZ.fits_u32_implies_fits (SZ.v vb + 1);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let nc = SZ.add vc 1sz;
    assert (pure (SZ.v nc == SZ.v vc + 1 /\ SZ.v dbl == pow2 (reveal e + 1)));
    (* Name the comparison and restate its defining property, so that the
       join after the branch reasons about a variable rather than about an
       unreduced [match] on a machine-integer comparison. *)
    let wrap = SZ.eq nc dbl;
    assert (pure (wrap == (SZ.v nc = SZ.v dbl)));
    if wrap {
      assert (pure (SZ.v nc == SZ.v dbl));
      b := SZ.add vb 1sz;
      c := 0sz;
      assert (pure (SZ.v vi + 1 == (SZ.v vb + 1) * pow2 (reveal e + 1) + 0 /\
                    0 < pow2 (reveal e + 1)));
    } else {
      assert (pure (SZ.v nc <> SZ.v dbl));
      assert (pure (SZ.v nc <= SZ.v dbl));
      assert (pure (SZ.v nc < SZ.v dbl));
      c := nc;
      assert (pure (SZ.v vi + 1 == SZ.v vb * pow2 (reveal e + 1) + SZ.v nc));
      assert (pure (SZ.v nc < pow2 (reveal e + 1)));
    };
    i := SZ.add vi 1sz;
  };
  T.drop_table zt;
  with v. assert (A.pts_to dst v);
  assert (pure (forall (k: nat). k < n ==>
                  S16.v (Seq.index v k) ==
                    Seq.index (ntt_layer (reveal e) (as_poly vs)) k));
  as_poly_intro v (ntt_layer (reveal e) (as_poly vs));
  assert (pure (as_poly v == ntt_layer (reveal e) (as_poly vs)));
}

(** The Gentleman-Sande layer: the roots are read from the far end of the
    table and the multiplication happens after the subtraction rather than
    before it, which is what makes the two mutually inverse. *)
inline_for_extraction
fn intt_layer_impl (dst src: A.array zqt) (len half: SZ.t)
         (#e: erased nat) (#p: perm)
         (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (1 <= reveal e /\ reveal e <= 7 /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vd == n /\ Seq.length vs == n)
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs **
        pure (1 <= reveal e /\ reveal e <= 7 /\
              Seq.length v == n /\ Seq.length vs == n /\
              as_poly v == intt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let zt = T.table zeta_arr 128sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  HSZ.fits32 ();
  Math.pow2_le_compat 7 (reveal e);
  Math.pow2_le_compat 7 (7 - reveal e);
  assert_norm (pow2 7 == 128);
  SZ.fits_u32_implies_fits (SZ.v len + SZ.v len);
  SZ.fits_u32_implies_fits (SZ.v half + SZ.v half);
  let dbl = SZ.add len len;
  Math.pow2_double_sum (reveal e);
  assert (pure (SZ.v dbl == pow2 (reveal e + 1)));
  let top = SZ.sub (SZ.add half half) 1sz;
  let mut i = 0sz;
  let mut b = 0sz;
  let mut c = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi vb vc: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** pts_to b vb ** pts_to c vc **
    A.pts_to dst v ** A.pts_to src #p vs ** A.pts_to zt #pz zeta_table **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          SZ.v vi == SZ.v vb * pow2 (reveal e + 1) + SZ.v vc /\
          SZ.v vc < pow2 (reveal e + 1) /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) ==
               Seq.index (intt_layer (reveal e) (as_poly vs)) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let vb = !b;
    let vc = !c;
    layer_split (reveal e) (SZ.v vb) (SZ.v vc);
    intt_butterfly dst src zt vi len (SZ.sub top vb) (SZ.lt vc len) #e;
    Math.pow2_le_compat 8 (reveal e + 1);
    Math.pow2_plus 1 (reveal e);
    assert_norm (pow2 1 == 2);
    Math.distributivity_add_left (SZ.v vb) 1 (pow2 (reveal e + 1));
    assert_norm (pow2 8 == 256);
    assert_norm (256 < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v vc + 1);
    SZ.fits_u32_implies_fits (SZ.v vb + 1);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let nc = SZ.add vc 1sz;
    assert (pure (SZ.v nc == SZ.v vc + 1 /\ SZ.v dbl == pow2 (reveal e + 1)));
    (* As in [ntt_layer_impl], spell out each branch. *)
    if (SZ.eq nc dbl) {
      assert (pure (SZ.v nc == SZ.v dbl));
      b := SZ.add vb 1sz;
      c := 0sz;
      assert (pure (SZ.v vi + 1 == (SZ.v vb + 1) * pow2 (reveal e + 1) + 0 /\
                    0 < pow2 (reveal e + 1)));
    } else {
      assert (pure (SZ.v nc <> SZ.v dbl));
      assert (pure (SZ.v nc <= SZ.v dbl));
      assert (pure (SZ.v nc < SZ.v dbl));
      assert (pure (SZ.v vi + 1 == SZ.v vb * pow2 (reveal e + 1) + SZ.v nc));
      assert (pure (SZ.v nc < pow2 (reveal e + 1)));
      c := nc;
    };
    i := SZ.add vi 1sz;
  };
  T.drop_table zt;
  with v. assert (A.pts_to dst v);
  assert (pure (forall (k: nat). k < n ==>
                  S16.v (Seq.index v k) ==
                    Seq.index (intt_layer (reveal e) (as_poly vs)) k));
  as_poly_intro v (intt_layer (reveal e) (as_poly vs));
  assert (pure (as_poly v == intt_layer (reveal e) (as_poly vs)));
}

(** A 256-word copy; {!Hacl.Impl.Copy} is about bytes. *)
inline_for_extraction
fn poly_copy (dst src: A.array zqt) (#p: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (Seq.length vd == n /\ Seq.length vs == n)
ensures A.pts_to dst vs ** A.pts_to src #p vs
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #p vs **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  Seq.lemma_eq_intro v vs;
  assert (pure (v == reveal vs));
}

(** {2 The transforms} *)

(** [f <- NTT(f)], in place up to the scratch buffer. *)
fn ntt_inplace (f tmp: A.array zqt) (#vf #vt: erased (Seq.seq zqt))
requires A.pts_to f vf ** A.pts_to tmp vt **
         pure (Seq.length vf == n /\ Seq.length vt == n)
ensures exists* v w. A.pts_to f v ** A.pts_to tmp w **
        pure (Seq.length vf == n /\ Seq.length v == n /\ Seq.length w == n /\
              as_poly v == ntt (as_poly vf))
{
  A.pts_to_len f;
  A.pts_to_len tmp;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  ntt_layer_impl tmp f 128sz 1sz #7;
  ntt_layer_impl f tmp 64sz 2sz #6;
  ntt_layer_impl tmp f 32sz 4sz #5;
  ntt_layer_impl f tmp 16sz 8sz #4;
  ntt_layer_impl tmp f 8sz 16sz #3;
  ntt_layer_impl f tmp 4sz 32sz #2;
  ntt_layer_impl tmp f 2sz 64sz #1;
  ntt_unfold (as_poly vf);
  poly_copy f tmp;
}

(** [f <- NTT^-1(f)].  The layers run the other way and the whole thing is
    scaled by [128^-1] at the end. *)
fn intt_inplace (f tmp: A.array zqt) (#vf #vt: erased (Seq.seq zqt))
requires A.pts_to f vf ** A.pts_to tmp vt **
         pure (Seq.length vf == n /\ Seq.length vt == n)
ensures exists* v w. A.pts_to f v ** A.pts_to tmp w **
        pure (Seq.length vf == n /\ Seq.length v == n /\ Seq.length w == n /\
              as_poly v == intt (as_poly vf))
{
  A.pts_to_len f;
  A.pts_to_len tmp;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  intt_layer_impl tmp f 2sz 64sz #1;
  intt_layer_impl f tmp 4sz 32sz #2;
  intt_layer_impl tmp f 8sz 16sz #3;
  intt_layer_impl f tmp 16sz 8sz #4;
  intt_layer_impl tmp f 32sz 4sz #5;
  intt_layer_impl f tmp 64sz 2sz #6;
  intt_layer_impl tmp f 128sz 1sz #7;
  intt_unfold (as_poly vf);
  with w. assert (A.pts_to tmp w);
  let ci : zqt = S16.classify 3303us;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to f v ** A.pts_to tmp w **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length w == n /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) == mul inv_128 (Seq.index (as_poly w) k)))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(tmp.(vi));
    A.((f.(vi) <- zq_mul ci x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to f v);
  as_poly_intro v (poly_scale inv_128 (as_poly w));
  assert (pure (as_poly v == poly_scale inv_128 (as_poly w)));
}

(** {2 The pointwise product}
    [dst <- MultiplyNTTs(a, b)].  Algorithm 11 is 128 independent products
    of linear polynomials modulo [X^2 - gamma_i]; the loop runs over the
    128 pairs and writes two coefficients at a time, and [gamma_i] comes
    out of the one zeta table by {!gammas_zetas}. *)
(* Extending a pointwise property by the two indices just written.  Stated as
   a top-level lemma: the case analysis is trivial here, but ruinous when it
   has to happen inside the Pulse proof state. *)
let extend_by_two (v: Seq.seq zqt) (res: poly) (i: nat { 2 * i + 2 <= n })
  : Lemma (requires Seq.length v == n /\
                    (forall (k: nat). k < 2 * i ==>
                       S16.v (Seq.index v k) == Seq.index res k) /\
                    S16.v (Seq.index v (2 * i)) == Seq.index res (2 * i) /\
                    S16.v (Seq.index v (2 * i + 1)) == Seq.index res (2 * i + 1))
          (ensures forall (k: nat). k < 2 * i + 2 ==>
                     S16.v (Seq.index v k) == Seq.index res k)
  = ()

(* The two coefficients of the [i]th base-case product, at concrete indices. *)
let multiply_ntts_pair (f g: poly) (i: nat { i < 128 })
  : Lemma (Seq.index (multiply_ntts f g) (2 * i) ==
             add (mul (Seq.index f (2 * i)) (Seq.index g (2 * i)))
                 (mul (mul (Seq.index f (2 * i + 1)) (Seq.index g (2 * i + 1)))
                      (gammas i)) /\
           Seq.index (multiply_ntts f g) (2 * i + 1) ==
             add (mul (Seq.index f (2 * i)) (Seq.index g (2 * i + 1)))
                 (mul (Seq.index f (2 * i + 1)) (Seq.index g (2 * i))))
  = multiply_ntts_index f g (2 * i);
    multiply_ntts_index f g (2 * i + 1);
    Math.cancel_mul_div i 2;
    Math.lemma_div_plus 1 i 2;
    Math.lemma_mod_plus 1 i 2;
    Math.lemma_mod_plus 0 i 2;
    assert ((2 * i) / 2 == i /\ (2 * i) % 2 == 0);
    assert ((2 * i + 1) / 2 == i /\ (2 * i + 1) % 2 == 1)

let pair_bound (i: nat { i < 128 }) : Lemma (2 * i + 2 <= n) = ()

(** One of the 128 quadratic products, as a function of its own for the
    same reason the butterflies are. *)
#push-options "--z3rlimit 600"
inline_for_extraction
fn base_mul (dst a b zt: A.array zqt) (i: SZ.t)
            (#pa #pb #pz: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         A.pts_to zt #pz zeta_table **
         pure (SZ.v i < 128 /\ Seq.length vd == n /\
               Seq.length va == n /\ Seq.length vb == n /\
               (forall (k: nat). k < 2 * SZ.v i ==>
                  S16.v (Seq.index vd k) ==
                    Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k))
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        A.pts_to zt #pz zeta_table **
        pure (SZ.v i < 128 /\ Seq.length v == n /\
              Seq.length va == n /\ Seq.length vb == n /\
              (forall (k: nat). k < 2 * SZ.v i + 2 ==>
                 S16.v (Seq.index v k) ==
                   Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k))
{
  A.pts_to_len dst;
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  SZ.fits_u32_implies_fits (SZ.v i + SZ.v i);
  let j = SZ.add i i;
  SZ.fits_u32_implies_fits (SZ.v j + 1);
  let j1 = SZ.add j 1sz;
  let z = A.(zt.(i));
  gammas_zetas (SZ.v i);
  multiply_ntts_index (as_poly va) (as_poly vb) (SZ.v j);
  multiply_ntts_index (as_poly va) (as_poly vb) (SZ.v j1);
  let g = zq_mul (zq_mul z z) (S16.classify 17us);
  let a0 = A.(a.(j));
  let a1 = A.(a.(j1));
  let b0 = A.(b.(j));
  let b1 = A.(b.(j1));
  Math.cancel_mul_div (SZ.v i) 2;
  Math.lemma_div_plus 1 (SZ.v i) 2;
  Math.lemma_mod_plus 1 (SZ.v i) 2;
  assert (pure (S16.v g == gammas (SZ.v i)));
  multiply_ntts_pair (as_poly va) (as_poly vb) (SZ.v i);
  as_poly_index va (SZ.v j);
  as_poly_index va (SZ.v j1);
  as_poly_index vb (SZ.v j);
  as_poly_index vb (SZ.v j1);
  let c0 = zq_add (zq_mul a0 b0) (zq_mul (zq_mul a1 b1) g);
  let c1 = zq_add (zq_mul a0 b1) (zq_mul a1 b0);
  assert (pure (S16.v c0 ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb)) (SZ.v j)));
  assert (pure (S16.v c1 ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb)) (SZ.v j1)));
  assert (pure (SZ.v j == 2 * SZ.v i /\ SZ.v j1 == 2 * SZ.v i + 1));
  A.((dst.(j) <- c0));
  with v0. assert (A.pts_to dst v0);
  assert (pure (Seq.index v0 (SZ.v j) == c0 /\
                (forall (k: nat). k < Seq.length v0 /\ k <> SZ.v j ==>
                   Seq.index v0 k == Seq.index vd k)));
  A.((dst.(j1) <- c1));
  with v1. assert (A.pts_to dst v1);
  assert (pure (Seq.index v1 (SZ.v j1) == c1 /\
                (forall (k: nat). k < Seq.length v1 /\ k <> SZ.v j1 ==>
                   Seq.index v1 k == Seq.index v0 k)));
  assert (pure (Seq.length v1 == n /\ Seq.index v1 (SZ.v j) == c0));
  (* The two freshly written entries, at concrete indices. *)
  assert (pure (S16.v (Seq.index v1 (2 * SZ.v i)) ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb))
                            (2 * SZ.v i)));
  assert (pure (S16.v (Seq.index v1 (2 * SZ.v i + 1)) ==
                  Seq.index (multiply_ntts (as_poly va) (as_poly vb))
                            (2 * SZ.v i + 1)));
  (* Everything below them is untouched by the two writes. *)
  assert (pure (forall (k: nat). k < 2 * SZ.v i ==>
                  S16.v (Seq.index v1 k) ==
                    Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k));
  extend_by_two v1 (multiply_ntts (as_poly va) (as_poly vb)) (SZ.v i);
  assert (pure (forall (k: nat). k < 2 * SZ.v i + 2 ==>
                  S16.v (Seq.index v1 k) ==
                    Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k));
}

#pop-options

fn multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == multiply_ntts (as_poly va) (as_poly vb))
{
  A.pts_to_len dst;
  A.pts_to_len a;
  A.pts_to_len b;
  let zt = T.table zeta_arr 128sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 128sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    A.pts_to zt #pz zeta_table **
    pure (SZ.v vi <= 128 /\ Seq.length v == n /\
          Seq.length va == n /\ Seq.length vb == n /\
          (forall (k: nat). k < 2 * SZ.v vi ==>
             S16.v (Seq.index v k) ==
               Seq.index (multiply_ntts (as_poly va) (as_poly vb)) k))
  decreases (128 - SZ.v (!i))
  {
    let vi = !i;
    assert (pure (SZ.v vi < 128));
    pair_bound (SZ.v vi);
    base_mul dst a b zt vi;
    HSZ.fits32 ();
    assert_norm (128 < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  T.drop_table zt;
  with v. assert (A.pts_to dst v);
  as_poly_intro v (multiply_ntts (as_poly va) (as_poly vb));
  assert (pure (as_poly v == multiply_ntts (as_poly va) (as_poly vb)));
}

#pop-options
