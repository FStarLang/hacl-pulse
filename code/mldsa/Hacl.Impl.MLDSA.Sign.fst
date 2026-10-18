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


(** Algorithm 7, [ML-DSA.Sign_internal], from the message representative
    [mu].

    Constant time.  The private key and the mask [y] are secret.  Each
    attempt declassifies exactly its four rejection verdicts, as FIPS 204
    section 3.6.3 and the reference implementation do: whether an attempt
    is rejected, and which test rejected it, depends only on values that
    the accepted signature, or the public key, does not reveal anything
    more about.  The hint is computed under a secret mask and only its
    population count is declassified, for the last test; once that test
    passes the hint is part of the signature. *)
module Hacl.Impl.MLDSA.Sign

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.NTT
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Spec.MLDSA.Rounding
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Poly
open Hacl.Impl.MLDSA.Vec
open Hacl.Impl.MLDSA.Round
open Hacl.Impl.MLDSA.VecRound
open Hacl.Impl.MLDSA.Hint
open Hacl.Impl.MLDSA.Sampler
open Hacl.Impl.MLDSA.Pack
open Hacl.Impl.MLDSA.Glue

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module HSZ = Hacl.SizeT
module Sub = Hacl.Impl.Sub
module Copy = Hacl.Impl.Copy
module M = Spec.MLDSA

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The signing context} *)

let ctx_of (p: params) (va: Seq.seq zqt { Seq.length va == p.k * p.l * n })
           (vs1: Seq.seq zqt { Seq.length vs1 == p.l * n })
           (vs2 vt0: (s: Seq.seq zqt { Seq.length s == p.k * n }))
  : GTot (M.sign_ctx p)
  = { M.sc_a = as_zqs va; M.sc_s1 = as_zqs vs1; M.sc_s2 = as_zqs vs2; M.sc_t0 = as_zqs vt0 }

inline_for_extraction
let g1_beta (#p: erased params) (g1bits tau eta: SZ.t)
  : Pure S32.t
      (requires SZ.v g1bits == p.gamma1_bits /\ SZ.v tau == p.tau /\ SZ.v eta == p.eta)
      (ensures fun r -> S32.v r == gamma1 p - beta p /\ S32.v r <= half_q)
  = assert_norm (pow2 17 == 131072);
    assert_norm (pow2 19 == 524288);
    assert_norm (pow2 32 == 4294967296);
    beta_lt p;
    let g = if g1bits = 17sz then 131072ul else 524288ul in
    let b = U32.mul (SZ.sizet_to_uint32 tau) (SZ.sizet_to_uint32 eta) in
    S32.classify (U32.sub g b)

inline_for_extraction
let g2_beta (#p: erased params) (gd: U32.t { g2_div_ok p gd }) (tau eta: SZ.t)
  : Pure S32.t
      (requires SZ.v tau == p.tau /\ SZ.v eta == p.eta)
      (ensures fun r -> S32.v r == gamma2 p - beta p /\ S32.v r <= half_q)
  = assert_norm (pow2 32 == 4294967296);
    beta_lt p;
    gamma2_cases p;
    let g = if U32.eq gd 88ul then 95232ul else 261888ul in
    let b = U32.mul (SZ.sizet_to_uint32 tau) (SZ.sizet_to_uint32 eta) in
    S32.classify (U32.sub g b)

inline_for_extraction
let g2_bound (#p: erased params) (gd: U32.t { g2_div_ok p gd })
  : r: S32.t { S32.v r == gamma2 p /\ S32.v r <= half_q }
  = gamma2_cases p;
    gamma2_w #p gd

(** {2 One attempt} *)

(** [w <- NTT^-1(A NTT(y))]. *)
fn commit_impl (p: erased params) (w a y: A.array zqt)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t)
               ([@@@FStar.Attributes.monomorphize] l: SZ.t)
               (#vw: erased (Seq.seq zqt)) (#pa #py: perm) (#va #vy: erased (Seq.seq zqt))
requires A.pts_to w vw ** A.pts_to a #pa va ** A.pts_to y #py vy **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ Seq.length vw == p.k * n /\
               Seq.length va == p.k * p.l * n /\ Seq.length vy == p.l * n)
ensures exists* (r: Seq.seq zqt). A.pts_to w r ** A.pts_to a #pa va ** A.pts_to y #py vy **
  pure (Seq.length r == p.k * n /\ Seq.length va == p.k * p.l * n /\ Seq.length vy == p.l * n /\
        as_zqs r == M.commit p (as_zqs va) (as_zqs vy))
{
  HSZ.fits32 ();
  let ln = SZ.mul l 256sz;
  let mut yh = [| (S32.zero <: zqt); ln |];
  zcopy yh y ln;
  vec_ntt_impl yh l;
  let mut tmp = [| (S32.zero <: zqt); 256sz |];
  mat_vec_mul_impl w a yh tmp k l;
  vec_intt_impl w k;
  ()
}

(** [v <- v + NTT^-1(c s-hat)] ([add = true]) or [v <- v - NTT^-1(c s-hat)]. *)
fn cs_update (v c s: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t) (plus: bool)
             (#vv: erased (Seq.seq zqt)) (#pc #ps: perm) (#vc #vs: erased (Seq.seq zqt))
requires A.pts_to v vv ** A.pts_to c #pc vc ** A.pts_to s #ps vs **
         pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length vv == SZ.v k * n /\
               Seq.length vc == n /\ Seq.length vs == SZ.v k * n)
ensures exists* (r: Seq.seq zqt). A.pts_to v r ** A.pts_to c #pc vc ** A.pts_to s #ps vs **
  pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length r == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
        Seq.length vc == n /\ Seq.length vs == SZ.v k * n /\
        (let cs = vec_intt #(SZ.v k) (vec_scale #(SZ.v k) (as_poly vc) (as_zqs vs)) in
         as_zqs r == (if plus then vec_add #(SZ.v k) (as_zqs vv) cs
                      else vec_sub #(SZ.v k) (as_zqs vv) cs)))
{
  HSZ.fits32 ();
  let kn = SZ.mul k 256sz;
  let mut cs = [| (S32.zero <: zqt); kn |];
  vec_scale_impl cs c s k;
  with ucs0. assert (A.pts_to cs ucs0);
  vec_intt_impl cs k;
  with ucs. assert (A.pts_to cs ucs);
  assert (pure (as_zqs ucs == vec_intt #(SZ.v k) (vec_scale #(SZ.v k) (as_poly vc) (as_zqs vs))));
  if plus {
    add_inplace v cs kn;
    with r. assert (A.pts_to v r);
    add_eq (SZ.v k) r vv ucs;
    ()
  } else {
    sub_inplace v cs kn;
    with r. assert (A.pts_to v r);
    sub_eq (SZ.v k) r vv ucs;
    ()
  }
}

(** The last two tests and the encoding.  [ct0 = NTT^-1(c t0-hat)];
    [r = w - c s2]. *)
fn hint_and_encode (p: erased params) (sg: A.array S8.t) (z r c t0: A.array zqt)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                   (gd: U32.t)
                   (#vs: erased (Seq.seq S8.t)) (#pz #pr #pc #pt: perm)
                   (#vz #vr #vc #vt: erased (Seq.seq zqt))
requires A.pts_to sg vs ** A.pts_to z #pz vz ** A.pts_to r #pr vr **
         A.pts_to c #pc vc ** A.pts_to t0 #pt vt **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v ctl == ct_len p /\
               SZ.v g1bits == p.gamma1_bits /\ SZ.v omega == p.omega /\
               U32.v gd == p.gamma2_div /\
               Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
               Seq.length vr == p.k * n /\ Seq.length vc == n /\ Seq.length vt == p.k * n)
returns ok: bool
ensures exists* (v: Seq.seq S8.t). A.pts_to sg v ** A.pts_to z #pz vz ** A.pts_to r #pr vr **
  A.pts_to c #pc vc ** A.pts_to t0 #pt vt **
  pure (Seq.length vs == sig_len p /\ Seq.length v == sig_len p /\
        Seq.length vz == p.l * n /\ Seq.length vr == p.k * n /\
        Seq.length vc == n /\ Seq.length vt == p.k * n /\
        (let ct0 = vec_intt #p.k (vec_scale #p.k (as_poly vc) (as_zqs vt)) in
         let h = vec_make_hint p #p.k (vec_map #p.k neg ct0) (vec_add #p.k (as_zqs vr) ct0) in
         ok == (all_lt ct0 (gamma2 p) && count_true h <= p.omega) /\
         (ok ==> v == sig_encode p (Seq.slice vs 0 (ct_len p)) (as_zqs vz) h)))
{
  HSZ.fits32 ();
  let kn = SZ.mul k 256sz;
  let mut ct0 = [| (S32.zero <: zqt); kn |];
  vec_scale_impl ct0 c t0 k;
  vec_intt_impl ct0 k;
  let ok1 = all_lt_impl ct0 kn (g2_bound #p gd);
  let mut h = [| (S32.zero <: S32.t); kn |];
  let cnt = make_hint_impl h ct0 r p gd k;
  let ok2 = U32.lte cnt (SZ.sizet_to_uint32 omega);
  if (ok1 && ok2) {
    sig_encode_impl p sg z h k l ctl g1bits omega;
    true
  } else {
    false
  }
}

let attempt_eq (p: params) (sc: M.sign_ctx p) (mu rho: Seq.lseq S8.t 64)
               (a: nat { a < max_attempts })
               (y w r z: Seq.seq zqt) (w1: Seq.seq zqt) (ct: Seq.lseq S8.t (ct_len p))
               (c: poly) (ok1 ok2 ok3: bool) (vs: Seq.lseq S8.t (sig_len p))
  : Lemma (requires
      Seq.length y == p.l * n /\ Seq.length z == p.l * n /\
      Seq.length w == p.k * n /\ Seq.length r == p.k * n /\ Seq.length w1 == p.k * n /\
      as_zqs y == expand_mask p rho a /\
      as_zqs w == M.commit p sc.M.sc_a (as_zqs y) /\
      as_ints w1 == vec_high_bits p #p.k (as_zqs w) /\
      ct == M.challenge_hash p mu (as_ints w1) /\
      c == ntt (sample_in_ball p ct) /\
      as_zqs z == vec_add #p.l (as_zqs y) (vec_intt #p.l (vec_scale #p.l c sc.M.sc_s1)) /\
      as_zqs r == vec_sub #p.k (as_zqs w) (vec_intt #p.k (vec_scale #p.k c sc.M.sc_s2)) /\
      (beta_lt p;
       ok1 == all_lt (as_zqs z) (gamma1 p - beta p) /\
       ok2 == all_lt (vec_low_bits p #p.k (as_zqs r)) (gamma2 p - beta p)) /\
      (ok1 && ok2 ==>
        (let ct0 = vec_intt #p.k (vec_scale #p.k c sc.M.sc_t0) in
         let h = vec_make_hint p #p.k (vec_map #p.k neg ct0) (vec_add #p.k (as_zqs r) ct0) in
         ok3 == (all_lt ct0 (gamma2 p) && count_true h <= p.omega) /\
         (ok3 ==> vs == sig_encode p ct (as_zqs z) h))))
    (ensures (if ok1 && ok2 && ok3 then M.sign_attempt p sc mu rho a == Some vs
              else M.sign_attempt p sc mu rho a == None))
  = ()

(** Algorithm 7, lines 11 to 32: one attempt with counter [kappa = a l].
    On success [sg] holds the signature. *)
fn attempt_impl (p: erased params) (sg: A.array S8.t) (a s1 s2 t0: A.array zqt)
                (mu rho: A.array S8.t)
                ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                (gd: U32.t) (kappa: SZ.t) (att: erased (x: nat { x < max_attempts }))
                (#vs: erased (Seq.seq S8.t)) (#pa #p1 #p2 #p0 #pm #pr: perm)
                (#va #v1 #v2 #v0: erased (Seq.seq zqt)) (#vm #vr: erased (Seq.seq S8.t))
requires A.pts_to sg vs ** A.pts_to a #pa va ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 **
         A.pts_to t0 #p0 v0 ** A.pts_to mu #pm vm ** A.pts_to rho #pr vr **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               SZ.v kappa == att * p.l /\
               Seq.length vs == sig_len p /\ Seq.length va == p.k * p.l * n /\
               Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
               Seq.length vm == 64 /\ Seq.length vr == 64)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to a #pa va ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 **
  A.pts_to t0 #p0 v0 ** A.pts_to mu #pm vm ** A.pts_to rho #pr vr **
  pure (Seq.length vs == sig_len p /\ Seq.length v == sig_len p /\
        Seq.length va == p.k * p.l * n /\
        Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
        Seq.length vm == 64 /\ Seq.length vr == 64 /\
        (if ok then M.sign_attempt p (ctx_of p va v1 v2 v0) vm vr att == Some v
         else M.sign_attempt p (ctx_of p va v1 v2 v0) vm vr att == None))
{
  A.pts_to_len sg;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sig_len p);
  assert (pure (ct_len p <= sig_len p));
  let kn = SZ.mul k 256sz;
  let ln = SZ.mul l 256sz;
  (* y and w = A y *)
  let mut y = [| (S32.zero <: zqt); ln |];
  expand_mask_impl p y rho l g1bits kappa att;
  with vy. assert (A.pts_to y vy);
  let mut w = [| (S32.zero <: zqt); kn |];
  commit_impl p w a y k l;
  with vw. assert (A.pts_to w vw);
  (* c~ = H(mu || w1Encode(HighBits w)), straight into the signature *)
  let mut w1 = [| (S32.zero <: zqt); kn |];
  high_bits_impl w1 w p gd k;
  with vw1. assert (A.pts_to w1 vw1);
  let ct = Sub.sub sg 0sz ctl;
  challenge_impl p ct mu w1 k ctl gd;
  with vct. assert (A.pts_to ct vct);
  let mut c = [| (S32.zero <: zqt); 256sz |];
  sample_in_ball_impl p c ct ctl tau;
  Sub.unsub sg 0 (SZ.v ctl) ct;
  with vs1. assert (A.pts_to sg vs1);
  assert (pure (Seq.equal (Seq.slice vs1 0 (ct_len p)) vct));
  ntt_inplace c;
  with vc. assert (A.pts_to c vc);
  (* z = y + c s1 and r = w - c s2 *)
  cs_update y c s1 l true;
  with vz. assert (A.pts_to y vz);
  cs_update w c s2 k false;
  with vr'. assert (A.pts_to w vr');
  let ok1 = all_lt_impl y ln (g1_beta #p g1bits tau eta);
  let ok2 = low_lt_impl w p gd k (g2_beta #p gd tau eta);
  if (ok1 && ok2) {
    let ok3 = hint_and_encode p sg y w c t0 k l ctl g1bits omega gd;
    with vfin. assert (A.pts_to sg vfin);
    attempt_eq p (ctx_of p va v1 v2 v0) vm vr att vy vw vr' vz vw1 vct (as_poly vc)
               ok1 ok2 ok3 vfin;
    ok3
  } else {
    attempt_eq p (ctx_of p va v1 v2 v0) vm vr att vy vw vr' vz vw1 vct (as_poly vc)
               ok1 ok2 false vs1;
    false
  }
}

(** {2 The rejection loop} *)

#push-options "--fuel 1 --ifuel 1"
let loop_unfold (p: params) (sc: M.sign_ctx p) (mu rho: Seq.lseq S8.t 64)
                (a: nat { a < max_attempts })
  : Lemma (M.sign_loop p sc mu rho a ==
           (match M.sign_attempt p sc mu rho a with
            | Some s -> Some s
            | None -> M.sign_loop p sc mu rho (a + 1)))
  = ()

let loop_end (p: params) (sc: M.sign_ctx p) (mu rho: Seq.lseq S8.t 64)
  : Lemma (M.sign_loop p sc mu rho max_attempts == None)
  = ()
#pop-options

(** Algorithm 7, lines 10 to 33: attempts [0, 1, ...] until one
    succeeds, at most [max_attempts] of them. *)
fn loop_impl (p: erased params) (sg: A.array S8.t) (a s1 s2 t0: A.array zqt)
             (mu rho: A.array S8.t)
             ([@@@FStar.Attributes.monomorphize] k: SZ.t)
             ([@@@FStar.Attributes.monomorphize] l: SZ.t)
             ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
             ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
             ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
             ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
             ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
             (gd: U32.t)
             (#vs: erased (Seq.seq S8.t)) (#pa #p1 #p2 #p0 #pm #pr: perm)
             (#va #v1 #v2 #v0: erased (Seq.seq zqt)) (#vm #vr: erased (Seq.seq S8.t))
requires A.pts_to sg vs ** A.pts_to a #pa va ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 **
         A.pts_to t0 #p0 v0 ** A.pts_to mu #pm vm ** A.pts_to rho #pr vr **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vs == sig_len p /\ Seq.length va == p.k * p.l * n /\
               Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
               Seq.length vm == 64 /\ Seq.length vr == 64)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to a #pa va ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 **
  A.pts_to t0 #p0 v0 ** A.pts_to mu #pm vm ** A.pts_to rho #pr vr **
  pure (Seq.length v == sig_len p /\ Seq.length va == p.k * p.l * n /\
        Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
        Seq.length vm == 64 /\ Seq.length vr == 64 /\
        (if ok then M.sign_loop p (ctx_of p va v1 v2 v0) vm vr 0 == Some v
         else M.sign_loop p (ctx_of p va v1 v2 v0) vm vr 0 == None))
{
  A.pts_to_len sg;
  HSZ.fits32 ();
  let mut i = 0sz;
  let mut fin = false;
  while (let vf = !fin; let vi = !i; (not vf && SZ.lt vi 1024sz))
  invariant exists* (vi: SZ.t) (vf: bool) (w: Seq.seq S8.t).
    pts_to i vi ** pts_to fin vf ** A.pts_to sg w **
    pure (SZ.v vi <= max_attempts /\ Seq.length w == sig_len p /\
          Seq.length va == p.k * p.l * n /\
          Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
          Seq.length vm == 64 /\ Seq.length vr == 64 /\
          (if vf then M.sign_loop p (ctx_of p va v1 v2 v0) vm vr 0 == Some w
           else M.sign_loop p (ctx_of p va v1 v2 v0) vm vr 0 ==
                M.sign_loop p (ctx_of p va v1 v2 v0) vm vr (SZ.v vi)))
  decreases (max_attempts - SZ.v (!i))
  {
    let vi = !i;
    let att : erased (x: nat { x < max_attempts }) = hide (SZ.v vi);
    let kappa = SZ.mul vi l;
    let ok = attempt_impl p sg a s1 s2 t0 mu rho k l eta tau ctl g1bits omega gd kappa att;
    loop_unfold p (ctx_of p va v1 v2 v0) vm vr (SZ.v vi);
    fin := ok;
    i := SZ.add vi 1sz;
  };
  with vi. assert (pts_to i vi);
  loop_end p (ctx_of p va v1 v2 v0) vm vr;
  !fin
}

(** {2 Algorithm 7} *)

let ctx_eq (p: params) (vk: Seq.lseq S8.t (sk_len p))
           (va: Seq.seq zqt { Seq.length va == p.k * p.l * n })
           (vs1: Seq.seq zqt { Seq.length vs1 == p.l * n })
           (vs2 vt0: (s: Seq.seq zqt { Seq.length s == p.k * n }))
  : Lemma (requires
      as_zqs va == expand_a p (sk_decode p vk).sk_rho /\
      as_zqs vs1 == vec_ntt #p.l (sk_decode p vk).sk_s1 /\
      as_zqs vs2 == vec_ntt #p.k (sk_decode p vk).sk_s2 /\
      as_zqs vt0 == vec_ntt #p.k (sk_decode p vk).sk_t0)
    (ensures ctx_of p va vs1 vs2 vt0 == M.sign_ctx_of p (sk_decode p vk))
  = ()

(** [A-hat] from [rho] and the NTT forms of [s1], [s2] and [t0]. *)
fn setup_impl (p: erased params) (a s1 s2 t0: A.array zqt) (sk: A.array S8.t)
              ([@@@FStar.Attributes.monomorphize] k: SZ.t)
              ([@@@FStar.Attributes.monomorphize] l: SZ.t)
              ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
              (#wa #w1 #w2 #w0: erased (Seq.seq zqt)) (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to a wa ** A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to t0 w0 **
         A.pts_to sk #pk vk **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length vk == sk_len p /\ Seq.length wa == p.k * p.l * n /\
               Seq.length w1 == p.l * n /\ Seq.length w2 == p.k * n /\ Seq.length w0 == p.k * n)
ensures exists* (va v1 v2 v0: Seq.seq zqt).
  A.pts_to a va ** A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to t0 v0 **
  A.pts_to sk #pk vk **
  pure (Seq.length vk == sk_len p /\ Seq.length va == p.k * p.l * n /\
        Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
        ctx_of p va v1 v2 v0 == M.sign_ctx_of p (sk_decode p vk))
{
  A.pts_to_len sk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sk_len p);
  sk_layout p;
  sk_decode_impl p s1 s2 t0 sk k l eta;
  vec_ntt_impl s1 l;
  vec_ntt_impl s2 k;
  vec_ntt_impl t0 k;
  let rho = Sub.sub sk 0sz 32sz;
  expand_a_impl p a rho k l;
  Sub.unsub_id sk 0 32 rho;
  with va. assert (A.pts_to a va);
  with v1. assert (A.pts_to s1 v1);
  with v2. assert (A.pts_to s2 v2);
  with v0. assert (A.pts_to t0 v0);
  ctx_eq p vk va v1 v2 v0;
  ()
}

let rho2_eq (vk: Seq.seq S8.t) (vr vm v: Seq.seq S8.t)
  : Lemma (requires Seq.length vk >= 64 /\ Seq.length vr == 32 /\ Seq.length vm == 64 /\
                    Seq.length v == 128 /\
                    (forall (t: nat). t < 32 ==> Seq.index v t == Seq.index vk (32 + t)) /\
                    (forall (t: nat). t < 32 ==> Seq.index v (32 + t) == Seq.index vr t) /\
                    (forall (t: nat). t < 64 ==> Seq.index v (64 + t) == Seq.index vm t))
          (ensures v == Seq.append (Seq.slice vk 32 64) (Seq.append vr vm))
  = Seq.lemma_eq_intro v (Seq.append (Seq.slice vk 32 64) (Seq.append vr vm))

(** [rho'' = H(K || rnd || mu, 64)]. *)
fn rho2_impl (out sk rnd mu: A.array S8.t)
             (#vo: erased (Seq.seq S8.t)) (#pk #pr #pm: perm) (#vk #vr #vm: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to sk #pk vk ** A.pts_to rnd #pr vr ** A.pts_to mu #pm vm **
         pure (Seq.length vo == 64 /\ Seq.length vk >= 64 /\ SZ.fits (Seq.length vk) /\
               Seq.length vr == 32 /\ Seq.length vm == 64)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to out v ** A.pts_to sk #pk vk ** A.pts_to rnd #pr vr ** A.pts_to mu #pm vm **
  pure (Seq.length vk >= 64 /\ Seq.length vr == 32 /\ Seq.length vm == 64 /\
        v == M.hash (Seq.append (Seq.slice vk 32 64) (Seq.append vr vm)) 64)
{
  A.pts_to_len sk;
  let mut seed = [| (S8.zero <: S8.t); 128sz |];
  A.pts_to_len seed;
  Copy.copy_range seed 0sz sk 32sz 32sz;
  Copy.copy_at seed 32sz rnd 32sz;
  Copy.copy_at seed 64sz mu 64sz;
  with vsd. assert (A.pts_to seed vsd);
  rho2_eq vk vr vm vsd;
  Hacl.Hash.SHA3.shake256 out 64sz seed 128sz;
  ()
}

(** Algorithm 7 from [mu], with the per-signature randomness [rnd]
    ([rnd = 0^32] for the deterministic variant). *)
fn sign_mu_impl (sg sk mu rnd: A.array S8.t) (p: erased params)
                ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                (gd: U32.t)
                (#vs: erased (Seq.seq S8.t)) (#pk #pm #pr: perm)
                (#vk #vm #vr: erased (Seq.seq S8.t))
requires A.pts_to sg vs ** A.pts_to sk #pk vk ** A.pts_to mu #pm vm ** A.pts_to rnd #pr vr **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vs == sig_len p /\ Seq.length vk == sk_len p /\
               Seq.length vm == 64 /\ Seq.length vr == 32)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to sk #pk vk ** A.pts_to mu #pm vm ** A.pts_to rnd #pr vr **
  pure (Seq.length v == sig_len p /\ Seq.length vk == sk_len p /\
        Seq.length vm == 64 /\ Seq.length vr == 32 /\
        (if ok then M.sign_mu p vk vm vr == Some v else M.sign_mu p vk vm vr == None))
{
  A.pts_to_len sk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sk_len p);
  sk_layout p;
  let kn = SZ.mul k 256sz;
  let ln = SZ.mul l 256sz;
  let kln = SZ.mul (SZ.mul k l) 256sz;
  let mut a = [| (S32.zero <: zqt); kln |];
  let mut s1 = [| (S32.zero <: zqt); ln |];
  let mut s2 = [| (S32.zero <: zqt); kn |];
  let mut t0 = [| (S32.zero <: zqt); kn |];
  setup_impl p a s1 s2 t0 sk k l eta;
  let mut rho = [| (S8.zero <: S8.t); 64sz |];
  rho2_impl rho sk rnd mu;
  loop_impl p sg a s1 s2 t0 mu rho k l eta tau ctl g1bits omega gd
}

#pop-options
