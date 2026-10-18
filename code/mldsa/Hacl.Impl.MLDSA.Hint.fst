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


(** [HintBitPack] and [HintBitUnpack].

    A hint lives in memory as one secret word per coefficient, [0] or [1]
    ({!hint_view}).  It is packed only once a signature has been accepted,
    at which point it is part of the public output, so the packer
    declassifies it and branches.  Unpacking reads a public signature.  It
    is {!Spec.MLDSA.Encode.hint_unpack} verbatim: scatter the positions,
    re-pack, and accept exactly when the bytes come back. *)
module Hacl.Impl.MLDSA.Hint

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = Hacl.Secret.Cast
module Declassify = Hacl.Secret.Declassify
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module HSZ = Hacl.SizeT
module KZ = Spec.MLKEM.Zq
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let hint_view (s: Seq.seq S32.t) : GTot (Seq.lseq bool (Seq.length s))
  = Seq.init_ghost (Seq.length s) (fun i -> S32.v (Seq.index s i) = 1)

let hint_view_index (s: Seq.seq S32.t) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (hint_view s) i == (S32.v (Seq.index s i) = 1))
          [SMTPat (Seq.index (hint_view s) i)]
  = Seq.init_ghost_index_ (Seq.length s) (fun i -> S32.v (Seq.index s i) = 1) i

let hint_bits (s: Seq.seq S32.t) : prop
  = forall (i: nat). i < Seq.length s ==> S32.v (Seq.index s i) <= 1

let hint_dims (p: params) (k omega: SZ.t) : prop
  = SZ.v k == p.k /\ SZ.v omega == p.omega

(** {2 Packing} *)

let pinit (p: params) : hint_state p = (Seq.create (hint_len p) 0uy, 0)

let hs (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat) : hint_state p
  = Loops.repeati t (hint_pack_step p h) (pinit p)

#push-options "--ifuel 1 --z3rlimit 100"
let hs_step (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat { t < p.k * n })
  : Lemma (requires snd (hs p h t) <= p.omega)
          (ensures (assert_norm (pow2 8 == 256);
                    KZ.div_lt t p.k n;
                    let y = fst (hs p h t) in
                    let idx = snd (hs p h t) in
                    let y' = fst (hs p h (t + 1)) in
                    let idx' = snd (hs p h (t + 1)) in
                    let hit = Seq.index h t && idx < p.omega in
                    idx' == (if hit then idx + 1 else idx) /\ idx' <= p.omega /\
                    (forall (u: nat). u < hint_len p ==>
                       U8.v (Seq.index y' u) ==
                         (if t % n = n - 1 && u = p.omega + t / n then idx'
                          else if hit && u = idx then t % n
                          else U8.v (Seq.index y u)))))
  = Loops.unfold_repeati t (hint_pack_step p h) (pinit p);
    assert_norm (pow2 8 == 256);
    KZ.div_lt t p.k n
#pop-options

let hs_final (p: params) (h: Seq.lseq bool (p.k * n)) (v: Seq.seq S8.t)
  : Lemma (requires Seq.length v == hint_len p /\
                    (forall (u: nat). u < hint_len p ==>
                       S8.v (Seq.index v u) == U8.v (Seq.index (fst (hs p h (p.k * n))) u)))
          (ensures v == hint_pack p h)
  = let y = fst (hs p h (p.k * n)) in
    let aux (u: nat { u < hint_len p }) : Lemma (Seq.index v u == Seq.index (hint_pack p h) u)
      = Seq.init_ghost_index_ (hint_len p) (fun i -> S8.classify (Seq.index y i)) u;
        S8.v_extensional (Seq.index v u) (Seq.index (hint_pack p h) u) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro v (hint_pack p h)

let hs_zero (p: params) (h: Seq.lseq bool (p.k * n)) (u: nat { u < hint_len p })
  : Lemma (snd (hs p h 0) == 0 /\ U8.v (Seq.index (fst (hs p h 0)) u) == 0)
  = Loops.repeati_zero (hint_pack_step p h) (pinit p)

inline_for_extraction
let sz_byte (j: SZ.t { SZ.v j < 256 }) : r: S8.t { S8.v r == SZ.v j }
  = HSZ.fits32 ();
    assert_norm (pow2 8 == 256);
    Math.small_mod (SZ.v j) (pow2 8);
    SZ.fits_u32_implies_fits 256;
    Cast.u32_to_u8 (S32.classify (SZ.sizet_to_uint32 j))

#push-options "--z3rlimit 200"

(** [out <- HintBitPack h]. *)
fn hint_pack_impl (out: A.array S8.t) (h: A.array S32.t) (p: erased params)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                  (#ph: perm) (#vo: erased (Seq.seq S8.t)) (#vh: erased (Seq.seq S32.t))
requires A.pts_to out vo ** A.pts_to h #ph vh **
         pure (hint_dims p k omega /\ Seq.length vh == p.k * n /\ Seq.length vo == hint_len p)
ensures exists* v. A.pts_to out v ** A.pts_to h #ph vh **
        pure (hint_dims p k omega /\ Seq.length vh == p.k * n /\
              v == hint_pack p (hint_view vh))
{
  A.pts_to_len out;
  A.pts_to_len h;
  HSZ.fits32 ();
  assert_norm (8 * 256 < pow2 32);
  SZ.fits_u32_implies_fits (p.k * n);
  SZ.fits_u32_implies_fits (hint_len p);
  let len = SZ.add omega k;
  let kn = SZ.mul k 256sz;
  let mut u = 0sz;
  while (let vu = !u; SZ.lt vu len)
  invariant exists* (vu: SZ.t) (v: Seq.seq S8.t).
    pts_to u vu ** A.pts_to out v **
    pure (SZ.v vu <= hint_len p /\ Seq.length v == hint_len p /\
          (forall (w: nat). w < SZ.v vu ==> S8.v (Seq.index v w) == 0))
  decreases (hint_len p - SZ.v (!u))
  {
    let vu = !u;
    A.(out.(vu) <- S8.zero);
    u := SZ.add vu 1sz;
  };
  with v0. assert (A.pts_to out v0);
  Classical.forall_intro (hs_zero p (hint_view vh));
  hs_zero p (hint_view vh) 0;
  let mut idx = 0sz;
  let mut t = 0sz;
  while (let vt = !t; SZ.lt vt kn)
  invariant exists* (vt vi: SZ.t) (v: Seq.seq S8.t).
    pts_to t vt ** pts_to idx vi ** A.pts_to out v ** A.pts_to h #ph vh **
    pure (SZ.v vt <= p.k * n /\ Seq.length v == hint_len p /\
          hint_dims p k omega /\ Seq.length vh == p.k * n /\
          SZ.v vi == snd (hs p (hint_view vh) (SZ.v vt)) /\ SZ.v vi <= p.omega /\
          (forall (w: nat). w < hint_len p ==>
             S8.v (Seq.index v w) == U8.v (Seq.index (fst (hs p (hint_view vh) (SZ.v vt))) w)))
  decreases (p.k * n - SZ.v (!t))
  {
    let vt = !t;
    let vi = !idx;
    hs_step p (hint_view vh) (SZ.v vt);
    KZ.div_lt (SZ.v vt) p.k n;
    let ht = Declassify.u32 A.(h.(vt));
    let j = SZ.rem vt 256sz;
    let i = SZ.div vt 256sz;
    let hit = (U32.eq ht 1ul && SZ.lt vi omega);
    let cur = A.(out.(vi));
    A.(out.(vi) <- (if hit then sz_byte j else cur));
    let vi' = (if hit then SZ.add vi 1sz else vi);
    idx := vi';
    let slot = SZ.add omega i;
    let cur2 = A.(out.(slot));
    A.(out.(slot) <- (if SZ.eq j 255sz then sz_byte vi' else cur2));
    t := SZ.add vt 1sz;
  };
  with vt v. assert (pts_to t vt ** A.pts_to out v);
  hs_final p (hint_view vh) v;
  ()
}

#pop-options

(** {2 Unpacking} *)

let scatter_poly_upto (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat) (m: nat)
                      (h: Seq.lseq bool (p.k * n)) : GTot (Seq.lseq bool (p.k * n))
  = if i < p.k then Loops.repeati_g m (hint_scatter_step p y i) h else h

let scatter_upto (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat)
  : GTot (Seq.lseq bool (p.k * n))
  = Loops.repeati_g i (hint_scatter_poly p y) (Seq.create (p.k * n) false)

let view_upd (s: Seq.seq S32.t) (i: nat { i < Seq.length s }) (x: S32.t)
  : Lemma (requires S32.v x == 1)
          (ensures hint_view (Seq.upd s i x) == Seq.upd (hint_view s) i true)
  = Seq.lemma_eq_intro (hint_view (Seq.upd s i x)) (Seq.upd (hint_view s) i true)

inline_for_extraction
let byte_sz (x: S8.t) : r: SZ.t { SZ.v r == S8.v x }
  = HSZ.fits32 ();
    SZ.uint32_to_sizet (Declassify.u32 (Cast.u8_to_u32 x))

let scatter_upto_zero (p: params) (y: Seq.lseq S8.t (hint_len p))
  : Lemma (scatter_upto p y 0 == Seq.create (p.k * n) false)
  = Loops.repeati_g_zero (hint_scatter_poly p y) (Seq.create (p.k * n) false)

let scatter_poly_zero (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k })
                      (h: Seq.lseq bool (p.k * n))
  : Lemma (scatter_poly_upto p y i 0 h == h)
  = Loops.repeati_g_zero (hint_scatter_step p y i) h

let scatter_poly_next (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k })
                      (m: nat) (h: Seq.lseq bool (p.k * n))
  : Lemma (scatter_poly_upto p y i (m + 1) h ==
           hint_scatter_step p y i m (scatter_poly_upto p y i m h))
  = Loops.unfold_repeati_g m (hint_scatter_step p y i) h

let scatter_next (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k })
  : Lemma (scatter_upto p y (i + 1) == scatter_poly_upto p y i p.omega (scatter_upto p y i))
  = Loops.unfold_repeati_g i (hint_scatter_poly p y) (Seq.create (p.k * n) false)

(** One position byte: [h'] is [h] with the marked coefficient set, when
    the position is in range. *)
let scatter_one (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k })
                (m: nat { m < p.omega }) (s s': Seq.seq S32.t) (pos: nat) (c: bool)
  : Lemma (requires Seq.length s == p.k * n /\
                    c == (hint_lo p y i <= m && m < hint_hi p y i) /\
                    pos == i * n + S8.v (Seq.index y m) /\ pos < p.k * n /\
                    s' == Seq.upd s pos (if c then S32.classify 1ul else Seq.index s pos))
          (ensures hint_view s' == hint_scatter_step p y i m (hint_view s))
  = if c then view_upd s pos (S32.classify 1ul)
    else Seq.lemma_eq_intro s' s

let pos_bound (k: pos) (i: nat { i < k }) (b: nat { b < n })
  : Lemma (i * n + b < k * n /\ i * n + b < 8 * 256 \/ k > 8)
  = Math.lemma_mult_le_right n (i + 1) k

let view_zeros (s: Seq.seq S32.t) (m: nat)
  : Lemma (requires Seq.length s == m /\ (forall (w: nat). w < m ==> S32.v (Seq.index s w) == 0))
          (ensures hint_view s == Seq.create m false)
  = Seq.lemma_eq_intro (hint_view s) (Seq.create m false)

let unpack_result (p: params) (vy: Seq.lseq S8.t (hint_len p)) (v: Seq.seq S32.t) (ok: bool)
  : Lemma (requires Seq.length v == p.k * n /\ hint_view v == hint_scatter p vy /\
                    (ok <==> hint_pack p (hint_view v) == vy))
          (ensures hint_unpack p vy == (if ok then Some (hint_view v) else None))
  = ()

let seq_eq_upto (#a: Type) (s1 s2: Seq.seq a) (m: nat) : prop
  = m <= Seq.length s1 /\ m <= Seq.length s2 /\
    (forall (w: nat). w < m ==> Seq.index s1 w == Seq.index s2 w)

let seq_eq_step (s1 s2: Seq.seq S8.t) (m: nat) (o e: bool)
  : Lemma (requires m < Seq.length s1 /\ m < Seq.length s2 /\
                    (o <==> seq_eq_upto s1 s2 m) /\
                    (e <==> S8.v (Seq.index s1 m) == S8.v (Seq.index s2 m)))
          (ensures (o && e) <==> seq_eq_upto s1 s2 (m + 1))
  = if e then S8.v_extensional (Seq.index s1 m) (Seq.index s2 m)

let seq_eq_done (s1 s2: Seq.seq S8.t)
  : Lemma (requires Seq.length s1 == Seq.length s2)
          (ensures seq_eq_upto s1 s2 (Seq.length s1) <==> s1 == s2)
  = let aux () : Lemma (requires seq_eq_upto s1 s2 (Seq.length s1)) (ensures s1 == s2)
      = Seq.lemma_eq_intro s1 s2 in
    Classical.move_requires aux ()

#push-options "--z3rlimit 200"

fn scatter_poly_impl (h: A.array S32.t) (y: A.array S8.t) (p: erased params)
                     ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                     ([@@@FStar.Attributes.monomorphize] omega: SZ.t) (vi: SZ.t)
                     (#py: perm) (#vh: erased (Seq.seq S32.t)) (#vy: erased (Seq.seq S8.t))
requires A.pts_to h vh ** A.pts_to y #py vy **
         pure (hint_dims p k omega /\ SZ.v vi < p.k /\ Seq.length vh == p.k * n /\
               Seq.length vy == hint_len p /\ hint_bits vh /\
               hint_view vh == scatter_upto p vy (SZ.v vi))
ensures exists* v. A.pts_to h v ** A.pts_to y #py vy **
        pure (Seq.length v == p.k * n /\ hint_bits v /\ Seq.length vy == hint_len p /\
              SZ.v vi < p.k /\
              hint_view v == scatter_poly_upto p vy (SZ.v vi) p.omega (scatter_upto p vy (SZ.v vi)))
{
  A.pts_to_len h;
  A.pts_to_len y;
  HSZ.fits32 ();
  assert_norm (8 * 256 < pow2 32);
  let lo = (if SZ.eq vi 0sz then 0sz else byte_sz A.(y.(SZ.sub (SZ.add omega vi) 1sz)));
  let hi = byte_sz A.(y.(SZ.add omega vi));
  scatter_poly_zero p vy (SZ.v vi) (scatter_upto p vy (SZ.v vi));
  let mut m = 0sz;
  while (let vm = !m; SZ.lt vm omega)
  invariant exists* (vm: SZ.t) (v: Seq.seq S32.t).
    pts_to m vm ** A.pts_to h v ** A.pts_to y #py vy **
    pure (SZ.v vi < p.k /\ SZ.v vm <= p.omega /\ Seq.length v == p.k * n /\
          hint_dims p k omega /\ Seq.length vy == hint_len p /\ hint_bits v /\
          SZ.v lo == hint_lo p vy (SZ.v vi) /\ SZ.v hi == hint_hi p vy (SZ.v vi) /\
          hint_view v == scatter_poly_upto p vy (SZ.v vi) (SZ.v vm) (scatter_upto p vy (SZ.v vi)))
  decreases (p.omega - SZ.v (!m))
  {
    let vm = !m;
    with v. assert (A.pts_to h v);
    let b = byte_sz A.(y.(vm));
    pos_bound p.k (SZ.v vi) (SZ.v b);
    let pos = SZ.add (SZ.mul vi 256sz) b;
    let c = (SZ.lte lo vm && SZ.lt vm hi);
    let cur = A.(h.(pos));
    A.(h.(pos) <- (if c then S32.classify 1ul else cur));
    with v'. assert (A.pts_to h v');
    scatter_one p vy (SZ.v vi) (SZ.v vm) v v' (SZ.v pos) c;
    scatter_poly_next p vy (SZ.v vi) (SZ.v vm) (scatter_upto p vy (SZ.v vi));
    m := SZ.add vm 1sz;
  };
  with vm v2. assert (pts_to m vm ** A.pts_to h v2);
  assert (pure (SZ.v vm == p.omega));
  ()
}

(** [h <- ] the scatter of [y]; [true] iff [y] is a valid hint encoding,
    that is, iff [HintBitUnpack] accepts it. *)
fn hint_unpack_impl (h: A.array S32.t) (y: A.array S8.t) (p: erased params)
                    ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                    (#py: perm) (#vh: erased (Seq.seq S32.t)) (#vy: erased (Seq.seq S8.t))
requires A.pts_to h vh ** A.pts_to y #py vy **
         pure (hint_dims p k omega /\ Seq.length vh == p.k * n /\ Seq.length vy == hint_len p)
returns ok: bool
ensures exists* v. A.pts_to h v ** A.pts_to y #py vy **
        pure (hint_dims p k omega /\ Seq.length v == p.k * n /\ Seq.length vy == hint_len p /\
              hint_bits v /\
              hint_unpack p vy == (if ok then Some (hint_view v) else None))
{
  A.pts_to_len h;
  A.pts_to_len y;
  HSZ.fits32 ();
  assert_norm (8 * 256 < pow2 32);
  SZ.fits_u32_implies_fits (p.k * n);
  SZ.fits_u32_implies_fits (hint_len p);
  let kn = SZ.mul k 256sz;
  let mut t = 0sz;
  while (let vt = !t; SZ.lt vt kn)
  invariant exists* (vt: SZ.t) (v: Seq.seq S32.t).
    pts_to t vt ** A.pts_to h v **
    pure (SZ.v vt <= p.k * n /\ Seq.length v == p.k * n /\
          (forall (w: nat). w < SZ.v vt ==> S32.v (Seq.index v w) == 0))
  decreases (p.k * n - SZ.v (!t))
  {
    let vt = !t;
    A.(h.(vt) <- S32.zero);
    t := SZ.add vt 1sz;
  };
  with v0. assert (A.pts_to h v0);
  view_zeros v0 (p.k * n);
  scatter_upto_zero p vy;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** A.pts_to h v ** A.pts_to y #py vy **
    pure (SZ.v vi <= p.k /\ Seq.length v == p.k * n /\ hint_dims p k omega /\
          Seq.length vy == hint_len p /\ hint_bits v /\
          hint_view v == scatter_upto p vy (SZ.v vi))
  decreases (p.k - SZ.v (!i))
  {
    let vi = !i;
    scatter_poly_impl h y p k omega vi;
    scatter_next p vy (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to h v);
  assert (pure (hint_view v == hint_scatter p vy));
  let len = SZ.add omega k;
  let mut tmp = [| (S8.zero <: S8.t); len |];
  Mem.track tmp;
  hint_pack_impl tmp h p k omega;
  with vt. assert (A.pts_to tmp vt);
  let mut ok = true;
  let mut u = 0sz;
  while (let vu = !u; SZ.lt vu len)
  invariant exists* (vu: SZ.t) (vok: bool).
    pts_to u vu ** pts_to ok vok ** A.pts_to tmp vt ** A.pts_to y #py vy **
    pure (SZ.v vu <= hint_len p /\ Seq.length vt == hint_len p /\ Seq.length vy == hint_len p /\
          (vok <==> seq_eq_upto vt vy (SZ.v vu)))
  decreases (hint_len p - SZ.v (!u))
  {
    let vu = !u;
    let vok = !ok;
    let a = Declassify.u8 A.(tmp.(vu));
    let bb = Declassify.u8 A.(y.(vu));
    seq_eq_step vt vy (SZ.v vu) vok (U8.eq a bb);
    ok := (vok && U8.eq a bb);
    u := SZ.add vu 1sz;
  };
  let r = !ok;
  seq_eq_done vt vy;
  unpack_result p vy v r;
  Mem.wipe tmp len;
  r
}

#pop-options
#pop-options
