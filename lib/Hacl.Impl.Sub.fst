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

(** Handing a window of an array to a function that wants a whole one.

    Ed25519 keeps a signature as sixty-four bytes and signs with the first
    thirty-two and the last thirty-two; HKDF builds one message buffer and
    hashes a suffix of it.  Neither wants to copy, and neither function being
    called should have to learn about offsets, so what is needed is a way to
    say "these thirty-two bytes, on their own" and then take it back.

    Pulse's array library has the pieces -- [gsub] names the window, [sub]
    hands out a pointer to it, and the mask machinery tracks which cells you
    still hold.  This module glues them into the bracket the callers actually
    want: {!sub} gives back an array carrying a plain [pts_to], plus a {!rest}
    token standing for everything outside the window, and {!unsub} trades the
    two back for a [pts_to] on the original.

    In C this is pointer arithmetic and nothing else: [sub a i j] is [a + i]
    and {!unsub} is not emitted at all. *)
module Hacl.Impl.Sub

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq

(** The mask machinery works on sequences of [option t] -- [None] where the
    permission has been lent out.  Before anything is lent out, every cell is
    [Some]. *)
let opt (#t: Type0) (v: Seq.seq t) : Seq.seq (option t) =
  Seq.init (Seq.length v) (fun k -> Some (Seq.index v k))

let opt_len (#t: Type0) (v: Seq.seq t)
  : Lemma (Seq.length (opt v) == Seq.length v) [SMTPat (Seq.length (opt v))]
  = ()

let opt_index (#t: Type0) (v: Seq.seq t) (k: nat { k < Seq.length v })
  : Lemma (Seq.index (opt v) k == Some (Seq.index v k)) [SMTPat (Seq.index (opt v) k)]
  = ()

(** Everything of [a] except the window [[i, j)]: the same cells, with the
    window's permission subtracted. *)
let rest (#t: Type0) (a: A.array t) (p: perm) (i j: nat) (v: Seq.seq t) : slprop =
  A.pts_to_mask a #p (opt v) (fun k -> ~(i <= k /\ k < j))

(** [a[i .. j)] as an array of its own, plus a receipt for the remainder.

    [inline_for_extraction] is not a performance hint, it is what makes the
    paragraph above true.  Left as a real C function this is monomorphized
    once per element type, and a monomorphization is a shared function that
    the extraction may stamp with the [target] attribute of an unrelated
    caller: the [uint32] instance came out carrying
    [target("aes,pclmul,ssse3,sse4.1")] although its only callers are
    SHA-256's.  clang will not inline a callee whose target features are not
    a subset of the caller's, so every [a + i] in the SHA-EXT block function
    became a real call -- thirty-nine of them per block, and three quarters
    of the running time.  Inlined, there is no function to mislabel. *)
inline_for_extraction
fn sub (#t: Type0) (a: A.array t) (#p: perm) (i: SZ.t) (j: SZ.t)
       (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v /\
                                 Seq.length v == A.length a })
requires A.pts_to a #p v
returns b: A.array t
ensures rewrites_to b (A.gsub a (SZ.v i) (SZ.v j))
ensures A.pts_to b #p (Seq.slice v (SZ.v i) (SZ.v j)) **
        rest a p (SZ.v i) (SZ.v j) v
{
  A.pts_to_len a;
  A.to_mask a;
  with s. assert (A.pts_to_mask a #p s (fun _ -> True));
  A.mask_ext a (opt v) (fun _ -> True);
  let b = A.sub a i (hide (SZ.v j));
  A.mask_mext b (fun _ -> True);
  A.from_mask b;
  with w. assert (A.pts_to b #p w);
  assert (pure (Seq.equal w (Seq.slice v (SZ.v i) (SZ.v j))));
  A.mask_mext a (fun k -> ~(SZ.v i <= k /\ k < SZ.v j));
  fold (rest a p (SZ.v i) (SZ.v j) v);
  b
}

(** Give the window back.  [v'] is what the callee left in it, so the original
    array now holds [v] with [[i, j)] overwritten. *)
ghost fn unsub (#t: Type0) (a: A.array t) (#p: perm)
               (i: nat) (j: nat { i <= j /\ j <= A.length a })
               (b: A.array t { b == A.gsub a i j })
               (#v: erased (Seq.seq t)) (#v': erased (Seq.seq t))
requires rest a p i j v ** A.pts_to b #p v' **
         pure (Seq.length v == A.length a /\ Seq.length v' == j - i)
ensures exists* (w: Seq.seq t).
  A.pts_to a #p w **
  pure (Seq.length w == Seq.length v /\ Seq.length v' == j - i /\
        (forall (k: nat). k < Seq.length w ==>
           Seq.index w k == (if i <= k && k < j
                             then Seq.index v' (k - i)
                             else Seq.index v k)))
{
  unfold (rest a p i j v);
  A.pts_to_mask_len a;
  rewrite each b as A.gsub a i j;
  A.to_mask (A.gsub a i j);
  A.return_sub a;
  with s. assert (A.pts_to_mask a #p s (fun k -> ~(i <= k /\ k < j) \/
                                                 (i <= k /\ k < j /\ (fun _ -> True) (k - i))));
  A.mask_mext a (fun _ -> True);
  A.from_mask a;
}

(** The common case: the callee only read the window, so the array comes back
    exactly as it went in.  Doing the pointwise-to-[Seq.equal] step here, once,
    keeps it out of every caller's proof context. *)
ghost fn unsub_id (#t: Type0) (a: A.array t) (#p: perm)
                  (i: nat) (j: nat { i <= j /\ j <= A.length a })
                  (b: A.array t { b == A.gsub a i j })
                  (#v: erased (Seq.seq t) { Seq.length v == A.length a })
requires rest a p i j v ** A.pts_to b #p (Seq.slice v i j)
ensures A.pts_to a #p v
{
  unsub a i j b;
  with w. assert (A.pts_to a #p w);
  assert (pure (Seq.equal w v));
  ()
}
