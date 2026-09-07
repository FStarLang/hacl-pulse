(**
   Bounded iteration combinators used to give specifications a shape that
   matches an imperative [while] loop.

   [repeati n f acc] unfolds on the *right*:

     repeati (i + 1) f acc == f i (repeati i f acc)

   which is exactly the step a forward counting loop takes.  A Pulse loop whose
   invariant is [state == repeati i f acc0] therefore discharges its body
   obligation by [unfold_repeati], with no extra reasoning.
*)
module Hacl.Spec.Loops

module Seq = FStar.Seq

let rec repeati (#a: Type) (n: nat) (f: (i: nat -> a -> a)) (acc: a)
  : Tot a (decreases n)
  = if n = 0 then acc else f (n - 1) (repeati (n - 1) f acc)

let unfold_repeati (#a: Type) (n: nat) (f: (i: nat -> a -> a)) (acc: a)
  : Lemma (repeati (n + 1) f acc == f n (repeati n f acc))
  = ()

let repeati_zero (#a: Type) (f: (i: nat -> a -> a)) (acc: a)
  : Lemma (repeati 0 f acc == acc)
  = ()

(** [repeati] restricted to a range, phrased as an offset of [repeati]. *)
let repeat_from (#a: Type) (lo: nat) (n: nat) (f: (i: nat -> a -> a)) (acc: a) : a =
  repeati n (fun i x -> f (lo + i) x) acc

(** The same, for a step that is only ghostly computable -- which is what a
    specification written over [Hacl.Secret.Word.of_v] ends up being. *)
let rec repeati_g (#a: Type) (n: nat) (f: (i: nat -> a -> GTot a)) (acc: a)
  : GTot a (decreases n)
  = if n = 0 then acc else f (n - 1) (repeati_g (n - 1) f acc)

let unfold_repeati_g (#a: Type) (n: nat) (f: (i: nat -> a -> GTot a)) (acc: a)
  : Lemma (repeati_g (n + 1) f acc == f n (repeati_g n f acc))
  = ()

(** Splitting an iteration in two, which is what lets an implementation run the
    message blocks and the padding blocks in separate loops while the
    specification remains a single fold. *)
let rec repeati_g_split (#a: Type) (m: nat) (n: nat { m <= n }) (f: (i: nat -> a -> GTot a)) (acc: a)
  : Lemma (ensures repeati_g n f acc == repeati_g (n - m) (fun i x -> f (m + i) x) (repeati_g m f acc))
          (decreases (n - m))
  = if n = m then () else repeati_g_split m (n - 1) f acc

let repeati_g_zero (#a: Type) (f: (i: nat -> a -> GTot a)) (acc: a)
  : Lemma (repeati_g 0 f acc == acc)
  = ()
