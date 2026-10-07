module Spec.Group.Prime

(** Primality of the field primes, by Pocklington certificates.

    [pock n l] checks a certificate for [n]: every entry [(q, a, u)] has
    [q | n - 1], [a^(n-1) = 1 (mod n)] and [(a^((n-1)/q) - 1) * u = 1
    (mod n)]; the [q] are strictly increasing, and the square of their
    product exceeds [n].  If every [q] is prime then so is [n]
    ({!pock_sound}).  Small primes are checked by trial division
    ({!trial_sound}).  The proof avoids multiplicative orders: for a prime
    factor [r] of [n], if [q] does not divide [r - 1] then [q] is invertible
    modulo [r - 1], and Fermat's little theorem then forces
    [a^((n-1)/q) = 1 (mod r)], contradicting the certificate. *)

open FStar.Math.Euclid
module F = FStar.Math.Fermat
module M = FStar.Math.Lemmas
module L = FStar.List.Tot

(** {2 Powers} *)

let rec pow_plus (a: int) (n k: nat)
  : Lemma (ensures F.pow a (n + k) == F.pow a n * F.pow a k) (decreases n)
  = if n = 0 then () else begin
      pow_plus a (n - 1) k;
      M.paren_mul_right a (F.pow a (n - 1)) (F.pow a k)
    end

let rec pow_mul (a: int) (n k: nat)
  : Lemma (ensures F.pow a (n * k) == F.pow (F.pow a n) k) (decreases k)
  = if k = 0 then () else begin
      pow_mul a n (k - 1);
      pow_plus a n (n * (k - 1))
    end

let rec pow_one (k: nat) : Lemma (ensures F.pow 1 k == 1) (decreases k) =
  if k = 0 then () else pow_one (k - 1)

let rec pow_mod_base (a: int) (n: nat) (m: pos)
  : Lemma (ensures F.pow (a % m) n % m == F.pow a n % m) (decreases n)
  = if n = 0 then () else begin
      pow_mod_base a (n - 1) m;
      calc (==) {
        F.pow (a % m) n % m;
        == { }
        ((a % m) * F.pow (a % m) (n - 1)) % m;
        == { M.lemma_mod_mul_distr_r (a % m) (F.pow (a % m) (n - 1)) m }
        ((a % m) * (F.pow (a % m) (n - 1) % m)) % m;
        == { }
        ((a % m) * (F.pow a (n - 1) % m)) % m;
        == { M.lemma_mod_mul_distr_r (a % m) (F.pow a (n - 1)) m }
        ((a % m) * F.pow a (n - 1)) % m;
        == { M.lemma_mod_mul_distr_l a (F.pow a (n - 1)) m }
        (a * F.pow a (n - 1)) % m;
      }
    end

(** Square-and-multiply, for use by the normalizer. *)
let rec pow_mod (a: nat) (n: nat) (m: pos) : Tot nat (decreases n) =
  if n = 0 then 1 % m
  else
    let h = pow_mod a (n / 2) m in
    let h2 = (h * h) % m in
    if n % 2 = 0 then h2 else (h2 * a) % m

let rec pow_mod_lemma (a: nat) (n: nat) (m: pos)
  : Lemma (ensures pow_mod a n m == F.pow a n % m) (decreases n)
  = if n = 0 then () else begin
      let k = n / 2 in
      pow_mod_lemma a k m;
      let h = pow_mod a k m in
      let pk = F.pow a k in
      assert (h == pk % m);
      pow_plus a k k;
      calc (==) {
        (h * h) % m;
        == { M.lemma_mod_mul_distr_l pk h m }
        (pk * h) % m;
        == { M.lemma_mod_mul_distr_r pk pk m }
        (pk * pk) % m;
        == { }
        F.pow a (k + k) % m;
      };
      if n % 2 = 0 then assert (n == k + k)
      else begin
        assert (n == (k + k) + 1);
        pow_plus a (k + k) 1;
        M.lemma_mod_mul_distr_l (F.pow a (k + k)) a m;
        M.lemma_mod_mul_distr_l (pk * pk) a m
      end
    end

(** {2 Divisibility helpers} *)

let mod_of_mod_divisor (x: int) (n: pos) (r: pos)
  : Lemma (requires n % r = 0) (ensures (x % n) % r == x % r)
  = let j = n / r in
    M.lemma_div_mod n r;
    assert (n == j * r);
    M.lemma_div_mod x n;
    M.paren_mul_right (x / n) j r;
    M.lemma_mod_plus (x % n) ((x / n) * j) r

let divisor_le (e: int) (r: pos)
  : Lemma (requires e `divides` r /\ e > 0) (ensures e <= r)
  = eliminate exists q. r = q * e
    with (if q <= 0 then M.lemma_mult_le_right e q 0 else M.lemma_mult_le_right e 1 q)

let divides_mod0 (e: int) (n: pos)
  : Lemma (requires e `divides` n /\ e > 0) (ensures n % e = 0)
  = divides_mod n e

(** {2 The least divisor} *)

let rec least_div (n: int { n > 1 }) (d: int { 1 < d /\ d <= n /\ (forall (e: int). 1 < e /\ e < d ==> n % e <> 0) })
  : Tot (r: int { 1 < r /\ r <= n /\ n % r = 0 /\ (forall (e: int). 1 < e /\ e < r ==> n % e <> 0) })
        (decreases n - d)
  = if n % d = 0 then d else least_div n (d + 1)

let least_prime (n: int { n > 1 }) (r: int)
  : Lemma (requires 1 < r /\ r <= n /\ n % r = 0 /\ (forall (e: int). 1 < e /\ e < r ==> n % e <> 0))
          (ensures is_prime r)
  = let aux (d: int) : Lemma (requires d `divides` r) (ensures d = 1 \/ d = -1 \/ d = r \/ d = -r) =
      let e = if d >= 0 then d else -d in
      if d < 0 then divides_opp d r;
      assert (e `divides` r);
      if e = 0 then (eliminate exists q. r = q * e with ())
      else begin
        divisor_le e r;
        mod_divides n r;
        divides_transitive e r n;
        divides_mod0 e n
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let small_factor (n: int { n > 1 })
  : Lemma (requires ~(is_prime n))
          (ensures exists (r: int). is_prime r /\ r * r <= n /\ n % r = 0)
  = let r = least_div n 2 in
    least_prime n r;
    if r = n then least_prime n n
    else begin
      let k = n / r in
      M.lemma_div_mod n r;
      assert (n == r * k);
      assert (k > 1);
      M.lemma_mod_mul_distr_l r k k;
      M.cancel_mul_mod r k;
      assert (n % k = 0);
      assert (k >= r);
      M.lemma_mult_le_left r r k
    end

(** {2 Trial division} *)

let rec trial (n: pos) (d: pos) : Tot bool (decreases (n + 1) - d) =
  if d * d > n then true
  else if d > n then true
  else if n % d = 0 then false
  else trial n (d + 1)

let rec trial_no (n: pos) (d: pos) (r: int)
  : Lemma (requires trial n d /\ 2 <= d /\ d <= r /\ r * r <= n /\ n % r = 0)
          (ensures False) (decreases (n + 1) - d)
  = M.lemma_mult_le_left d d r; M.lemma_mult_le_right r d r;
    if d = r then () else trial_no n (d + 1) r

let trial_sound (n: pos)
  : Lemma (requires n > 1 /\ trial n 2) (ensures is_prime n)
  = let aux () : Lemma (requires ~(is_prime n)) (ensures False) =
      small_factor n;
      eliminate exists (r: int). is_prime r /\ r * r <= n /\ n % r = 0
      with trial_no n 2 r
    in
    FStar.Classical.move_requires aux ()

(** {2 Pocklington} *)

type entry = nat & nat & nat

let step (n: pos) (e: entry) : bool =
  let (q, a, u) = e in
  q > 1 && (n - 1) % q = 0 && pow_mod a (n - 1) n = 1 &&
  ((pow_mod a ((n - 1) / q) n + (n - 1)) * u) % n = 1

let rec steps (n: pos) (l: list entry) : bool =
  match l with [] -> true | e :: t -> step n e && steps n t

let rec prod (l: list entry) : pos =
  match l with [] -> 1 | (q, _, _) :: t -> (if q = 0 then 1 else q) * prod t

let rec all_gt (q: nat) (l: list entry) : bool =
  match l with [] -> true | (q', _, _) :: t -> q' > q && all_gt q t

let rec sorted (l: list entry) : bool =
  match l with [] -> true | (q, _, _) :: t -> all_gt q t && sorted t

let rec all_prime (l: list entry) : prop =
  match l with [] -> True | (q, _, _) :: t -> is_prime q /\ all_prime t

let pock (n: pos) (l: list entry) : bool =
  n > 1 && steps n l && sorted l && prod l * prod l > n

(** Fermat, in the periodic form. *)
let pow_period (a: int) (x: nat) (r: int)
  : Lemma (requires is_prime r /\ a % r <> 0)
          (ensures F.pow a x % r == F.pow a (x % (r - 1)) % r)
  = let k = x / (r - 1) in
    let s = x % (r - 1) in
    M.lemma_div_mod x (r - 1);
    M.swap_mul (r - 1) k;
    pow_plus a ((r - 1) * k) s;
    pow_mul a (r - 1) k;
    F.fermat_alt r a;
    pow_mod_base (F.pow a (r - 1)) k r;
    pow_one k;
    M.lemma_mod_mul_distr_l (F.pow (F.pow a (r - 1)) k) (F.pow a s) r

let unit_of_pow (a: int) (k: pos) (r: int)
  : Lemma (requires r > 1 /\ F.pow a k % r == 1) (ensures a % r <> 0)
  = if a % r = 0 then begin
      pow_mod_base a k r;
      assert (F.pow 0 k == 0 * F.pow 0 (k - 1))
    end

let inv_mod (q: int) (r: int)
  : Pure nat (requires is_prime q /\ r >= 2 /\ (r - 1) % q <> 0)
             (ensures fun t -> (t * q) % (r - 1) == 1 % (r - 1))
  = let s = (r - 1) % q in
    let (x, y) = bezout_prime q s in
    let kq = (r - 1) / q in
    M.lemma_div_mod (r - 1) q;
    let t0 = x - y * kq in
    M.distributivity_sub_left x (y * kq) q;
    M.paren_mul_right y kq q;
    M.swap_mul kq q;
    assert (t0 * q + y * (r - 1) == 1);
    let t = t0 % (r - 1) in
    M.lemma_mod_mul_distr_l t0 q (r - 1);
    M.lemma_mod_plus (t0 * q) y (r - 1);
    t

let pow_reduce (a: int) (mm q t: nat) (r: int)
  : Lemma (requires is_prime r /\ a % r <> 0 /\ F.pow a (q * mm) % r == 1 /\
                    (t * q) % (r - 1) == 1 % (r - 1))
          (ensures F.pow a mm % r == 1)
  = M.lemma_mod_mul_distr_r mm (t * q) (r - 1);
    M.lemma_mod_mul_distr_r mm 1 (r - 1);
    assert ((mm * (t * q)) % (r - 1) == mm % (r - 1));
    pow_period a mm r;
    pow_period a (mm * (t * q)) r;
    M.paren_mul_right mm t q; M.swap_mul mm t; M.paren_mul_right t mm q;
    M.swap_mul mm q; M.swap_mul t (q * mm);
    assert (mm * (t * q) == (q * mm) * t);
    pow_mul a (q * mm) t;
    pow_mod_base (F.pow a (q * mm)) t r;
    pow_one t

let cert_contra (w: int) (n: pos) (u: int) (r: int)
  : Lemma (requires r > 1 /\ n % r = 0 /\ w % r == 1 /\ ((w + (n - 1)) * u) % n = 1)
          (ensures False)
  = mod_of_mod_divisor ((w + (n - 1)) * u) n r;
    M.lemma_mod_mul_distr_l (w + (n - 1)) u r;
    M.lemma_mod_plus_distr_l w (n - 1) r;
    M.lemma_mod_plus_distr_l n (-1) r;
    assert ((w + (n - 1)) % r == 0)

let step_divides (n: pos) (q a u: nat) (r: int)
  : Lemma (requires step n (q, a, u) /\ is_prime q /\ is_prime r /\ n % r = 0)
          (ensures (r - 1) % q = 0)
  = if (r - 1) % q <> 0 then begin
      let mm = (n - 1) / q in
      M.lemma_div_mod (n - 1) q;
      assert (n - 1 == q * mm);
      pow_mod_lemma a (n - 1) n;
      mod_of_mod_divisor (F.pow a (n - 1)) n r;
      assert (F.pow a (n - 1) % r == 1);
      unit_of_pow a (n - 1) r;
      let t = inv_mod q r in
      pow_reduce a mm q t r;
      pow_mod_lemma a mm n;
      mod_of_mod_divisor (F.pow a mm) n r;
      cert_contra (pow_mod a mm n) n u r
    end

let rec all_div (k: int) (l: list entry) : prop =
  match l with [] -> True | (q, _, _) :: t -> q > 0 /\ k % q = 0 /\ all_div k t

let rec steps_divides (n: pos) (l: list entry) (r: int)
  : Lemma (requires steps n l /\ all_prime l /\ is_prime r /\ n % r = 0)
          (ensures all_div (r - 1) l)
  = match l with
    | [] -> ()
    | (q, a, u) :: t -> step_divides n q a u r; steps_divides n t r

let rec gt_not_div (q: int) (l: list entry)
  : Lemma (requires is_prime q /\ all_gt q l /\ all_prime l) (ensures prod l % q <> 0)
  = match l with
    | [] -> ()
    | (q', _, _) :: t ->
      gt_not_div q t;
      if (q' * prod t) % q = 0 then begin
        euclid_prime q q' (prod t);
        mod_divides q' q
      end

let rec prod_divides (l: list entry) (k: pos)
  : Lemma (requires sorted l /\ all_prime l /\
                    all_div k l)
          (ensures k % prod l = 0)
  = match l with
    | [] -> ()
    | (q, a, u) :: t ->
      prod_divides t k;
      gt_not_div q t;
      let p = prod t in
      let j = k / p in
      M.lemma_div_mod k p;
      assert (k == p * j);
      euclid_prime q p j;
      let i = j / q in
      M.lemma_div_mod j q;
      assert (k == p * (q * i));
      M.paren_mul_right p q i;
      M.swap_mul p q;
      M.cancel_mul_mod i (q * p)

#push-options "--z3rlimit 20"
let pock_sound (n: pos) (l: list entry)
  : Lemma (requires pock n l /\ all_prime l) (ensures is_prime n)
  = let aux () : Lemma (requires ~(is_prime n)) (ensures False) =
      small_factor n;
      eliminate exists (r: int). is_prime r /\ r * r <= n /\ n % r = 0
      with begin
        steps_divides n l r;
        prod_divides l (r - 1);
        let f = prod l in
        M.lemma_div_mod (r - 1) f;
        assert ((r - 1) / f >= 1);
        M.lemma_mult_le_left f 1 ((r - 1) / f);
        assert (f <= r - 1);
        M.lemma_mult_le_left f f (r - 1);
        M.lemma_mult_le_right (r - 1) f (r - 1)
      end
    in
    FStar.Classical.move_requires aux ()
#pop-options

let all_prime_nil () : Lemma (all_prime []) = ()

let all_prime_cons (q a u: nat) (t: list entry)
  : Lemma (requires is_prime q /\ all_prime t) (ensures all_prime ((q, a, u) :: t))
  = ()
