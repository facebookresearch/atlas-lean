/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Nat Real Filter Asymptotics Finset

noncomputable section

/-- A natural number `n` is `B`-smooth if all of its prime factors are at most `B`,
i.e. `n ∈ Nat.smoothNumbers (B + 1)`. Smoothness is the key notion underlying
subexponential factoring algorithms. -/
def IsSmooth (B : ℕ) (n : ℕ) : Prop := n ∈ Nat.smoothNumbers (B + 1)

/-- `B`-smoothness is decidable: it reduces to deciding membership of `n` in the
finite-indexed set `Nat.smoothNumbers (B + 1)`. -/
instance (B n : ℕ) : Decidable (IsSmooth B n) :=
  inferInstanceAs (Decidable (n ∈ Nat.smoothNumbers (B + 1)))

/-- Unfolded characterization of smoothness: `IsSmooth B n` iff `n ≠ 0` and every
prime factor of `n` is at most `B`. -/
theorem isSmooth_iff {B n : ℕ} :
    IsSmooth B n ↔ n ≠ 0 ∧ ∀ p ∈ n.primeFactorsList, p ≤ B := by
  simp only [IsSmooth, Nat.smoothNumbers, Set.mem_setOf_eq, Nat.lt_add_one_iff]

/-- The count `Ψ(x, y)`: the number of `⌊y⌋`-smooth positive integers up to `⌊x⌋`. -/
def smoothCount (x y : ℝ) : ℕ :=
  (Nat.smoothNumbersUpTo (⌊x⌋₊) (⌊y⌋₊ + 1)).card

/-- The Canfield–Erdős–Pomerance filter on `(u, x)`: pairs going to infinity
constrained by `u < (1 - ε) · log x / log log x`. Used to state the CEP asymptotic. -/
def cepFilter (ε : ℝ) : Filter (ℝ × ℝ) :=
  (atTop ×ˢ atTop) ⊓
    Filter.principal {p : ℝ × ℝ | p.1 < (1 - ε) * Real.log p.2 / Real.log (Real.log p.2)}


end

/-- The factor base of bound `B`: the finset of primes `q ≤ B`. -/
def factorBase (B : ℕ) : Finset ℕ :=
  Nat.primesBelow (B + 1)

/-- Membership in the factor base: `q ∈ factorBase B` iff `q ≤ B` and `q` is prime. -/
theorem mem_factorBase_iff {q B : ℕ} :
    q ∈ factorBase B ↔ q ≤ B ∧ q.Prime := by
  simp only [factorBase, Nat.mem_primesBelow, Nat.lt_add_one_iff]

section DiscreteLog

variable {G : Type*} [CommGroup G]
  {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
  {n : ℕ} (hn : Nat.card G = n)

/-- The discrete logarithm of `β ∈ G` to base `g` (where `g` generates the cyclic
group of order `n`), valued in `ZMod n`. Built by transporting through the
isomorphism `G ≃ Multiplicative (ZMod n)` induced by the generator. -/
noncomputable def dlog (β : G) : ZMod n :=
  Multiplicative.toAdd ((zmodMulEquivOfGenerator hg hn).symm β)

/-- The discrete log is a homomorphism on products: `dlog(xy) = dlog x + dlog y`. -/
theorem dlog_mul (x y : G) :
    dlog hg hn (x * y) = dlog hg hn x + dlog hg hn y := by
  simp only [dlog, map_mul]; rfl

/-- The discrete log sends inverses to negatives: `dlog(x⁻¹) = -dlog x`. -/
theorem dlog_inv (x : G) :
    dlog hg hn x⁻¹ = -dlog hg hn x := by
  simp only [dlog, map_inv]; rfl

/-- The discrete log of `g^i` is `i` modulo `n`. -/
theorem dlog_zpow_g (i : ℤ) :
    dlog hg hn (g ^ i) = (i : ZMod n) := by
  simp [dlog, zmodMulEquivOfGenerator_symm_apply_zpow]

/-- The discrete log is ℤ-linear on integer powers: `dlog(x^k) = k · dlog x`. -/
theorem dlog_zpow (x : G) (k : ℤ) :
    dlog hg hn (x ^ k) = (k : ZMod n) * dlog hg hn x := by
  unfold dlog
  rw [map_zpow]
  show (k : ℤ) • (Multiplicative.toAdd ((zmodMulEquivOfGenerator hg hn).symm x)) = _
  simp [zsmul_eq_mul]

/-- Additivity of discrete log over a finite product:
`dlog(∏_{q ∈ S} f q) = ∑_{q ∈ S} dlog (f q)`. -/
theorem dlog_prod (S : Finset ℕ) (f : ℕ → G) :
    dlog hg hn (∏ q ∈ S, f q) = ∑ q ∈ S, dlog hg hn (f q) := by
  induction S using Finset.induction_on with
  | empty => simp [dlog, map_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, dlog_mul, Finset.sum_insert ha, ih]

/-- The discrete log of the generator is `1 ∈ ZMod n`. -/
theorem dlog_generator : dlog hg hn g = (1 : ZMod n) := by
  have := dlog_zpow_g hg hn (1 : ℤ)
  simp at this
  exact this

/-- The discrete log of the identity is `0 ∈ ZMod n`. -/
theorem dlog_one : dlog hg hn (1 : G) = (0 : ZMod n) := by
  have := dlog_zpow_g hg hn (0 : ℤ)
  simp at this
  exact this

end DiscreteLog

/-- Index-calculus relation: if `g^e · b⁻¹ = ∏ f(q)^{exps q}` over a factor base,
then in `ZMod n` (`n = |G|`) the discrete logs satisfy
`∑ exps q · dlog(f q) + dlog b = e`. This is the linear equation collected
during the index-calculus discrete log algorithm. -/
theorem index_calculus_relation {G : Type*} [CommGroup G]
    {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    {n : ℕ} (hn : Nat.card G = n)
    (S : Finset ℕ) (f : ℕ → G) (exps : ℕ → ℤ) (b : G) (e : ℤ)
    (hfact : g ^ e * b⁻¹ = ∏ q ∈ S, f q ^ exps q) :
    (∑ q ∈ S, (exps q : ZMod n) * dlog hg hn (f q)) + dlog hg hn b = (e : ZMod n) := by
  have h1 : dlog hg hn (g ^ e * b⁻¹) = dlog hg hn (∏ q ∈ S, f q ^ exps q) := by
    rw [hfact]
  rw [dlog_mul, dlog_inv, dlog_zpow_g, dlog_prod] at h1
  simp_rw [dlog_zpow] at h1
  have h2 : (e : ZMod n) = (∑ x ∈ S, ↑(exps x) * dlog hg hn (f x)) + dlog hg hn b := by
    rw [← h1]; ring
  exact h2.symm

/-- A single relation collected during index calculus with smoothness bound `B`:
records the exponent on the generator and the exponent vector over the factor
base (supported within `factorBase B`). -/
structure IndexCalculusRelation (B : ℕ) where
  exponent : ℤ
  factorExponents : ℕ → ℤ
  support_subset : ∀ q, factorExponents q ≠ 0 → q ∈ factorBase B

/-- Configuration parameters for index calculus modulo a prime `p`: the prime
`p`, its primality witness, the smoothness bound `B`, and the group order
`N = p - 1`. -/
structure IndexCalculusConfig where
  p : ℕ
  hp : Nat.Prime p
  B : ℕ
  N : ℕ := p - 1

/-- The factor base associated with an index-calculus configuration. -/
def IndexCalculusConfig.factorBaseSet (cfg : IndexCalculusConfig) : Finset ℕ :=
  factorBase cfg.B

/-- Size of the factor base in the configuration. -/
def IndexCalculusConfig.factorBaseSize (cfg : IndexCalculusConfig) : ℕ :=
  cfg.factorBaseSet.card

/-- Number of relations needed to solve the linear system in index calculus:
factor-base size plus one. -/
def IndexCalculusConfig.relationsNeeded (cfg : IndexCalculusConfig) : ℕ :=
  cfg.factorBaseSize + 1

/-- Validity of a recorded relation in a group `G` with generator `g` and
factor-base lift `f`: the equation `g^{exponent} · b⁻¹ = ∏ f(q)^{factorExponents q}`
holds. -/
def IndexCalculusRelation.IsValid {G : Type*} [CommGroup G]
    (R : IndexCalculusRelation B) (g b : G) (f : ℕ → G) : Prop :=
  g ^ R.exponent * b⁻¹ = ∏ q ∈ factorBase B, f q ^ R.factorExponents q

namespace PollardPM1

open Nat Finset

/-- Pollard p−1 smooth exponent: the product `∏_{ℓ ≤ B prime} ℓ^{⌈log_ℓ N⌉}`,
guaranteed to be divisible by every `B`-smooth integer up to `N`. -/
def smoothExponent (N B : ℕ) : ℕ :=
  (Nat.primesBelow (B + 1)).prod (fun ℓ => ℓ ^ Nat.clog ℓ N)

/-- Local definition of `B`-smoothness used in the Pollard p−1 analysis:
`n ≠ 0` and every prime factor is at most `B`. -/
def IsBSmooth (B n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p ∈ n.primeFactorsList, p ≤ B

/-- The largest prime factor of `n`, taken to be `0` if `n` has no prime factors. -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldl max 0

/-- Pollard p−1 factoring step: computes `gcd(a^m - 1, N)` for the smooth
exponent `m = smoothExponent N B`. Returns a nontrivial factor of `N` if one
is found by either `gcd(a, N)` or `gcd(a^m - 1, N)`. -/
noncomputable def pollardPM1 (N B a : ℕ) : Option ℕ :=
  let d₁ := Nat.gcd a N
  if 1 < d₁ ∧ d₁ < N then some d₁
  else
    let m := smoothExponent N B
    let b := a ^ m % N
    let d₂ := Nat.gcd (b - 1) N
    if 1 < d₂ ∧ d₂ < N then some d₂
    else none

/-- One stage of Pollard p−1: raise `b` to `ℓ^e` modulo `N`. -/
def pollardStep (N ℓ e b : ℕ) : ℕ := b ^ (ℓ ^ e) % N

/-- The initial accumulator is bounded by any `List.foldl max` outcome. -/
lemma le_foldl_max_init {l : List ℕ} {init : ℕ} :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    exact le_trans (le_max_left init x) ih

/-- Every element of the list is bounded by the `foldl max` of the list. -/
lemma le_foldl_max_of_mem_list {l : List ℕ} {x : ℕ} (hx : x ∈ l) (init : ℕ) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons head tail ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_trans (le_max_right init x) le_foldl_max_init
    · exact ih hx' _

/-- For nonzero `n`, `n` is automatically `largestPrimeFactor n`-smooth. -/
lemma isBSmooth_largestPrimeFactor {n : ℕ} (hn : n ≠ 0) :
    IsBSmooth (largestPrimeFactor n) n :=
  ⟨hn, fun _p hp => le_foldl_max_of_mem_list hp 0⟩

/-- If the initial accumulator and all list elements are `≤ B`, then so is
`List.foldl max init l`. -/
lemma foldl_max_le_of_init_and_elems {l : List ℕ} {init B : ℕ}
    (hinit : init ≤ B) (h : ∀ x ∈ l, x ≤ B) :
    l.foldl max init ≤ B := by
  induction l generalizing init with
  | nil => simpa [List.foldl]
  | cons a as ih =>
    simp only [List.foldl]
    have ha : a ≤ B := h a List.mem_cons_self
    apply ih (max_le hinit ha)
    intro x hx
    exact h x (List.mem_cons_of_mem a hx)

/-- For `q > 1` and nonzero `n < N`, the `q`-adic valuation of `n` is at most
`clog q N`. Used to bound prime-power factors of smooth `n`. -/
lemma factorization_le_clog {q n N : ℕ} (hq : 1 < q) (hn : n ≠ 0) (hnN : n < N) :
    n.factorization q ≤ Nat.clog q N := by
  have h1 := Nat.ordProj_dvd n q
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
  exact le_of_lt ((Nat.lt_clog_iff_pow_lt hq).mpr (lt_of_le_of_lt h2 hnN))

/-- The smooth exponent `smoothExponent N B` is positive. -/
lemma smoothExponent_pos (N B : ℕ) : 0 < smoothExponent N B := by
  unfold smoothExponent
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.Prime.pos (Nat.mem_primesBelow.mp hℓ).2).ne')

/-- A prime `q > B` does not divide `smoothExponent N B`, since the smooth
exponent only uses primes `ℓ ≤ B`. -/
lemma prime_not_dvd_smoothExponent {q N B : ℕ} (hq : Nat.Prime q) (hqB : B < q) :
    ¬(q ∣ smoothExponent N B) := by
  unfold smoothExponent
  apply hq.prime.not_dvd_finset_prod (g := fun ℓ => ℓ ^ Nat.clog ℓ N)
  intro ℓ hℓ
  rw [Nat.mem_primesBelow] at hℓ
  intro h_dvd
  have hℓq : ℓ ≠ q := by omega
  have hq_dvd_ℓ : q ∣ ℓ := hq.prime.dvd_of_dvd_pow h_dvd
  rcases hℓ.2.eq_one_or_self_of_dvd q hq_dvd_ℓ with h | h
  · exact hq.ne_one h
  · exact hℓq h.symm

/-- Key divisibility lemma for Pollard p−1: any `B`-smooth `n < N` divides
`smoothExponent N B`. -/
theorem dvd_smoothExponent_of_isBSmooth {n N B : ℕ} (hsmooth : IsBSmooth B n) (hnN : n < N) :
    n ∣ smoothExponent N B := by
  rw [← Nat.factorization_le_iff_dvd hsmooth.1 (smoothExponent_pos N B).ne']
  rw [Finsupp.le_iff]
  intro q hq_supp
  rw [Nat.support_factorization] at hq_supp
  have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_supp
  have hqB : q ≤ B := by
    rw [Nat.mem_primeFactors_iff_mem_primeFactorsList] at hq_supp
    exact hsmooth.2 q hq_supp
  have h_dvd : q ^ (Nat.clog q N) ∣ smoothExponent N B :=
    Finset.dvd_prod_of_mem _ (by rw [Nat.mem_primesBelow]; exact ⟨by omega, hq_prime⟩)
  have h_fact_ge : Nat.clog q N ≤ (smoothExponent N B).factorization q := by
    have := (Nat.factorization_le_iff_dvd
      (pow_ne_zero _ hq_prime.pos.ne') (smoothExponent_pos N B).ne').mpr h_dvd
    have h := this q
    rwa [hq_prime.factorization_pow, Finsupp.single_apply, if_pos rfl] at h
  exact le_trans (factorization_le_clog hq_prime.one_lt hsmooth.1 hnN) h_fact_ge

/-- Pollard p−1 correctness: for prime `p` with `(p − 1)` being `B`-smooth and
less than `N`, any unit `u ∈ (ZMod p)ˣ` satisfies `u^{smoothExponent N B} = 1`. -/
theorem pow_smoothExponent_eq_one_mod {p N B : ℕ} (hp : Nat.Prime p)
    (hsmooth : IsBSmooth B (p - 1)) (hnN : p - 1 < N)
    (u : (ZMod p)ˣ) :
    (u : ZMod p) ^ (smoothExponent N B) = 1 := by
  have h_dvd : p.totient ∣ smoothExponent N B := by
    rw [Nat.totient_prime hp]
    exact dvd_smoothExponent_of_isBSmooth hsmooth hnN
  obtain ⟨k, hk⟩ := h_dvd
  rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, one_pow]

/-- If `p ∣ N`, `q ∣ N`, `p` prime, `p ∣ n`, but `q ∤ n`, and `N > 1`, then
`gcd(n, N)` is a proper nontrivial divisor of `N`. This is the abstract
correctness of "gcd reveals a factor" used at the end of Pollard p−1 / ECM. -/
lemma gcd_proper_divisor {n N p q : ℕ}
    (hpN : p ∣ N) (hqN : q ∣ N)
    (hp : Nat.Prime p)
    (hpn : p ∣ n) (hqn : ¬(q ∣ n))
    (hN : 1 < N) :
    1 < Nat.gcd n N ∧ Nat.gcd n N < N := by
  constructor
  · have : p ∣ Nat.gcd n N := Nat.dvd_gcd hpn hpN
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right n (by omega)) this)
  · have hgcd_dvd_N : Nat.gcd n N ∣ N := Nat.gcd_dvd_right n N
    have hgcd_dvd_n : Nat.gcd n N ∣ n := Nat.gcd_dvd_left n N
    have hne : Nat.gcd n N ≠ N := by
      intro heq
      rw [heq] at hgcd_dvd_n
      exact hqn (dvd_trans hqN hgcd_dvd_n)
    exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) hgcd_dvd_N) hne

/-- Monotonicity of `smoothExponent` in the smoothness bound: if `B₁ ≤ B₂`
then `smoothExponent N B₁ ∣ smoothExponent N B₂`. -/
lemma smoothExponent_dvd_of_le {N B₁ B₂ : ℕ} (h : B₁ ≤ B₂) :
    smoothExponent N B₁ ∣ smoothExponent N B₂ := by
  unfold smoothExponent
  apply Finset.prod_dvd_prod_of_subset
  intro ℓ hℓ
  rw [Nat.mem_primesBelow] at hℓ ⊢
  exact ⟨by omega, hℓ.2⟩

/-- For any list `l`, `l.foldl max init` is either an element of `l` or equals
the initial value `init`. -/
lemma list_foldl_max_mem_or_eq_init : ∀ (l : List ℕ) (init : ℕ),
    l.foldl max init ∈ l ∨ l.foldl max init = init := by
  intro l
  induction l with
  | nil => intro init; right; rfl
  | cons a as ih =>
    intro init
    simp only [List.foldl]
    rcases ih (max init a) with h | h
    · left; exact List.mem_cons_of_mem a h
    · rw [h]
      by_cases hle : init ≤ a
      · left; simp only [max_eq_right hle]; exact List.Mem.head as
      · right; omega

/-- If `largestPrimeFactor n` is actually prime, then it appears in `n`'s
prime-factors list. -/
lemma largestPrimeFactor_mem_primeFactorsList {n : ℕ}
    (h : Nat.Prime (largestPrimeFactor n)) :
    largestPrimeFactor n ∈ n.primeFactorsList := by
  unfold largestPrimeFactor at h ⊢
  rcases list_foldl_max_mem_or_eq_init n.primeFactorsList 0 with hm | hm
  · exact hm
  · rw [hm] at h; exact absurd h (by decide)

/-- If `largestPrimeFactor n` is prime and `n ≠ 0`, then it actually divides `n`. -/
lemma largestPrimeFactor_dvd {n : ℕ}
    (h : Nat.Prime (largestPrimeFactor n)) (hn : n ≠ 0) :
    largestPrimeFactor n ∣ n :=
  ((Nat.mem_primeFactorsList hn).mp (largestPrimeFactor_mem_primeFactorsList h)).2

/-- Cardinality bound used in Pollard p−1 second-stage analysis: for prime `q`
with `ℓ = largestPrimeFactor (q − 1)` prime and `ℓ ∤ m`, we have
`|ker(x ↦ x^m : (ZMod q)ˣ)| · ℓ ≤ q − 1`. -/
theorem card_mth_roots_mul_largest_prime_le
    {q m : ℕ} (hq : Nat.Prime q)
    (hℓq_prime : Nat.Prime (largestPrimeFactor (q - 1)))
    (hℓq_not_dvd : ¬(largestPrimeFactor (q - 1) ∣ m)) :
    Nat.card ↥(powMonoidHom (α := (ZMod q)ˣ) m).ker * largestPrimeFactor (q - 1) ≤ q - 1 := by
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  rw [IsCyclic.card_powMonoidHom_ker]
  have hqm1_ne : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  rw [show Nat.card (ZMod q)ˣ = q - 1 from by
    haveI : Fact q.Prime := ⟨hq⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]]
  have h_gcd_dvd : (q - 1).gcd m ∣ q - 1 := Nat.gcd_dvd_left _ _
  have h_not_dvd_gcd : ¬(largestPrimeFactor (q - 1) ∣ (q - 1).gcd m) :=
    fun h => hℓq_not_dvd (dvd_trans h (Nat.gcd_dvd_right _ _))
  have hcop : Nat.Coprime ((q - 1).gcd m) (largestPrimeFactor (q - 1)) := by
    rwa [Nat.coprime_comm, hℓq_prime.coprime_iff_not_dvd]
  have hℓ_dvd : largestPrimeFactor (q - 1) ∣ q - 1 :=
    largestPrimeFactor_dvd hℓq_prime hqm1_ne
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hqm1_ne)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h_gcd_dvd hℓ_dvd)

/-- If `largestPrimeFactor n > 0`, it is actually a prime. -/
lemma largestPrimeFactor_prime_of_pos {n : ℕ} (h : 0 < largestPrimeFactor n) :
    Nat.Prime (largestPrimeFactor n) := by
  unfold largestPrimeFactor at h ⊢
  rcases list_foldl_max_mem_or_eq_init n.primeFactorsList 0 with hm | hm
  · exact Nat.prime_of_mem_primeFactorsList hm
  · omega

end PollardPM1

namespace ECMFactoring

open Nat Finset

/-- Short Weierstrass curve over a commutative ring: `y² = x³ + a x + b`,
realized by setting `(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, a, b)`. -/
def shortWeierstrass {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a, b⟩

/-- ECM discriminant of the short Weierstrass curve `y² = x³ + a x + b`:
`4 a³ + 27 b²`. The full `Δ` differs by a factor `-16`. -/
def ecmDiscriminant {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 + 27 * b ^ 2

/-- The standard Weierstrass discriminant `Δ` of `shortWeierstrass a b` equals
`-16 (4 a³ + 27 b²) = -16 · ecmDiscriminant a b`. -/
theorem shortWeierstrass_Δ {R : Type*} [CommRing R] (a b : R) :
    (shortWeierstrass a b).Δ = -16 * ecmDiscriminant a b := by
  simp only [shortWeierstrass, ecmDiscriminant, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Configuration data for the elliptic curve method (ECM): the modulus `N`,
the smoothness bound `B`, the prime-search bound `M`, and a witness `1 < N`. -/
structure ECMConfig where
  N : ℕ
  B : ℕ
  M : ℕ
  hN : 1 < N

/-- ECM curve parameters over `ℤ`: choice of `a` and a base point `(x₀, y₀)`.
The value of `b` is computed so that `(x₀, y₀)` lies on the curve. -/
structure ECMCurveParams where
  a : ℤ
  x₀ : ℤ
  y₀ : ℤ

/-- The constant term `b` of the ECM curve, chosen so that `(x₀, y₀)` lies on
`y² = x³ + a x + b`. -/
def ECMCurveParams.b (params : ECMCurveParams) : ℤ :=
  params.y₀ ^ 2 - params.x₀ ^ 3 - params.a * params.x₀

/-- The elliptic curve over `ℤ` associated to ECM parameters. -/
def ECMCurveParams.curve (params : ECMCurveParams) : WeierstrassCurve ℤ :=
  shortWeierstrass params.a params.b

/-- ECM discriminant of the chosen curve. -/
def ECMCurveParams.disc (params : ECMCurveParams) : ℤ :=
  ecmDiscriminant params.a params.b

/-- By construction of `b`, the prescribed base point `(x₀, y₀)` satisfies the
Weierstrass equation. -/
theorem ECMCurveParams.point_on_curve (params : ECMCurveParams) :
    WeierstrassCurve.Affine.Equation params.curve params.x₀ params.y₀ := by
  unfold WeierstrassCurve.Affine.Equation Polynomial.evalEval
  simp only [ECMCurveParams.curve, shortWeierstrass, ECMCurveParams.b,
    WeierstrassCurve.Affine.polynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- The ECM curve reduced modulo a prime `p`, viewed as an affine
Weierstrass curve over `ZMod p`. -/
def ECMCurveParams.curveModP (params : ECMCurveParams) (p : ℕ) :
    WeierstrassCurve.Affine (ZMod p) :=
  params.curve.map (Int.castRingHom (ZMod p))

/-- Per-prime exponent used in ECM: `⌊log_ℓ ((√M + 1)²)⌋ + 1`, large enough
to cover any prime-power up to `(√M + 1)²` as a factor of the multiplier. -/
def ecmSmoothExponent (ℓ M : ℕ) : ℕ :=
  Nat.log ℓ ((Nat.sqrt M + 1) ^ 2) + 1

/-- Lower bound: `ℓ^{ecmSmoothExponent ℓ M − 1} ≤ (√M + 1)²`, used to show the
exponent isn't too large. -/
theorem ecmSmoothExponent_bound_le (ℓ M : ℕ) (_hℓ : 1 < ℓ) :
    ℓ ^ (ecmSmoothExponent ℓ M - 1) ≤ (Nat.sqrt M + 1) ^ 2 := by
  simp only [ecmSmoothExponent, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self ℓ (by positivity)

/-- Upper bound: `(√M + 1)² < ℓ^{ecmSmoothExponent ℓ M}`, used to show the
exponent is large enough. -/
theorem ecmSmoothExponent_bound_lt (ℓ M : ℕ) (hℓ : 1 < ℓ) :
    (Nat.sqrt M + 1) ^ 2 < ℓ ^ ecmSmoothExponent ℓ M := by
  simp only [ecmSmoothExponent]
  exact Nat.lt_pow_succ_log_self hℓ _

/-- ECM smooth scalar `k = ∏_{ℓ < B prime} ℓ^{ecmSmoothExponent ℓ M}`: every
`B`-smooth integer at most `(√M + 1)²` divides this scalar. -/
def ecmSmoothScalar (B M : ℕ) : ℕ :=
  ∏ ℓ ∈ (Finset.range B).filter Nat.Prime, ℓ ^ ecmSmoothExponent ℓ M

/-- Positivity of the ECM smooth scalar. -/
theorem ecmSmoothScalar_pos (B M : ℕ) : 0 < ecmSmoothScalar B M := by
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/-- The ECM smooth scalar is itself a `B`-smooth number. -/
theorem ecmSmoothScalar_smooth (B M : ℕ) :
    ecmSmoothScalar B M ∈ Nat.smoothNumbers B := by
  rw [Nat.mem_smoothNumbers]
  constructor
  · exact (ecmSmoothScalar_pos B M).ne'
  · intro q hq
    rw [Nat.mem_primeFactorsList (ecmSmoothScalar_pos B M).ne'] at hq
    obtain ⟨hqp, hq_dvd⟩ := hq
    simp only [ecmSmoothScalar] at hq_dvd
    rw [hqp.prime.dvd_finset_prod_iff (fun ℓ => ℓ ^ ecmSmoothExponent ℓ M)] at hq_dvd
    obtain ⟨ℓ, hℓ_mem, hq_dvd_pow⟩ := hq_dvd
    rw [Finset.mem_filter, Finset.mem_range] at hℓ_mem
    have hq_dvd_ℓ := hqp.dvd_of_dvd_pow hq_dvd_pow
    have hqℓ := (Nat.prime_dvd_prime_iff_eq hqp hℓ_mem.2).mp hq_dvd_ℓ
    omega

/-- For positive `n` and `p > 1`, the `p`-adic valuation of `n` is at most
`log_p n`. -/
theorem factorization_le_log_of_pos {n p : ℕ} (hn : 0 < n) (hp : 1 < p) :
    n.factorization p ≤ Nat.log p n :=
  Nat.le_log_of_pow_le hp (le_of_dvd hn (Nat.ordProj_dvd n p))

/-- For prime `p < B`, the full prime-power factor `p^{ecmSmoothExponent p M}`
divides the ECM smooth scalar. -/
theorem prime_pow_dvd_ecmSmoothScalar {B M p : ℕ} (hp : Nat.Prime p) (hpB : p < B) :
    p ^ ecmSmoothExponent p M ∣ ecmSmoothScalar B M :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpB, hp⟩)

/-- Key divisibility for ECM: any nonzero `B`-smooth `n ≤ (√M + 1)²` divides
the ECM smooth scalar `ecmSmoothScalar B M`. -/
theorem smooth_dvd_ecmSmoothScalar {n B M : ℕ} (hn : n ≠ 0)
    (hsmooth : n ∈ Nat.smoothNumbers B) (hbound : n ≤ (Nat.sqrt M + 1) ^ 2) :
    n ∣ ecmSmoothScalar B M := by
  rw [Nat.mem_smoothNumbers] at hsmooth
  rw [← Nat.factorization_le_iff_dvd hn (ecmSmoothScalar_pos B M).ne']
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hfp : n.factorization p = 0
    · simp [hfp]
    · have hpn : p ∈ n.primeFactorsList := by
        rw [Nat.mem_primeFactorsList hn]
        exact ⟨hp, (hp.dvd_iff_one_le_factorization hn).mpr (Nat.pos_of_ne_zero hfp)⟩
      have hpB : p < B := hsmooth.2 p hpn
      have hdvd := prime_pow_dvd_ecmSmoothScalar (M := M) hp hpB
      have hfact := (hp.pow_dvd_iff_le_factorization (ecmSmoothScalar_pos B M).ne').mp hdvd
      calc n.factorization p
          ≤ Nat.log p n :=
            factorization_le_log_of_pos (Nat.pos_of_ne_zero hn) hp.one_lt
        _ ≤ Nat.log p ((Nat.sqrt M + 1) ^ 2) := Nat.log_mono_right hbound
        _ ≤ (ecmSmoothScalar B M).factorization p := by
            simp only [ecmSmoothExponent] at hfact; omega
  · simp [hp]

/-- ECM algebraic step: in the situation `P₁` on the reduction mod `p₁`,
where the order of `P₁` is `B`-smooth and bounded, while the order of `P₂` is
*not* `B`-smooth, multiplying by the ECM smooth scalar kills `P₁` but not
`P₂`. This separation is what allows ECM to find a factor. -/
lemma ecm_algebraic_step
    (cfg : ECMConfig) (params : ECMCurveParams)
    (p₁ p₂ : ℕ) [Fact (Nat.Prime p₁)] [Fact (Nat.Prime p₂)]
    (hp₁M : p₁ ≤ cfg.M)
    (P₁ : (params.curveModP p₁).Point) (P₂ : (params.curveModP p₂).Point)
    (hsmooth₁ : addOrderOf P₁ ∈ Nat.smoothNumbers cfg.B)
    (hord₁_bound : addOrderOf P₁ ≤ (Nat.sqrt p₁ + 1) ^ 2)
    (hnotsmooth₂ : addOrderOf P₂ ∉ Nat.smoothNumbers cfg.B) :
    (ecmSmoothScalar cfg.B cfg.M) • P₁ = 0 ∧
    (ecmSmoothScalar cfg.B cfg.M) • P₂ ≠ 0 := by
  constructor
  ·
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    have hord₁_pos : addOrderOf P₁ ≠ 0 :=
      (Nat.mem_smoothNumbers.mp hsmooth₁).1
    apply smooth_dvd_ecmSmoothScalar hord₁_pos hsmooth₁
    calc addOrderOf P₁
        ≤ (Nat.sqrt p₁ + 1) ^ 2 := hord₁_bound
      _ ≤ (Nat.sqrt cfg.M + 1) ^ 2 := by
          apply Nat.pow_le_pow_left
          exact Nat.add_le_add_right (Nat.sqrt_le_sqrt hp₁M) 1
  ·
    intro h
    apply hnotsmooth₂
    exact Nat.mem_smoothNumbers_of_dvd (ecmSmoothScalar_smooth cfg.B cfg.M)
      (addOrderOf_dvd_of_nsmul_eq_zero h)

end ECMFactoring

namespace MontgomeryTorsion

open Nat Finset

variable {k : Type*} [Field k]

/-- The Montgomery form equation `B y² = x³ + A x² + x` over a field `k`. -/
def MontgomeryOnCurve (A B x y : k) : Prop :=
  B * y ^ 2 = x ^ 3 + A * x ^ 2 + x

/-- Auxiliary: if `A² ≠ 4` then `A + 2 ≠ 0`, since `A² - 4 = (A + 2)(A - 2)`. -/
lemma ne_add_two_zero_of_sq_ne_four {A : k} (h : A ^ 2 ≠ 4) : A + 2 ≠ 0 := by
  intro h_eq
  exact h (sub_eq_zero.mp (by have : A ^ 2 - 4 = (A + 2) * (A - 2) := by ring
                              rw [this, h_eq, zero_mul]))

/-- Auxiliary: if `A² ≠ 4` then `A - 2 ≠ 0`. -/
lemma ne_sub_two_zero_of_sq_ne_four {A : k} (h : A ^ 2 ≠ 4) : A - 2 ≠ 0 := by
  intro h_eq
  exact h (sub_eq_zero.mp (by have : A ^ 2 - 4 = (A + 2) * (A - 2) := by ring
                              rw [this, h_eq, mul_zero]))

/-- If the polynomial `r² + A r + 1 = 0` has no root in `k` (char ≠ 2), then
its discriminant `A² - 4` is a non-square. -/
lemma not_isSquare_disc_of_no_roots (h2 : (2 : k) ≠ 0)
    {A : k} (hno_root : ∀ r : k, r ^ 2 + A * r + 1 ≠ 0) :
    ¬ IsSquare (A ^ 2 - 4) := by
  intro ⟨d, hd⟩
  have hd' : d ^ 2 = A ^ 2 - 4 := by rw [sq]; linear_combination -hd
  have h4 : (4 : k) ≠ 0 := by
    intro h; apply h2; have : (4 : k) = 2 * 2 := by ring
    rw [this] at h; exact (mul_eq_zero.mp h).elim id id
  have : ((-A + d) / 2) ^ 2 + A * ((-A + d) / 2) + 1 = 0 := by
    suffices h : 4 * (((-A + d) / 2) ^ 2 + A * ((-A + d) / 2) + 1) = 0 by
      exact (mul_eq_zero.mp h).resolve_left h4
    have key : 4 * (((-A + d) / 2) ^ 2 + A * ((-A + d) / 2) + 1) =
      d ^ 2 - A ^ 2 + 4 := by field_simp; ring
    rw [key]; linear_combination hd'
  exact hno_root _ this

/-- Quadratic-character lemma over a finite field: if `a, b, c` are all nonzero
and `a · b` is *not* a square, then at least one of `a · c` or `b · c` is a
square. -/
lemma isSquare_mul_or_of_not_isSquare_mul [Fintype k] [DecidableEq k]
    {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ¬ IsSquare (a * b)) :
    IsSquare (a * c) ∨ IsSquare (b * c) := by
  have hχ_ab := quadraticChar_neg_one_iff_not_isSquare.mpr h
  rw [map_mul] at hχ_ab
  have hχa := quadraticChar_dichotomy (a := a) ha
  have hχb := quadraticChar_dichotomy (a := b) hb
  have hχc := quadraticChar_dichotomy (a := c) hc
  rcases hχa with ha1 | ha1 <;> rcases hχb with hb1 | hb1 <;>
    rw [ha1, hb1] at hχ_ab <;> simp at hχ_ab
  · rcases hχc with hc1 | hc1
    · left; exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hc)).mp
        (by rw [map_mul, ha1, hc1, mul_one])
    · right; exact (quadraticChar_one_iff_isSquare (mul_ne_zero hb hc)).mp
        (by rw [map_mul, hb1, hc1]; ring)
  · rcases hχc with hc1 | hc1
    · right; exact (quadraticChar_one_iff_isSquare (mul_ne_zero hb hc)).mp
        (by rw [map_mul, hb1, hc1, mul_one])
    · left; exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hc)).mp
        (by rw [map_mul, ha1, hc1]; ring)

/-- If `A · B⁻¹` is a square in `k` and `B ≠ 0`, then there exists `y` with
`B y² = A`. Used to produce y-coordinates of torsion points. -/
lemma exists_By_sq_eq_of_isSquare_mul_inv {A B : k} (hB : B ≠ 0)
    (h : IsSquare (A * B⁻¹)) :
    ∃ y : k, B * y ^ 2 = A := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  have h1 : A = t * t * B := by
    calc A = A * B⁻¹ * B := by field_simp
    _ = t * t * B := by rw [ht]
  rw [sq, mul_comm B (t * t)]
  exact h1.symm

/-- Montgomery torsion existence (Theorem 10.14 of Sutherland's notes): over a
finite field `k` of characteristic ≠ 2, a Montgomery curve `B y² = x³ + A x² + x`
(with `B ≠ 0`, `A² ≠ 4`) always has either two distinct rational points of
order 2 coming from a factorization `(x - r)(x - s)` of `x² + A x + 1`, or a
rational point of order 4 (a `y` with `B y² = A ± 2`). -/
theorem montgomery_torsion_10_14 [Fintype k] [DecidableEq k]
    (h2 : (2 : k) ≠ 0)
    {A B : k} (hB : B ≠ 0) (hA : A ^ 2 ≠ 4) :

    (∃ r s : k, r ≠ 0 ∧ s ≠ 0 ∧ r ≠ s ∧
      r ^ 2 + A * r + 1 = 0 ∧ s ^ 2 + A * s + 1 = 0)

    ∨ (∃ y : k, B * y ^ 2 = A + 2) ∨ (∃ y : k, B * y ^ 2 = A - 2) := by

  by_cases h : ∃ r : k, r ^ 2 + A * r + 1 = 0
  ·
    left
    obtain ⟨r, hr⟩ := h

    refine ⟨r, -A - r, ?_, ?_, ?_, hr, ?_⟩
    ·
      intro heq; rw [heq] at hr; simp at hr
    ·
      intro heq
      have : (-A - r) ^ 2 + A * (-A - r) + 1 = 0 := by linear_combination hr
      rw [heq] at this; simp at this
    ·

      intro heq
      apply hA
      have h2r : 2 * r = -A := by linear_combination heq
      have hA_eq : A = -(2 * r) := by linear_combination h2r
      have hr1 : r ^ 2 = 1 := by
        have := hr; rw [hA_eq] at this; linear_combination -this
      calc A ^ 2 = (-(2 * r)) ^ 2 := by rw [hA_eq]
        _ = 4 * r ^ 2 := by ring
        _ = 4 * 1 := by rw [hr1]
        _ = 4 := by ring
    ·
      linear_combination hr
  ·
    right
    push Not at h

    have hdisc : ¬ IsSquare (A ^ 2 - 4) := not_isSquare_disc_of_no_roots h2 h
    have hfactor : A ^ 2 - 4 = (A + 2) * (A - 2) := by ring
    rw [hfactor] at hdisc

    have hAp2 : A + 2 ≠ 0 := ne_add_two_zero_of_sq_ne_four hA
    have hAm2 : A - 2 ≠ 0 := ne_sub_two_zero_of_sq_ne_four hA
    have hBinv : B⁻¹ ≠ 0 := inv_ne_zero hB

    rcases isSquare_mul_or_of_not_isSquare_mul hAp2 hAm2 hBinv hdisc with hsq | hsq
    · left; exact exists_By_sq_eq_of_isSquare_mul_inv hB hsq
    · right; exact exists_By_sq_eq_of_isSquare_mul_inv hB hsq

/-- A point `(x, 0)` of order 2 on the Montgomery curve `B y² = x³ + A x² + x`,
characterized by lying on the curve with `y = 0` and `x ≠ 0`. -/
def IsOrder2Point (A B x : k) : Prop :=
  MontgomeryOnCurve A B x 0 ∧ x ≠ 0

/-- A point `(x, y)` of order 4 on the Montgomery curve: a curve point with
`y ≠ 0` and `x = ±1`. -/
def IsOrder4Point (A B x y : k) : Prop :=
  MontgomeryOnCurve A B x y ∧ y ≠ 0 ∧ (x = 1 ∨ x = -1)

/-- The Montgomery curve has an order-4 rational subgroup if it has either
two distinct order-2 points or an order-4 point. -/
def HasSubgroupOfOrder4 (A B : k) : Prop :=
  (∃ x₁ x₂ : k, x₁ ≠ x₂ ∧ IsOrder2Point A B x₁ ∧ IsOrder2Point A B x₂) ∨
  (∃ x y : k, IsOrder4Point A B x y)

/-- A nonzero root `r` of `x² + A x + 1` yields an order-2 point `(r, 0)` on the
Montgomery curve. -/
lemma isOrder2Point_of_root {A B r : k}
    (hr : r ^ 2 + A * r + 1 = 0) (hr0 : r ≠ 0) :
    IsOrder2Point A B r := by
  refine ⟨?_, hr0⟩
  unfold MontgomeryOnCurve
  have : r ^ 3 + A * r ^ 2 + r = r * (r ^ 2 + A * r + 1) := by ring
  rw [this, hr, mul_zero]; ring

/-- If `B y² = A + 2` with `y ≠ 0`, then `(1, y)` is an order-4 point. -/
lemma isOrder4Point_at_one {A B y : k}
    (hy : B * y ^ 2 = A + 2) (hyNe : y ≠ 0) :
    IsOrder4Point A B 1 y :=
  ⟨by unfold MontgomeryOnCurve; linear_combination hy, hyNe, Or.inl rfl⟩

/-- If `B y² = A - 2` with `y ≠ 0`, then `(-1, y)` is an order-4 point. -/
lemma isOrder4Point_at_neg_one {A B y : k}
    (hy : B * y ^ 2 = A - 2) (hyNe : y ≠ 0) :
    IsOrder4Point A B (-1) y :=
  ⟨by unfold MontgomeryOnCurve; linear_combination hy, hyNe, Or.inr rfl⟩

/-- Under `A² ≠ 4`, an equation `B y² = A + 2` forces `y ≠ 0` (otherwise
`A = -2`, contradicting `A² ≠ 4`). -/
lemma y_ne_zero_of_By_sq_eq_add_two {A B y : k} (hA : A ^ 2 ≠ 4)
    (hy : B * y ^ 2 = A + 2) : y ≠ 0 := by
  intro heq; rw [heq, sq, mul_zero, mul_zero] at hy; apply hA
  have : A = -(2 : k) := by linear_combination hy.symm
  rw [this]; ring

/-- Under `A² ≠ 4`, an equation `B y² = A - 2` forces `y ≠ 0`. -/
lemma y_ne_zero_of_By_sq_eq_sub_two {A B y : k} (hA : A ^ 2 ≠ 4)
    (hy : B * y ^ 2 = A - 2) : y ≠ 0 := by
  intro heq; rw [heq, sq, mul_zero, mul_zero] at hy; apply hA
  have : A = (2 : k) := by linear_combination hy.symm
  rw [this]; ring

/-- The short Weierstrass equation `y² = x³ + a x + b` over `k`. -/
def ShortWeierstrassOnCurve (a b x y : k) : Prop :=
  y ^ 2 = x ^ 3 + a * x + b

/-- "Squareness" step in Theorem 10.15 of Sutherland: if `(u, v)` is a point on
the short Weierstrass curve and `2 · (u, v) = (x₀, 0)`, then `(u - x₀)² =
3 x₀² + a` and `3 x₀² + a ≠ 0`. This is the key squareness that allows
converting to Montgomery form. -/
theorem theorem_10_15_squareness
    (h2 : (2 : k) ≠ 0)
    {a b x₀ u v : k}
    (hcurve_P : ShortWeierstrassOnCurve a b u v)
    (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
    (hv : v ≠ 0)
    (hdouble : x₀ = ((3 * u ^ 2 + a) / (2 * v)) ^ 2 - 2 * u) :
    (u - x₀) ^ 2 = 3 * x₀ ^ 2 + a ∧ (3 * x₀ ^ 2 + a ≠ 0) := by

  have hb : b = -x₀ ^ 3 - a * x₀ := by
    unfold ShortWeierstrassOnCurve at hcurve_2P; simp at hcurve_2P
    linear_combination -hcurve_2P

  have hv2 : v ^ 2 = u ^ 3 + a * u + (-x₀ ^ 3 - a * x₀) := by
    rw [hb] at hcurve_P; exact hcurve_P

  have h2v : (2 * v) ≠ 0 := mul_ne_zero h2 hv
  have hdbl_clear : (x₀ + 2 * u) * ((2 * v) ^ 2) = (3 * u ^ 2 + a) ^ 2 := by
    have h1 : x₀ + 2 * u = ((3 * u ^ 2 + a) / (2 * v)) ^ 2 := by
      linear_combination hdouble
    rw [h1, div_pow, div_mul_cancel₀]
    exact pow_ne_zero 2 h2v
  have h_denom : 4 * (x₀ + 2 * u) * (u ^ 3 + a * u - x₀ ^ 3 - a * x₀) =
      (3 * u ^ 2 + a) ^ 2 := by
    calc 4 * (x₀ + 2 * u) * (u ^ 3 + a * u - x₀ ^ 3 - a * x₀)
        = (x₀ + 2 * u) * (4 * (u ^ 3 + a * u - x₀ ^ 3 - a * x₀)) := by ring
      _ = (x₀ + 2 * u) * (4 * v ^ 2) := by rw [hv2]; ring
      _ = (x₀ + 2 * u) * ((2 * v) ^ 2) := by ring
      _ = (3 * u ^ 2 + a) ^ 2 := hdbl_clear

  have hsq_eq : ((u - x₀) ^ 2 - (3 * x₀ ^ 2 + a)) ^ 2 = 0 := by
    linear_combination -h_denom

  have huz : (u - x₀) ^ 2 = 3 * x₀ ^ 2 + a := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq_eq
    linear_combination this
  exact ⟨huz, by
    intro h0
    have hu_eq : u = x₀ := by
      rw [h0] at huz
      exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp huz)
    have : v ^ 2 = 0 := by rw [hu_eq] at hv2; linear_combination hv2
    exact hv (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)⟩

/-- The forward direction of the Theorem 10.15 isomorphism: the substitution
`(x, y) ↦ (B (x - x₀), B y)` sends short Weierstrass points
`y² = x³ + a x + b` to Montgomery-form points `B Y² = X³ + A X² + X` for
`A = 3 x₀ B` and `B² (3 x₀² + a) = 1`. -/
theorem theorem_10_15_isomorphism
    {a b x₀ A B : k}
    (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
    (hB_sq : B ^ 2 * (3 * x₀ ^ 2 + a) = 1)
    (hA : A = 3 * x₀ * B) :
    ∀ x y : k, ShortWeierstrassOnCurve a b x y →
      MontgomeryOnCurve A B (B * (x - x₀)) (B * y) := by
  intro x y hxy
  unfold MontgomeryOnCurve
  rw [hA]
  have hb : b = -x₀ ^ 3 - a * x₀ := by
    unfold ShortWeierstrassOnCurve at hcurve_2P; simp at hcurve_2P
    linear_combination -hcurve_2P
  unfold ShortWeierstrassOnCurve at hxy
  rw [hb] at hxy
  have hstep : B ^ 2 * y ^ 2 =
      B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (x - x₀) := by
    have hpoly : x ^ 3 + a * x + (-x₀ ^ 3 - a * x₀) =
      (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (3 * x₀ ^ 2 + a) * (x - x₀) := by ring
    calc B ^ 2 * y ^ 2
        = B ^ 2 * (x ^ 3 + a * x + (-x₀ ^ 3 - a * x₀)) := by rw [hxy]
      _ = B ^ 2 * ((x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) +
            (3 * x₀ ^ 2 + a) * (x - x₀)) := by rw [hpoly]
      _ = B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) +
            B ^ 2 * ((3 * x₀ ^ 2 + a) * (x - x₀)) := by ring
      _ = B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (x - x₀) := by
            congr 1
            rw [show B ^ 2 * ((3 * x₀ ^ 2 + a) * (x - x₀)) =
              B ^ 2 * (3 * x₀ ^ 2 + a) * (x - x₀) from by ring]
            rw [hB_sq, one_mul]
  calc B * (B * y) ^ 2
      = B * (B ^ 2 * y ^ 2) := by ring
    _ = B * (B ^ 2 * (x ^ 3 - 3 * x₀ ^ 2 * x + 2 * x₀ ^ 3) + (x - x₀)) := by rw [hstep]
    _ = (B * (x - x₀)) ^ 3 + 3 * x₀ * B * (B * (x - x₀)) ^ 2 + B * (x - x₀) := by ring

/-- The inverse direction of the Theorem 10.15 isomorphism: the substitution
`(X, Y) ↦ (X / B + x₀, Y / B)` sends Montgomery-form points back to short
Weierstrass points. -/
theorem theorem_10_15_inverse
    {a b x₀ A B : k}
    (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
    (hB_sq : B ^ 2 * (3 * x₀ ^ 2 + a) = 1)
    (hA : A = 3 * x₀ * B) :
    ∀ X Y : k, MontgomeryOnCurve A B X Y →
      ShortWeierstrassOnCurve a b (X / B + x₀) (Y / B) := by
  have hB : B ≠ 0 := by intro hB0; rw [hB0] at hB_sq; simp at hB_sq
  have hb : b = -x₀ ^ 3 - a * x₀ := by
    unfold ShortWeierstrassOnCurve at hcurve_2P; simp at hcurve_2P
    linear_combination -hcurve_2P
  intro X Y hXY
  unfold MontgomeryOnCurve at hXY
  unfold ShortWeierstrassOnCurve
  rw [hb, hA] at *
  field_simp
  linear_combination hXY - X * hB_sq

/-- The two substitutions of Theorem 10.15 are inverse to each other on
coordinates, in both directions. -/
theorem theorem_10_15_round_trip
    {x₀ B : k}
    (hB : B ≠ 0) :

    (∀ x y : k, (B * (x - x₀)) / B + x₀ = x ∧ (B * y) / B = y) ∧

    (∀ X Y : k, B * ((X / B + x₀) - x₀) = X ∧ B * (Y / B) = Y) :=
  ⟨fun x y => ⟨by field_simp; ring, by field_simp⟩,
   fun X Y => ⟨by field_simp; ring, by field_simp⟩⟩

/-- Theorem 10.15 of Sutherland (Montgomery model from order-4 point): if
`E : y² = x³ + a x + b` has a point `P = (u, v)` whose double is the
2-torsion point `(x₀, 0)`, then `3 x₀² + a` is a square in `k`, and `E` can be
put in Montgomery form `E'' : B y² = x³ + A x² + x` with `B = 1/√(3 x₀² + a)`
and `A = 3 x₀ B`; the map `(x, y) ↦ (B (x - x₀), B y)` gives a bijective
isomorphism `E ≃ E''`. -/
theorem theorem_10_15
    (h2 : (2 : k) ≠ 0)
    {a b x₀ u v : k}
    (hcurve_P : ShortWeierstrassOnCurve a b u v)
    (hcurve_2P : ShortWeierstrassOnCurve a b x₀ 0)
    (hv : v ≠ 0)
    (hdouble : x₀ = ((3 * u ^ 2 + a) / (2 * v)) ^ 2 - 2 * u) :

    ((u - x₀) ^ 2 = 3 * x₀ ^ 2 + a ∧ (3 * x₀ ^ 2 + a ≠ 0)) ∧

    (∀ B A : k, B ^ 2 * (3 * x₀ ^ 2 + a) = 1 → A = 3 * x₀ * B →

      (∀ x y : k, ShortWeierstrassOnCurve a b x y →
        MontgomeryOnCurve A B (B * (x - x₀)) (B * y)) ∧

      (∀ X Y : k, MontgomeryOnCurve A B X Y →
        ShortWeierstrassOnCurve a b (X / B + x₀) (Y / B)) ∧

      (∀ x y : k, (B * (x - x₀)) / B + x₀ = x ∧ (B * y) / B = y) ∧

      (∀ X Y : k, B * ((X / B + x₀) - x₀) = X ∧ B * (Y / B) = Y)) := by
  refine ⟨theorem_10_15_squareness h2 hcurve_P hcurve_2P hv hdouble,
    fun _B _A hB hA => ?_⟩
  have hBne : _B ≠ 0 := by intro h0; rw [h0] at hB; simp at hB
  exact ⟨theorem_10_15_isomorphism hcurve_2P hB hA,
         theorem_10_15_inverse hcurve_2P hB hA,
         (theorem_10_15_round_trip hBne).1,
         (theorem_10_15_round_trip hBne).2⟩

end MontgomeryTorsion
