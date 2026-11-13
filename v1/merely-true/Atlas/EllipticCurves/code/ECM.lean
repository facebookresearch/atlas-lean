/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.EllipticCurves.code.IntegerFactorization

noncomputable section

open Nat Finset

/-- The short Weierstrass curve `y² = x³ + a x + b` over a commutative ring `R`,
represented as a `WeierstrassCurve` with `a₁ = a₂ = a₃ = 0`, `a₄ = a` and `a₆ = b`. -/
def shortWeierstrass {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a, b⟩

/-- The discriminant quantity `4 a³ + 27 b²` of the short Weierstrass curve
`y² = x³ + a x + b`, used by ECM (Algorithm 10.11) to detect a nontrivial gcd with `N`. -/
def ecmDiscriminant {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 + 27 * b ^ 2

/-- The `Δ` invariant of the short Weierstrass curve `y² = x³ + a x + b` equals
`-16 (4 a³ + 27 b²)`. -/
theorem shortWeierstrass_Δ {R : Type*} [CommRing R] (a b : R) :
    (shortWeierstrass a b).Δ = -16 * ecmDiscriminant a b := by
  simp only [shortWeierstrass, ecmDiscriminant, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Configuration data for ECM (Algorithm 10.11): the integer `N` to be factored
(with `1 < N`), a smoothness bound `B` for primes used in the scalar, and a prime bound `M`. -/
structure ECMConfig where
  N : ℕ
  B : ℕ
  M : ℕ
  hN : 1 < N

/-- The randomly chosen curve parameters used by ECM: a coefficient `a` together
with the initial point `(x₀, y₀)` on the resulting short Weierstrass curve. -/
structure ECMCurveParams where
  a : ℤ
  x₀ : ℤ
  y₀ : ℤ

/-- The coefficient `b = y₀² - x₀³ - a x₀` derived from `(a, x₀, y₀)` so that the
short Weierstrass curve `y² = x³ + a x + b` passes through `(x₀, y₀)`. -/
def ECMCurveParams.b (params : ECMCurveParams) : ℤ :=
  params.y₀ ^ 2 - params.x₀ ^ 3 - params.a * params.x₀

/-- The short Weierstrass curve over `ℤ` determined by `params`. -/
def ECMCurveParams.curve (params : ECMCurveParams) : WeierstrassCurve ℤ :=
  shortWeierstrass params.a params.b

/-- The discriminant `4 a³ + 27 b²` of the ECM curve defined by `params`. -/
def ECMCurveParams.disc (params : ECMCurveParams) : ℤ :=
  ecmDiscriminant params.a params.b

/-- By construction, the chosen point `(x₀, y₀)` satisfies the affine Weierstrass
equation of `params.curve`. -/
theorem ECMCurveParams.point_on_curve (params : ECMCurveParams) :
    WeierstrassCurve.Affine.Equation params.curve params.x₀ params.y₀ := by
  unfold WeierstrassCurve.Affine.Equation Polynomial.evalEval
  simp only [ECMCurveParams.curve, shortWeierstrass, ECMCurveParams.b,
    WeierstrassCurve.Affine.polynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- Reduce the ECM curve modulo a prime `p`, viewing it as an affine curve over `ZMod p`. -/
def ECMCurveParams.curveModP (params : ECMCurveParams) (p : ℕ) :
    WeierstrassCurve.Affine (ZMod p) :=
  params.curve.map (Int.castRingHom (ZMod p))

/-- The exponent `e` such that `ℓ^{e-1} ≤ (√M + 1)² < ℓ^e`, as used by ECM
to ensure every smooth order ≤ `(√M + 1)²` divides the scaled scalar. -/
def ecmSmoothExponent (ℓ M : ℕ) : ℕ :=
  Nat.log ℓ ((Nat.sqrt M + 1) ^ 2) + 1

/-- Lower-bound side of the defining property: `ℓ^{e-1} ≤ (√M + 1)²` for `e = ecmSmoothExponent ℓ M`. -/
theorem ecmSmoothExponent_bound_le (ℓ M : ℕ) (_hℓ : 1 < ℓ) :
    ℓ ^ (ecmSmoothExponent ℓ M - 1) ≤ (Nat.sqrt M + 1) ^ 2 := by
  simp only [ecmSmoothExponent, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self ℓ (by positivity)

/-- Strict upper-bound side: `(√M + 1)² < ℓ^e` for `e = ecmSmoothExponent ℓ M`. -/
theorem ecmSmoothExponent_bound_lt (ℓ M : ℕ) (hℓ : 1 < ℓ) :
    (Nat.sqrt M + 1) ^ 2 < ℓ ^ ecmSmoothExponent ℓ M := by
  simp only [ecmSmoothExponent]
  exact Nat.lt_pow_succ_log_self hℓ _

/-- The ECM scalar multiplier: the product `∏_{ℓ < B prime} ℓ^{ecmSmoothExponent ℓ M}`,
designed so that every `B`-smooth integer ≤ `(√M + 1)²` divides it. -/
def ecmSmoothScalar (B M : ℕ) : ℕ :=
  ∏ ℓ ∈ (Finset.range B).filter Nat.Prime, ℓ ^ ecmSmoothExponent ℓ M

/-- Partial ECM scalar accumulated up to and including the prime `ℓ₁`: the product
`∏_{ℓ ≤ ℓ₁ prime} ℓ^{ecmSmoothExponent ℓ M}`. -/
def ecmPartialScalar (ℓ₁ M : ℕ) : ℕ :=
  ∏ ℓ ∈ (Finset.range (ℓ₁ + 1)).filter Nat.Prime, ℓ ^ ecmSmoothExponent ℓ M

/-- The ECM scalar `ecmSmoothScalar B M` is strictly positive. -/
theorem ecmSmoothScalar_pos (B M : ℕ) : 0 < ecmSmoothScalar B M := by
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/-- The partial ECM scalar `ecmPartialScalar ℓ₁ M` is strictly positive. -/
theorem ecmPartialScalar_pos (ℓ₁ M : ℕ) : 0 < ecmPartialScalar ℓ₁ M := by
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/-- The ECM scalar `ecmSmoothScalar B M` is itself `B`-smooth: all of its prime
factors are strictly less than `B`. -/
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

/-- The partial ECM scalar `ecmPartialScalar ℓ₁ M` is `(ℓ₁ + 1)`-smooth: all of its
prime factors are at most `ℓ₁`. -/
theorem ecmPartialScalar_smooth (ℓ₁ M : ℕ) :
    ecmPartialScalar ℓ₁ M ∈ Nat.smoothNumbers (ℓ₁ + 1) := by
  rw [Nat.mem_smoothNumbers]
  constructor
  · exact (ecmPartialScalar_pos ℓ₁ M).ne'
  · intro q hq
    rw [Nat.mem_primeFactorsList (ecmPartialScalar_pos ℓ₁ M).ne'] at hq
    obtain ⟨hqp, hq_dvd⟩ := hq
    simp only [ecmPartialScalar] at hq_dvd
    rw [hqp.prime.dvd_finset_prod_iff (fun ℓ => ℓ ^ ecmSmoothExponent ℓ M)] at hq_dvd
    obtain ⟨ℓ, hℓ_mem, hq_dvd_pow⟩ := hq_dvd
    rw [Finset.mem_filter, Finset.mem_range] at hℓ_mem
    have hq_dvd_ℓ := hqp.dvd_of_dvd_pow hq_dvd_pow
    have hqℓ := (Nat.prime_dvd_prime_iff_eq hqp hℓ_mem.2).mp hq_dvd_ℓ
    omega

/-- The `p`-adic valuation of a positive integer is bounded by `log_p n`. -/
theorem Nat.factorization_le_log_of_pos' {n p : ℕ} (hn : 0 < n) (hp : 1 < p) :
    n.factorization p ≤ Nat.log p n :=
  Nat.le_log_of_pow_le hp (le_of_dvd hn (Nat.ordProj_dvd n p))

/-- Each prime power factor `p^{ecmSmoothExponent p M}` (with `p < B` prime) divides
the ECM scalar `ecmSmoothScalar B M`. -/
theorem prime_pow_dvd_ecmSmoothScalar {B M p : ℕ} (hp : Nat.Prime p) (hpB : p < B) :
    p ^ ecmSmoothExponent p M ∣ ecmSmoothScalar B M :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpB, hp⟩)

/-- Each prime power factor `p^{ecmSmoothExponent p M}` (with `p ≤ ℓ₁` prime) divides
the partial ECM scalar `ecmPartialScalar ℓ₁ M`. -/
theorem prime_pow_dvd_ecmPartialScalar {ℓ₁ M p : ℕ} (hp : Nat.Prime p) (hpB : p ≤ ℓ₁) :
    p ^ ecmSmoothExponent p M ∣ ecmPartialScalar ℓ₁ M :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

/-- Key divisibility property: every nonzero `B`-smooth integer `n ≤ (√M + 1)²` divides
the ECM scalar `ecmSmoothScalar B M`. -/
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
            Nat.factorization_le_log_of_pos' (Nat.pos_of_ne_zero hn) hp.one_lt
        _ ≤ Nat.log p ((Nat.sqrt M + 1) ^ 2) := Nat.log_mono_right hbound
        _ ≤ (ecmSmoothScalar B M).factorization p := by
            simp only [ecmSmoothExponent] at hfact; omega
  · simp [hp]

/-- Partial analogue: every nonzero `(ℓ₁ + 1)`-smooth integer `n ≤ (√M + 1)²` divides
the partial ECM scalar `ecmPartialScalar ℓ₁ M`. -/
theorem smooth_dvd_ecmPartialScalar {n ℓ₁ M : ℕ} (hn : n ≠ 0)
    (hsmooth : n ∈ Nat.smoothNumbers (ℓ₁ + 1)) (hbound : n ≤ (Nat.sqrt M + 1) ^ 2) :
    n ∣ ecmPartialScalar ℓ₁ M := by
  rw [Nat.mem_smoothNumbers] at hsmooth
  rw [← Nat.factorization_le_iff_dvd hn (ecmPartialScalar_pos ℓ₁ M).ne']
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hfp : n.factorization p = 0
    · simp [hfp]
    · have hpn : p ∈ n.primeFactorsList := by
        rw [Nat.mem_primeFactorsList hn]
        exact ⟨hp, (hp.dvd_iff_one_le_factorization hn).mpr (Nat.pos_of_ne_zero hfp)⟩
      have hpB : p < ℓ₁ + 1 := hsmooth.2 p hpn
      have hpℓ₁ : p ≤ ℓ₁ := by omega
      have hdvd := prime_pow_dvd_ecmPartialScalar (ℓ₁ := ℓ₁) (M := M) hp hpℓ₁
      have hfact := (hp.pow_dvd_iff_le_factorization (ecmPartialScalar_pos ℓ₁ M).ne').mp hdvd
      calc n.factorization p
          ≤ Nat.log p n :=
            Nat.factorization_le_log_of_pos' (Nat.pos_of_ne_zero hn) hp.one_lt
        _ ≤ Nat.log p ((Nat.sqrt M + 1) ^ 2) := Nat.log_mono_right hbound
        _ ≤ (ecmPartialScalar ℓ₁ M).factorization p := by
            simp only [ecmSmoothExponent] at hfact; omega
  · simp [hp]

/-- The outcome of one trial of ECM (Algorithm 10.11): either a proper nontrivial
divisor `d` of `N` (with `1 < d < N`, `d ∣ N`), or `failure`. -/
inductive ECMResult (N : ℕ) where
  | factor (d : ℕ) (hd_gt : 1 < d) (hd_lt : d < N) (hd_dvd : d ∣ N) : ECMResult N
  | failure : ECMResult N

/-- `ECMResult.isSuccess` is `True` exactly when the result is a factor, `False` on failure. -/
def ECMResult.isSuccess {N : ℕ} : ECMResult N → Prop
  | ECMResult.factor _ _ _ _ => True
  | ECMResult.failure => False

/-- Correctness of ECM (Theorem 10.12): assume `N` has distinct prime divisors `p₁, p₂`
with `p₁ ≤ M`, the discriminant is not divisible by `N`, and reductions `P₁ ∈ E(𝔽_{p₁})`,
`P₂ ∈ E(𝔽_{p₂})` are such that `|P₁|` is `ℓ₁`-smooth (with `|P₁| ≤ (√p₁ + 1)²`) but
`|P₂|` is not. Then the partial scalar kills `P₁` modulo `p₁` while leaving `P₂`
nonzero modulo `p₂`, so the gcd step exposes a nontrivial factor of `N`. -/
theorem ecm_correctness
    (cfg : ECMConfig) (params : ECMCurveParams)

    (p₁ p₂ : ℕ) [Fact (Nat.Prime p₁)] [Fact (Nat.Prime p₂)] (_hne : p₁ ≠ p₂)
    (_hdvd₁ : p₁ ∣ cfg.N) (_hdvd₂ : p₂ ∣ cfg.N)

    (hp₁M : p₁ ≤ cfg.M)

    (_hdisc : ¬ (↑cfg.N : ℤ) ∣ params.disc)

    (ℓ₁ : ℕ) (_hℓ₁_prime : Nat.Prime ℓ₁) (_hℓ₁_bound : ℓ₁ < cfg.B)

    (P₁ : (params.curveModP p₁).Point) (P₂ : (params.curveModP p₂).Point)

    (hsmooth₁ : addOrderOf P₁ ∈ Nat.smoothNumbers (ℓ₁ + 1))

    (hord₁_bound : addOrderOf P₁ ≤ (Nat.sqrt p₁ + 1) ^ 2)

    (hnotsmooth₂ : addOrderOf P₂ ∉ Nat.smoothNumbers (ℓ₁ + 1)) :

    (ecmPartialScalar ℓ₁ cfg.M) • P₁ = 0 ∧
    (ecmPartialScalar ℓ₁ cfg.M) • P₂ ≠ 0 := by
  constructor
  ·

    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    have hord₁_pos : addOrderOf P₁ ≠ 0 :=
      (Nat.mem_smoothNumbers.mp hsmooth₁).1
    apply smooth_dvd_ecmPartialScalar hord₁_pos hsmooth₁

    calc addOrderOf P₁
        ≤ (Nat.sqrt p₁ + 1) ^ 2 := hord₁_bound
      _ ≤ (Nat.sqrt cfg.M + 1) ^ 2 := by
          apply Nat.pow_le_pow_left
          exact Nat.add_le_add_right (Nat.sqrt_le_sqrt hp₁M) 1
  ·


    intro h
    apply hnotsmooth₂
    exact Nat.mem_smoothNumbers_of_dvd (ecmPartialScalar_smooth ℓ₁ cfg.M)
      (addOrderOf_dvd_of_nsmul_eq_zero h)

end
