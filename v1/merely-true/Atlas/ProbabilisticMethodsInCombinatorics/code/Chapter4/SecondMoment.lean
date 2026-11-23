/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.Variance

set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Filter

namespace SecondMoment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}

/-- Shorthand for the variance $\mathrm{Var}(X) = \mathbb{E}[(X - \mathbb{E}X)^2]$
of a random variable $X$ with respect to a measure $\mu$. -/
noncomputable abbrev Var (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ProbabilityTheory.variance X μ

end SecondMoment

namespace ProbabilityTheory

/-- **Chebyshev's inequality.** For an $L^2$ random variable $X$ and any $t > 0$,
$$\mathbb{P}\bigl(|X - \mathbb{E}X| \ge t\bigr) \le \frac{\mathrm{Var}(X)}{t^2}.$$ -/
theorem chebyshev_inequality {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / t ^ 2) :=
  meas_ge_le_variance_div_sq hX ht

/-- **Second moment bound on the probability of vanishing.** If $X \in L^2$ and
$\mathbb{E}X > 0$, then $\mathbb{P}(X = 0) \le \mathrm{Var}(X) / (\mathbb{E}X)^2$.
This is Lemma 4.2.4 (Corollary 4.1.7) in Probabilistic Methods in Combinatorics. -/
theorem prob_eq_zero_le_variance_div_sq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (hE : 0 < ∫ ω, X ω ∂μ) :
    μ {ω | X ω = 0} ≤ ENNReal.ofReal (Var[X; μ] / (∫ ω, X ω ∂μ) ^ 2) := by


  have h_sub : {ω | X ω = 0} ⊆ {ω | (∫ ω, X ω ∂μ) ≤ |X ω - ∫ ω, X ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω, zero_sub, abs_neg, abs_of_pos hE]

  calc μ {ω | X ω = 0}
      ≤ μ {ω | (∫ ω, X ω ∂μ) ≤ |X ω - ∫ ω, X ω ∂μ|} := measure_mono h_sub
    _ ≤ ENNReal.ofReal (Var[X; μ] / (∫ ω, X ω ∂μ) ^ 2) :=
        meas_ge_le_variance_div_sq hX hE

/-- **Asymptotic second moment method (single measure).** If a sequence $(X_n)$ of
$L^2$ random variables on a common probability space has $\mathbb{E}X_n > 0$ and
$\mathrm{Var}(X_n) / (\mathbb{E}X_n)^2 \to 0$, then $\mathbb{P}(X_n = 0) \to 0$. -/
theorem tendsto_prob_eq_zero_of_variance_div_sq_tendsto
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ)
    (hE : ∀ n, 0 < ∫ ω, X n ω ∂μ)
    (hVar : Tendsto (fun n => Var[X n; μ] / (∫ ω, X n ω ∂μ) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => μ {ω | X n ω = 0}) atTop (nhds 0) := by
  have hup : Tendsto (fun n => ENNReal.ofReal (Var[X n; μ] / (∫ ω, X n ω ∂μ) ^ 2)) atTop (nhds 0) := by
    have h := ENNReal.tendsto_ofReal hVar
    rwa [ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => zero_le _) (fun n => prob_eq_zero_le_variance_div_sq (hX n) (hE n))

open scoped Topology in
/-- **Second moment method (Corollary 4.1.8).** Given a sequence of probability spaces
$(\Omega_n, \mu_n)$ and $L^2$ random variables $X_n$ with $\mathbb{E}_{\mu_n}[X_n] > 0$,
if $\mathrm{Var}(X_n) / (\mathbb{E}X_n)^2 \to 0$ then $\mu_n(X_n = 0) \to 0$. -/
theorem second_moment_method
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n))
    (hμ_pos : ∀ n, 0 < (μ n)[X n])
    (hVar : Tendsto (fun n => Var[X n ; μ n] / (μ n)[X n] ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n) {ω | X n ω = 0}) atTop (𝓝 0) := by
  have h_upper_tends : Tendsto (fun n => ENNReal.ofReal (Var[X n ; μ n] / (μ n)[X n] ^ 2))
      atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hVar
    rwa [ENNReal.ofReal_zero] at this
  have h_bound : ∀ n, (μ n) {ω | X n ω = 0} ≤
      ENNReal.ofReal (Var[X n ; μ n] / (μ n)[X n] ^ 2) :=
    fun n => prob_eq_zero_le_variance_div_sq (hX n) (hμ_pos n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper_tends
    (fun n => zero_le _) h_bound

end ProbabilityTheory
