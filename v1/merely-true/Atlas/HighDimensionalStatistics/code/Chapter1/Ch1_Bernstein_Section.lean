/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Prop_1_1_full
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_5
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_13
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_8
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_16
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19

open MeasureTheory Real Set Measure ProbabilityTheory

/-- **Proposition 1.1 (Gaussian Mills' tail bound).** For the standard normal
distribution and `t > 0`, the upper-tail probability satisfies
`P(X > t) ≤ (1 / √(2π)) · t⁻¹ · exp(-t²/2)`. -/
theorem proposition_1_1 (t : ℝ) (ht : 0 < t) :
    gaussianReal 0 1 (Ioi t) ≤
      ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹ * t⁻¹ * Real.exp (-(t ^ 2 / 2))) :=
  Rigollet.Chapter1.proposition_1_1_mills_prob_upper t ht

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Theorem 1.13 (Bernstein's inequality).** For independent sub-exponential
variables `X₁,…,Xₙ` with parameter `λ`, both the upper and lower tails of the
sample mean satisfy
`P(X̄ ≥ t), P(X̄ ≤ -t) ≤ exp(-(n/2) · min(t²/λ², t/λ))`. -/
theorem theorem_1_13 {n : ℕ} {X : Fin n → Ω → ℝ} {t lambda : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hlam : 0 < lambda)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (hSubExp : ∀ i, @IsSubExponential _ _ (μ := μ) _ (X i) lambda)
    (hInt : ∀ i (s : ℝ), |s| ≤ 1 / lambda →
      Integrable (fun ω => Real.exp (s * X i ω)) μ) :
    max (μ.real {ω | t ≤ 1 / ↑n * ∑ i, X i ω})
        (μ.real {ω | 1 / ↑n * ∑ i, X i ω ≤ -t}) ≤
      Real.exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) :=
  theorem_1_13_bernstein_inequality hn ht hlam hIndep hMeas hSubExp hInt

/-- **Lemma 1.15 (Bounded random variables are sub-Gaussian).** A centered
random variable `X` taking values in `[a,b]` almost surely is sub-Gaussian
with variance proxy `(b-a)²/4`. This is the Hoeffding lemma packaged as
Lemma 1.15. -/
theorem lemma_1_15_bounded_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hab : a < b) (hMeas : Measurable X) (hInt : Integrable X μ)
    (ha : ∀ᵐ ω ∂μ, a ≤ X ω) (hb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hMean : ∫ ω, X ω ∂μ = 0) :
    IsSubGaussian X ((b - a) ^ 2 / 4) μ :=
  lemma_1_8_hoeffding hab hMeas hInt ha hb hMean

/-- **Theorem 1.16 (Maximum over a polytope of sub-Gaussian linear forms).**
If the linear forms `ω ↦ g(ω)(v)` are sub-Gaussian for each vertex `v ∈ S`,
then the probability that the supremum over the convex hull of `S` exceeds `t`
is at most `|S|` times the standard sub-Gaussian tail bound. -/
theorem theorem_1_16 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : Ω → E →ₗ[ℝ] ℝ) (S : Finset E) {σsq : ℝ}
    (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => (g ω) v) σsq μ) (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ ∈ (convexHull ℝ) ↑S, (g ω) θ > t} ≤
      S.card • ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * σsq)))) :=
  theorem_1_16_polytope_subgaussian g S hsg t ht

/-- **Definition 1.17 / existence of ε-nets.** For any set `K` in a pseudo
metric space and any `ε > 0`, there exists a maximal `ε`-separated subset
`N ⊆ K` (any two distinct points are at distance `> ε`) which is also an
ε-net of `K` (every `z ∈ K` is within `ε` of some `x ∈ N`). -/
theorem def_1_17_epsilon_net_exists {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, N ⊆ K ∧ (∀ x ∈ N, ∀ y ∈ N, x ≠ y → ε < dist x y) ∧
      ∀ z ∈ K, ∃ x ∈ N, dist x z ≤ ε :=
  exists_maximal_separated_net K ε hε

/-- **Theorem 1.19 (Expectation bound for sub-Gaussian random vectors).**
If `X` is a `d`-dimensional sub-Gaussian random vector with proxy `σ²`, then
`E ‖X‖ ≤ 4 √σ² · √d`. -/
theorem theorem_1_19_expectation {d : ℕ} (hd : 0 < d)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {_ : IsProbabilityMeasure μ}
    {X : Ω → EuclideanSpace ℝ (Fin d)} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ) :
    ∫ ω, ‖X ω‖ ∂μ ≤ 4 * Real.sqrt σsq * Real.sqrt d :=
  theorem_1_19_expectation_bound hd hσ hsg

/-- **Theorem 1.19 (Tail bound for the supremum of sub-Gaussian linear forms
on the unit ball).** With `X` a sub-Gaussian random vector with proxy `σ²`,
the probability that `sup_{‖θ‖≤1} ⟨θ, X⟩` exceeds `t` is bounded by
`6^d · exp(-t²/(8σ²))`. -/
theorem theorem_1_19_tail {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ (Fin d)} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t} ≤
      ENNReal.ofReal ((6 : ℝ) ^ d * Real.exp (-(t ^ 2 / (8 * σsq)))) :=
  theorem_1_19_tail_bound hd hσ hsg t ht

/-- **Theorem 1.19 (High-probability norm bound for a sub-Gaussian random
vector).** With probability at least `1 - δ`,
`‖X‖ ≤ 4 √σ² · √d + 2 √σ² · √(2 log(1/δ))`. -/
theorem theorem_1_19_high_probability {d : ℕ} (hd : 0 < d)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {_ : IsProbabilityMeasure μ}
    {X : Ω → EuclideanSpace ℝ (Fin d)} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    μ {ω | ‖X ω‖ > 4 * Real.sqrt σsq * Real.sqrt d +
        2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ))} ≤
      ENNReal.ofReal δ :=
  theorem_1_19_high_prob hd hσ hsg hδ_pos hδ_lt
