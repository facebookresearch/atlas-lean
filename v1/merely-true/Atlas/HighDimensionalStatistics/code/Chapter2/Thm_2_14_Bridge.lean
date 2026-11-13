/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_4
import Mathlib

open Matrix MeasureTheory Metric Set Real ENNReal Finset

noncomputable section

/-- Identification `Fin n → ℝ → EuclideanSpace ℝ (Fin n)` used to switch between
pointwise and Euclidean representations. -/
abbrev toEuc (n : ℕ) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm

/-- Inverse of `toEuc`: forgets the Euclidean structure. -/
abbrev fromEuc (n : ℕ) : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) :=
  (WithLp.equiv 2 (Fin n → ℝ))

/-- The `dotProduct` of two vectors agrees with the Euclidean inner product of their
Euclidean images. -/
lemma dotProduct_eq_inner_euclidean {n : ℕ} (v w : Fin n → ℝ) :
    dotProduct v w = @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (toEuc n v) (toEuc n w) := by
  simp only [PiLp.inner_apply, WithLp.equiv_symm_apply, dotProduct, toEuc]
  congr 1; ext i
  simp [inner, Inner.inner, mul_comm]

/-- Euclidean norm equals the square root of the dot product. -/
lemma euclidean_norm_eq_sqrt_dotProduct {n : ℕ} (v : Fin n → ℝ) :
    ‖toEuc n v‖ = Real.sqrt (dotProduct v v) := by
  have h : dotProduct v v = ‖toEuc n v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [dotProduct, WithLp.equiv_symm_apply, toEuc]
    congr 1; ext i; simp [sq_abs]; ring
  rw [h, Real.sqrt_sq (norm_nonneg _)]

/-- `‖v‖ ≤ 1` iff `⟨v, v⟩ ≤ 1`. -/
lemma euclidean_norm_le_one_iff {n : ℕ} (v : Fin n → ℝ) :
    ‖toEuc n v‖ ≤ 1 ↔ dotProduct v v ≤ 1 := by
  rw [euclidean_norm_eq_sqrt_dotProduct, sqrt_le_one]

/-- Transports a sub-Gaussian projection assumption phrased with `dotProduct` to one
phrased with the Euclidean inner product. -/
lemma subgaussian_inner_from_dotProduct
    {p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → Fin p → ℝ} {σsq : ℝ}
    (hsg : ∀ (a : Fin p → ℝ), dotProduct a a ≤ 1 →
      IsSubGaussian (fun ω => dotProduct a (Z ω)) σsq μ)
    (θ : EuclideanSpace ℝ (Fin p)) (hθ : ‖θ‖ ≤ 1) :
    IsSubGaussian (fun ω => @inner ℝ _ _ θ (toEuc p (Z ω))) σsq μ := by

  have hconv : ∀ ω, @inner ℝ (EuclideanSpace ℝ (Fin p)) _ θ (toEuc p (Z ω)) =
      dotProduct (fromEuc p θ) (Z ω) := by
    intro ω
    conv_lhs => rw [show θ = toEuc p (fromEuc p θ) from
      ((WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ).symm]
    exact (dotProduct_eq_inner_euclidean (fromEuc p θ) (Z ω)).symm

  have hunit : dotProduct (fromEuc p θ) (fromEuc p θ) ≤ 1 := by
    rw [← euclidean_norm_le_one_iff]
    rw [show toEuc p (fromEuc p θ) = θ from
      (WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ]
    exact hθ

  have h := hsg (fromEuc p θ) hunit
  simp_rw [hconv]
  exact h

/-- If the coordinates `ε_i` are independent sub-Gaussians with variance proxy `σ²`,
then any unit-norm linear combination `⟨a, ε⟩` is sub-Gaussian with the same proxy. -/
lemma subgaussian_inner_from_coord
    {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : Ω → Fin n → ℝ} {σsq : ℝ} (hσ : 0 ≤ σsq)
    (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) σsq μ)
    (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ)
      (fun i ω => ε ω i) μ)
    (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
    (a : EuclideanSpace ℝ (Fin n)) (ha : ‖a‖ ≤ 1) :
    IsSubGaussian (fun ω => @inner ℝ _ _ a (toEuc n (ε ω))) σsq μ := by
  apply subgaussian_inner_from_dotProduct _ a ha
  intro v hv

  have hdot_eq : ∀ ω, dotProduct v (ε ω) = ∑ i : Fin n, v i * ε ω i := by
    intro ω; simp only [dotProduct]
  simp_rw [hdot_eq]

  have h16 := theorem_1_6_subgaussian_vector hε hε_indep hε_meas v

  have hdvv : ∑ i : Fin n, v i ^ 2 = dotProduct v v := by
    simp only [dotProduct]; congr 1; ext i; ring
  exact h16.mono_variance (by
    rw [hdvv]
    calc σsq * dotProduct v v ≤ σsq * 1 := mul_le_mul_of_nonneg_left hv hσ
      _ = σsq := mul_one _)

/-- Vector form of the supremum-of-projections tail bound (a `dotProduct`-flavoured
restatement of Theorem 1.19): for sub-Gaussian projections, the probability that some
unit vector `θ` satisfies `⟨θ, Z⟩ > t` is at most `6^p · exp(-t²/(8σ²))`. -/
theorem theorem_1_19_tail_bound_vec
    {p : ℕ} (hp : 0 < p)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → Fin p → ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hsg : ∀ (a : Fin p → ℝ), dotProduct a a ≤ 1 →
      IsSubGaussian (fun ω => dotProduct a (Z ω)) σsq μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ θ : Fin p → ℝ, dotProduct θ θ ≤ 1 ∧ dotProduct θ (Z ω) > t} ≤
      ENNReal.ofReal ((6 : ℝ) ^ p * Real.exp (-(t ^ 2 / (8 * σsq)))) := by


  set X' : Ω → EuclideanSpace ℝ (Fin p) := fun ω => toEuc p (Z ω) with hX'_def

  have hsg' : ∀ (a : EuclideanSpace ℝ (Fin p)), ‖a‖ ≤ 1 →
      IsSubGaussian (fun ω => @inner ℝ _ _ a (X' ω)) σsq μ := by
    intro a ha
    exact subgaussian_inner_from_dotProduct hsg a ha

  have h_tail := theorem_1_19_tail_bound hp hσ hsg' t ht


  suffices h_eq :
      {ω | ∃ θ : Fin p → ℝ, dotProduct θ θ ≤ 1 ∧ dotProduct θ (Z ω) > t} =
      {ω | ∃ θ' : EuclideanSpace ℝ (Fin p), ‖θ'‖ ≤ 1 ∧
        @inner ℝ _ _ θ' (X' ω) > t} by
    rw [h_eq]; exact h_tail
  ext ω
  constructor
  ·
    rintro ⟨θ, hθ_unit, hθ_inner⟩
    refine ⟨toEuc p θ, ?_, ?_⟩
    · rwa [euclidean_norm_le_one_iff]
    · rw [hX'_def, ← dotProduct_eq_inner_euclidean]
      exact hθ_inner
  ·
    rintro ⟨θ', hθ'_norm, hθ'_inner⟩
    refine ⟨fromEuc p θ', ?_, ?_⟩
    · rw [← euclidean_norm_le_one_iff]
      rwa [show toEuc p (fromEuc p θ') = θ' from
        (WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ']
    · rw [hX'_def] at hθ'_inner
      conv at hθ'_inner =>
        arg 1; rw [show θ' = toEuc p (fromEuc p θ') from
          ((WithLp.equiv 2 (Fin p → ℝ)).symm_apply_apply θ').symm]
      rw [← dotProduct_eq_inner_euclidean] at hθ'_inner
      exact hθ'_inner

end
