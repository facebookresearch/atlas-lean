/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib

open MeasureTheory Real ProbabilityTheory

noncomputable section

namespace Problem_1_4

/-- The operator (spectral) norm of an `n × m` real matrix viewed as a
continuous linear map between Euclidean spaces. -/
def matrixOpNorm {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- For a centered integrable function `f` with `exp ∘ f` integrable,
`∫ (e^{f} - 1 - f) dμ = ∫ e^{f} dμ - 1`. This is the algebraic identity
used in the analysis of `IsSubGaussian` with proxy `0`. -/
lemma integral_exp_sub_one_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ)
    (hef : Integrable (fun ω => Real.exp (f ω)) μ)
    (hmean : ∫ ω, f ω ∂μ = 0) :
    ∫ ω, (Real.exp (f ω) - 1 - f ω) ∂μ = ∫ ω, Real.exp (f ω) ∂μ - 1 := by
  calc ∫ ω, (Real.exp (f ω) - 1 - f ω) ∂μ
      = ∫ ω, ((fun ω => Real.exp (f ω) - 1) ω - f ω) ∂μ := by ring_nf
    _ = ∫ ω, (fun ω => Real.exp (f ω) - 1) ω ∂μ - ∫ ω, f ω ∂μ :=
        integral_sub (hef.sub (integrable_const 1)) hf
    _ = _ := by
        rw [hmean, sub_zero]
        show ∫ ω, (Real.exp (f ω) - 1) ∂μ = _
        calc ∫ ω, (Real.exp (f ω) - 1) ∂μ
            = ∫ ω, ((fun ω => Real.exp (f ω)) ω - (fun _ => (1:ℝ)) ω) ∂μ := by ring_nf
          _ = _ := by
              rw [integral_sub hef (integrable_const 1)]
              simp [integral_const]

/-- **Problem 1.4 key step.** A variable that is sub-Gaussian with variance
proxy `0` must equal `0` almost surely. The argument combines the MGF bound
at `s = 1` with Jensen's inequality applied to `exp`. -/
lemma subgaussian_zero_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hSG : IsSubGaussian X 0 μ) : X =ᵐ[μ] 0 := by
  obtain ⟨hint, hmean, hexp_int, hmgf⟩ := hSG
  have hmgf1 : ∀ s, ∫ ω, Real.exp (s * X ω) ∂μ ≤ 1 := by
    intro s; have := hmgf s; simp at this; exact this
  have hexp_int1 : Integrable (fun ω => Real.exp (X ω)) μ := by
    have := hexp_int 1; simp only [one_mul] at this; exact this
  have hg_nonneg : ∀ ω, 0 ≤ Real.exp (X ω) - 1 - X ω := by
    intro ω; linarith [add_one_le_exp (X ω)]
  have hg_int : Integrable (fun ω => Real.exp (X ω) - 1 - X ω) μ :=
    (hexp_int1.sub (integrable_const 1)).sub hint
  have hg_integral := integral_exp_sub_one_sub hint hexp_int1 hmean
  have h_le : ∫ ω, Real.exp (X ω) ∂μ ≤ 1 := by
    have := hmgf1 1; simp only [one_mul] at this; exact this
  have h_ge : 1 ≤ ∫ ω, Real.exp (X ω) ∂μ := by
    have hJ := convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (by simp) hint hexp_int1
    rw [hmean] at hJ; simp at hJ; exact hJ
  have hg_zero : ∫ ω, (Real.exp (X ω) - 1 - X ω) ∂μ = 0 := by
    rw [hg_integral]; linarith
  have hg_ae : (fun ω => Real.exp (X ω) - 1 - X ω) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hg_nonneg) hg_int).mp hg_zero
  exact hg_ae.mono fun ω hω => by
    simp only [Pi.zero_apply] at hω
    have : Real.exp (X ω) = 1 + X ω := by linarith
    by_contra hne
    exact absurd this (ne_of_gt (by linarith [add_one_lt_exp hne]))

end Problem_1_4
