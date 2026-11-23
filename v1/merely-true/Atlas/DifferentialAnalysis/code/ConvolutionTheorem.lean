/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.SchwartzTranslation
import Atlas.DifferentialAnalysis.code.HormanderFundamental
import Atlas.DifferentialAnalysis.code.DistributionSupport
import Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Atlas.DifferentialAnalysis.code.SobolevEmbedding

open scoped SchwartzMap LineDeriv Pointwise
open TemperedDistribution SchwartzMap DifferentialOperators Distribution
     SobolevSpace SchwartzRepresentation

noncomputable section

namespace DifferentialOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The convolution of a tempered distribution `u` with a Schwartz function `φ`, viewed
as a function `x ↦ ⟨u, φ(· - x)⟩` on `E`. -/
noncomputable def tempDistSchwartzConv
    (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) : E → ℂ :=
  fun x => u (compSubConstCLM ℂ x φ)

/-- Pointwise unfolding of `tempDistSchwartzConv`: its value at `x` is `u` applied to the
translated Schwartz function `y ↦ φ(y - x)`. -/
@[simp]
theorem tempDistSchwartzConv_apply
    (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) (x : E) :
    tempDistSchwartzConv u φ x = u (compSubConstCLM ℂ x φ) := rfl


/-- The convolution `tempDistSchwartzConv u φ` of a tempered distribution `u` with a
Schwartz function `φ` has polynomial growth: there exist `k : ℕ` and `C ≥ 0` such that
`‖(u * φ)(x)‖ ≤ C (1 + ‖x‖)^k` for all `x`. -/
theorem tempDistSchwartzConv_polynomial_growth
    (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x : E,
      ‖tempDistSchwartzConv u φ x‖ ≤ C * (1 + ‖x‖) ^ k := by

  let q : Seminorm ℂ 𝓢(E, ℂ) := (normSeminorm ℂ ℂ).comp u.toLinearMap
  have hq_cont : Continuous q := continuous_norm.comp u.cont
  obtain ⟨s, C_u, _, hCu_le⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq_cont

  let k : ℕ := s.sup (fun m => m.1)

  let C_φ : NNReal := s.sup (fun m =>
    ⟨(Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ,
     apply_nonneg _ _⟩)
  refine ⟨k, ↑C_u * 2 ^ k * ↑C_φ, by positivity, fun x => ?_⟩

  have h1 : q (compSubConstCLM ℂ x φ) ≤
      (C_u • s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) :=
    hCu_le (compSubConstCLM ℂ x φ)

  have h2 : (s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) ≤
      (1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro m hm
    have hbound := TemperedDistributions.SchwartzMap.seminorm_compSubConst_le ℂ m.1 m.2 φ x
    have hm1_le : m.1 ≤ k := Finset.le_sup (f := fun m => m.1) hm
    have h1x : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hCφ_le : (Finset.Iic (m.1, m.2)).sup
        (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ ≤ ↑C_φ := by
      exact_mod_cast Finset.le_sup (f := fun m : ℕ × ℕ =>
        (⟨(Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ,
          apply_nonneg _ _⟩ : NNReal)) hm
    calc SchwartzMap.seminorm ℂ m.1 m.2 (compSubConstCLM ℂ x φ)
        ≤ (1 + ‖x‖) ^ m.1 * 2 ^ m.1 *
            (Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ :=
          hbound
      _ ≤ (1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ := by
          have hp1 := pow_le_pow_right₀ h1x hm1_le
          have hp2 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm1_le
          calc (1 + ‖x‖) ^ m.1 * 2 ^ m.1 *
                ((Finset.Iic (m.1, m.2)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ
              ≤ (1 + ‖x‖) ^ k * 2 ^ k *
                ((Finset.Iic (m.1, m.2)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ := by
                  apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
                  exact mul_le_mul hp1 hp2 (by positivity) (by positivity)
            _ ≤ (1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ := by
                  exact mul_le_mul_of_nonneg_left hCφ_le (by positivity)


  have h3 : q (compSubConstCLM ℂ x φ) = ‖u (compSubConstCLM ℂ x φ)‖ := rfl
  calc ‖u (compSubConstCLM ℂ x φ)‖
      = q (compSubConstCLM ℂ x φ) := h3.symm
    _ ≤ (C_u • s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) := h1
    _ = ↑C_u * (s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) := rfl
    _ ≤ ↑C_u * ((1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ↑C_u * 2 ^ k * ↑C_φ * (1 + ‖x‖) ^ k := by ring







end DifferentialOperators

end
