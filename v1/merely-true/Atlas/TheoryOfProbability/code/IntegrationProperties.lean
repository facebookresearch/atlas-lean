/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Basic properties of the Lebesgue (Bochner) integral.** Bundles the five
standard facts about integration of real-valued functions against a measure `μ`:
1. **Positivity**: if `f ≥ 0` a.e. then `∫ f dμ ≥ 0`.
2. **Linearity**: for integrable `f, g` and real scalars `a, b`,
   `∫ (a·f + b·g) dμ = a·∫ f dμ + b·∫ g dμ`.
3. **Monotonicity**: if `f ≤ g` a.e. (both integrable) then `∫ f dμ ≤ ∫ g dμ`.
4. **a.e. congruence**: if `f = g` a.e. then `∫ f dμ = ∫ g dμ`.
5. **Triangle inequality**: `|∫ f dμ| ≤ ∫ |f| dμ`. -/
theorem integration_properties :
    (∀ f : α → ℝ, (0 ≤ᵐ[μ] f) → 0 ≤ ∫ x, f x ∂μ) ∧
    (∀ (f g : α → ℝ) (a b : ℝ), Integrable f μ → Integrable g μ →
      ∫ x, (a • f x + b • g x) ∂μ = a • ∫ x, f x ∂μ + b • ∫ x, g x ∂μ) ∧
    (∀ (f g : α → ℝ), Integrable f μ → Integrable g μ → f ≤ᵐ[μ] g →
      ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ) ∧
    (∀ (f g : α → ℝ), f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ) ∧
    (∀ f : α → ℝ, ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun f hf => integral_nonneg_of_ae hf
  · intro f g a b hf hg
    have h := integral_add (hf.smul a) (hg.smul b)
    simp only [Pi.smul_apply] at h
    rw [h, integral_smul a f, integral_smul b g]
  · exact fun f g hf hg h => integral_mono_ae hf hg h
  · exact fun f g h => integral_congr_ae h
  · exact fun f => norm_integral_le_integral_norm f

end
