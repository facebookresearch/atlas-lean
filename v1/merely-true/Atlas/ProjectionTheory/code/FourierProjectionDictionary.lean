/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory VectorFourier

noncomputable section

namespace FourierProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section WithMeasure
variable [MeasurableSpace E]

/-- Projection of `f : E → ℂ` onto a subspace `V ⊂ E`, defined by integrating out
the orthogonal directions: `(π_V f)(y) = ∫_{V^⊥} f(y + z) dμ_perp(z)`. -/
def subspaceProjection (V : Submodule ℝ E)
    (μ_perp : Measure ↥(Vᗮ))
    (f : E → ℂ) (y : ↥V) : ℂ :=
  ∫ z : ↥(Vᗮ), f ((y : E) + (z : E)) ∂μ_perp

end WithMeasure

/-- For `ξ ∈ V` and `z ∈ V^⊥`, the orthogonal component drops out of the inner
product: `⟨y + z, ξ⟩_E = ⟨y, ξ⟩_V`. This identifies the phase appearing in the
Fourier integral on `E` with the phase on `V`. -/
lemma innerₗ_add_orthogonal_eq (V : Submodule ℝ E)
    (y ξ : ↥V) (z : ↥(Vᗮ)) :
    (innerₗ E) ((↑y : E) + (↑z : E)) (↑ξ : E) = (innerₗ ↥V) y ξ := by
  simp only [innerₗ_apply_apply, inner_add_left]
  rw [V.coe_inner]
  have hz : @inner ℝ E _ (z : E) (ξ : E) = 0 :=
    Submodule.inner_left_of_mem_orthogonal ξ.2 z.2
  linarith

variable [MeasurableSpace E]

/--
Fourier projection dictionary lemma. For any subspace `V ⊂ E` and any frequency
`ξ ∈ V`,
$$\widehat{\pi_V f}(\xi) = \hat f(\xi),$$
i.e. the Fourier transform of the projection `π_V f` at `ξ ∈ V` equals the
Fourier transform of `f` at the same `ξ` viewed in `E`. The proof unfolds both
Fourier integrals, uses Fubini on the splitting `E = V ⊕ V^⊥`, and observes that
the phase `e(-⟨x, ξ⟩)` depends only on the `V`-component of `x` (since `ξ ∈ V`).
-/
theorem fourier_projection_dictionary (V : Submodule ℝ E)
    (μ_V : Measure ↥V) (μ_perp : Measure ↥(Vᗮ)) (μ_E : Measure E)
    (f : E → ℂ) (ξ : ↥V)
    (hμ : ∀ g : E → ℂ, Integrable g μ_E →
      ∫ x : E, g x ∂μ_E = ∫ y : ↥V, ∫ z : ↥(Vᗮ), g ((y : E) + (z : E)) ∂μ_perp ∂μ_V)
    (hfξ_int : Integrable (fun x => Real.fourierChar (-(innerₗ E x (ξ : E))) • f x) μ_E) :
    fourierIntegral Real.fourierChar μ_V (innerₗ ↥V) (subspaceProjection V μ_perp f) ξ =
    fourierIntegral Real.fourierChar μ_E (innerₗ E) f (↑ξ : E) := by

  simp only [fourierIntegral]


  rw [hμ _ hfξ_int]

  congr 1
  ext y


  simp_rw [innerₗ_add_orthogonal_eq V y ξ]

  simp only [subspaceProjection]
  simp_rw [Circle.smul_def]


  exact (integral_smul _ _).symm

end FourierProjection
