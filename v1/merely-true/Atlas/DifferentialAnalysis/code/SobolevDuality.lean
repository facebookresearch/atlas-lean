/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.FourierInversion

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap
open TestFunctions

noncomputable section

namespace SobolevDuality

variable (n : ℕ)

/-- The Sobolev weight `⟨ξ⟩^s = (1 + |ξ|²)^(s/2)` on the dual variable `ξ`, used to define
the Sobolev space `H^s` via the Fourier transform. -/
def sobolevWeight (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (japaneseBracket n ξ) ^ s

/-- The Sobolev weight is strictly positive everywhere. -/
theorem sobolevWeight_pos (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    0 < sobolevWeight n s ξ :=
  Real.rpow_pos_of_pos (japaneseBracket_pos n ξ) s

/-- Membership in the Sobolev space `H^s` of order `s`: a tempered distribution `u` belongs to
`H^s` if its Fourier transform `𝓕 u` is represented (against Schwartz test functions) by an `L²`
function divided by the Sobolev weight `⟨ξ⟩^s`. -/
def MemHs (s : ℝ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n) → ℂ,
    MemLp g 2 ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ

/-- The Sobolev space `H^s` as the subtype of tempered distributions satisfying `MemHs`. -/
def Hs (s : ℝ) : Type :=
  { u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) // MemHs n s u }

/-- Proposition 9.8 (Sobolev duality): the antilinear isometric isomorphism
`H^{-s} ≃ (H^s)*` identifying the Sobolev space of order `-s` with the continuous dual of `H^s`. -/
noncomputable def dualIdentification (s : ℝ) :
    SobolevSpace.Hs n (-s) ≃ₗᵢ⋆[ℂ] (SobolevSpace.Hs n s →L[ℂ] ℂ) :=
  SobolevSpace.dualIdentification n s

end SobolevDuality

end
