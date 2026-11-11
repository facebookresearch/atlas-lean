/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.WavefrontSetProducts
import Atlas.DifferentialAnalysis.code.WavefrontCharacterization

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory

namespace WavefrontSet

variable {n : ℕ}






/-- A renamed wrapper around `not_mem_css_iff_neg_not_mem_css_fourier_fourier`:
non-membership in `Css u₁` at `p` is equivalent to non-membership in `Css (𝓕(𝓕 u₁))`
at `-p`. -/
theorem not_mem_css_iff_neg_not_mem_css_fourier_fourier'
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (p : ClosedBall n) :
    p ∉ Css u₁ ↔ (-p) ∉ Css (𝓕 (𝓕 u₁)) :=
  not_mem_css_iff_neg_not_mem_css_fourier_fourier u₁ p



/-- The boundary-product set is preserved under the swap-and-negate map
`(p, q) ↦ (q, -p)`. -/
theorem boundaryProd_swap_neg' {p q : ClosedBall n}
    (hpq : (p, q) ∈ BoundaryProd n) : (q, -p) ∈ BoundaryProd n := by
  simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hpq ⊢
  exact hpq.symm



end WavefrontSet

end
