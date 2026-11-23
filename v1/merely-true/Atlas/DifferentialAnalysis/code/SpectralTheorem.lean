/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Atlas.DifferentialAnalysis.code.HilbertSpace

noncomputable section

open scoped ComplexInnerProductSpace

namespace SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectrum of a bounded operator on a complex Banach space is compact. -/
theorem spectrum_isCompact (T : H →L[ℂ] H) :
    IsCompact (spectrum ℂ T) :=
  spectrum.isCompact T

/-- The spectrum of a bounded operator is contained in the closed ball of radius `‖T‖`. -/
theorem spectrum_subset_closedBall_norm [NontrivialTopology H] (T : H →L[ℂ] H) :
    spectrum ℂ T ⊆ Metric.closedBall (0 : ℂ) ‖T‖ :=
  spectrum.subset_closedBall_norm T

/-- The spectrum of a bounded operator is compact and contained in the closed ball of radius `‖T‖`. -/
theorem spectrum_compact_subset_closedBall [NontrivialTopology H] (T : H →L[ℂ] H) :
    IsCompact (spectrum ℂ T) ∧ spectrum ℂ T ⊆ Metric.closedBall (0 : ℂ) ‖T‖ :=
  ⟨spectrum_isCompact T, spectrum_subset_closedBall_norm T⟩

open Polynomial in
/-- Polynomial functional calculus norm bound for self-adjoint operators: the operator
norm of `q(A)` is bounded by any uniform bound on `|q(t)|` over the spectrum. -/
theorem norm_polynomial_selfAdjoint_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (q : ℝ[X]) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ t ∈ spectrum ℝ A, ‖eval t q‖ ≤ c) :
    ‖aeval A q‖ ≤ c := by
  rw [← cfc_polynomial q A hA]
  exact norm_cfc_le hc hbound

open Polynomial in
/-- Variant of `norm_polynomial_selfAdjoint_le` where the bound is verified on a containing
interval `[m, M]` of the spectrum. -/
theorem norm_polynomial_selfAdjoint_le_Icc (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (q : ℝ[X]) (m M : ℝ)
    (hspec : spectrum ℝ A ⊆ Set.Icc m M) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ t ∈ Set.Icc m M, ‖eval t q‖ ≤ c) :
    ‖aeval A q‖ ≤ c :=
  norm_polynomial_selfAdjoint_le A hA q hc fun t ht => hbound t (hspec ht)

end SpectralTheorem

end
