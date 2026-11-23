/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Atlas.DifferentialAnalysis.code.DifferentialOperators

open scoped SchwartzMap
open MvPolynomial SchwartzMap

noncomputable section

namespace SmoothingOperators

open scoped LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]







end SmoothingOperators

namespace DifferentialOperators

variable {n : ℕ}

/-- Evaluation of a multivariate complex polynomial at a real Euclidean point,
viewed as a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
def evalAtReal (P : MvPolynomial (Fin n) ℂ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  MvPolynomial.eval (fun i => (ξ i : ℂ)) P

/-- The polynomial `P` has a polynomial lower bound of degree `m` with
constant `C > 0` if, for every `ξ` of norm larger than `1/C`, the
inequality `‖P(ξ)‖ ≥ C · ‖ξ‖^m` holds. -/
def HasPolyLowerBound (P : MvPolynomial (Fin n) ℂ) (m : ℕ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
    ‖ξ‖ > 1 / C → ‖evalAtReal P ξ‖ ≥ C * ‖ξ‖ ^ m

/-- The pointwise reciprocal of a polynomial: `ξ ↦ 1 / P(ξ)`, with
`P(ξ) = 0` mapped to `0` by the inverse convention. -/
def polyReciprocal (P : MvPolynomial (Fin n) ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun ξ => (evalAtReal P ξ)⁻¹


end DifferentialOperators

end
