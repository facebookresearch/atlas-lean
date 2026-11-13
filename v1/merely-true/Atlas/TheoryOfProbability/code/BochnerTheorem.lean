/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.CharacteristicFunction

open MeasureTheory Complex

namespace ProbabilityTheory

/-- A complex-valued function `φ : ℝ → ℂ` is *positive definite* if for every
finite collection of times `t : Fin n → ℝ` and complex coefficients
`z : Fin n → ℂ`, the Hermitian form
`∑_{i,j} φ(t_i - t_j) z_i \overline{z_j}` has nonnegative real part.
Equivalently, the matrix `(φ(t_i - t_j))_{i,j}` is positive semidefinite. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (z : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, φ (t i - t j) * z i * starRingEnd ℂ (z j)).re

/-- A real-valued function `φ : ℝ → ℝ` is *positive definite* if its complex
embedding `(↑) ∘ φ : ℝ → ℂ` is positive definite in the sense of
`IsPositiveDefinite`. -/
def IsPositiveDefiniteReal (φ : ℝ → ℝ) : Prop :=
  IsPositiveDefinite ((↑) ∘ φ)

/-- A function `φ : ℝ → ℂ` is a *characteristic function* if it arises as the
characteristic function `t ↦ ∫ e^{itx} dμ(x)` of some probability measure
`μ` on `ℝ`. -/
def IsCharacteristicFun (φ : ℝ → ℂ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = φ t

/-- A real-valued function `φ : ℝ → ℝ` is a characteristic function if its
complex embedding `(↑) ∘ φ` is. -/
def IsCharacteristicFunReal (φ : ℝ → ℝ) : Prop :=
  IsCharacteristicFun ((↑) ∘ φ)



end ProbabilityTheory
