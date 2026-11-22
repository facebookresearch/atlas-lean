/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators

open scoped SchwartzMap
open TemperedDistribution MvPolynomial Set Function MeasureTheory

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- A tempered distribution `u` is *smooth* if it is represented by integration against a
smooth function `f : ℝⁿ → ℂ`, i.e. `u(ψ) = ∫ ψ · f` for all Schwartz test functions `ψ`. -/
def IsSmooth (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ⊤ f ∧
    ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u ψ = ∫ x, ψ x • f x

/-- A smooth cutoff function: a `C^∞` complex-valued function on `ℝⁿ` with compact support. -/
def IsSmoothCutoff (φ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ

/-- The singular support of a tempered distribution `u`: the set of points `x₀` for which no
smooth cutoff function `φ` with `φ x₀ ≠ 0` makes the localised distribution `φ · u` smooth. -/
def singSupp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x₀ | ¬ ∃ φ : EuclideanSpace ℝ (Fin n) → ℂ,
    IsSmoothCutoff φ ∧ φ x₀ ≠ 0 ∧ IsSmooth (smulLeftCLM ℂ φ u)}














end DifferentialOperators

end
