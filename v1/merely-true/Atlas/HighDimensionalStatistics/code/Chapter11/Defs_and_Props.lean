/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 800000

noncomputable section

open scoped SchwartzMap
open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

/-- A constant-coefficient differential operator on tempered distributions: a
nonzero continuous `ℂ`-linear endomorphism of `𝓢'(E, ℂ)`. -/
structure ConstCoeffDiffOp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The underlying continuous linear map on tempered distributions. -/
  toDistribCLM : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)
  /-- The operator is nonzero. -/
  ne_zero : toDistribCLM ≠ 0

/-- A tempered distribution `E_sol` is a fundamental solution of `P` if
`P(E_sol) = δ₀`. -/
def IsTemperedFundamentalSolution
    (P : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (E_sol : 𝓢'(E, ℂ)) : Prop :=
  P E_sol = TemperedDistribution.delta 0

/-- Alias for `IsTemperedFundamentalSolution` matching the textbook numbering
(Definition 11.3). -/
abbrev def_11_3_fundamental_solution := @IsTemperedFundamentalSolution

section Prop_11_1

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]

end Prop_11_1

section Prop_11_2

end Prop_11_2

section Lemma_11_5

/-- The first standard basis vector `(1, 0)` of `ℝ²`. -/
def e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second standard basis vector `(0, 1)` of `ℝ²`. -/
def e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- The Cauchy–Riemann (∂̄) operator `(1/2)(∂_x + i ∂_y)` acting on tempered
distributions on `ℝ²`. -/
def dbarOp : 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  (1 / 2 : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) e₁
  + Complex.I • LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) e₂)

/-- The Cauchy kernel `(2π)⁻¹ (x + i y)⁻¹` viewed as a function on `ℝ × ℝ`, a
fundamental solution of the ∂̄ operator. -/
def cauchyRiemannKernel : ℝ × ℝ → ℂ := fun p =>
  (2 * Real.pi)⁻¹ * (↑p.1 + Complex.I * ↑p.2)⁻¹

end Lemma_11_5

section Def_11_8

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]

/-- The singular support of a tempered distribution `u`: the set of points near
which `u` cannot be locally represented by a Schwartz function. -/
def SingularSupport (u : 𝓢'(E, ℂ)) : Set E :=
  {x : E |
    ∀ (φ : E → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ x ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ∉
        Set.range (SchwartzMap.toTemperedDistributionCLM E ℂ)}

/-- `F` is a parametrix for `P` if `P F` agrees with `δ₀` modulo a smooth
(Schwartz) error term. -/
def IsParametrix
    (P : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (F : 𝓢'(E, ℂ)) : Prop :=
  P F - TemperedDistribution.delta 0 ∈
    Set.range (SchwartzMap.toTemperedDistributionCLM E ℂ)

/-- `P` is hypoelliptic if it admits a parametrix whose singular support is
contained in `{0}`. -/
def IsHypoelliptic
    (P : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) : Prop :=
  ∃ F : 𝓢'(E, ℂ), IsParametrix E P F ∧ SingularSupport E F ⊆ {0}

/-- Textbook alias for `IsParametrix` (Definition 11.8, parametrix part). -/
abbrev def_11_8_parametrix := @IsParametrix

/-- Textbook alias for `IsHypoelliptic` (Definition 11.8, hypoelliptic part). -/
abbrev def_11_8_hypoelliptic := @IsHypoelliptic

end Def_11_8

/-- A polynomial symbol `P` is elliptic of order `m` if its degree-`m` homogeneous
component is nonvanishing on `ℝⁿ \ {0}`. -/
def IsElliptic {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (m : ℕ) : Prop :=
  ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (MvPolynomial.homogeneousComponent m P) ≠ 0

/-- Textbook alias for `IsElliptic` (Definition 11.11). -/
abbrev def_11_11_elliptic := @IsElliptic

end Chapter11
