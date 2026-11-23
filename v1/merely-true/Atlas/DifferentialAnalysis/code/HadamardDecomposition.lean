/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped SchwartzMap

noncomputable section

namespace HadamardDecomposition

variable (n : ℕ)

/-- The `j`-th coordinate function on `EuclideanSpace ℝ (Fin n)`, viewed as a
complex-valued function. -/
def coordFun (j : Fin n) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => (x j : ℂ)

/-- The `j`-th coordinate function on `EuclideanSpace ℝ (Fin n)`, packaged as
a continuous real-linear map into `ℂ`. -/
def coordCLM (j : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj j)

/-- The plain coordinate function `coordFun n j` agrees pointwise with its
continuous-linear-map version `coordCLM n j`. -/
lemma coordFun_eq_coordCLM (j : Fin n) : coordFun n j = coordCLM n j := by
  ext x; simp [coordFun, coordCLM, EuclideanSpace.proj]

/-- Each coordinate function on Euclidean space has temperate growth (it is
linear, hence at most linearly bounded). -/
lemma coordFun_hasTemperateGrowth (j : Fin n) :
    Function.HasTemperateGrowth (coordFun n j) := by
  rw [coordFun_eq_coordCLM]; exact ContinuousLinearMap.hasTemperateGrowth _

/-- The Hadamard decomposition coefficient functions: given a Schwartz
function `φ` and a coordinate index `j`, this is the function whose value at
`x` is `∫₀¹ (∂_j φ)(t · x) dt`.  These functions appear in the identity
`φ(x) = Σⱼ xⱼ · ψⱼ(x)` when `φ` vanishes at the origin. -/
def hadamardPsiFun (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∫ t in (0:ℝ)..1, fderiv ℝ (⇑φ) ((t : ℝ) • x) (EuclideanSpace.single j 1)








end HadamardDecomposition

end
