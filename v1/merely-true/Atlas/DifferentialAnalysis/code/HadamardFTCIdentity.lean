/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp

open scoped SchwartzMap
open MeasureTheory

noncomputable section

namespace HadamardDecomposition

/-- Helper for the Hadamard / fundamental-theorem-of-calculus identity: the map
`t ↦ (Dφ)(t · x) v` is continuous, since it is the composition of the continuous
Schwartz Fréchet derivative `Dφ`, the continuous ray `t ↦ t · x`, and continuous
evaluation at the fixed vector `v`. -/
lemma continuous_fderiv_comp_smul_path {n : ℕ}
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x v : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun t : ℝ => fderiv ℝ (⇑φ) (t • x) v) := by
  have h1 : Continuous (⇑(SchwartzMap.fderivCLM ℝ
      (EuclideanSpace ℝ (Fin n)) ℂ φ)) :=
    (SchwartzMap.fderivCLM ℝ _ ℂ φ).continuous
  have h2 : Continuous (fun t : ℝ => t • x) :=
    continuous_id.smul continuous_const
  have h3 : Continuous (fun t : ℝ => (⇑(SchwartzMap.fderivCLM ℝ _ ℂ φ)) (t • x)) :=
    h1.comp h2
  exact h3.clm_apply continuous_const

end HadamardDecomposition
