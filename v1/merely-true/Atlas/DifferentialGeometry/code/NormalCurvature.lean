/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.Manifolds

noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

def normalCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (X : Fin n → ℝ) : ℝ :=
  (X ⬝ᵥ (secondFundamentalForm patch x).mulVec X) /
  (X ⬝ᵥ (firstFundamentalForm patch x).mulVec X)



theorem normalCurvature_denom_pos {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (X : Fin n → ℝ) (hX : X ≠ 0) :
    (0 : ℝ) < X ⬝ᵥ (firstFundamentalForm patch x).mulVec X := by
  have hG := firstFundamentalForm_posDef patch x hx
  have h := hG.dotProduct_mulVec_pos (x := X) hX
  simp only [star_trivial] at h
  exact h

theorem normalCurvature_eq_ratio {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (X : Fin n → ℝ) :
    normalCurvature patch x X =
    (X ⬝ᵥ (firstFundamentalForm patch x).mulVec ((shapeOperator patch x).mulVec X)) /
    (X ⬝ᵥ (firstFundamentalForm patch x).mulVec X) := by
  unfold normalCurvature
  congr 1

  congr 1
  have hG := firstFundamentalForm_posDef patch x hx
  have hdet : IsUnit (firstFundamentalForm patch x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  unfold shapeOperator
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]

end
