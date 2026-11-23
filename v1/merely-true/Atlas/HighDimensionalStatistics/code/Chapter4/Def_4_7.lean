/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.StarOrdered

open Matrix Real

noncomputable section

/-- **Definition 4.7** (Spiked covariance model). The matrix `S` follows the spiked
covariance model with spike strength `θ > 0` and unit spike direction `v` if
$\Sigma = \theta v v^\top + I_d$. -/
def IsSpikedCovariance {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < θ ∧ ‖v‖ = 1 ∧ S = θ • (vecMulVec v v) + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The principal angle between two vectors `u` and `v`, defined as
$\arccos(|\langle u, v\rangle|)$ — always in $[0, \pi/2]$. -/
noncomputable def principalAngle {d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  arccos |@inner ℝ _ _ u v|

/-- A spiked covariance matrix is positive semidefinite. -/
theorem IsSpikedCovariance.posSemidef {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    {θ : ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (h : IsSpikedCovariance S θ v) : S.PosSemidef := by
  obtain ⟨hθ, _, hS⟩ := h
  rw [hS]
  apply PosSemidef.add
  · have : vecMulVec (v : Fin d → ℝ) v = vecMulVec v (star v) := by
      simp [star_trivial]
    rw [this]
    exact (posSemidef_vecMulVec_self_star v).smul (le_of_lt hθ)
  · exact PosSemidef.one

/-- A spiked covariance matrix is Hermitian (symmetric in the real case). -/
theorem IsSpikedCovariance.isHermitian {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    {θ : ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (h : IsSpikedCovariance S θ v) : S.IsHermitian :=
  h.posSemidef.isHermitian

/-- A unit vector dotted with itself equals one. -/
lemma dotProduct_self_eq_one_of_norm_eq_one {d : ℕ} {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) : (v : Fin d → ℝ) ⬝ᵥ v = 1 := by
  have h1 : @inner ℝ _ _ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  rw [show (v : Fin d → ℝ) ⬝ᵥ v = @inner ℝ _ _ v v from by simp [inner, dotProduct]]
  exact h1

/-- The spike direction `v` is an eigenvector of the spiked covariance with eigenvalue
`1 + θ`. -/
theorem IsSpikedCovariance.mulVec_spike {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    {θ : ℝ} {v : EuclideanSpace ℝ (Fin d)}
    (h : IsSpikedCovariance S θ v) :
    S.mulVec v = (1 + θ) • v := by
  obtain ⟨_, hv, hS⟩ := h
  rw [hS]
  simp only [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
  rw [dotProduct_self_eq_one_of_norm_eq_one hv]
  ext i
  simp [add_comm, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- The principal angle is nonnegative. -/
theorem principalAngle_nonneg {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ principalAngle u v :=
  arccos_nonneg _

/-- The principal angle is bounded above by `π`. -/
theorem principalAngle_le_pi {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    principalAngle u v ≤ π :=
  arccos_le_pi _

/-- The principal angle is at most `π/2` (since `arccos` is taken of an absolute value). -/
theorem principalAngle_le_pi_div_two {d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) :
    principalAngle u v ≤ π / 2 := by
  unfold principalAngle
  rw [show π / 2 = arccos 0 from by simp [arccos_zero]]
  exact arccos_le_arccos (abs_nonneg _)

/-- The principal angle is symmetric in its two arguments. -/
theorem principalAngle_comm {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    principalAngle u v = principalAngle v u := by
  unfold principalAngle
  congr 1
  rw [abs_eq_abs]
  left
  exact (real_inner_comm u v).symm

end
