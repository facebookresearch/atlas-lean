/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra

open Module FiniteDimensional

namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real vector space carrying a symplectic form must have even dimension: if $\Omega$ is a
nondegenerate alternating form on $V$, then $\dim_\mathbb{R} V \in 2\mathbb{N}$. -/
theorem symplectic_even_dim [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω) :
    Even (finrank ℝ V) := by
  set n := finrank ℝ V
  set b := finBasis ℝ V
  set M := LinearMap.BilinForm.toMatrix b Ω

  have hskew : M.transpose = -M := by
    ext i j
    simp only [M, LinearMap.BilinForm.toMatrix_apply, Matrix.transpose_apply, Matrix.neg_apply]
    exact sympl_skew hΩ.alt (b j) (b i)

  have hNondeg : Ω.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hΩ.alt.isRefl).mpr hΩ.nondeg
  have hdet : M.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hNondeg

  have key : M.det = (-1 : ℝ) ^ n * M.det := by
    calc M.det = M.transpose.det := (Matrix.det_transpose M).symm
    _ = (-M).det := by rw [hskew]
    _ = (-1) ^ Fintype.card (Fin n) * M.det := Matrix.det_neg M
    _ = (-1 : ℝ) ^ n * M.det := by rw [Fintype.card_fin]

  have h6 : (-1 : ℝ) ^ n = 1 := by
    have : (-1 : ℝ) ^ n * M.det = 1 * M.det := by linarith
    exact mul_right_cancel₀ hdet this

  rwa [neg_one_pow_eq_one_iff_even] at h6
  norm_num

end SymplecticLinearAlgebra
