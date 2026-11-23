/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant

namespace SOAction


section DetIsometry

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
         [FiniteDimensional k V]

/-- The determinant of any isometry of a nondegenerate bilinear form satisfies $(\det g)^2 = 1$. -/
theorem isometry_det_sq_eq_one
    (B : LinearMap.BilinForm k V) (hnd : B.Nondegenerate)
    (g : V ≃ₗ[k] V) (hiso : ∀ v w, B (g v) (g w) = B v w) :
    ((g : V →ₗ[k] V).det) ^ 2 = 1 := by
  set b := Module.Free.chooseBasis k V
  set Q := LinearMap.BilinForm.toMatrix b B
  set M := LinearMap.toMatrix b b (g : V →ₗ[k] V)

  have hcomp : B.comp (↑g) (↑g) = B := by
    ext v w; simp [LinearMap.BilinForm.comp_apply, hiso]

  have hmat : Q = M.transpose * Q * M := by
    have := LinearMap.BilinForm.toMatrix_comp b b B (↑g) (↑g)
    rw [hcomp] at this; exact this

  have hQdet : Q.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd

  rw [show (g : V →ₗ[k] V).det = M.det from by simp [M, LinearMap.det_toMatrix]]

  have h1 : Q.det = (M.transpose * Q * M).det := congr_arg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1

  have h2 : (M.det ^ 2 - 1) * Q.det = 0 := by
    have := sub_eq_zero.mpr h1.symm; ring_nf; ring_nf at this; exact this

  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).elim id (absurd · hQdet))

/-- An isometry of a nondegenerate bilinear form has determinant $\pm 1$. -/
theorem isometry_det_eq_one_or_neg_one
    (B : LinearMap.BilinForm k V) (hnd : B.Nondegenerate)
    (g : V ≃ₗ[k] V) (hiso : ∀ v w, B (g v) (g w) = B v w) :
    (g : V →ₗ[k] V).det = 1 ∨ (g : V →ₗ[k] V).det = -1 := by
  have h := isometry_det_sq_eq_one B hnd g hiso
  have h1 := sub_eq_zero.mpr h

  have h2 : ((g : V →ₗ[k] V).det - 1) * ((g : V →ₗ[k] V).det + 1) = 0 := by
    ring_nf; ring_nf at h1; exact h1
  rcases mul_eq_zero.mp h2 with h3 | h4
  · left; exact sub_eq_zero.mp h3
  · right; exact eq_neg_of_add_eq_zero_left h4

/-- The special isometry group $\mathrm{SO}(B)$: isometries of $B$ with determinant 1. -/
def SpecialIsometryGroup (B : LinearMap.BilinForm k V) : Set (V ≃ₗ[k] V) :=
  { g | (∀ v w, B (g v) (g w) = B v w) ∧ (g : V →ₗ[k] V).det = 1 }

end DetIsometry


section HypSwap

variable {k : Type*} [Field k]

/-- The $2 \times 2$ swap matrix has determinant $-1$. -/
theorem hyp_swap_det_neg_one :
    Matrix.det (!![0, (1 : k); 1, 0]) = -1 := by
  rw [Matrix.det_fin_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- An isometry of a hyperbolic plane $(e_1, e_2)$ which sends $e_1 \mapsto a e_2$ and
$e_2 \mapsto a^{-1} e_1$ has determinant $-1$. -/
theorem hyp_plane_swap_isometry_det
    (e₁ e₂ : Fin 2 → k) (b : Module.Basis (Fin 2) k (Fin 2 → k))
    (hb1 : b 0 = e₁) (hb2 : b 1 = e₂)
    (g : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k))
    (a : k) (ha : a ≠ 0) (hge1 : g e₁ = a • e₂) (hge2 : g e₂ = a⁻¹ • e₁) :
    (g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)).det = -1 := by
  rw [show (g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)).det =
    (LinearMap.toMatrix b b (↑g)).det from by simp [LinearMap.det_toMatrix]]
  have hge1' : (↑g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (b 0) = a • b 1 := by
    simp [hb1, hb2, hge1, LinearEquiv.coe_coe]
  have hge2' : (↑g : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (b 1) = a⁻¹ • b 0 := by
    simp [hb1, hb2, hge2, LinearEquiv.coe_coe]
  have hM : LinearMap.toMatrix b b (↑g) = !![0, a⁻¹; a, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hge1', hge2', Module.Basis.repr_self,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  rw [hM, Matrix.det_fin_two]; simp; exact inv_mul_cancel₀ ha

end HypSwap

end SOAction
