/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Matrix

theorem vertex_integral_of_det_pm_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (rows : Fin n → Fin m) (hrows : Function.Injective rows)
    (y : Fin n → ℝ)
    (hy_feasible : ∀ i, ∑ j, (A i j : ℝ) * y j ≤ (b i : ℝ))
    (hy_tight : ∀ k, ∑ j, (A (rows k) j : ℝ) * y j = (b (rows k) : ℝ))
    (hdet : (A.submatrix rows id).det = 1 ∨ (A.submatrix rows id).det = -1) :
    ∀ j, ∃ z : ℤ, y j = (z : ℝ) := by
  set A₁ := A.submatrix rows id
  set b₁ := b ∘ rows

  have hunit : IsUnit A₁.det := by
    cases hdet with
    | inl h => rw [h]; exact isUnit_one
    | inr h => rw [h]; exact isUnit_one.neg

  set z := A₁⁻¹.mulVec b₁

  have hz : A₁.mulVec z = b₁ := by
    simp only [z, mulVec_mulVec, mul_nonsing_inv A₁ hunit, one_mulVec]

  set A₁ℝ := A₁.map (Int.cast : ℤ → ℝ)

  have hunit_real : IsUnit A₁ℝ := by
    rw [isUnit_iff_isUnit_det]
    rw [show A₁ℝ.det = (Int.cast : ℤ → ℝ) A₁.det from (Int.cast_det A₁).symm]
    cases hdet with
    | inl h => simp [h]
    | inr h => simp [h]

  have hy_eq : A₁ℝ.mulVec y = fun k => (b₁ k : ℝ) := by
    funext k
    simp only [mulVec, dotProduct, A₁ℝ, map_apply, b₁, Function.comp]
    exact hy_tight k
  have hz_eq : A₁ℝ.mulVec (fun j => (z j : ℝ)) = fun k => (b₁ k : ℝ) := by
    funext k
    simp only [mulVec, dotProduct, A₁ℝ, map_apply]
    have hk := congr_fun hz k
    simp only [mulVec, dotProduct] at hk
    exact_mod_cast hk

  have heq : y = fun j => (z j : ℝ) :=
    mulVec_injective_of_isUnit hunit_real (hy_eq.trans hz_eq.symm)

  intro j
  exact ⟨z j, congr_fun heq j⟩

end Matrix
