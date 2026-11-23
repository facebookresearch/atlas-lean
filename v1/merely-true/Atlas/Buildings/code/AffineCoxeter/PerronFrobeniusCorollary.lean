/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Finset BigOperators CoxeterGroup PerronFrobeniusProof

namespace PerronFrobeniusCorollary

variable {n : ℕ}

/-- Inserting a zero in slot $i_0$ does not change the quadratic form value: $Q_f(\iota_{i_0}(0, w)) = Q_g(w)$
where $g$ is the submatrix obtained by deleting row/column $i_0$. -/
lemma QF_insertNth_zero (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (n + 1)) (w : Fin n → ℝ) :
    QF f (Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) w) =
    QF (fun i j => f (i₀.succAbove i) (i₀.succAbove j)) w := by
  simp only [QF]
  rw [Fin.sum_univ_succAbove _ i₀]
  simp only [Fin.insertNth_apply_same, zero_mul, Finset.sum_const_zero, zero_add]
  congr 1; funext s
  rw [Fin.sum_univ_succAbove _ i₀]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- The off-diagonal sign condition $f_{st} \le 0$ for $s \ne t$ is inherited by any principal submatrix. -/
lemma restrictForm_offDiag (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (n + 1))
    (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
    ∀ s t : Fin n, s ≠ t → f (i₀.succAbove s) (i₀.succAbove t) ≤ 0 := by
  intro s t hst
  exact hOffDiag _ _ (Fin.succAbove_right_injective.ne hst)

/-- If $w \ne 0$ then inserting $0$ at $i_0$ in the absolute-value vector $|w|$ is still nonzero. -/
lemma insertNth_abs_ne_zero (i₀ : Fin (n + 1)) (w : Fin n → ℝ) (hw : w ≠ 0) :
    Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) (fun k => |w k|) ≠ 0 := by
  intro h
  apply hw
  funext k
  have := congr_fun h (i₀.succAbove k)
  simp [Fin.insertNth_apply_succAbove] at this
  exact this

/-- The "insert $0$ at $i_0$" version of $|w|$ has all components $\ge 0$. -/
lemma insertNth_abs_nonneg (i₀ : Fin (n + 1)) (w : Fin n → ℝ) :
    ∀ b, Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) (fun k => |w k|) b ≥ 0 := by
  intro b
  by_cases h : b = i₀
  · simp [h, Fin.insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove, abs_nonneg]

/-- **Perron–Frobenius corollary**: any proper principal submatrix of an indecomposable, off-diagonal
nonpositive, positive semidefinite Gram matrix is **positive definite**. Equivalently, the Coxeter
form of an affine type becomes spherical on every proper parabolic. -/
theorem submatrix_positive_definite
    (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hPSD : ∀ u : Fin (n + 1) → ℝ, QF f u ≥ 0)
    (hOffDiag : ∀ s t : Fin (n + 1), s ≠ t → f s t ≤ 0)
    (hIndecomp : FormIndecomposable f)
    (i₀ : Fin (n + 1)) :
    ∀ w : Fin n → ℝ, w ≠ 0 →
    QF (fun i j => f (i₀.succAbove i) (i₀.succAbove j)) w > 0 := by
  intro w hw

  set g := fun i j => f (i₀.succAbove i) (i₀.succAbove j) with hg_def

  have hOffDiag_g : ∀ s t : Fin n, s ≠ t → g s t ≤ 0 :=
    restrictForm_offDiag f i₀ hOffDiag

  by_contra h_not_pos
  push_neg at h_not_pos

  set v := Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) (fun k => |w k|) with hv_def

  have hQF_v : QF f v = QF g (fun k => |w k|) := QF_insertNth_zero f i₀ (fun k => |w k|)

  have habs_le : QF g (fun k => |w k|) ≤ QF g w := QF_abs_le g w hOffDiag_g


  have hPSD_v : QF f v ≥ 0 := hPSD v

  have hQF_v_zero : QF f v = 0 := le_antisymm (by linarith) hPSD_v

  have hv_nonneg : ∀ b, v b ≥ 0 := insertNth_abs_nonneg i₀ w
  have hv_ne : v ≠ 0 := insertNth_abs_ne_zero i₀ w hw

  have hv_pos : ∀ b, v b > 0 :=
    nonneg_kernel_pos f v hPSD hQF_v_zero hv_nonneg hv_ne hOffDiag hIndecomp

  have hv_i₀ : v i₀ = 0 := by simp [hv_def, Fin.insertNth_apply_same]
  linarith [hv_pos i₀]

end PerronFrobeniusCorollary
