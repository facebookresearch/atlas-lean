/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix Real

namespace EllipsoidMethod

variable {n : ℕ}

noncomputable def Ellipsoid (D : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | dotProduct (x - z) (D⁻¹.mulVec (x - z)) ≤ 1}

noncomputable def updateMatrix (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (D - (2 / ((n : ℝ) + 1)) • (1 / dotProduct a (D.mulVec a)) •
      vecMulVec (D.mulVec a) (D.mulVec a))

lemma quadForm_pos (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    0 < dotProduct a (D.mulVec a) := by
  have h := hD.dotProduct_mulVec_pos ha
  rwa [star_trivial] at h

lemma det_sub_smul_vecMulVec_of_isUnit (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (t : ℝ) (u v : Fin n → ℝ) :
    (A - t • vecMulVec u v).det = A.det * (1 - t * dotProduct v (A⁻¹.mulVec u)) := by
  have hmulvec : A.mulVec (A⁻¹.mulVec u) = u := by
    rw [mulVec_mulVec, mul_nonsing_inv A hA, one_mulVec]
  have hfactor : A - t • vecMulVec u v = A * (1 - t • vecMulVec (A⁻¹.mulVec u) v) := by
    rw [mul_sub, Matrix.mul_one, mul_smul_comm, mul_vecMulVec, hmulvec]
  rw [hfactor, det_mul]
  congr 1
  have h1 : t • vecMulVec (A⁻¹.mulVec u) v = vecMulVec (t • A⁻¹.mulVec u) v := by
    ext i j; simp [vecMulVec, mul_assoc]
  rw [h1, vecMulVec_eq (Fin 1), det_one_sub_mul_comm]
  simp [det_unique, replicateRow, replicateCol, dotProduct, mul_apply]

lemma updateMatrix_det_ratio (hn : 1 < n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (updateMatrix D a).det / D.det =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) := by
  have hDetUnit : IsUnit D.det := by
    rw [isUnit_iff_ne_zero]; exact ne_of_gt hD.det_pos
  have haDa_pos := quadForm_pos D hD a ha
  have haDa_ne : dotProduct a (D.mulVec a) ≠ 0 := ne_of_gt haDa_pos
  have hdet_pos : (0 : ℝ) < D.det := hD.det_pos
  unfold updateMatrix
  rw [det_smul, Fintype.card_fin]
  have hcoeff : (2 / ((n : ℝ) + 1)) • (1 / dotProduct a (D.mulVec a)) •
      vecMulVec (D.mulVec a) (D.mulVec a) =
    (2 / ((n : ℝ) + 1) / dotProduct a (D.mulVec a)) •
      vecMulVec (D.mulVec a) (D.mulVec a) := by
    rw [smul_smul]; ring_nf
  rw [hcoeff]
  rw [det_sub_smul_vecMulVec_of_isUnit D hDetUnit _ (D.mulVec a) (D.mulVec a)]
  have hinv : D⁻¹.mulVec (D.mulVec a) = a := by
    rw [mulVec_mulVec, nonsing_inv_mul D hDetUnit, one_mulVec]
  rw [hinv, dotProduct_comm (D.mulVec a) a]
  have hsimp : 2 / ((n : ℝ) + 1) / dotProduct a (D.mulVec a) * dotProduct a (D.mulVec a)
    = 2 / ((n : ℝ) + 1) := by
    field_simp
  rw [hsimp, mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hdet_pos)]
  congr 1
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp
  ring

lemma volume_ratio_numerical_bound (hn : 1 < n) :
    ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) ≤
      Real.exp (-1 / ((n : ℝ) + 1)) := by
  have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hn1_pos' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnsq_sub : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hLHS_pos : (0 : ℝ) < ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n *
      (((n : ℝ) - 1) / ((n : ℝ) + 1)) := by
    apply mul_pos
    · apply pow_pos; apply div_pos; positivity; linarith
    · apply div_pos <;> linarith
  rw [← Real.log_le_log_iff hLHS_pos (exp_pos _), Real.log_exp]
  rw [Real.log_mul (ne_of_gt (pow_pos (div_pos (by positivity : (0:ℝ) < (n:ℝ)^2) hnsq_sub) n))
      (ne_of_gt (div_pos hn1_pos' hn1_pos)),
      Real.log_pow]

  have hstep1 : (n : ℝ) * Real.log ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ≤
      (n : ℝ) / ((n : ℝ) ^ 2 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : (0:ℝ) < (n:ℝ)^2) hnsq_sub)
    have h2 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) - 1 = 1 / ((n : ℝ) ^ 2 - 1) := by
      field_simp; ring
    have h3 : Real.log ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ≤ 1 / ((n : ℝ) ^ 2 - 1) := by
      linarith
    calc (n : ℝ) * Real.log ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1))
        ≤ (n : ℝ) * (1 / ((n : ℝ) ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hn_pos)
      _ = (n : ℝ) / ((n : ℝ) ^ 2 - 1) := by ring

  have hstep2 : Real.log (((n : ℝ) - 1) / ((n : ℝ) + 1)) ≤ -2 / (n : ℝ) := by
    have h_pos_frac : (0 : ℝ) < 2 / ((n : ℝ) - 1) := by positivity
    have h_log_lb := Real.lt_log_one_add_of_pos h_pos_frac
    have h_simp : 2 * (2 / ((n : ℝ) - 1)) / (2 / ((n : ℝ) - 1) + 2) = 2 / (n : ℝ) := by
      field_simp; ring
    rw [h_simp] at h_log_lb
    have h_ratio : (1 : ℝ) + 2 / ((n : ℝ) - 1) = ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
      field_simp; ring
    rw [h_ratio] at h_log_lb
    have h_eq : ((n : ℝ) - 1) / ((n : ℝ) + 1) = (((n : ℝ) + 1) / ((n : ℝ) - 1))⁻¹ := by
      rw [inv_div]
    rw [h_eq, Real.log_inv]
    have h : -(2 / (n : ℝ)) = -2 / (n : ℝ) := by ring
    rw [← h]
    exact le_of_lt (neg_lt_neg h_log_lb)

  have hstep3 : (n : ℝ) / ((n : ℝ) ^ 2 - 1) + (-2 / (n : ℝ)) ≤ -1 / ((n : ℝ) + 1) := by
    have h_eq : (n : ℝ) / ((n : ℝ) ^ 2 - 1) + (-2 / (n : ℝ)) - (-1 / ((n : ℝ) + 1)) =
        (2 - (n : ℝ)) / ((n : ℝ) * ((n : ℝ) ^ 2 - 1)) := by
      field_simp; ring
    have h_nonpos : (2 - (n : ℝ)) / ((n : ℝ) * ((n : ℝ) ^ 2 - 1)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · apply mul_nonneg (le_of_lt hn_pos) (le_of_lt hnsq_sub)
    linarith

  calc (n : ℝ) * Real.log ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) +
        Real.log (((n : ℝ) - 1) / ((n : ℝ) + 1))
      ≤ (n : ℝ) / ((n : ℝ) ^ 2 - 1) + (-2 / (n : ℝ)) := add_le_add hstep1 hstep2
    _ ≤ -1 / ((n : ℝ) + 1) := hstep3

theorem ellipsoid_volume_ratio_le_exp (hn : 1 < n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    ((updateMatrix D a).det / D.det) ^ ((1 : ℝ) / 2) ≤
      Real.exp (-1 / (2 * ((n : ℝ) + 1))) := by
  have hdet_eq := updateMatrix_det_ratio hn D hD a ha
  have hbound := volume_ratio_numerical_bound hn
  have hx : 0 ≤ (updateMatrix D a).det / D.det := by
    rw [hdet_eq]
    apply mul_nonneg
    · apply pow_nonneg
      apply div_nonneg
      · positivity
      · have : (1 : ℝ) < (n : ℝ) ^ 2 := by
          have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          nlinarith
        linarith
    · apply div_nonneg
      · have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        linarith
      · have : (0 : ℝ) < (n : ℝ) := by positivity
        linarith
  rw [hdet_eq]
  calc ((↑n ^ 2 / (↑n ^ 2 - 1)) ^ n * ((↑n - 1) / (↑n + 1))) ^ ((1 : ℝ) / 2)
      ≤ (Real.exp (-1 / ((n : ℝ) + 1))) ^ ((1 : ℝ) / 2) := by
        apply Real.rpow_le_rpow
        · rwa [← hdet_eq]
        · exact hbound
        · positivity
    _ = Real.exp ((-1 / ((n : ℝ) + 1)) * (1 / 2)) := by
        rw [rpow_def_of_pos (exp_pos _), Real.log_exp, mul_comm]
    _ = Real.exp (-1 / (2 * ((n : ℝ) + 1))) := by
        congr 1; field_simp

end EllipsoidMethod
