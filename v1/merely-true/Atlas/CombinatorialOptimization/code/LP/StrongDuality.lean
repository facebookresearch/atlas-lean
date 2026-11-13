/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.LP.Farkas
import Atlas.CombinatorialOptimization.code.LP.WeakDualityStandard

open Matrix Finset

noncomputable def sdAugMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ := fun i j =>
  Fin.lastCases
    (Fin.lastCases (1 : ℝ) (fun j' => -(c j')))
    (fun i' => Fin.lastCases (0 : ℝ) (fun j' => A i' j'))
    i j

noncomputable def sdAugRhs {m : ℕ} (b : Fin m → ℝ) (v : ℝ) : Fin (m + 1) → ℝ := fun i =>
  Fin.lastCases (-v) (fun i' => b i') i

lemma augSys_to_primal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (b : Fin m → ℝ) (v : ℝ) (z : Fin (n + 1) → ℝ)
    (hz_nn : ∀ j, 0 ≤ z j) (hBz : (sdAugMat A c) *ᵥ z = sdAugRhs b v) :
    let x := fun j => z (Fin.castSucc j)
    (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b ∧ dotProduct c x ≥ v := by
  intro x
  have hrow_i : ∀ i : Fin m, (A *ᵥ x) i = b i := by
    intro i
    have := congr_fun hBz (Fin.castSucc i)
    simp only [sdAugMat, sdAugRhs, mulVec, dotProduct, Fin.lastCases_castSucc] at this
    rw [Fin.sum_univ_castSucc] at this
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, zero_mul, add_zero] at this
    exact this
  have hrow_last : ∑ j : Fin n, -(c j) * z (Fin.castSucc j) + z (Fin.last n) = -v := by
    have := congr_fun hBz (Fin.last m)
    simp only [sdAugMat, sdAugRhs, mulVec, dotProduct, Fin.lastCases_last] at this
    rw [Fin.sum_univ_castSucc] at this
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_mul] at this
    exact this
  refine ⟨fun j => hz_nn _, funext hrow_i, ?_⟩
  simp only [dotProduct, ge_iff_le, x]
  have key : ∑ j : Fin n, -(c j) * z (Fin.castSucc j) =
    -(∑ j : Fin n, c j * z (Fin.castSucc j)) := by
    simp [Finset.sum_neg_distrib, neg_mul]
  linarith [hz_nn (Fin.last n)]

lemma sd_farkas_alternative_false {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x₀ : Fin n → ℝ) (hx₀_nn : ∀ j, 0 ≤ x₀ j) (hAx₀ : A *ᵥ x₀ = b)
    (v : ℝ) (hv_ub : ∀ (y : Fin m → ℝ), (∀ j, c j ≤ (Aᵀ *ᵥ y) j) → v ≤ dotProduct b y)
    (w : Fin (m + 1) → ℝ)
    (hw_nn : ∀ j, 0 ≤ ((sdAugMat A c)ᵀ *ᵥ w) j)
    (hw_dot : dotProduct (sdAugRhs b v) w < 0) : False := by
  set yy := fun i : Fin m => w (Fin.castSucc i)
  set mu := w (Fin.last m)

  have hmu_nn : 0 ≤ mu := by
    have h := hw_nn (Fin.last n)
    simp only [sdAugMat, mulVec, dotProduct, transpose_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, zero_mul,
               Finset.sum_const_zero, zero_add, one_mul] at h
    exact h

  have hATyy : ∀ j : Fin n, (Aᵀ *ᵥ yy) j ≥ mu * c j := by
    intro j
    have h := hw_nn (Fin.castSucc j)
    simp only [sdAugMat, mulVec, dotProduct, transpose_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at h
    simp only [mulVec, dotProduct, transpose_apply, ge_iff_le]
    linarith

  have hdot : dotProduct b yy - v * mu < 0 := by
    simp only [sdAugRhs, dotProduct] at hw_dot
    rw [Fin.sum_univ_castSucc] at hw_dot
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at hw_dot
    simp only [dotProduct]
    linarith

  rcases eq_or_lt_of_le hmu_nn with hmu0 | hmu_pos
  ·
    have hmu0' : mu = 0 := hmu0.symm
    have hATyy_nn : ∀ j, 0 ≤ (Aᵀ *ᵥ yy) j := by
      intro j; have := hATyy j; rw [hmu0'] at this; linarith
    have hby_neg : dotProduct b yy < 0 := by rw [hmu0'] at hdot; linarith
    have hby_nn : 0 ≤ dotProduct b yy := by
      calc dotProduct b yy = dotProduct (A *ᵥ x₀) yy := by rw [hAx₀]
        _ = dotProduct x₀ (Aᵀ *ᵥ yy) := by
            rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
        _ ≥ 0 := Finset.sum_nonneg fun j _ => mul_nonneg (hx₀_nn j) (hATyy_nn j)
    linarith
  ·
    have hdf : ∀ j : Fin n, c j ≤ (Aᵀ *ᵥ (fun i => yy i / mu)) j := by
      intro j
      simp only [mulVec, dotProduct, transpose_apply]
      rw [show ∑ i : Fin m, A i j * (yy i / mu) =
        (∑ i : Fin m, A i j * yy i) / mu from by
        rw [Finset.sum_div]; congr 1; ext i; ring]
      have h := hATyy j
      simp only [mulVec, dotProduct, transpose_apply, ge_iff_le] at h
      rw [le_div_iff₀ hmu_pos]
      linarith
    have hbyymu : dotProduct b (fun i => yy i / mu) < v := by
      simp only [dotProduct]
      rw [show ∑ i : Fin m, b i * (yy i / mu) =
        (∑ i : Fin m, b i * yy i) / mu from by
        rw [Finset.sum_div]; congr 1; ext i; ring]
      rw [div_lt_iff₀ hmu_pos]
      simp only [dotProduct] at hdot
      linarith
    have := hv_ub _ hdf
    linarith

noncomputable def dualAugMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin (n + 1)) (Fin (m + (m + (n + 1)))) ℝ := fun row col =>
  Fin.addCases
    (fun i => Fin.lastCases (-(b i)) (fun j => A i j) row)
    (fun col' => Fin.addCases
      (fun i => Fin.lastCases (b i) (fun j => -(A i j)) row)
      (fun col'' => Fin.lastCases
          (Fin.lastCases (-1 : ℝ) (fun _ => (0 : ℝ)) row)
          (fun j' => Fin.lastCases (0 : ℝ) (fun j => if j = j' then -1 else 0) row)
          col'')
      col')
    col

noncomputable def dualAugRhs {n : ℕ} (c : Fin n → ℝ) (v : ℝ) : Fin (n + 1) → ℝ := fun row =>
  Fin.lastCases (-v) (fun j => c j) row

lemma augDualSys_to_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (v : ℝ) (z : Fin (m + (m + (n + 1))) → ℝ)
    (hz_nn : ∀ k, 0 ≤ z k)
    (hCz : (dualAugMat A b) *ᵥ z = dualAugRhs c v) :
    let y_opt := fun i : Fin m => z (Fin.castAdd (m + (n + 1)) i) -
      z (Fin.natAdd m (Fin.castAdd (n + 1) i))
    (∀ j, c j ≤ (Aᵀ *ᵥ y_opt) j) ∧ dotProduct b y_opt ≤ v := by
  intro y_opt

  have hrow_j : ∀ j : Fin n, (Aᵀ *ᵥ y_opt) j = c j +
      z (Fin.natAdd m (Fin.natAdd m (Fin.castSucc j))) := by
    intro j
    have h := congr_fun hCz (Fin.castSucc j)
    simp only [dualAugMat, dualAugRhs, mulVec, dotProduct, Fin.lastCases_castSucc] at h
    rw [Fin.sum_univ_add] at h
    simp only [Fin.addCases_left, Fin.addCases_right] at h
    rw [Fin.sum_univ_add] at h
    simp only [Fin.addCases_left, Fin.addCases_right] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.lastCases_last, zero_mul, add_zero, Fin.lastCases_castSucc] at h

    simp only [mulVec, dotProduct, transpose_apply, y_opt]
    have hite : ∑ x : Fin n, (if j = x then (-1 : ℝ) else 0) *
        z (Fin.natAdd m (Fin.natAdd m (Fin.castSucc x))) =
        -(z (Fin.natAdd m (Fin.natAdd m (Fin.castSucc j)))) := by
      simp only [ite_mul, zero_mul, neg_mul, one_mul]
      rw [Finset.sum_ite_eq]; simp
    have hneg_sum : ∑ i : Fin m, -(A i j) * z (Fin.natAdd m (Fin.castAdd (n + 1) i)) =
        -(∑ i : Fin m, A i j * z (Fin.natAdd m (Fin.castAdd (n + 1) i))) := by
      simp [Finset.sum_neg_distrib, neg_mul]
    rw [show ∑ i : Fin m, A i j * (z (Fin.castAdd (m + (n + 1)) i) -
        z (Fin.natAdd m (Fin.castAdd (n + 1) i))) =
        ∑ i : Fin m, A i j * z (Fin.castAdd (m + (n + 1)) i) -
        ∑ i : Fin m, A i j * z (Fin.natAdd m (Fin.castAdd (n + 1) i)) from by
      rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring]


    linarith [hite, hneg_sum]

  have hrow_last : dotProduct b y_opt + z (Fin.natAdd m (Fin.natAdd m (Fin.last n))) = v := by
    have h := congr_fun hCz (Fin.last n)
    simp only [dualAugMat, dualAugRhs, mulVec, dotProduct, Fin.lastCases_last] at h
    rw [Fin.sum_univ_add] at h
    simp only [Fin.addCases_left, Fin.addCases_right] at h
    rw [Fin.sum_univ_add] at h
    simp only [Fin.addCases_left, Fin.addCases_right] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul,
               Finset.sum_const_zero, neg_mul, one_mul] at h
    simp only [dotProduct, y_opt]
    have hneg_sum1 : ∑ i : Fin m, -(b i * z (Fin.castAdd (m + (n + 1)) i)) =
        -(∑ i : Fin m, b i * z (Fin.castAdd (m + (n + 1)) i)) := by
      simp [Finset.sum_neg_distrib]
    rw [show ∑ i : Fin m, b i * (z (Fin.castAdd (m + (n + 1)) i) -
        z (Fin.natAdd m (Fin.castAdd (n + 1) i))) =
        ∑ i : Fin m, b i * z (Fin.castAdd (m + (n + 1)) i) -
        ∑ i : Fin m, b i * z (Fin.natAdd m (Fin.castAdd (n + 1) i)) from by
      rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring]
    linarith [hneg_sum1]
  refine ⟨fun j => ?_, ?_⟩
  ·
    rw [hrow_j j]; linarith [hz_nn (Fin.natAdd m (Fin.natAdd m (Fin.castSucc j)))]
  ·
    linarith [hz_nn (Fin.natAdd m (Fin.natAdd m (Fin.last n)))]

lemma sd_dual_farkas_alternative_false {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (v : ℝ)
    (hv_is_ub : ∀ (x : Fin n → ℝ), (∀ j, 0 ≤ x j) → A *ᵥ x = b → dotProduct c x ≤ v)
    (x₀ : Fin n → ℝ) (hx₀_nn : ∀ j, 0 ≤ x₀ j) (hAx₀ : A *ᵥ x₀ = b)
    (w : Fin (n + 1) → ℝ)
    (hw_nn : ∀ k, 0 ≤ ((dualAugMat A b)ᵀ *ᵥ w) k)
    (hw_dot : dotProduct (dualAugRhs c v) w < 0) : False := by
  set x' := fun j : Fin n => -(w (Fin.castSucc j))
  set β := -(w (Fin.last n))

  have hx'_nn : ∀ j : Fin n, 0 ≤ x' j := by
    intro j
    have h := hw_nn (Fin.natAdd m (Fin.natAdd m (Fin.castSucc j)))
    simp only [dualAugMat, transpose_apply, mulVec, dotProduct,
               Fin.addCases_right, Fin.lastCases_castSucc] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.lastCases_last, zero_mul, Fin.lastCases_castSucc] at h
    have heq : ∑ x : Fin n, (if x = j then (-1 : ℝ) else 0) * w (Fin.castSucc x) =
        -(w (Fin.castSucc j)) := by
      simp only [ite_mul, zero_mul, neg_mul, one_mul]
      rw [Finset.sum_ite_eq']; simp
    linarith

  have hβ_nn : 0 ≤ β := by
    have h := hw_nn (Fin.natAdd m (Fin.natAdd m (Fin.last n)))
    simp only [dualAugMat, transpose_apply, mulVec, dotProduct,
               Fin.addCases_right, Fin.lastCases_last] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.lastCases_castSucc, zero_mul, Finset.sum_const_zero,
               zero_add, Fin.lastCases_last, neg_mul, one_mul] at h
    linarith

  have hAx' : A *ᵥ x' = β • b := by
    ext i
    have h_yp := hw_nn (Fin.castAdd (m + (n + 1)) i)
    simp only [dualAugMat, transpose_apply, mulVec, dotProduct,
               Fin.addCases_left] at h_yp
    rw [Fin.sum_univ_castSucc] at h_yp
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, neg_mul] at h_yp
    have h_ym := hw_nn (Fin.natAdd m (Fin.castAdd (n + 1) i))
    simp only [dualAugMat, transpose_apply, mulVec, dotProduct,
               Fin.addCases_right, Fin.addCases_left] at h_ym
    rw [Fin.sum_univ_castSucc] at h_ym
    simp only [Fin.lastCases_castSucc, neg_mul, Fin.lastCases_last] at h_ym
    have hsum_neg : ∑ x : Fin n, -(A i x * w (Fin.castSucc x)) =
        -(∑ x : Fin n, A i x * w (Fin.castSucc x)) := by
      simp [Finset.sum_neg_distrib]
    have heq : ∑ x : Fin n, A i x * w (Fin.castSucc x) = b i * w (Fin.last n) := by
      linarith
    simp only [mulVec, dotProduct, x', Pi.smul_apply, smul_eq_mul, β]
    rw [show ∑ j : Fin n, A i j * -(w (Fin.castSucc j)) =
      -(∑ j : Fin n, A i j * w (Fin.castSucc j)) from by
      simp [Finset.sum_neg_distrib, mul_neg]]
    rw [heq]; ring

  have hobj : dotProduct c x' > v * β := by
    simp only [dualAugRhs, dotProduct] at hw_dot
    rw [Fin.sum_univ_castSucc] at hw_dot
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, neg_mul] at hw_dot
    simp only [dotProduct, x', β]
    rw [show ∑ j : Fin n, c j * -(w (Fin.castSucc j)) =
      -(∑ j : Fin n, c j * w (Fin.castSucc j)) from by
      simp [Finset.sum_neg_distrib, mul_neg]]
    linarith

  rcases eq_or_lt_of_le hβ_nn with hβ0 | hβ_pos
  ·
    have hβ0' : β = 0 := hβ0.symm
    rw [hβ0', zero_smul] at hAx'
    rw [hβ0', mul_zero] at hobj
    have hcx'_pos : (0 : ℝ) < dotProduct c x' := hobj
    have hcx₀_le : dotProduct c x₀ ≤ v := hv_is_ub x₀ hx₀_nn hAx₀
    set t := (v - dotProduct c x₀) / (dotProduct c x') + 1
    have ht_pos : 0 < t :=
      lt_of_lt_of_le one_pos (le_add_of_nonneg_left
        (div_nonneg (by linarith) (le_of_lt hcx'_pos)))
    have hfeas : A *ᵥ (x₀ + t • x') = b := by
      simp [mulVec_add, Matrix.mulVec_smul, hAx₀, hAx']
    have hnn : ∀ j, 0 ≤ (x₀ + t • x') j := by
      intro j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hx₀_nn j) (mul_nonneg (le_of_lt ht_pos) (hx'_nn j))
    have key : t * dotProduct c x' > v - dotProduct c x₀ := by
      rw [show t = (v - dotProduct c x₀) / (dotProduct c x') + 1 from rfl,
          add_mul, div_mul_cancel₀ _ (ne_of_gt hcx'_pos)]
      linarith
    have hadd : dotProduct c (x₀ + t • x') = dotProduct c x₀ + t * dotProduct c x' := by
      simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show ∑ j : Fin n, c j * (x₀ j + t * x' j) =
        ∑ j : Fin n, (c j * x₀ j + c j * (t * x' j)) from by congr 1; ext j; ring,
        Finset.sum_add_distrib,
        show ∑ j : Fin n, c j * (t * x' j) = t * ∑ j : Fin n, c j * x' j from by
          rw [Finset.mul_sum]; congr 1; ext j; ring]
    linarith [hv_is_ub (x₀ + t • x') hnn hfeas]
  ·
    have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
    have hx'β_feas : A *ᵥ (fun j => x' j / β) = b := by
      ext i; simp only [mulVec, dotProduct]
      rw [show ∑ j, A i j * (x' j / β) = (∑ j, A i j * x' j) / β from by
        rw [Finset.sum_div]; congr 1; ext j; ring]
      have := congr_fun hAx' i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [this, mul_div_cancel_left₀ (b i) hβ_ne]
    have hx'β_nn : ∀ j, 0 ≤ (fun j => x' j / β) j := fun j =>
      div_nonneg (hx'_nn j) (le_of_lt hβ_pos)
    have hobj' : dotProduct c (fun j => x' j / β) > v := by
      simp only [dotProduct]
      rw [show ∑ j, c j * (x' j / β) = (∑ j, c j * x' j) / β from by
        rw [Finset.sum_div]; congr 1; ext j; ring]
      rw [gt_iff_lt, lt_div_iff₀ hβ_pos]
      simp only [dotProduct] at hobj; linarith
    linarith [hv_is_ub _ hx'β_nn hx'β_feas]

