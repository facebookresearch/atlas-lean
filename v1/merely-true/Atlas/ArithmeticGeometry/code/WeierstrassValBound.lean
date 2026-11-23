/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Normed.Group.Ultra

open Padic

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

lemma zpow_inj_prime {a b : ℤ} (h : (p : ℝ) ^ a = (p : ℝ) ^ b) : a = b := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  exfalso
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  rcases lt_or_gt_of_ne hab with h1 | h1
  · exact absurd h (ne_of_lt ((zpow_lt_zpow_iff_right₀ hp1).mpr h1))
  · exact absurd h (ne_of_gt ((zpow_lt_zpow_iff_right₀ hp1).mpr h1))

lemma val_neg_implies_norm_gt_one {a : ℚ_[p]} (h : valuation a < 0) : 1 < ‖a‖ := by
  have : ¬(0 ≤ valuation a) := not_le.mpr h
  rwa [← Padic.norm_le_one_iff_val_nonneg, not_le] at this

lemma ultra3_padic {a b c : ℚ_[p]} (hb : ‖b‖ < ‖a‖) (hc : ‖c‖ < ‖a‖) :
    ‖a + b + c‖ = ‖a‖ := by
  have h1 : ‖b + c‖ < ‖a‖ := lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt hb hc)
  rw [show a + b + c = a + (b + c) by ring]
  exact (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h1)).trans
    (max_eq_left h1.le)

lemma ultra4_padic {a b c d : ℚ_[p]} (hb : ‖b‖ < ‖a‖) (hc : ‖c‖ < ‖a‖) (hd : ‖d‖ < ‖a‖) :
    ‖a + b + c + d‖ = ‖a‖ := by
  have h1 : ‖b + c + d‖ < ‖a‖ := by
    calc ‖b + c + d‖ ≤ max ‖b + c‖ ‖d‖ := Padic.nonarchimedean _ _
      _ ≤ max (max ‖b‖ ‖c‖) ‖d‖ := by gcongr; exact Padic.nonarchimedean _ _
      _ < ‖a‖ := by simp only [max_lt_iff]; exact ⟨⟨hb, hc⟩, hd⟩
  rw [show a + b + c + d = a + (b + c + d) by ring]
  exact (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h1)).trans
    (max_eq_left h1.le)

lemma rhs_norm_le_one {a₂ a₄ a₆ x : ℚ_[p]}
    (hn₂ : ‖a₂‖ ≤ 1) (hn₄ : ‖a₄‖ ≤ 1) (hn₆ : ‖a₆‖ ≤ 1) (hx_le : ‖x‖ ≤ 1) :
    ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆‖ ≤ 1 := by
  have h1 : ‖x ^ 3‖ ≤ 1 := by
    rw [norm_pow]; exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hx_le 3) (one_pow 3).le
  have h2 : ‖a₂ * x ^ 2‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc ‖a₂‖ * ‖x‖ ^ 2 ≤ 1 * 1 ^ 2 := by
          apply mul_le_mul hn₂ (pow_le_pow_left₀ (norm_nonneg _) hx_le 2) (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = 1 := by ring
  have h3 : ‖a₄ * x‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖a₄‖ * ‖x‖ ≤ 1 * 1 := by
          apply mul_le_mul hn₄ hx_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆‖
      ≤ max (max (max ‖x ^ 3‖ ‖a₂ * x ^ 2‖) ‖a₄ * x‖) ‖a₆‖ := by
        calc ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆‖
            ≤ max ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x‖ ‖a₆‖ := Padic.nonarchimedean _ _
          _ ≤ max (max ‖x ^ 3 + a₂ * x ^ 2‖ ‖a₄ * x‖) ‖a₆‖ := by
              apply max_le_max_right; exact Padic.nonarchimedean _ _
          _ ≤ max (max (max ‖x ^ 3‖ ‖a₂ * x ^ 2‖) ‖a₄ * x‖) ‖a₆‖ := by
              gcongr
              exact Padic.nonarchimedean _ _
    _ ≤ 1 := by
        simp only [max_le_iff]
        exact ⟨⟨⟨h1, h2⟩, h3⟩, hn₆⟩

lemma rhs_norm_eq_cube {a₂ a₄ a₆ x : ℚ_[p]}
    (hn₂ : ‖a₂‖ ≤ 1) (hn₄ : ‖a₄‖ ≤ 1) (hn₆ : ‖a₆‖ ≤ 1) (hx_gt : 1 < ‖x‖) :
    ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆‖ = ‖x‖ ^ 3 := by
  have h_a2x2 : ‖a₂ * x ^ 2‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖a₂‖ * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right hn₂ (pow_nonneg (norm_nonneg _) _)
      _ = ‖x‖ ^ 2 := one_mul _
      _ < ‖x‖ ^ 3 := by
          rw [show ‖x‖ ^ 3 = ‖x‖ ^ 2 * ‖x‖ from by ring]
          exact lt_mul_of_one_lt_right (pow_pos (by linarith) 2) hx_gt
  have h_a4x : ‖a₄ * x‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow]
    calc ‖a₄‖ * ‖x‖ ≤ 1 * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right hn₄ (norm_nonneg _)
      _ = ‖x‖ := one_mul _
      _ < ‖x‖ ^ 3 := by nlinarith [sq_nonneg ‖x‖]
  have h_a6 : ‖a₆‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    calc ‖a₆‖ ≤ 1 := hn₆
      _ < ‖x‖ := hx_gt
      _ < ‖x‖ ^ 3 := by nlinarith [sq_nonneg ‖x‖]
  rw [ultra4_padic h_a2x2 h_a4x h_a6, norm_pow]

theorem weierstrass_valuation_bound_proof
    {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (hc : 0 ≤ valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧
          0 ≤ valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧
          0 ≤ valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧
          0 ≤ valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧
          0 ≤ valuation (algebraMap ℚ ℚ_[p] W.a₆))
    {x y : ℚ_[p]} (h : (W.baseChange ℚ_[p]).toAffine.Nonsingular x y)
    (hni : ¬ (0 ≤ valuation x ∧ 0 ≤ valuation y)) :
    y ≠ 0 ∧ (1 : ℤ) ≤ valuation x - valuation y := by

  have heq : y ^ 2 + (W.baseChange ℚ_[p]).toAffine.a₁ * x * y +
      (W.baseChange ℚ_[p]).toAffine.a₃ * y =
      x ^ 3 + (W.baseChange ℚ_[p]).toAffine.a₂ * x ^ 2 +
      (W.baseChange ℚ_[p]).toAffine.a₄ * x +
      (W.baseChange ℚ_[p]).toAffine.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp h.1

  set a₁ := (W.baseChange ℚ_[p]).toAffine.a₁
  set a₂ := (W.baseChange ℚ_[p]).toAffine.a₂
  set a₃ := (W.baseChange ℚ_[p]).toAffine.a₃
  set a₄ := (W.baseChange ℚ_[p]).toAffine.a₄
  set a₆ := (W.baseChange ℚ_[p]).toAffine.a₆

  have ha₁_eq : a₁ = algebraMap ℚ ℚ_[p] W.a₁ := by
    simp [a₁]
  have ha₂_eq : a₂ = algebraMap ℚ ℚ_[p] W.a₂ := by
    simp [a₂]
  have ha₃_eq : a₃ = algebraMap ℚ ℚ_[p] W.a₃ := by
    simp [a₃]
  have ha₄_eq : a₄ = algebraMap ℚ ℚ_[p] W.a₄ := by
    simp [a₄]
  have ha₆_eq : a₆ = algebraMap ℚ ℚ_[p] W.a₆ := by
    simp [a₆]
  have hn₁ : ‖a₁‖ ≤ 1 := by rw [ha₁_eq]; exact (norm_le_one_iff_val_nonneg _).mpr hc.1
  have hn₂ : ‖a₂‖ ≤ 1 := by rw [ha₂_eq]; exact (norm_le_one_iff_val_nonneg _).mpr hc.2.1
  have hn₃ : ‖a₃‖ ≤ 1 := by rw [ha₃_eq]; exact (norm_le_one_iff_val_nonneg _).mpr hc.2.2.1
  have hn₄ : ‖a₄‖ ≤ 1 := by rw [ha₄_eq]; exact (norm_le_one_iff_val_nonneg _).mpr hc.2.2.2.1
  have hn₆ : ‖a₆‖ ≤ 1 := by rw [ha₆_eq]; exact (norm_le_one_iff_val_nonneg _).mpr hc.2.2.2.2

  have heq_norm : ‖y ^ 2 + a₁ * x * y + a₃ * y‖ = ‖x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆‖ := by
    rw [heq]

  have hx_neg : valuation x < 0 := by
    by_contra hx_ge
    push Not at hx_ge
    have hni' : ¬(0 ≤ valuation y) := fun hy => hni ⟨hx_ge, hy⟩
    have hy_neg : valuation y < 0 := not_le.mp hni'
    have hy_gt : 1 < ‖y‖ := val_neg_implies_norm_gt_one hy_neg
    have hx_le : ‖x‖ ≤ 1 := (norm_le_one_iff_val_nonneg _).mpr hx_ge
    have hRHS_le := rhs_norm_le_one hn₂ hn₄ hn₆ hx_le

    have h_a1xy : ‖a₁ * x * y‖ < ‖y ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_pow]
      calc ‖a₁‖ * ‖x‖ * ‖y‖ ≤ 1 * 1 * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul hn₁ hx_le (norm_nonneg _) zero_le_one
            · exact norm_nonneg _
        _ = ‖y‖ := by ring
        _ < ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
    have h_a3y : ‖a₃ * y‖ < ‖y ^ 2‖ := by
      rw [norm_mul, norm_pow]
      calc ‖a₃‖ * ‖y‖ ≤ 1 * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right hn₃ (norm_nonneg _)
        _ = ‖y‖ := one_mul _
        _ < ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
    have hLHS : ‖y ^ 2 + a₁ * x * y + a₃ * y‖ = ‖y‖ ^ 2 := by
      rw [ultra3_padic h_a1xy h_a3y, norm_pow]

    have : 1 < ‖y‖ ^ 2 := by nlinarith
    linarith

  have hy_neg : valuation y < 0 := by
    by_contra hy_ge
    push Not at hy_ge
    have hx_gt : 1 < ‖x‖ := val_neg_implies_norm_gt_one hx_neg
    have hy_le : ‖y‖ ≤ 1 := (norm_le_one_iff_val_nonneg _).mpr hy_ge

    have hRHS := rhs_norm_eq_cube hn₂ hn₄ hn₆ hx_gt

    have hLHS_le : ‖y ^ 2 + a₁ * x * y + a₃ * y‖ ≤ ‖x‖ := by
      have h1 : ‖y ^ 2‖ ≤ ‖x‖ := by
        rw [norm_pow]
        calc ‖y‖ ^ 2 ≤ 1 ^ 2 := by
              exact pow_le_pow_left₀ (norm_nonneg _) hy_le 2
          _ = 1 := one_pow 2
          _ ≤ ‖x‖ := le_of_lt hx_gt
      have h2 : ‖a₁ * x * y‖ ≤ ‖x‖ := by
        rw [norm_mul, norm_mul]
        calc ‖a₁‖ * ‖x‖ * ‖y‖ ≤ 1 * ‖x‖ * 1 := by
              gcongr
          _ = ‖x‖ := by ring
      have h3 : ‖a₃ * y‖ ≤ ‖x‖ := by
        rw [norm_mul]
        calc ‖a₃‖ * ‖y‖ ≤ 1 * 1 := by
              apply mul_le_mul hn₃ hy_le (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
          _ ≤ ‖x‖ := le_of_lt hx_gt
      calc ‖y ^ 2 + a₁ * x * y + a₃ * y‖
          ≤ max ‖y ^ 2 + a₁ * x * y‖ ‖a₃ * y‖ := Padic.nonarchimedean _ _
        _ ≤ max (max ‖y ^ 2‖ ‖a₁ * x * y‖) ‖a₃ * y‖ := by
            apply max_le_max_right; exact Padic.nonarchimedean _ _
        _ ≤ ‖x‖ := by
            simp only [max_le_iff]
            exact ⟨⟨h1, h2⟩, h3⟩

    have : ‖x‖ < ‖x‖ ^ 3 := by nlinarith [sq_nonneg ‖x‖]
    linarith

  have hx_ne : x ≠ 0 := by intro hx0; simp [hx0] at hx_neg
  have hy_ne : y ≠ 0 := by intro hy0; simp [hy0] at hy_neg
  have hx_gt : 1 < ‖x‖ := val_neg_implies_norm_gt_one hx_neg
  have hy_gt : 1 < ‖y‖ := val_neg_implies_norm_gt_one hy_neg

  have hy_gt_x : ‖x‖ < ‖y‖ := by
    by_contra hyx
    push Not at hyx

    have hLHS_le : ‖y ^ 2 + a₁ * x * y + a₃ * y‖ ≤ ‖x‖ ^ 2 := by
      have h1 : ‖y ^ 2‖ ≤ ‖x‖ ^ 2 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hyx 2
      have h2 : ‖a₁ * x * y‖ ≤ ‖x‖ ^ 2 := by
        rw [norm_mul, norm_mul]
        calc ‖a₁‖ * ‖x‖ * ‖y‖ ≤ 1 * ‖x‖ * ‖x‖ := by
              gcongr
          _ = ‖x‖ ^ 2 := by ring
      have h3 : ‖a₃ * y‖ ≤ ‖x‖ ^ 2 := by
        rw [norm_mul]
        calc ‖a₃‖ * ‖y‖ ≤ 1 * ‖x‖ := by
              apply mul_le_mul hn₃ hyx (norm_nonneg _) zero_le_one
          _ = ‖x‖ := one_mul _
          _ ≤ ‖x‖ ^ 2 := by nlinarith
      calc ‖y ^ 2 + a₁ * x * y + a₃ * y‖
          ≤ max ‖y ^ 2 + a₁ * x * y‖ ‖a₃ * y‖ := Padic.nonarchimedean _ _
        _ ≤ max (max ‖y ^ 2‖ ‖a₁ * x * y‖) ‖a₃ * y‖ := by
            apply max_le_max_right; exact Padic.nonarchimedean _ _
        _ ≤ ‖x‖ ^ 2 := by
            simp only [max_le_iff]
            exact ⟨⟨h1, h2⟩, h3⟩
    have hRHS := rhs_norm_eq_cube hn₂ hn₄ hn₆ hx_gt
    have : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
      rw [show ‖x‖ ^ 3 = ‖x‖ ^ 2 * ‖x‖ from by ring]
      exact lt_mul_of_one_lt_right (pow_pos (by linarith) 2) hx_gt
    linarith

  have h_a1xy_lt : ‖a₁ * x * y‖ < ‖y ^ 2‖ := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖a₁‖ * ‖x‖ * ‖y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hn₁ (norm_nonneg _)
          · exact norm_nonneg _
      _ = ‖x‖ * ‖y‖ := by ring
      _ < ‖y‖ * ‖y‖ := by nlinarith
      _ = ‖y‖ ^ 2 := by ring
  have h_a3y_lt : ‖a₃ * y‖ < ‖y ^ 2‖ := by
    rw [norm_mul, norm_pow]
    calc ‖a₃‖ * ‖y‖ ≤ 1 * ‖y‖ := by
          apply mul_le_mul_of_nonneg_right hn₃ (norm_nonneg _)
      _ = ‖y‖ := one_mul _
      _ < ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
  have hLHS : ‖y ^ 2 + a₁ * x * y + a₃ * y‖ = ‖y‖ ^ 2 := by
    rw [ultra3_padic h_a1xy_lt h_a3y_lt, norm_pow]
  have hRHS := rhs_norm_eq_cube hn₂ hn₄ hn₆ hx_gt
  have hnorm_eq : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by linarith

  have hval_eq : 2 * valuation y = 3 * valuation x := by
    rw [norm_eq_zpow_neg_valuation hx_ne, norm_eq_zpow_neg_valuation hy_ne] at hnorm_eq
    simp only [← zpow_natCast, ← zpow_mul] at hnorm_eq
    have key := zpow_inj_prime hnorm_eq
    push_cast at key
    omega

  exact ⟨hy_ne, by omega⟩
