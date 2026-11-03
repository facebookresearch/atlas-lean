/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.Convolution
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset BigOperators

namespace BooleanFourier

noncomputable def vol {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x = true).card : ℝ) / (2 ^ n : ℝ)

lemma vol_nonneg {n : ℕ} (f : (Fin n → Bool) → Bool) : 0 ≤ vol f := by
  unfold vol; positivity

lemma vol_le_one {n : ℕ} (f : (Fin n → Bool) → Bool) : vol f ≤ 1 := by
  unfold vol
  rw [div_le_one (by positivity : (2 : ℝ) ^ n > 0)]
  have h := Finset.card_filter_le Finset.univ (fun x => f x = true)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h


theorem parseval_signed {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ S : Finset (Fin n),
      fourierCoeff (fun x => boolToReal (f x)) S ^ 2 = 1 := by
  rw [parseval]
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  simp_rw [boolToReal_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one, one_div]
  exact_mod_cast inv_mul_cancel₀ h2n

noncomputable def agreementProb {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (1 / (2 : ℝ) ^ n) ^ 2 *
    ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      if boolToReal (f x) * boolToReal (f y) = boolToReal (f (boolMul x y)) then 1 else 0

lemma boolToReal_agreement_indicator {n : ℕ} (f : (Fin n → Bool) → Bool)
    (x y : Fin n → Bool) :
    (if boolToReal (f x) * boolToReal (f y) = boolToReal (f (boolMul x y))
      then (1 : ℝ) else 0) =
    (1 + boolToReal (f x) * boolToReal (f y) * boolToReal (f (boolMul x y))) / 2 := by
  cases hfx : f x <;> cases hfy : f y <;> cases hfz : f (boolMul x y)
  all_goals simp [boolToReal]
  all_goals norm_num

lemma tripleCorrelation_eq_sum_cube {n : ℕ} (g : (Fin n → Bool) → ℝ) :
    (1 / (2 : ℝ) ^ n) ^ 2 *
      ∑ x : Fin n → Bool, ∑ y : Fin n → Bool, g x * g y * g (boolMul x y) =
    ∑ S : Finset (Fin n), fourierCoeff g S ^ 3 := by

  have hconv_expand : (1 / (2 : ℝ) ^ n) ^ 2 *
      ∑ x : Fin n → Bool, ∑ y : Fin n → Bool, g x * g y * g (boolMul x y) =
      (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, g x * conv g g x := by
    unfold conv
    simp_rw [show ∀ x : Fin n → Bool,
      g x * (1 / (2 : ℝ) ^ n * ∑ y : Fin n → Bool, g y * g (boolMul x y)) =
      1 / (2 : ℝ) ^ n * (∑ y : Fin n → Bool, g x * (g y * g (boolMul x y)))
      from fun x => by rw [← Finset.mul_sum]; ring]
    rw [← Finset.mul_sum]
    have hrw : ∀ x : Fin n → Bool,
        ∑ y : Fin n → Bool, g x * (g y * g (boolMul x y)) =
        ∑ y : Fin n → Bool, g x * g y * g (boolMul x y) :=
      fun x => Finset.sum_congr rfl (fun y _ => by ring)
    simp_rw [hrw]
    ring
  rw [hconv_expand]

  have hplanch := plancherel g (conv g g)
  unfold innerProduct at hplanch
  rw [← hplanch]

  congr 1
  ext S
  rw [fourierCoeff_conv g g S]
  ring

lemma agreementProb_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    agreementProb f =
    (1 + ∑ S : Finset (Fin n),
      fourierCoeff (fun x => boolToReal (f x)) S ^ 3) / 2 := by
  unfold agreementProb

  simp_rw [boolToReal_agreement_indicator f]

  simp_rw [show ∀ x : Fin n → Bool,
      ∑ y : Fin n → Bool,
        (1 + boolToReal (f x) * boolToReal (f y) * boolToReal (f (boolMul x y))) / 2 =
      (∑ y : Fin n → Bool,
        (1 + boolToReal (f x) * boolToReal (f y) * boolToReal (f (boolMul x y)))) / 2
    from fun x => (Finset.sum_div Finset.univ _ 2).symm]

  simp_rw [Finset.sum_add_distrib]

  have hcard_y : ∑ _y : Fin n → Bool, (1 : ℝ) = (2 : ℝ) ^ n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hcard_y]

  rw [show ∑ x : Fin n → Bool,
      ((2 : ℝ) ^ n +
        ∑ y : Fin n → Bool,
          boolToReal (f x) * boolToReal (f y) * boolToReal (f (boolMul x y))) / 2 =
      (∑ x : Fin n → Bool,
        ((2 : ℝ) ^ n +
          ∑ y : Fin n → Bool,
            boolToReal (f x) * boolToReal (f y) * boolToReal (f (boolMul x y)))) / 2
    from (Finset.sum_div Finset.univ _ 2).symm]
  rw [Finset.sum_add_distrib]

  have hcard_x : ∑ _x : Fin n → Bool, (2 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, sq]
  rw [hcard_x]

  set g : (Fin n → Bool) → ℝ := fun x => boolToReal (f x)
  have htriple := tripleCorrelation_eq_sum_cube g


  set T := ∑ x : Fin n → Bool, ∑ y : Fin n → Bool, g x * g y * g (boolMul x y)
  set F := ∑ S : Finset (Fin n), fourierCoeff g S ^ 3
  have h1 : (1 / (2 : ℝ) ^ n) ^ 2 * ((2 : ℝ) ^ n) ^ 2 = 1 := by field_simp
  have heq : (1 / (2 : ℝ) ^ n) ^ 2 * (((2 : ℝ) ^ n) ^ 2 + T) = 1 + F := by
    rw [mul_add, h1, htriple]
  linarith

end BooleanFourier

open Finset BigOperators BooleanFourier in
lemma flipCoord_eq_flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipCoord x i = flipAt i x := rfl

open Finset BigOperators BooleanFourier in
lemma influence_eq_influenceReal {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    influence f i = influenceReal (fun x => boolToReal (f x)) i := by
  classical
  unfold influence influenceReal
  have hterm : ∀ x : Fin n → Bool,
      ((boolToReal (f x) - boolToReal (f (flipAt i x))) / 2) ^ 2 =
      if f x ≠ f (flipCoord x i) then (1 : ℝ) else 0 := by
    intro x
    cases hfx : f x <;> cases hfy : f (flipAt i x)
    all_goals simp [boolToReal, hfy, flipCoord_eq_flipAt]
    all_goals norm_num
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

open Finset BigOperators BooleanFourier in
lemma totalInfluence_eq_totalInfluenceReal {n : ℕ} (f : (Fin n → Bool) → Bool) :
    totalInfluence f = totalInfluenceReal (fun x => boolToReal (f x)) := by
  unfold totalInfluence totalInfluenceReal
  exact Finset.sum_congr rfl (fun i _ => influence_eq_influenceReal f i)

open Finset BigOperators BooleanFourier in
theorem totalInfluence_eq_weighted_fourier' {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    totalInfluence f =
    ∑ S : Finset (Fin n),
      (S.card : ℝ) * fourierCoeff (fun x => boolToReal (f x)) S ^ 2 := by
  rw [totalInfluence_eq_totalInfluenceReal]
  exact totalInfluenceReal_eq_sum_card_fourierCoeff_sq _

namespace BooleanFourier

theorem exists_fourierCoeff_ge_of_sum_cube_ge {n : ℕ} (f : (Fin n → Bool) → Bool) (δ : ℝ)
    (hδ : ∑ S : Finset (Fin n),
      fourierCoeff (fun x => boolToReal (f x)) S ^ 3 ≥ 2 * δ) :
    ∃ S : Finset (Fin n),
      fourierCoeff (fun x => boolToReal (f x)) S ≥ 2 * δ := by
  classical
  set g : (Fin n → Bool) → ℝ := fun x => boolToReal (f x)


  by_contra h
  push Not at h

  have hparseval : ∑ S : Finset (Fin n), fourierCoeff g S ^ 2 = 1 :=
    parseval_signed f

  have ⟨S₀, _, hS₀_pos⟩ : ∃ S₀ ∈ (Finset.univ : Finset (Finset (Fin n))),
      (0 : ℝ) < fourierCoeff g S₀ ^ 2 := by
    by_contra hall
    push Not at hall
    have hzero : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
        fourierCoeff g S ^ 2 = 0 := by
      intro S hS; linarith [sq_nonneg (fourierCoeff g S), hall S hS]
    have := Finset.sum_eq_zero (fun S hS => hzero S hS)
    linarith

  have hterm_le : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      fourierCoeff g S ^ 3 ≤ (2 * δ) * fourierCoeff g S ^ 2 := by
    intro S _
    have hsq : (0 : ℝ) ≤ fourierCoeff g S ^ 2 := sq_nonneg _
    have heq : fourierCoeff g S ^ 3 = fourierCoeff g S * fourierCoeff g S ^ 2 := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_of_lt (h S)) hsq

  have hterm_lt : fourierCoeff g S₀ ^ 3 < (2 * δ) * fourierCoeff g S₀ ^ 2 := by
    have heq : fourierCoeff g S₀ ^ 3 = fourierCoeff g S₀ * fourierCoeff g S₀ ^ 2 := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_right (h S₀) hS₀_pos

  have hlt : ∑ S : Finset (Fin n), fourierCoeff g S ^ 3 < 2 * δ := by
    have hsum_lt := Finset.sum_lt_sum hterm_le ⟨S₀, Finset.mem_univ _, hterm_lt⟩
    have hbound : ∑ S : Finset (Fin n), (2 * δ) * fourierCoeff g S ^ 2 = 2 * δ := by
      rw [← Finset.mul_sum, hparseval, mul_one]
    linarith
  linarith

theorem exists_fourierCoeff_ge_of_agreementProb {n : ℕ} (f : (Fin n → Bool) → Bool) (δ : ℝ)
    (hδ : agreementProb f ≥ 1/2 + δ) :
    ∃ S : Finset (Fin n),
      fourierCoeff (fun x => boolToReal (f x)) S ≥ 2 * δ := by
  apply exists_fourierCoeff_ge_of_sum_cube_ge

  have heq := agreementProb_eq f
  linarith

end BooleanFourier
