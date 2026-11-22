/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.FourierExpansion
import Atlas.BooleanFunctions.code.Parseval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff

open Finset BigOperators

namespace BooleanFourier

open scoped symmDiff

noncomputable def influenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool,
    ((f x - f (flipAt i x)) / 2) ^ 2

lemma chi_flipAt_of_not_mem {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (x : Fin n → Bool) : chi S (flipAt i x) = chi S x := by
  simp only [chi, flipAt]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have hjne : j ≠ i := fun h => hi (h ▸ hj)
  exact Function.update_of_ne hjne _ _

lemma chi_mul_chi_eq {n : ℕ} (S S' : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x * chi S' x = chi (S ∆ S') x := by
  classical
  simp only [chi]
  have h1 : (∏ i ∈ S, boolToReal (x i)) * (∏ i ∈ S', boolToReal (x i)) =
      (∏ i ∈ S ∪ S', boolToReal (x i)) * (∏ i ∈ S ∩ S', boolToReal (x i)) := by
    rw [← Finset.prod_union_inter]
  have h2 : S ∪ S' = (S ∆ S') ∪ (S ∩ S') := by
    ext a; simp [Finset.mem_symmDiff]; tauto
  have h3 : Disjoint (S ∆ S') (S ∩ S') := by
    simp only [Finset.disjoint_left, Finset.mem_symmDiff, Finset.mem_inter]
    intro a ha hb
    rcases ha with ⟨_, h⟩ | ⟨_, h⟩
    · exact h hb.2
    · exact h hb.1
  have h4 : (∏ i ∈ S ∪ S', boolToReal (x i)) =
      (∏ i ∈ S ∆ S', boolToReal (x i)) * (∏ i ∈ S ∩ S', boolToReal (x i)) := by
    rw [h2, Finset.prod_union h3]
  have h5 : (∏ i ∈ S ∩ S', boolToReal (x i)) * (∏ i ∈ S ∩ S', boolToReal (x i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp [boolToReal_mul_self]
  calc (∏ i ∈ S, boolToReal (x i)) * (∏ i ∈ S', boolToReal (x i))
      = (∏ i ∈ S ∪ S', boolToReal (x i)) * (∏ i ∈ S ∩ S', boolToReal (x i)) := h1
    _ = ((∏ i ∈ S ∆ S', boolToReal (x i)) * (∏ i ∈ S ∩ S', boolToReal (x i))) *
        (∏ i ∈ S ∩ S', boolToReal (x i)) := by rw [h4]
    _ = (∏ i ∈ S ∆ S', boolToReal (x i)) *
        ((∏ i ∈ S ∩ S', boolToReal (x i)) * (∏ i ∈ S ∩ S', boolToReal (x i))) := by ring
    _ = (∏ i ∈ S ∆ S', boolToReal (x i)) * 1 := by rw [h5]
    _ = ∏ i ∈ S ∆ S', boolToReal (x i) := by ring

lemma sum_chi_mul_chi_x {n : ℕ} (S S' : Finset (Fin n)) :
    ∑ x : Fin n → Bool, chi S x * chi S' x =
      if S = S' then (2 : ℝ) ^ n else 0 := by
  classical
  simp_rw [chi_mul_chi_eq]
  rw [sum_chi]
  simp [Finset.symmDiff_eq_empty]

theorem influenceReal_eq_sum_fourierCoeff_sq {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (i : Fin n) :
    influenceReal f i =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (i ∈ ·),
        fourierCoeff f S ^ 2 := by
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  unfold influenceReal
  set T := (Finset.univ : Finset (Finset (Fin n))).filter (i ∈ ·) with hT_def
  have diff_eq : ∀ x : Fin n → Bool,
      f x - f (flipAt i x) =
        2 * ∑ S ∈ T, fourierCoeff f S * chi S x := by
    intro x
    have hfx := fourier_expansion f x
    have hfx' := fourier_expansion f (flipAt i x)
    have calc1 : f x - f (flipAt i x) =
        ∑ S : Finset (Fin n), fourierCoeff f S * (chi S x - chi S (flipAt i x)) := by
      rw [hfx, hfx', ← Finset.sum_sub_distrib]
      congr 1; ext S; ring
    rw [calc1]
    have calc2 : ∀ S : Finset (Fin n),
        fourierCoeff f S * (chi S x - chi S (flipAt i x)) =
        if i ∈ S then 2 * (fourierCoeff f S * chi S x) else 0 := by
      intro S
      by_cases hi : i ∈ S
      · rw [chi_flipAt S i hi x]; simp only [hi, if_true]; ring
      · rw [chi_flipAt_of_not_mem S i hi x]; simp only [hi, if_false, sub_self, mul_zero]
    simp_rw [calc2, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    rfl
  have simp_eq : ∀ x : Fin n → Bool,
      ((f x - f (flipAt i x)) / 2) ^ 2 =
      (∑ S ∈ T, fourierCoeff f S * chi S x) ^ 2 := by
    intro x; rw [diff_eq x]; ring
  simp_rw [simp_eq]
  have expand_sq : ∀ x : Fin n → Bool,
      (∑ S ∈ T, fourierCoeff f S * chi S x) ^ 2 =
      ∑ S ∈ T, ∑ S' ∈ T,
        fourierCoeff f S * fourierCoeff f S' * (chi S x * chi S' x) := by
    intro x
    rw [sq, Finset.sum_mul]
    congr 1; ext S; rw [Finset.mul_sum]
    congr 1; ext S'; ring
  simp_rw [expand_sq]
  have pull_out :
      (1 / (2 : ℝ) ^ n) *
      (∑ x : Fin n → Bool, ∑ S ∈ T, ∑ S' ∈ T,
        fourierCoeff f S * fourierCoeff f S' * (chi S x * chi S' x)) =
      (1 / (2 : ℝ) ^ n) * ∑ S ∈ T, ∑ S' ∈ T,
        fourierCoeff f S * fourierCoeff f S' *
          (∑ x : Fin n → Bool, chi S x * chi S' x) := by
    congr 1
    rw [Finset.sum_comm]
    congr 1; ext S
    rw [Finset.sum_comm]
    congr 1; ext S'
    rw [Finset.mul_sum]
  rw [pull_out]
  simp_rw [sum_chi_mul_chi_x]
  have collapse_inner : ∀ S ∈ T,
      (∑ S' ∈ T, fourierCoeff f S * fourierCoeff f S' *
        (if S = S' then (2 : ℝ) ^ n else 0)) =
      fourierCoeff f S ^ 2 * (2 : ℝ) ^ n := by
    intro S hS
    have : ∀ S' : Finset (Fin n),
        fourierCoeff f S * fourierCoeff f S' *
          (if S = S' then (2 : ℝ) ^ n else 0) =
        if S' = S then fourierCoeff f S ^ 2 * (2 : ℝ) ^ n else 0 := by
      intro S'
      split_ifs with h1 h2 h2
      · subst h1; ring
      · exfalso; exact h2 h1.symm
      · exfalso; exact h1 h2.symm
      · ring
    simp_rw [this]
    rw [Finset.sum_ite_eq']
    simp [hS]
  rw [show (1 / (2 : ℝ) ^ n) * ∑ S ∈ T, ∑ S' ∈ T,
      fourierCoeff f S * fourierCoeff f S' *
        (if S = S' then (2 : ℝ) ^ n else 0) =
      (1 / (2 : ℝ) ^ n) * ∑ S ∈ T,
        fourierCoeff f S ^ 2 * (2 : ℝ) ^ n from by
    congr 1; exact Finset.sum_congr rfl collapse_inner]
  rw [← Finset.sum_mul]
  field_simp

noncomputable def totalInfluenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ i : Fin n, influenceReal f i

theorem totalInfluenceReal_eq_sum_card_fourierCoeff_sq {n : ℕ}
    (f : (Fin n → Bool) → ℝ) :
    totalInfluenceReal f =
      ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2 := by
  classical
  unfold totalInfluenceReal
  simp_rw [influenceReal_eq_sum_fourierCoeff_sq]


  simp_rw [Finset.sum_filter]

  rw [Finset.sum_comm]

  congr 1
  ext S
  rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]

noncomputable def varianceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (· ≠ ∅), fourierCoeff f S ^ 2

theorem totalInfluenceReal_ge_varianceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    totalInfluenceReal f ≥ varianceReal f := by
  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq]
  unfold varianceReal
  rw [Finset.sum_filter]
  apply ge_iff_le.mpr
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S ≠ ∅
  · simp only [if_pos hS]
    have hcard : (1 : ℝ) ≤ (S.card : ℝ) :=
      Nat.one_le_cast.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
    nlinarith [sq_nonneg (fourierCoeff f S)]
  · push Not at hS
    simp [hS]

lemma sq_eq_self_of_zero_one {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : Fin n → Bool) :
    f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem varianceReal_eq_quarter_of_balanced {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hbal : fourierCoeff f ∅ = 1 / 2) :
    varianceReal f = 1 / 4 := by

  have hparseval := parseval f

  have hfsq : ∀ x : Fin n → Bool, f x ^ 2 = f x := sq_eq_self_of_zero_one f hf

  have hparseval' : ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 =
      (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x := by
    rw [hparseval]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => hfsq x)

  have hfcoeff_empty : fourierCoeff f ∅ = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x := by
    unfold fourierCoeff
    simp [chi]

  have hsum_sq : ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 / 2 := by
    rw [hparseval', ← hfcoeff_empty, hbal]

  have hvar_split : varianceReal f =
      ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 - fourierCoeff f ∅ ^ 2 := by
    classical
    unfold varianceReal
    have herase : (Finset.univ : Finset (Finset (Fin n))).filter (· ≠ ∅) =
        Finset.univ.erase ∅ := by
      ext S; simp [Finset.mem_erase, Finset.mem_filter]
    rw [herase]
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
      (fun S => fourierCoeff f S ^ 2) (Finset.mem_univ ∅)
    linarith

  rw [hvar_split, hsum_sq, hbal]
  norm_num

theorem totalInfluenceReal_ge_quarter_of_balanced {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hbal : fourierCoeff f ∅ = 1 / 2) :
    totalInfluenceReal f ≥ 1 / 4 := by
  have hvar := varianceReal_eq_quarter_of_balanced f hf hbal
  have hinfl := totalInfluenceReal_ge_varianceReal f
  linarith

end BooleanFourier
