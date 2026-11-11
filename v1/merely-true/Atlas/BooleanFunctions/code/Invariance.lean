/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.LindebergHybrid
import Atlas.BooleanFunctions.code.InvarianceDefs
import Mathlib.Probability.Distributions.Gaussian.Real
import Atlas.BooleanFunctions.code.MajorityStablest

noncomputable section

open Finset BigOperators MeasureTheory

namespace BooleanFourier

def linearBooleanFunction {n : ℕ} (a : Fin n → ℝ) : (Fin n → Bool) → ℝ :=
  fun x => ∑ i : Fin n, a i * boolToReal (x i)

noncomputable def singletonCoeffs {n : ℕ} (a : Fin n → ℝ) :
    Finset (Fin n) → ℝ :=
  fun S => if h : ∃ i, S = {i} then a h.choose else 0

lemma singletonCoeffs_singleton {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    singletonCoeffs a {i} = a i := by
  simp only [singletonCoeffs]
  have h : ∃ j, ({i} : Finset (Fin n)) = {j} := ⟨i, rfl⟩
  rw [dif_pos h]
  congr 1
  exact Finset.singleton_injective h.choose_spec.symm

lemma singletonCoeffs_non_singleton {n : ℕ} (a : Fin n → ℝ)
    (S : Finset (Fin n)) (hS : ¬∃ i, S = {i}) :
    singletonCoeffs a S = 0 := by
  simp [singletonCoeffs, hS]

lemma singleton_filter_eq_image {n : ℕ} :
    (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ∃ i, S = {i}) =
      Finset.image (fun i => ({i} : Finset (Fin n))) Finset.univ := by
  ext S
  constructor
  · intro hS
    rw [Finset.mem_filter] at hS
    obtain ⟨_, i, rfl⟩ := hS
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro hS
    rw [Finset.mem_image] at hS
    obtain ⟨i, _, rfl⟩ := hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, rfl⟩

lemma singletonCoeffs_agree {n : ℕ} (a : Fin n → ℝ) (b : Fin n → Bool) :
    ∑ S : Finset (Fin n), singletonCoeffs a S * ∏ i ∈ S, boolToReal (b i) =
      linearBooleanFunction a b := by
  simp only [linearBooleanFunction]
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => ∃ i, S = {i})]
  have h_not : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ¬∃ i, S = {i}),
      singletonCoeffs a S * ∏ i ∈ S, boolToReal (b i) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [singletonCoeffs_non_singleton a S hS.2, zero_mul]
  rw [h_not, add_zero]
  rw [singleton_filter_eq_image]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  congr 1; ext i
  rw [singletonCoeffs_singleton, Finset.prod_singleton]

lemma singletonCoeffs_eval {n : ℕ} (a : Fin n → ℝ) (z : Fin n → ℝ) :
    ∑ S : Finset (Fin n), singletonCoeffs a S * ∏ i ∈ S, z i =
      ∑ i : Fin n, a i * z i := by
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => ∃ i, S = {i})]
  have h_not : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ¬∃ i, S = {i}),
      singletonCoeffs a S * ∏ i ∈ S, z i = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [singletonCoeffs_non_singleton a S hS.2, zero_mul]
  rw [h_not, add_zero]
  rw [singleton_filter_eq_image]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  congr 1; ext i
  rw [singletonCoeffs_singleton, Finset.prod_singleton]

def boolCDF {n : ℕ} (f : (Fin n → Bool) → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun x => f x ≤ t).card : ℝ) / (2 : ℝ) ^ n

def HasUnitVariance {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1

theorem claim_2_2_invariance {n : ℕ} (f : (Fin n → Bool) → ℝ) (τ : ℝ) (_hτ : 0 ≤ τ)
    (hInf : ∀ i : Fin n, fourierInfluence f i ≤ τ) :
    ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤
      τ ^ ((1 : ℝ) / 2) * ∑ i : Fin n, fourierInfluence f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hInf_nonneg : 0 ≤ fourierInfluence f i := by
    simp only [fourierInfluence]
    apply Finset.sum_nonneg
    intro S _
    split_ifs <;> positivity
  have hInf_le := hInf i

  have h_half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (fourierInfluence f i) ^ ((3 : ℝ) / 2)
      = (fourierInfluence f i) ^ (1 + (1 : ℝ) / 2) := by ring_nf
    _ = (fourierInfluence f i) ^ (1 : ℝ) * (fourierInfluence f i) ^ ((1 : ℝ) / 2) := by
        rcases eq_or_lt_of_le hInf_nonneg with h | h
        · simp [← h, Real.zero_rpow (by norm_num : (1 : ℝ) + 2⁻¹ ≠ 0),
            Real.zero_rpow (by norm_num : (1 : ℝ) ≠ 0),
            Real.zero_rpow (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]
        · exact Real.rpow_add h 1 (1/2)
    _ = fourierInfluence f i * (fourierInfluence f i) ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_one]
    _ ≤ fourierInfluence f i * τ ^ ((1 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow hInf_nonneg hInf_le h_half_nonneg
        · exact hInf_nonneg
    _ = τ ^ ((1 : ℝ) / 2) * fourierInfluence f i := by ring

lemma fourierInfluence_eq_influenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    fourierInfluence f i = influenceReal f i := by
  rw [influenceReal_eq_sum_fourierCoeff_sq]
  simp only [fourierInfluence]
  rw [← Finset.sum_filter]

lemma sum_fourierInfluence_eq_totalInfluenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∑ i : Fin n, fourierInfluence f i = totalInfluenceReal f := by
  simp_rw [fourierInfluence_eq_influenceReal]
  rfl

lemma totalInfluenceReal_le_degree_mul_varianceReal {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (d : ℕ) (hdeg : degree f ≤ d) :
    totalInfluenceReal f ≤ (d : ℝ) * varianceReal f := by
  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq]
  unfold varianceReal
  rw [Finset.sum_filter]

  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [ne_eq, hS, not_false_eq_true, ite_true]

    by_cases hcoeff : fourierCoeff f S = 0
    · simp [hcoeff]
    · have hsq : (0 : ℝ) ≤ fourierCoeff f S ^ 2 := sq_nonneg _
      apply mul_le_mul_of_nonneg_right _ hsq
      have h1 : S.card ≤ degree f := by
        unfold degree
        apply Finset.le_sup
        simp [hcoeff]
      exact_mod_cast h1.trans hdeg

end BooleanFourier

end
