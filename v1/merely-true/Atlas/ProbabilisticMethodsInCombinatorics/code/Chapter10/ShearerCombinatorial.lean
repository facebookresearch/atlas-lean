/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerChainRule
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Finset.Image

set_option maxHeartbeats 800000

open Finset BigOperators Real ShannonEntropy

namespace ShearerCombinatorial


/-- Shannon entropy of the uniform distribution on a nonempty finset $F$ equals $\log |F|$. -/
theorem shannonEntropy_uniform {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) (hF : F.Nonempty) :
    shannonEntropy (PMF.uniformOfFinset F hF) = Real.log F.card := by
  simp only [shannonEntropy]
  have hcard_pos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hF)
  have hcard_ne : (F.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hval : ∀ s : α, (PMF.uniformOfFinset F hF s).toReal =
      if s ∈ F then (1 : ℝ) / F.card else 0 := by
    intro s
    split_ifs with h
    · rw [PMF.uniformOfFinset_apply, if_pos h]
      simp [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
    · rw [PMF.uniformOfFinset_apply, if_neg h]
      simp
  simp_rw [hval]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ F)]
  have h_out : ∑ s ∈ Finset.univ.filter (· ∉ F),
      Real.negMulLog (if s ∈ F then (1 : ℝ) / ↑F.card else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [if_neg hs, Real.negMulLog_zero]
  rw [h_out, add_zero]
  have h_in : ∀ s ∈ Finset.univ.filter (· ∈ F),
      Real.negMulLog (if s ∈ F then (1 : ℝ) / ↑F.card else 0) =
      Real.negMulLog (1 / F.card) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [if_pos hs]
  rw [Finset.sum_congr rfl h_in, Finset.sum_const]
  have hcard_filter : (Finset.univ.filter (· ∈ F)).card = F.card := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hcard_filter, nsmul_eq_mul]
  simp only [Real.negMulLog, one_div, Real.log_inv]
  field_simp

/-- The Shannon entropy of a PMF is bounded by the logarithm of its support size, via Jensen's
inequality applied to $-x \log x$. -/
theorem entropy_le_log_support_card {S : Type*} [Fintype S] [DecidableEq S] (p : PMF S) :
    shannonEntropy p ≤ Real.log ((Finset.univ.filter (fun s => p s ≠ 0)).card) := by
  set supp := Finset.univ.filter (fun s => p s ≠ 0) with supp_def
  have hsupp_ne : supp.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hzero : ∀ s : S, (p s).toReal = 0 := by
      intro s
      by_cases hs : p s = 0
      · simp [hs]
      · exfalso
        have : s ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
        rw [h] at this; exact absurd this (Finset.notMem_empty _)
    have : ∑ s : S, (p s).toReal = 0 := by
      apply Finset.sum_eq_zero; intro s _; exact hzero s
    linarith [pmf_sum_toReal_eq_one p]
  have hn_pos : (0 : ℝ) < supp.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hsupp_ne)
  have hn_ne : (supp.card : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_split : shannonEntropy p = ∑ s ∈ supp, Real.negMulLog (p s).toReal := by
    simp only [shannonEntropy]
    symm
    apply Finset.sum_subset (Finset.subset_univ supp)
    intro s _ hs
    have : p s = 0 := by
      by_contra hne; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp [this]
  have hsupp_sum : ∑ s ∈ supp, (p s).toReal = 1 := by
    have : ∑ s ∈ supp, (p s).toReal = ∑ s : S, (p s).toReal := by
      apply Finset.sum_subset (Finset.subset_univ supp)
      intro s _ hs
      have : p s = 0 := by
        by_contra hne; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      simp [this]
    rw [this, pmf_sum_toReal_eq_one]
  rw [h_split]
  have hw_nn : ∀ i ∈ supp, (0 : ℝ) ≤ 1 / (supp.card : ℝ) :=
    fun _ _ => div_nonneg zero_le_one hn_pos.le
  have hw_sum : ∑ _ ∈ supp, (1 : ℝ) / (supp.card : ℝ) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hmem : ∀ i ∈ supp, (p i).toReal ∈ Set.Ici (0 : ℝ) :=
    fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg
  have jensen := concaveOn_negMulLog.le_map_sum hw_nn hw_sum hmem
  simp only [smul_eq_mul] at jensen
  have lhs_eq : ∑ s ∈ supp, (1 : ℝ) / (supp.card : ℝ) * negMulLog (p s).toReal =
      (1 / (supp.card : ℝ)) * ∑ s ∈ supp, negMulLog (p s).toReal := (Finset.mul_sum ..).symm
  have rhs_sum : ∑ s ∈ supp, (1 : ℝ) / (supp.card : ℝ) * (p s).toReal =
      1 / (supp.card : ℝ) := by
    rw [← Finset.mul_sum, hsupp_sum, mul_one]
  rw [lhs_eq, rhs_sum] at jensen
  have h_le : ∑ s ∈ supp, negMulLog (p s).toReal ≤
      (supp.card : ℝ) * negMulLog (1 / (supp.card : ℝ)) := by
    have := mul_le_mul_of_nonneg_left jensen hn_pos.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hn_ne, one_mul] at this
  have key : (supp.card : ℝ) * negMulLog (1 / (supp.card : ℝ)) =
      Real.log (supp.card : ℝ) := by
    simp [negMulLog]; field_simp
  linarith

/-- Pushing forward the uniform distribution on $F$ by a map $f$ gives entropy at most
$\log |f(F)|$. -/
theorem entropy_map_uniform_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (F : Finset α) (hF : F.Nonempty) (f : α → β) :
    shannonEntropy ((PMF.uniformOfFinset F hF).map f) ≤
    Real.log ((F.image f).card) := by

  have hsupport_le : (Finset.univ.filter (fun b => (PMF.uniformOfFinset F hF).map f b ≠ 0)).card ≤
      (F.image f).card := by
    apply Finset.card_le_card
    intro b hb
    rw [Finset.mem_filter] at hb

    rw [PMF.map_apply] at hb
    by_contra h_not_mem
    apply hb.2
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    split_ifs with hab
    · rw [PMF.uniformOfFinset_apply, if_neg]
      intro ha
      exact h_not_mem (Finset.mem_image.mpr ⟨a, ha, hab.symm⟩)
    · rfl

  have hsupp_pos : (0 : ℝ) <
      (Finset.univ.filter (fun b => (PMF.uniformOfFinset F hF).map f b ≠ 0)).card := by
    apply Nat.cast_pos.mpr
    apply Finset.Nonempty.card_pos
    obtain ⟨a, ha⟩ := hF
    refine ⟨f a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [PMF.map_apply]
    intro heq
    have := ENNReal.tsum_eq_zero.mp heq a
    simp only [↓reduceIte] at this
    rw [PMF.uniformOfFinset_apply, if_pos ha] at this
    simp at this

  calc shannonEntropy ((PMF.uniformOfFinset F hF).map f)
      ≤ Real.log ((Finset.univ.filter (fun b => (PMF.uniformOfFinset F hF).map f b ≠ 0)).card) :=
        entropy_le_log_support_card _
    _ ≤ Real.log ((F.image f).card) := by
        apply Real.log_le_log hsupp_pos
        exact_mod_cast hsupport_le


end ShearerCombinatorial

namespace LoomisWhitney

open Finset BigOperators Real ShannonEntropy

/-- Projection of `x : Fin n → α` onto all coordinates except the $i$-th one. -/
def coordProject {n : ℕ} {α : Type*} (i : Fin n) (x : Fin n → α) :
    ↥(Finset.univ.erase i : Finset (Fin n)) → α :=
  fun ⟨j, _⟩ => x j


end LoomisWhitney
