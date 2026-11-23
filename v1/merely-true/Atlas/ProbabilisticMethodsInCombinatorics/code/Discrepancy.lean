/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators

noncomputable section

namespace Discrepancy





variable {n m : ℕ}

/-- Indices at which a vector $a \in [-1,1]^m$ is in the open interior, i.e. neither $1$
nor $-1$. The discrepancy argument rounds these to a $\pm 1$ vector. -/
def interiorIndices (a : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => a i ≠ 1 ∧ a i ≠ -1)

/-- Feasibility predicate for the rounding step: a vector $a \in [-1,1]^m$ is feasible
with respect to vectors $v_1, \dots, v_m \in \mathbb{R}^n$ if $\sum_i a_i v_i = 0$. -/
def IsFeasible (v : Fin m → Fin n → ℝ) (a : Fin m → ℝ) : Prop :=
  (∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) ∧ ∑ i, a i • v i = 0

/-- Pivoting step. Given a feasible $a$ with more than $n$ interior coordinates, there is
another feasible $a'$ with strictly fewer interior coordinates, obtained by moving along a
linear dependency among the $v_i$'s on the interior set. -/
theorem feasible_improve (v : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (hfeas : IsFeasible v a) (hcard : n < (interiorIndices a).card) :
    ∃ a' : Fin m → ℝ, IsFeasible v a' ∧
      (interiorIndices a').card < (interiorIndices a).card := by
  classical
  set I := interiorIndices a with hI_def

  have not_lin_ind : ¬ LinearIndependent ℝ (fun i : I => v i.1) := by
    intro h_ind
    have h_le := h_ind.fintype_card_le_finrank
    simp at h_le; omega
  rw [Fintype.not_linearIndependent_iff] at not_lin_ind
  obtain ⟨c, hc_sum, j, hj_ne⟩ := not_lin_ind

  set d : Fin m → ℝ := fun i => if h : i ∈ I then c ⟨i, h⟩ else 0 with hd_def
  have hd_zero : ∀ i, i ∉ I → d i = 0 := fun i hi => by simp [hd_def, hi]

  have hd_sum : ∑ i : Fin m, d i • v i = 0 := by
    have h1 : ∑ i : Fin m, d i • v i = ∑ i ∈ I, d i • v i := by
      symm; apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi; simp [hd_def, hi]
    rw [h1, ← Finset.sum_attach]
    have h2 : ∀ i : I, d i.1 = c i := fun ⟨i, hi⟩ => by simp [hd_def, hi]
    simp_rw [h2]; exact hc_sum

  have ha_int : ∀ i ∈ I, -1 < a i ∧ a i < 1 := by
    intro i hi
    have hi' : a i ≠ 1 ∧ a i ≠ -1 := (Finset.mem_filter.mp hi).2
    exact ⟨lt_of_le_of_ne (hfeas.1 i).1 (Ne.symm hi'.2),
           lt_of_le_of_ne (hfeas.1 i).2 hi'.1⟩

  have hd_j : d j.1 ≠ 0 := by simp [hd_def, j.2, hj_ne]

  set ub := (I.filter (fun i => 0 < d i)).image (fun i => (1 - a i) / d i) ∪
            (I.filter (fun i => d i < 0)).image (fun i => (-1 - a i) / d i)
  have hub_nonempty : ub.Nonempty := by
    rcases lt_or_gt_of_ne hd_j with hlt | hgt
    · exact ⟨_, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨j.1, Finset.mem_filter.mpr ⟨j.2, hlt⟩, rfl⟩))⟩
    · exact ⟨_, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨j.1, Finset.mem_filter.mpr ⟨j.2, hgt⟩, rfl⟩))⟩
  have hub_pos : ∀ b ∈ ub, 0 < b := by
    intro b hb
    rcases Finset.mem_union.mp hb with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact div_pos (by linarith [(ha_int i (Finset.mem_filter.mp hi).1).2])
        (Finset.mem_filter.mp hi).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact div_pos_of_neg_of_neg (by linarith [(ha_int i (Finset.mem_filter.mp hi).1).1])
        (Finset.mem_filter.mp hi).2

  set t := ub.min' hub_nonempty
  have ht_pos : 0 < t := hub_pos t (Finset.min'_mem _ _)
  have ht_le_ub : ∀ b ∈ ub, t ≤ b := fun b hb => Finset.min'_le _ _ hb

  refine ⟨fun i => a i + t * d i, ⟨?_, ?_⟩, ?_⟩
  ·
    intro i; constructor
    · by_cases hi : i ∈ I
      · rcases lt_trichotomy (d i) 0 with hdi | hdi | hdi
        · have hmem : (-1 - a i) / d i ∈ ub :=
            Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
              ⟨i, Finset.mem_filter.mpr ⟨hi, hdi⟩, rfl⟩))
          have := ht_le_ub _ hmem
          rw [le_div_iff_of_neg hdi] at this; linarith
        · simp [hdi]; exact (hfeas.1 i).1
        · linarith [(ha_int i hi).1, mul_nonneg (le_of_lt ht_pos) (le_of_lt hdi)]
      · simp [hd_zero i hi]; exact (hfeas.1 i).1
    · by_cases hi : i ∈ I
      · rcases lt_trichotomy (d i) 0 with hdi | hdi | hdi
        · linarith [(ha_int i hi).2, mul_neg_of_pos_of_neg ht_pos hdi]
        · simp [hdi]; exact (hfeas.1 i).2
        · have hmem : (1 - a i) / d i ∈ ub :=
            Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
              ⟨i, Finset.mem_filter.mpr ⟨hi, hdi⟩, rfl⟩))
          have := ht_le_ub _ hmem
          rw [le_div_iff₀ hdi] at this; linarith
      · simp [hd_zero i hi]; exact (hfeas.1 i).2
  ·
    simp_rw [add_smul, mul_smul, Finset.sum_add_distrib]
    rw [hfeas.2, ← Finset.smul_sum, hd_sum, smul_zero, add_zero]
  ·
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    ·
      intro i hi
      simp [interiorIndices] at hi ⊢
      rw [hI_def]; simp [interiorIndices]
      constructor
      · intro h_eq
        have h_not_I : i ∉ I := by rw [hI_def]; simp [interiorIndices, h_eq]
        simp [hd_zero i h_not_I, h_eq] at hi
      · intro h_eq
        have h_not_I : i ∉ I := by rw [hI_def]; simp [interiorIndices, h_eq]
        simp [hd_zero i h_not_I, h_eq] at hi
    ·
      intro h_sub
      have ht_mem := Finset.min'_mem ub hub_nonempty
      rcases Finset.mem_union.mp ht_mem with h | h
      · obtain ⟨k, hk, htk⟩ := Finset.mem_image.mp h
        have hk' := Finset.mem_filter.mp hk
        have hk_bd : a k + t * d k = 1 := by
          have : t = (1 - a k) / d k := htk.symm
          rw [this, div_mul_cancel₀ (1 - a k) (ne_of_gt hk'.2)]; ring
        have hk_in := h_sub hk'.1
        simp [interiorIndices] at hk_in
        exact hk_in.1 hk_bd
      · obtain ⟨k, hk, htk⟩ := Finset.mem_image.mp h
        have hk' := Finset.mem_filter.mp hk
        have hk_bd : a k + t * d k = -1 := by
          have : t = (-1 - a k) / d k := htk.symm
          rw [this, div_mul_cancel₀ (-1 - a k) (ne_of_lt hk'.2)]; ring
        have hk_in := h_sub hk'.1
        simp [interiorIndices] at hk_in
        exact hk_in.2 hk_bd

/-- Iterating the pivoting step yields the technical rounding lemma underlying Spencer's
theorem: starting from $a = 0$ one can find a feasible $a \in [-1,1]^m$ with at most $n$
coordinates in the open interior. -/
theorem discrepancy_technical_lemma (n m : ℕ) (v : Fin m → Fin n → ℝ) :
    ∃ a : Fin m → ℝ,
      (∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) ∧
      (interiorIndices a).card ≤ n ∧
      ∑ i, a i • v i = 0 := by
  classical

  have h0_feas : IsFeasible v (fun _ => 0) := ⟨fun i => by simp, by simp⟩

  suffices h : ∀ k, ∀ a : Fin m → ℝ, IsFeasible v a →
      (interiorIndices a).card ≤ k →
      ∃ a' : Fin m → ℝ, IsFeasible v a' ∧ (interiorIndices a').card ≤ n by
    obtain ⟨a', ha', hcard'⟩ := h _ _ h0_feas le_rfl
    exact ⟨a', ha'.1, hcard', ha'.2⟩
  intro k
  induction k with
  | zero =>
    intro a ha hk
    exact ⟨a, ha, by omega⟩
  | succ k ih =>
    intro a ha hk
    by_cases hle : (interiorIndices a).card ≤ n
    · exact ⟨a, ha, hle⟩
    · push Not at hle
      obtain ⟨a', ha', hlt⟩ := feasible_improve v a ha hle
      exact ih a' ha' (by omega)

end Discrepancy
