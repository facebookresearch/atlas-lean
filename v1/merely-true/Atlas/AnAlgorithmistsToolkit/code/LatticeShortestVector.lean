/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

open InnerProductSpace Finset

namespace LatticeShortestVector

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsGramSchmidt (b b_star : Fin n → E) : Prop :=
  b_star = gramSchmidt ℝ b

theorem lattice_vector_norm_bound {n : ℕ} (hn : 0 < n)
    (b : Fin n → EuclideanSpace ℝ (Fin n))
    (_hb_li : LinearIndependent ℝ b)
    (b_star : Fin n → EuclideanSpace ℝ (Fin n))
    (hgs : IsGramSchmidt b b_star)
    (v : EuclideanSpace ℝ (Fin n))
    (hv_lattice : ∃ c : Fin n → ℤ, v = ∑ i, (c i : ℝ) • b i)
    (hv_nonzero : v ≠ 0) :
    ‖v‖ ≥ ⨅ i : Fin n, ‖b_star i‖ := by

  obtain ⟨c, hc_eq⟩ := hv_lattice

  have hc_ne_zero : ∃ j : Fin n, c j ≠ 0 := by
    by_contra h
    push Not at h
    have : v = 0 := by
      rw [hc_eq]
      simp [fun i => h i]
    exact hv_nonzero this

  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩

  let S := Finset.filter (fun i => c i ≠ 0) Finset.univ
  have hS_nonempty : S.Nonempty := by
    obtain ⟨j, hj⟩ := hc_ne_zero
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩

  let j := S.max' hS_nonempty
  have hj_mem : j ∈ S := Finset.max'_mem S hS_nonempty
  have hcj_ne : c j ≠ 0 := (Finset.mem_filter.mp hj_mem).2
  have hj_max : ∀ i, c i ≠ 0 → i ≤ j := by
    intro i hi
    exact Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  subst hgs
  set gs := gramSchmidt ℝ b


  have inner_gs_v : ⟪gs j, v⟫_ℝ = (c j : ℝ) * ‖gs j‖ ^ 2 := by
    rw [hc_eq, inner_sum]

    have h_sum : ∑ i : Fin n, ⟪gs j, (c i : ℝ) • b i⟫_ℝ =
        (c j : ℝ) * ⟪gs j, b j⟫_ℝ := by
      have h_eq : ∀ i : Fin n, ⟪gs j, (c i : ℝ) • b i⟫_ℝ =
          if i = j then (c j : ℝ) * ⟪gs j, b j⟫_ℝ else 0 := by
        intro i
        simp only [inner_smul_right]
        split_ifs with hij
        · subst hij; ring
        ·
          rcases lt_or_gt_of_ne hij with h_lt | h_gt
          ·
            rw [gramSchmidt_inv_triangular ℝ b h_lt, mul_zero]
          ·
            have hci : c i = 0 := by
              by_contra hci_ne
              exact absurd (hj_max i hci_ne) (not_le.mpr h_gt)
            simp [hci]
      simp_rw [h_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h_sum]

    have h_inner_self : ⟪gs j, b j⟫_ℝ = ‖gs j‖ ^ 2 := by
      have hdecomp := gramSchmidt_def'' ℝ b j


      conv_lhs => rw [hdecomp]
      rw [inner_add_right]


      have h_second_zero : ⟪gs j, ∑ i ∈ Iio j,
          (⟪gramSchmidt ℝ b ↑i, b ↑j⟫_ℝ / ↑‖gramSchmidt ℝ b ↑i‖ ^ 2) •
            gramSchmidt ℝ b ↑i⟫_ℝ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_Iio] at hk
        rw [inner_smul_right]
        have hortho : ⟪gs j, gramSchmidt ℝ b ↑k⟫_ℝ = 0 :=
          gramSchmidt_orthogonal ℝ b (Fin.ne_of_gt hk)
        rw [hortho, mul_zero]


      convert (show ⟪gs j, gs j⟫_ℝ + 0 = ‖gs j‖ ^ 2 from by
        rw [add_zero]; exact real_inner_self_eq_norm_sq (gs j)) using 1
      congr 1
    rw [h_inner_self]

  have h_cs := abs_real_inner_le_norm (gs j) v
  rw [inner_gs_v] at h_cs

  have hcj_abs : (1 : ℝ) ≤ |(c j : ℝ)| := by
    have : (1 : ℤ) ≤ |c j| := Int.one_le_abs hcj_ne
    exact_mod_cast this

  have h_norm_ge : ‖gs j‖ ≤ ‖v‖ := by
    by_cases hgs_zero : ‖gs j‖ = 0
    · rw [hgs_zero]; exact norm_nonneg v
    · have hgs_pos : (0 : ℝ) < ‖gs j‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hgs_zero)


      have h_abs_eq : |(c j : ℝ) * ‖gs j‖ ^ 2| = |(c j : ℝ)| * ‖gs j‖ ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg ‖gs j‖)]
      rw [h_abs_eq] at h_cs
      have h1 : ‖gs j‖ ^ 2 ≤ |(c j : ℝ)| * ‖gs j‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hcj_abs
      have h2 : ‖gs j‖ ^ 2 ≤ ‖gs j‖ * ‖v‖ := le_trans h1 h_cs
      have h3 : ‖gs j‖ * ‖gs j‖ ≤ ‖gs j‖ * ‖v‖ := by rwa [sq] at h2
      exact le_of_mul_le_mul_left h3 hgs_pos

  have h_iInf_le : ⨅ i : Fin n, ‖gs i‖ ≤ ‖gs j‖ :=
    ciInf_le (Finite.bddBelow_range (fun i => ‖gs i‖)) j
  linarith

end LatticeShortestVector

end
