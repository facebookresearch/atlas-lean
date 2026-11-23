/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.TotallyUnimodular

open Matrix SimpleGraph Finset

section Helpers

lemma neg_one_pow_mul_mem_signType_range (n : ℕ) (d : ℤ)
    (hd : d ∈ Set.range (SignType.cast : SignType → ℤ)) :
    (-1 : ℤ) ^ n * d ∈ Set.range (SignType.cast : SignType → ℤ) := by
  obtain ⟨s, rfl⟩ := hd
  have hpow : ((-1 : ℤ) ^ n = 1) ∨ ((-1 : ℤ) ^ n = -1) := by
    induction n with
    | zero => left; simp
    | succ k ih => rcases ih with h | h <;> [right; left] <;> simp [pow_succ, h]
  rcases hpow with h | h <;> rw [h] <;> fin_cases s <;>
    simp only [SignType.cast, mul_neg, mul_one, mul_zero, neg_neg]
  all_goals first
  | exact ⟨SignType.zero, rfl⟩
  | exact ⟨SignType.pos, rfl⟩
  | exact ⟨SignType.neg, rfl⟩

lemma Matrix.det_eq_zero_of_row_combination {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ)
    (c : Fin k → ℤ) (hc : c ≠ 0) (hsum : ∀ j, ∑ i, c i * M i j = 0) :
    M.det = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  rw [linearIndependent_iff']
  push_neg
  refine ⟨Finset.univ, c, ?_, ?_⟩
  · ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hsum j
  · simp only [Function.ne_iff] at hc
    obtain ⟨i, hi⟩ := hc
    exact ⟨i, Finset.mem_univ i, hi⟩

lemma Sym2.eq_mk_of_mem_of_mem {V : Type*} {a b : V} {e : Sym2 V}
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) : e = s(a, b) := by
  induction e using Sym2.ind with
  | h x y =>
    rcases Sym2.mem_iff.mp ha with rfl | rfl <;>
      rcases Sym2.mem_iff.mp hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hab.symm

end Helpers

section BipartiteTU

theorem SimpleGraph.incMatrix_isTotallyUnimodular_of_isBipartite
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsBipartite) :
    (incMatrix ℤ G).IsTotallyUnimodular := by
  obtain ⟨c⟩ := hG
  intro k f g hf hg
  induction k with
  | zero => simp [det_isEmpty]; exact ⟨1, rfl⟩
  | succ n ih =>
    set M := (incMatrix ℤ G).submatrix f g with hM_def

    have hM01 : ∀ i j, M i j = 0 ∨ M i j = 1 := by
      intro i j; simp only [M, submatrix_apply]
      rcases em (g j ∈ G.incidenceSet (f i)) with h | h
      · right; rwa [incMatrix_apply_eq_one_iff]
      · left; rwa [incMatrix_apply_eq_zero_iff]

    by_cases hcol_zero : ∃ j : Fin (n + 1), ∀ i, M i j = 0
    · obtain ⟨j, hj⟩ := hcol_zero
      rw [show M.det = 0 from det_eq_zero_of_column_eq_zero j hj]
      exact ⟨0, by simp⟩
    · push_neg at hcol_zero

      by_cases hcol_one : ∃ j : Fin (n + 1), ∃! i, M i j ≠ 0
      · obtain ⟨j, i, hi_ne, hi_uniq⟩ := hcol_one
        have hi1 : M i j = 1 := (hM01 i j).resolve_left hi_ne

        have hdet : M.det = (-1) ^ ((↑i : ℕ) + (↑j : ℕ)) *
            (M.submatrix i.succAbove j.succAbove).det := by
          rw [det_succ_column M j]
          conv_rhs => rw [show (-1 : ℤ) ^ ((↑i : ℕ) + (↑j : ℕ)) *
            (M.submatrix i.succAbove j.succAbove).det =
            (-1) ^ ((↑i : ℕ) + (↑j : ℕ)) * M i j *
            (M.submatrix i.succAbove j.succAbove).det by rw [hi1]; ring]
          apply Finset.sum_eq_single i
          · intro b _ hbi
            simp [show M b j = 0 from by by_contra hb; exact hbi (hi_uniq b hb)]
          · intro hi_mem; exact absurd (Finset.mem_univ i) hi_mem

        have hminor : M.submatrix i.succAbove j.succAbove =
            (incMatrix ℤ G).submatrix (f ∘ i.succAbove) (g ∘ j.succAbove) := by
          ext a b; simp [M, submatrix_apply]
        rw [hdet, hminor]
        exact neg_one_pow_mul_mem_signType_range _ _
          (ih (f ∘ i.succAbove) (g ∘ j.succAbove)
            (hf.comp Fin.succAbove_right_injective)
            (hg.comp Fin.succAbove_right_injective))
      ·
        push_neg at hcol_one

        set w : Fin (n + 1) → ℤ := fun i => if (c (f i) : Fin 2) = 0 then 1 else -1
        have hw_ne : w ≠ 0 := by
          intro heq; have h0 : w 0 = 0 := congr_fun heq 0
          simp only [w] at h0; split_ifs at h0 <;> omega
        suffices hsum : ∀ j, ∑ i, w i * M i j = 0 by
          rw [show M.det = 0 from
            Matrix.det_eq_zero_of_row_combination M w hw_ne hsum]
          exact ⟨0, by simp⟩

        intro j

        obtain ⟨i₁, hi₁_ne⟩ := hcol_zero j
        have hi₁_eq : M i₁ j = 1 := (hM01 i₁ j).resolve_left hi₁_ne

        have ⟨i₂, hi₂_ne, hi₂_neq⟩ : ∃ i₂, M i₂ j ≠ 0 ∧ i₂ ≠ i₁ := by
          by_contra hall; push_neg at hall
          exact hcol_one j ⟨i₁, hi₁_ne, fun y hy => hall y hy⟩
        have hi₂_eq : M i₂ j = 1 := (hM01 i₂ j).resolve_left hi₂_ne

        have hfi₁_info : f i₁ ∈ (g j : Sym2 V) ∧ g j ∈ G.edgeSet := by
          have h := hi₁_eq
          simp only [M, submatrix_apply, incMatrix_apply_eq_one_iff] at h
          exact ⟨h.2, h.1⟩
        have hfi₂_mem : f i₂ ∈ (g j : Sym2 V) := by
          have h := hi₂_eq
          simp only [M, submatrix_apply, incMatrix_apply_eq_one_iff] at h
          exact h.2
        have hfi_ne : f i₁ ≠ f i₂ := fun heq => hi₂_neq.symm (hf heq)

        have hgj_eq : g j = s(f i₁, f i₂) :=
          Sym2.eq_mk_of_mem_of_mem hfi₁_info.1 hfi₂_mem hfi_ne

        have hadj : G.Adj (f i₁) (f i₂) := by
          rw [← SimpleGraph.mem_edgeSet, ← hgj_eq]; exact hfi₁_info.2

        have hcolor_ne : c (f i₁) ≠ c (f i₂) := c.valid hadj

        have h_only_two : ∀ i, M i j ≠ 0 → i = i₁ ∨ i = i₂ := by
          intro i hi
          have hi_eq : M i j = 1 := (hM01 i j).resolve_left hi
          have hfi_mem : f i ∈ (g j : Sym2 V) := by
            have h := hi_eq
            simp only [M, submatrix_apply, incMatrix_apply_eq_one_iff] at h
            exact h.2
          rw [hgj_eq] at hfi_mem
          rcases Sym2.mem_iff.mp hfi_mem with heq | heq
          · left; exact hf heq
          · right; exact hf heq

        have h_split : ∀ i, w i * M i j = if i = i₁ ∨ i = i₂ then w i else 0 := by
          intro i
          rcases hM01 i j with h | h
          · simp only [h, mul_zero]
            split_ifs with hif
            · rcases hif with rfl | rfl <;> simp_all
            · rfl
          · have hi := h_only_two i (by rw [h]; exact one_ne_zero)
            simp [h, hi]
        simp_rw [h_split]
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, add_zero]
        have hfilter : Finset.univ.filter (fun i => i = i₁ ∨ i = i₂) = {i₁, i₂} := by
          ext i; simp
        rw [hfilter, Finset.sum_pair hi₂_neq.symm]

        simp only [w]
        omega

theorem SimpleGraph.constraintMatrix_isTotallyUnimodular_of_isBipartite
    {V : Type*} [DecidableEq V] [Fintype V] [DecidableEq (Sym2 V)]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsBipartite) :
    ((incMatrix ℤ G).fromRows (-1 : Matrix (Sym2 V) (Sym2 V) ℤ)).IsTotallyUnimodular := by
  apply Matrix.IsTotallyUnimodular.fromRows_unitlike
  · exact incMatrix_isTotallyUnimodular_of_isBipartite G hG
  · intro _ i
    refine ⟨i, SignType.neg, ?_⟩
    ext j
    simp only [Matrix.neg_apply, Matrix.one_apply, Pi.single_apply, SignType.cast]
    split_ifs <;> simp_all

end BipartiteTU
