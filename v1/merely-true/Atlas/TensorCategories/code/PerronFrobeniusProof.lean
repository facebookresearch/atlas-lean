/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex

open Finset BigOperators Matrix

set_option maxHeartbeats 800000

namespace PerronFrobenius

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Continuity of the `i`-th component of `M.mulVec` as a function of `(v, t)`. -/
lemma continuous_mulVec_component (M : Matrix ι ι ℝ) (i : ι) :
    Continuous (fun p : (ι → ℝ) × ℝ => M.mulVec p.1 i) := by
  simp only [mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_fst)

omit [DecidableEq ι] [Nonempty ι] in
/-- Each coordinate of a point in the standard simplex is bounded above by `1`. -/
lemma simplex_le_one {v : ι → ℝ} (hv : v ∈ stdSimplex ℝ ι) (i : ι) : v i ≤ 1 :=
  le_trans (single_le_sum (fun k _ => hv.1 k) (mem_univ i)) (le_of_eq hv.2)

omit [DecidableEq ι] [Nonempty ι] in
/-- For a strictly positive matrix `M` and any point in the standard simplex, every
coordinate of `M.mulVec v` is strictly positive. -/
lemma mulVec_pos (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    {v : ι → ℝ} (hv : v ∈ stdSimplex ℝ ι) (i : ι) :
    0 < M.mulVec v i := by
  simp only [mulVec, dotProduct]
  have ⟨j, hj⟩ : ∃ j, 0 < v j := by
    by_contra h; push Not at h
    linarith [hv.2, sum_nonpos (fun j (_ : j ∈ univ) => h j)]
  calc 0 < M i j * v j := mul_pos (hM i j) hj
    _ ≤ ∑ k, M i k * v k :=
        single_le_sum (fun k _ => mul_nonneg (le_of_lt (hM i k)) (hv.1 k)) (mem_univ j)

/-- Collatz-Wielandt set: pairs `(v, t)` with `v` in the standard simplex, `t ≥ 0`, and
`t * v i ≤ (M.mulVec v) i` for all `i`. The Perron-Frobenius eigenvalue is realised as the
supremum of `t` over this set. -/
def CWSet (M : Matrix ι ι ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | p.1 ∈ stdSimplex ℝ ι ∧ 0 ≤ p.2 ∧ ∀ i, p.2 * p.1 i ≤ M.mulVec p.1 i}

omit [DecidableEq ι] [Nonempty ι] in
/-- The Collatz-Wielandt set is closed. -/
lemma cwSet_closed (M : Matrix ι ι ℝ) : IsClosed (CWSet M) := by
  refine IsClosed.inter ((isClosed_stdSimplex ℝ ι).preimage continuous_fst) ?_
  refine IsClosed.inter (isClosed_le continuous_const continuous_snd) ?_
  change IsClosed {p : (ι → ℝ) × ℝ | ∀ i, p.2 * p.1 i ≤ M.mulVec p.1 i}
  rw [show {p : (ι → ℝ) × ℝ | ∀ i, p.2 * p.1 i ≤ M.mulVec p.1 i} =
      ⋂ i, {q : (ι → ℝ) × ℝ | q.2 * q.1 i ≤ M.mulVec q.1 i} from by ext; simp [Set.mem_iInter]]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_snd.mul ((continuous_apply i).comp continuous_fst))
      (continuous_mulVec_component M i)

omit [DecidableEq ι] [Nonempty ι] in
/-- The Collatz-Wielandt set is contained in the compact product of the standard simplex
and `[0, ∑ M i j]`. -/
lemma cwSet_subset_compact (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    CWSet M ⊆ (stdSimplex ℝ ι) ×ˢ (Set.Icc 0 (∑ i : ι, ∑ j : ι, M i j)) := by
  intro ⟨v, t⟩ ⟨hv, ht_nn, hle⟩
  exact ⟨hv, ht_nn,
    calc t = t * ∑ i, v i := by rw [hv.2, mul_one]
      _ = ∑ i, t * v i := mul_sum ..
      _ ≤ ∑ i, M.mulVec v i := sum_le_sum (fun i _ => hle i)
      _ ≤ ∑ i, ∑ j, M i j := by
          simp only [mulVec, dotProduct]
          exact sum_le_sum fun i _ => sum_le_sum fun j _ =>
            mul_le_of_le_one_right (le_of_lt (hM i j)) (simplex_le_one hv j)⟩

omit [DecidableEq ι] [Nonempty ι] in
/-- The Collatz-Wielandt set is compact. -/
lemma cwSet_compact (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    IsCompact (CWSet M) :=
  ((isCompact_stdSimplex ℝ ι).prod isCompact_Icc).of_isClosed_subset
    (cwSet_closed M) (cwSet_subset_compact M hM)

omit [DecidableEq ι] in
/-- The Collatz-Wielandt set is nonempty, witnessed by the uniform distribution paired
with `t = 0`. -/
lemma cwSet_nonempty (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    (CWSet M).Nonempty := by
  set n := Fintype.card ι
  set u : ι → ℝ := fun _ => (n : ℝ)⁻¹
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hu : u ∈ stdSimplex ℝ ι := ⟨fun _ => by positivity,
    by simp only [u, sum_const, card_univ, nsmul_eq_mul]
       exact mul_inv_cancel₀ (ne_of_gt hn)⟩
  exact ⟨⟨u, 0⟩,
    hu,
    le_refl _,
    fun i => by
      show (0 : ℝ) * u i ≤ M.mulVec u i
      rw [zero_mul]
      exact le_of_lt (by
        simp only [mulVec, dotProduct]
        exact sum_pos (fun j _ => mul_pos (hM i j) (by positivity)) univ_nonempty)⟩

/-- Perron-Frobenius existence theorem for strictly positive matrices: there exist a
strictly positive scalar `r` and a strictly positive eigenvector `v` such that
`M.mulVec v = r • v`. The proof maximises the second coordinate over the Collatz-Wielandt
set. -/
noncomputable def perronFrobeniusExistence
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v := by
  have hexist := (cwSet_compact M hM).exists_isMaxOn
    (cwSet_nonempty M hM) continuous_snd.continuousOn
  let p := hexist.choose
  have hp_mem := hexist.choose_spec.1
  have hp_max : IsMaxOn Prod.snd (CWSet M) p := hexist.choose_spec.2
  set v := p.1 with hv_def
  set r := p.2 with hr_def
  obtain ⟨hv_simp, hr_nn, hle⟩ := hp_mem
  have hle' : ∀ i, r * v i ≤ M.mulVec v i := hle

  have heq : M.mulVec v = r • v := by
    by_contra h
    have hex : ∃ i₀, r * v i₀ < M.mulVec v i₀ := by
      by_contra hall; push Not at hall
      exact h (funext fun i => le_antisymm (hall i) (hle' i))
    obtain ⟨i₀, hi₀⟩ := hex

    set w : ι → ℝ := fun i => M.mulVec v i - r * v i
    have hw_nn : ∀ i, 0 ≤ w i := fun i => by simp only [w]; linarith [hle' i]
    have hw_pos : 0 < w i₀ := by simp only [w]; linarith

    set s := ∑ i, M.mulVec v i
    have hs_pos : 0 < s := sum_pos (fun i _ => mulVec_pos M hM hv_simp i) univ_nonempty
    set v' : ι → ℝ := fun i => M.mulVec v i / s
    have hv'_simp : v' ∈ stdSimplex ℝ ι := ⟨
      fun i => div_nonneg (le_of_lt (mulVec_pos M hM hv_simp i)) (le_of_lt hs_pos),
      by simp only [v', ← sum_div]; exact div_self (ne_of_gt hs_pos)⟩

    have hMw_pos : ∀ i, 0 < M.mulVec w i := by
      intro i; simp only [mulVec, dotProduct]
      calc 0 < M i i₀ * w i₀ := mul_pos (hM i i₀) hw_pos
        _ ≤ ∑ k, M i k * w k :=
          single_le_sum (fun k _ => mul_nonneg (le_of_lt (hM i k)) (hw_nn k)) (mem_univ i₀)

    have hstrict : ∀ i, r * v' i < M.mulVec v' i := by
      intro i
      show r * (M.mulVec v i / s) < M.mulVec (fun i => M.mulVec v i / s) i
      have lhs_eq : r * (M.mulVec v i / s) = r * M.mulVec v i / s := by ring
      have rhs_eq : M.mulVec (fun i => M.mulVec v i / s) i =
          M.mulVec (M.mulVec v) i / s := by
        simp only [mulVec, dotProduct, mul_div_assoc']
        rw [sum_div]
      rw [lhs_eq, rhs_eq]
      apply div_lt_div_of_pos_right _ hs_pos
      have decomp : M.mulVec (M.mulVec v) i =
          r * M.mulVec v i + M.mulVec w i := by
        simp only [mulVec, dotProduct, w]; ring_nf
        conv_rhs => rw [mul_sum, ← sum_add_distrib]
        congr 1; ext x; ring
      linarith [hMw_pos i]

    have hgap : ∀ i, 0 < M.mulVec v' i - r * v' i := fun i => by linarith [hstrict i]
    set gap := univ.inf' univ_nonempty (fun i => M.mulVec v' i - r * v' i)
    have hgap_pos : 0 < gap :=
      (Finset.lt_inf'_iff _).mpr (fun i _ => hgap i)
    set δ := gap / 2
    have hδ_pos : 0 < δ := div_pos hgap_pos (by norm_num)
    have hδ_le : ∀ i, (r + δ) * v' i ≤ M.mulVec v' i := by
      intro i
      have h1 : gap ≤ M.mulVec v' i - r * v' i := inf'_le _ (mem_univ i)
      have h2 : δ ≤ gap := div_le_self (le_of_lt hgap_pos) (by norm_num : (1:ℝ) ≤ 2)
      have h3 : v' i ≤ 1 := simplex_le_one hv'_simp i

      nlinarith [hv'_simp.1 i]

    have hmem : (⟨v', r + δ⟩ : (ι → ℝ) × ℝ) ∈ CWSet M :=
      ⟨hv'_simp, by linarith, hδ_le⟩
    have : (r + δ : ℝ) ≤ r := hp_max hmem
    linarith

  have hv_pos : ∀ i, 0 < v i := by
    intro i
    have hMv_pos := mulVec_pos M hM hv_simp i
    have hMv_eq : M.mulVec v i = r * v i := by
      have := congr_fun heq i; simp [Pi.smul_apply, smul_eq_mul] at this; exact this
    rw [hMv_eq] at hMv_pos
    by_contra h; push Not at h
    have hvi0 : v i = 0 := le_antisymm h (hv_simp.1 i)
    rw [hvi0, mul_zero] at hMv_pos; exact lt_irrefl 0 hMv_pos
  have hr_pos : 0 < r := by
    have i₀ := Classical.arbitrary ι
    have hMv_pos := mulVec_pos M hM hv_simp i₀
    have hMv_eq : M.mulVec v i₀ = r * v i₀ := by
      have := congr_fun heq i₀; simp [Pi.smul_apply, smul_eq_mul] at this; exact this
    rw [hMv_eq] at hMv_pos
    rcases (mul_pos_iff.mp hMv_pos) with ⟨hr, _⟩ | ⟨_, hn⟩
    · exact hr
    · linarith [hv_pos i₀]
  exact ⟨r, v, hr_pos, hv_pos, heq⟩

end PerronFrobenius
