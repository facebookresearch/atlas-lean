/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff
import Atlas.AlgebraicCombinatorics.code.HasseWalks
import Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Atlas.AlgebraicCombinatorics.code.WalkCountBridge
import Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.Young.YoungDiagram

set_option autoImplicit false

open scoped Nat

noncomputable def HasseWalkFormula.numSYT (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card { chain : Fin (lam.card + 1) → YoungDiagram //
    chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    chain ⟨lam.card, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin lam.card,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
      chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

noncomputable def HasseWalkFormula.hasseWalkCount (ell : ℕ) (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card { walk : Fin (ell + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨ell, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin ell,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ }

noncomputable def HasseWalkFormula.upWalkCount (n : ℕ) (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card { walk : Fin (n + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨n, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin n,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

lemma HasseWalkFormula.upWalk_card_eq {n : ℕ}
    (walk : Fin (n + 1) → YoungDiagram)
    (hstart : walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hstep : ∀ j : Fin n,
      walk ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ ⋖
        walk ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (k : ℕ) (hk : k ≤ n) :
    (walk ⟨k, Nat.lt_succ_of_le hk⟩).card = k := by
  induction k with
  | zero =>
    simp only [hstart, YoungDiagram.card]
    simp
  | succ m ih =>
    have hm_le : m ≤ n := Nat.le_of_succ_le hk
    have hm_lt : m < n := Nat.lt_of_succ_le hk
    have h_covby := hstep ⟨m, hm_lt⟩
    have h_card := HasseWalks.card_covBy_succ h_covby
    rw [ih hm_le] at h_card
    exact h_card

theorem HasseWalkFormula.upWalkCount_eq_zero_of_ne (i : ℕ) (lam : YoungDiagram) (h : i ≠ lam.card) :
    HasseWalkFormula.upWalkCount i lam = 0 := by
  unfold HasseWalkFormula.upWalkCount
  have : IsEmpty { walk : Fin (i + 1) → YoungDiagram //
      walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
      walk ⟨i, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
      ∀ j : Fin i,
        walk ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ ⋖
          walk ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ } := by
    constructor
    intro ⟨walk, hstart, hend, hstep⟩
    exact h (by rw [← hend, HasseWalkFormula.upWalk_card_eq walk hstart hstep i le_rfl])
  exact Nat.card_of_isEmpty

theorem HasseWalkFormula.upWalkCount_eq_numSYT (lam : YoungDiagram) :
    (HasseWalkFormula.upWalkCount lam.card lam : ℚ) =
      (HasseWalkFormula.numSYT lam : ℚ) := by
  unfold HasseWalkFormula.upWalkCount HasseWalkFormula.numSYT
  rfl

def HasseWalkFormula.HasseWalkType (n : ℕ) (lam : YoungDiagram) :=
  { walk : Fin (n + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨n, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin n,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ }

lemma HasseWalkFormula.hasseWalkCount_eq_card' (n : ℕ) (lam : YoungDiagram) :
    HasseWalkFormula.hasseWalkCount n lam =
      Nat.card (HasseWalkFormula.HasseWalkType n lam) := by
  unfold HasseWalkFormula.hasseWalkCount HasseWalkFormula.HasseWalkType
  simp only [Nat.card]

lemma HasseWalkFormula.hasseWalk_card_le {m : ℕ}
    (walk : Fin (m + 1) → YoungDiagram)
    (hstart : walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hstep : ∀ i : Fin m,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (k : ℕ) (hk : k ≤ m) :
    (walk ⟨k, Nat.lt_succ_of_le hk⟩).card ≤ k := by
  induction k with
  | zero =>
    simp only [hstart, YoungDiagram.card]
    simp
  | succ p ih =>
    have hp_le : p ≤ m := Nat.le_of_succ_le hk
    have hp_lt : p < m := Nat.lt_of_succ_le hk
    have hp_eq : (⟨p, Nat.lt_succ_of_lt hp_lt⟩ : Fin (m + 1)) =
        ⟨p, Nat.lt_succ_of_le hp_le⟩ := rfl
    have hp1_eq : (⟨p + 1, Nat.succ_lt_succ hp_lt⟩ : Fin (m + 1)) =
        ⟨p + 1, Nat.lt_succ_of_le hk⟩ := rfl
    rcases hstep ⟨p, hp_lt⟩ with hup | hdown
    · have h_card := HasseWalks.card_covBy_succ hup
      rw [hp_eq, hp1_eq] at h_card
      have := ih hp_le
      omega
    · have h_card := HasseWalks.card_covBy_succ hdown
      rw [hp_eq, hp1_eq] at h_card
      have := ih hp_le
      omega

lemma HasseWalkFormula.yd_cell_bounded (yd : YoungDiagram) (i j : ℕ)
    (h : (i, j) ∈ yd.cells) : i < yd.card ∧ j < yd.card := by
  constructor
  · have hmem : ∀ i' : ℕ, i' ≤ i → (i', 0) ∈ yd.cells :=
      fun i' hi' => yd.isLowerSet (Prod.mk_le_mk.mpr ⟨hi', Nat.zero_le _⟩) h
    have hsub : Finset.image (fun i' => (i', 0)) (Finset.range (i + 1)) ⊆ yd.cells := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i', hi', rfl⟩ := hx
      exact hmem i' (by rw [Finset.mem_range] at hi'; omega)
    have hc : (Finset.image (fun i' => (i', 0)) (Finset.range (i + 1))).card = i + 1 := by
      rw [Finset.card_image_of_injective _ (by intro a b hab; exact (Prod.mk.inj hab).1)]
      exact Finset.card_range _
    have := Finset.card_le_card hsub; simp only [YoungDiagram.card]; omega
  · have hmem : ∀ j' : ℕ, j' ≤ j → (0, j') ∈ yd.cells :=
      fun j' hj' => yd.isLowerSet (Prod.mk_le_mk.mpr ⟨Nat.zero_le _, hj'⟩) h
    have hsub : Finset.image (fun j' => (0, j')) (Finset.range (j + 1)) ⊆ yd.cells := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨j', hj', rfl⟩ := hx
      exact hmem j' (by rw [Finset.mem_range] at hj'; omega)
    have hc : (Finset.image (fun j' => (0, j')) (Finset.range (j + 1))).card = j + 1 := by
      rw [Finset.card_image_of_injective _ (by intro a b hab; exact (Prod.mk.inj hab).2)]
      exact Finset.card_range _
    have := Finset.card_le_card hsub; simp only [YoungDiagram.card]; omega

lemma HasseWalkFormula.yd_cells_sub_grid {yd : YoungDiagram} {n : ℕ} (hn : yd.card ≤ n) :
    yd.cells ⊆ Finset.range n ×ˢ Finset.range n := by
  intro ⟨i, j⟩ hij
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨Nat.lt_of_lt_of_le (yd_cell_bounded yd i j hij).1 hn,
         Nat.lt_of_lt_of_le (yd_cell_bounded yd i j hij).2 hn⟩

lemma HasseWalkFormula.hasseWalkType_cells_bounded {m : ℕ}
    (w : Fin (m + 1) → YoungDiagram)
    (h0 : w ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hs : ∀ i : Fin m,
      w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (k : Fin (m + 1)) :
    (w k).cells ⊆ Finset.range m ×ˢ Finset.range m := by
  obtain ⟨k, hk⟩ := k
  apply yd_cells_sub_grid
  have := hasseWalk_card_le w h0 hs k (by omega)
  omega

instance HasseWalkFormula.hasseWalkType_finite (m : ℕ) (lam : YoungDiagram) :
    Finite (HasseWalkFormula.HasseWalkType m lam) := by
  let grid := Finset.range m ×ˢ Finset.range m
  apply Finite.of_injective
    (fun ⟨w, h0, _he, hs⟩ (i : Fin (m + 1)) =>
      (⟨(w ⟨i.val, i.isLt⟩).cells,
        Finset.mem_powerset.mpr
          (hasseWalkType_cells_bounded w h0 hs ⟨i.val, i.isLt⟩)⟩ :
        ↑(grid.powerset)))
  intro ⟨w1, h01, he1, hs1⟩ ⟨w2, h02, he2, hs2⟩ heq
  apply Subtype.ext; funext ⟨i, hi⟩
  have := congr_fun heq ⟨i, hi⟩
  simp at this
  exact YoungDiagram.ext_iff.mpr this

lemma covBy_of_mem_coversUp' {μ ν : YoungDiagram} (h : ν ∈ μ.coversUp) :
    μ ⋖ ν := by
  classical
  unfold YoungDiagram.coversUp at h
  rw [Finset.mem_image] at h
  obtain ⟨i, hi_mem, hν_eq⟩ := h
  have hadd := YoungDiagram.mem_addableRows_of_mem μ hi_mem
  simp only [dif_pos hadd] at hν_eq; subst hν_eq
  constructor
  · show μ.cells ⊂ (μ.addCell i hadd).cells
    rw [YoungDiagram.addCell_cells]; constructor
    · exact Finset.subset_union_left
    · intro hsub
      have := hsub (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at this; omega
  · intro z hz1 hz2
    have hcard_add : (μ.addCell i hadd).cells.card = μ.cells.card + 1 := by
      rw [YoungDiagram.addCell_cells, Finset.card_union_of_disjoint]
      · simp
      · rw [Finset.disjoint_singleton_right, YoungDiagram.mem_cells]
        intro hmem; rw [YoungDiagram.mem_iff_lt_rowLen] at hmem; omega
    have := Finset.card_lt_card hz1; have := Finset.card_lt_card hz2; omega

lemma mem_coversUp_of_covBy' {μ ν : YoungDiagram} (hcov : μ ⋖ ν) :
    ν ∈ μ.coversUp := by
  classical
  have hsub : μ.cells ⊆ ν.cells := hcov.lt.le
  have hcard := HasseWalks.card_covBy_succ hcov
  have hsdiff_card : (ν.cells \ μ.cells).card = 1 := by
    have h2 := Finset.card_sdiff_add_card_eq_card hsub
    simp only [YoungDiagram.card] at hcard; omega
  obtain ⟨⟨r, c⟩, hrc⟩ := Finset.card_eq_one.mp hsdiff_card
  have hrc_in : (r, c) ∈ ν.cells \ μ.cells := hrc ▸ Finset.mem_singleton_self _
  have hr_in_ν : (r, c) ∈ ν.cells := (Finset.mem_sdiff.mp hrc_in).1
  have hr_not_μ : (r, c) ∉ μ.cells := (Finset.mem_sdiff.mp hrc_in).2
  have hc_eq : c = μ.rowLen r := by
    apply le_antisymm
    · by_contra h; push Not at h
      have : (r, μ.rowLen r) ∉ μ.cells := by
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]; omega
      have : (r, μ.rowLen r) ∈ ν.cells :=
        ν.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, by omega⟩) hr_in_ν
      have : (r, μ.rowLen r) ∈ ν.cells \ μ.cells :=
        Finset.mem_sdiff.mpr ⟨‹(r, μ.rowLen r) ∈ ν.cells›, ‹(r, μ.rowLen r) ∉ μ.cells›⟩
      rw [hrc, Finset.mem_singleton, Prod.ext_iff] at this; omega
    · by_contra h; push Not at h
      exact hr_not_μ (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
  subst hc_eq
  have hadd : r = 0 ∨ μ.rowLen (r - 1) > μ.rowLen r := by
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    · right
      have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      have h1 : (r - 1, μ.rowLen r) ∈ ν.cells :=
        ν.isLowerSet (Prod.mk_le_mk.mpr ⟨by omega, le_refl _⟩) hr_in_ν
      have h2 : (r - 1, μ.rowLen r) ∈ μ.cells := by
        by_contra hn
        have := Finset.mem_sdiff.mpr ⟨h1, hn⟩
        rw [hrc, Finset.mem_singleton, Prod.ext_iff] at this; omega
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at h2; exact h2
  have hν_eq : ν = μ.addCell r hadd := by
    rw [YoungDiagram.ext_iff]; rw [YoungDiagram.addCell_cells]
    ext ⟨a, b⟩; constructor
    · intro hab
      by_cases hmem : (a, b) ∈ μ.cells
      · exact Finset.mem_union_left _ hmem
      · have := Finset.mem_sdiff.mpr ⟨hab, hmem⟩
        rw [hrc, Finset.mem_singleton, Prod.ext_iff] at this
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (Prod.ext this.1 this.2))
    · intro hab
      rcases Finset.mem_union.mp hab with h | h
      · exact hsub h
      · rw [Finset.mem_singleton] at h; rw [h]; exact hr_in_ν
  rw [hν_eq]; unfold YoungDiagram.coversUp; rw [Finset.mem_image]
  have hr_addable : r ∈ μ.addableRows := by
    rw [YoungDiagram.addableRows, Finset.mem_filter]; constructor
    · rw [Finset.mem_range]
      by_cases hrl : μ.rowLen r = 0
      · rcases hadd with rfl | h
        · omega
        · have hmem : (r - 1, 0) ∈ μ :=
            YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
          have := YoungDiagram.mem_iff_lt_colLen.mp hmem; omega
      · have hmem : (r, 0) ∈ μ :=
          YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
        have := YoungDiagram.mem_iff_lt_colLen.mp hmem; omega
    · exact hadd
  exact ⟨r, hr_addable, by simp [dif_pos hadd]⟩

lemma covBy_iff_mem_coversUp' (μ ν : YoungDiagram) :
    μ ⋖ ν ↔ ν ∈ μ.coversUp :=
  ⟨mem_coversUp_of_covBy', covBy_of_mem_coversUp'⟩

lemma covBy_of_mem_coversDown' {μ ν : YoungDiagram} (h : μ ∈ ν.coversDown) :
    μ ⋖ ν := by
  classical
  unfold YoungDiagram.coversDown at h
  rw [Finset.mem_image] at h
  obtain ⟨i, hi_mem, hμ_eq⟩ := h
  have hrem := YoungDiagram.mem_removableRows_of_mem ν hi_mem
  simp only [dif_pos hrem] at hμ_eq; subst hμ_eq
  have := YoungDiagram.self_mem_coversUp_removeCell ν i hrem
  exact covBy_of_mem_coversUp' this

lemma mem_coversDown_of_covBy' {μ ν : YoungDiagram} (hcov : μ ⋖ ν) :
    μ ∈ ν.coversDown := by
  classical
  have hup := mem_coversUp_of_covBy' hcov
  unfold YoungDiagram.coversUp at hup
  rw [Finset.mem_image] at hup
  obtain ⟨r, hr_mem, hν_eq⟩ := hup
  have hadd := YoungDiagram.mem_addableRows_of_mem μ hr_mem
  simp only [dif_pos hadd] at hν_eq
  subst hν_eq
  exact YoungDiagram.self_mem_coversDown_addCell μ r hadd

lemma covBy_iff_mem_coversDown' (μ ν : YoungDiagram) :
    μ ⋖ ν ↔ μ ∈ ν.coversDown :=
  ⟨mem_coversDown_of_covBy', covBy_of_mem_coversDown'⟩


open Classical in
theorem HasseWalkFormula.hasseWalkCount_succ_eq_finset_sum_DU
    (n : ℕ) (lam : YoungDiagram)
    (ih : ∀ μ, (HasseWalkFormula.hasseWalkCount n μ : ℤ) =
      (((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ n)
        WalkCountFormula.emptyBasis) μ) :
    (HasseWalkFormula.hasseWalkCount (n + 1) lam : ℤ) =
      ((WalkCountFormula.liftD + WalkCountFormula.liftU)
        (((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ n)
          WalkCountFormula.emptyBasis)) lam := by
  set f := ((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ n)
    WalkCountFormula.emptyBasis with hf_def
  rw [LinearMap.add_apply]
  simp only [WalkCountFormula.liftD, WalkCountFormula.liftU, Finsupp.lsum_apply]
  simp only [Finsupp.sum]
  rw [Finsupp.add_apply, Finset.sum_apply', Finset.sum_apply']
  simp only [LinearMap.smulRight_apply, LinearMap.id_apply,
    Finsupp.smul_apply, smul_eq_mul,
    WalkCountFormula.loweringOp_apply, WalkCountFormula.raisingOp_apply,
    mul_ite, mul_one, mul_zero]
  simp_rw [← ih]
  simp_rw [← covBy_iff_mem_coversDown' lam,
            ← covBy_iff_mem_coversUp']


  rw [← Finset.sum_add_distrib]


  conv_rhs => arg 2; ext x
              rw [show (if lam ⋖ x then (hasseWalkCount n x : ℤ) else 0) +
                       (if x ⋖ lam then (hasseWalkCount n x : ℤ) else 0) =
                  if (lam ⋖ x ∨ x ⋖ lam) then (hasseWalkCount n x : ℤ) else 0
              from by
                by_cases h1 : lam ⋖ x <;> by_cases h2 : x ⋖ lam <;> simp_all
                exact absurd (h1.lt.trans h2.lt) (lt_irrefl _)]
  rw [← Finset.sum_filter]
  set S := f.support.filter (fun x => lam ⋖ x ∨ x ⋖ lam) with hS_def

  rw [hasseWalkCount_eq_card']
  rw [← Nat.cast_sum, ← hasseWalkCount_eq_card']
  norm_cast

  have hmem_S : ∀ μ : YoungDiagram,
      (lam ⋖ μ ∨ μ ⋖ lam) → hasseWalkCount n μ ≠ 0 → μ ∈ S := by
    intro μ hcov hne
    rw [hS_def, Finset.mem_filter]
    refine ⟨Finsupp.mem_support_iff.mpr (fun hf0 => ?_), hcov⟩
    exact hne (Nat.cast_eq_zero.mp (by rw [ih]; exact hf0))
  rw [hasseWalkCount_eq_card']
  simp_rw [hasseWalkCount_eq_card']

  let fwd : HasseWalkType (n + 1) lam →
      (μ : ↑S) × HasseWalkType n μ := fun ⟨w, h0, he, hs⟩ =>
    let μ := w ⟨n, by omega⟩
    have hcov : lam ⋖ μ ∨ μ ⋖ lam := by
      have h1 := hs ⟨n, by omega⟩; simp only [μ]; rw [he] at h1; exact h1.symm
    let g : Fin (n + 1) → YoungDiagram := fun i => w ⟨i.val, by omega⟩
    have hg0 : g ⟨0, Nat.zero_lt_succ _⟩ = ⊥ := h0
    have hgn : g ⟨n, Nat.lt_succ_of_le le_rfl⟩ = μ := rfl
    have hgs : ∀ i : Fin n, g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
          g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
        g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
          g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
      intro ⟨i, hi⟩
      have := hs ⟨i, by omega⟩
      convert this using 2
    have hne : hasseWalkCount n μ ≠ 0 := by
      rw [hasseWalkCount_eq_card', Nat.card_ne_zero]
      exact ⟨⟨⟨g, hg0, hgn, hgs⟩⟩, inferInstance⟩
    (⟨⟨μ, hmem_S μ hcov hne⟩, ⟨g, hg0, hgn, hgs⟩⟩)
  let bwd : ((μ : ↑S) × HasseWalkType n μ) →
      HasseWalkType (n + 1) lam := fun ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩ =>
    have hcov : lam ⋖ μ ∨ μ ⋖ lam := by
      rw [hS_def, Finset.mem_filter] at hμ; exact hμ.2
    let w : Fin (n + 2) → YoungDiagram := fun i =>
      if h : i.val ≤ n then g ⟨i.val, by omega⟩ else lam
    have hw0 : w ⟨0, Nat.zero_lt_succ _⟩ = ⊥ := by
      simp only [w, show (0 : ℕ) ≤ n from Nat.zero_le n, dite_true]; exact hg0
    have hwn : w ⟨n + 1, Nat.lt_succ_of_le le_rfl⟩ = lam := by
      simp only [w, show ¬(n + 1 ≤ n) from by omega, dite_false]
    have hws : ∀ i : Fin (n + 1),
        w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
          w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
        w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
          w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
      intro ⟨i, hi⟩; simp only [w]
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
      · subst heq
        simp only [show i ≤ i from le_rfl, dite_true,
          show ¬(i + 1 ≤ i) from by omega, dite_false]
        rw [hgn]; exact hcov.symm
      · simp only [show i ≤ n from by omega, dite_true,
          show i + 1 ≤ n from by omega, dite_true]
        exact hgs ⟨i, by omega⟩
    ⟨w, hw0, hwn, hws⟩
  have hfwd_bwd : ∀ x, fwd (bwd x) = x := by
    intro ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩
    show fwd (bwd ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩) = ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩
    simp only [fwd, bwd]
    have h1 : (fun (i : Fin (n + 1)) =>
        (if h : (i : ℕ) ≤ n then g ⟨i, by omega⟩ else lam)) = g :=
      funext fun ⟨i, hi⟩ => dif_pos (by omega)
    have h2 : (if h : n ≤ n then g ⟨n, by omega⟩ else lam) = μ := by
      rw [dif_pos le_rfl]; exact hgn
    exact Sigma.ext (Subtype.ext h2) (by subst h2; exact heq_of_eq (Subtype.ext h1))
  have hbwd_fwd : ∀ x, bwd (fwd x) = x := by
    intro ⟨w, h0, he, hs⟩
    simp only [fwd, bwd]
    apply Subtype.ext; funext ⟨i, hi⟩
    show (if h : i ≤ n then w ⟨i, _⟩ else lam) = w ⟨i, hi⟩
    split_ifs with h
    · rfl
    · have hi_eq : i = n + 1 := by omega
      subst hi_eq; exact he.symm
  have equiv : HasseWalkType (n + 1) lam ≃
      ((μ : ↑S) × HasseWalkType n μ) :=
    { toFun := fwd, invFun := bwd, left_inv := hbwd_fwd, right_inv := hfwd_bwd }
  rw [Nat.card_congr equiv, Nat.card_sigma]
  exact Finset.sum_coe_sort S (fun μ => Nat.card (HasseWalkType n μ))

theorem HasseWalkFormula.hasseWalkCount_eq_DplusU_pow_apply
    (ell : ℕ) (lam : YoungDiagram) :
    (HasseWalkFormula.hasseWalkCount ell lam : ℤ) =
      (((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ ell)
        WalkCountFormula.emptyBasis) lam := by
  induction ell generalizing lam with
  | zero =>
    classical
    simp only [pow_zero]
    show (HasseWalkFormula.hasseWalkCount 0 lam : ℤ) = WalkCountFormula.emptyBasis lam
    simp only [WalkCountFormula.emptyBasis, Finsupp.single_apply]
    simp only [HasseWalkFormula.hasseWalkCount]
    split_ifs with h
    · subst h
      norm_cast
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun ⟨wa, ha, _, _⟩ ⟨wb, hb, _, _⟩ => Subtype.ext (funext fun ⟨k, hk⟩ => by
        interval_cases k; exact ha.trans hb.symm)⟩,
        ⟨⟨fun _ => ⊥, rfl, rfl, fun i => i.elim0⟩⟩⟩
    · norm_cast
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨_, hstart, hend, _⟩ => h (hstart.symm.trans hend)⟩
  | succ n ih =>
    simp only [pow_succ']
    show (HasseWalkFormula.hasseWalkCount (n + 1) lam : ℤ) =
      ((WalkCountFormula.liftD + WalkCountFormula.liftU)
        (((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ n)
          WalkCountFormula.emptyBasis)) lam
    exact HasseWalkFormula.hasseWalkCount_succ_eq_finset_sum_DU n lam ih


lemma YoungDiagram.covBy_of_mem_coversUp {μ ν : YoungDiagram} (h : ν ∈ μ.coversUp) :
    μ ⋖ ν := by
  classical
  unfold YoungDiagram.coversUp at h
  rw [Finset.mem_image] at h
  obtain ⟨i, hi_mem, hν_eq⟩ := h
  have hadd := YoungDiagram.mem_addableRows_of_mem μ hi_mem
  simp only [dif_pos hadd] at hν_eq; subst hν_eq
  constructor
  · show μ.cells ⊂ (μ.addCell i hadd).cells
    rw [YoungDiagram.addCell_cells]; constructor
    · exact Finset.subset_union_left
    · intro hsub
      have := hsub (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at this; omega
  · intro z hz1 hz2
    have hcard_add : (μ.addCell i hadd).cells.card = μ.cells.card + 1 := by
      rw [YoungDiagram.addCell_cells, Finset.card_union_of_disjoint]
      · simp
      · rw [Finset.disjoint_singleton_right, YoungDiagram.mem_cells]
        intro hmem; rw [YoungDiagram.mem_iff_lt_rowLen] at hmem; omega
    have := Finset.card_lt_card hz1; have := Finset.card_lt_card hz2; omega

lemma YoungDiagram.mem_coversUp_of_covBy {μ ν : YoungDiagram} (hcov : μ ⋖ ν) :
    ν ∈ μ.coversUp := by
  classical
  have hsub : μ.cells ⊆ ν.cells := hcov.lt.le
  have hcard := HasseWalks.card_covBy_succ hcov
  have hsdiff_card : (ν.cells \ μ.cells).card = 1 := by
    have h2 := Finset.card_sdiff_add_card_eq_card hsub
    simp only [YoungDiagram.card] at hcard; omega
  obtain ⟨⟨r, c⟩, hrc⟩ := Finset.card_eq_one.mp hsdiff_card
  have hrc_in : (r, c) ∈ ν.cells \ μ.cells := hrc ▸ Finset.mem_singleton_self _
  have hr_in_ν : (r, c) ∈ ν.cells := (Finset.mem_sdiff.mp hrc_in).1
  have hr_not_μ : (r, c) ∉ μ.cells := (Finset.mem_sdiff.mp hrc_in).2
  have hc_eq : c = μ.rowLen r := by
    apply le_antisymm
    · by_contra h; push Not at h
      have : (r, μ.rowLen r) ∉ μ.cells := by
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]; omega
      have : (r, μ.rowLen r) ∈ ν.cells :=
        ν.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, by omega⟩) hr_in_ν
      have : (r, μ.rowLen r) ∈ ν.cells \ μ.cells :=
        Finset.mem_sdiff.mpr ⟨‹(r, μ.rowLen r) ∈ ν.cells›, ‹(r, μ.rowLen r) ∉ μ.cells›⟩
      rw [hrc, Finset.mem_singleton, Prod.ext_iff] at this; omega
    · by_contra h; push Not at h
      exact hr_not_μ (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
  subst hc_eq
  have hadd : r = 0 ∨ μ.rowLen (r - 1) > μ.rowLen r := by
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    · right
      have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      have h1 : (r - 1, μ.rowLen r) ∈ ν.cells :=
        ν.isLowerSet (Prod.mk_le_mk.mpr ⟨by omega, le_refl _⟩) hr_in_ν
      have h2 : (r - 1, μ.rowLen r) ∈ μ.cells := by
        by_contra hn
        have := Finset.mem_sdiff.mpr ⟨h1, hn⟩
        rw [hrc, Finset.mem_singleton, Prod.ext_iff] at this; omega
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at h2; exact h2
  have hν_eq : ν = μ.addCell r hadd := by
    rw [YoungDiagram.ext_iff]; rw [YoungDiagram.addCell_cells]
    ext ⟨a, b⟩; constructor
    · intro hab
      by_cases hmem : (a, b) ∈ μ.cells
      · exact Finset.mem_union_left _ hmem
      · have := Finset.mem_sdiff.mpr ⟨hab, hmem⟩
        rw [hrc, Finset.mem_singleton, Prod.ext_iff] at this
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (Prod.ext this.1 this.2))
    · intro hab
      rcases Finset.mem_union.mp hab with h | h
      · exact hsub h
      · rw [Finset.mem_singleton] at h; rw [h]; exact hr_in_ν
  rw [hν_eq]; unfold YoungDiagram.coversUp; rw [Finset.mem_image]
  have hr_addable : r ∈ μ.addableRows := by
    rw [YoungDiagram.addableRows, Finset.mem_filter]; constructor
    · rw [Finset.mem_range]
      by_cases hrl : μ.rowLen r = 0
      · rcases hadd with rfl | h
        · omega
        · have hmem : (r - 1, 0) ∈ μ :=
            YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
          have := YoungDiagram.mem_iff_lt_colLen.mp hmem; omega
      · have hmem : (r, 0) ∈ μ :=
          YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
        have := YoungDiagram.mem_iff_lt_colLen.mp hmem; omega
    · exact hadd
  exact ⟨r, hr_addable, by simp [dif_pos hadd]⟩

lemma YoungDiagram.covBy_iff_mem_coversUp (μ ν : YoungDiagram) :
    μ ⋖ ν ↔ ν ∈ μ.coversUp :=
  ⟨YoungDiagram.mem_coversUp_of_covBy, YoungDiagram.covBy_of_mem_coversUp⟩

lemma YoungDiagram.covBy_of_mem_coversDown {μ ν : YoungDiagram} (h : μ ∈ ν.coversDown) :
    μ ⋖ ν := by
  classical
  unfold YoungDiagram.coversDown at h
  rw [Finset.mem_image] at h
  obtain ⟨i, hi_mem, hμ_eq⟩ := h
  have hrem := YoungDiagram.mem_removableRows_of_mem ν hi_mem
  simp only [dif_pos hrem] at hμ_eq; subst hμ_eq
  have := YoungDiagram.self_mem_coversUp_removeCell ν i hrem
  exact YoungDiagram.covBy_of_mem_coversUp this

lemma YoungDiagram.mem_coversDown_of_covBy {μ ν : YoungDiagram} (hcov : μ ⋖ ν) :
    μ ∈ ν.coversDown := by
  classical
  have hup := YoungDiagram.mem_coversUp_of_covBy hcov
  unfold YoungDiagram.coversUp at hup
  rw [Finset.mem_image] at hup
  obtain ⟨r, hr_mem, hν_eq⟩ := hup
  have hadd := YoungDiagram.mem_addableRows_of_mem μ hr_mem
  simp only [dif_pos hadd] at hν_eq
  subst hν_eq
  exact YoungDiagram.self_mem_coversDown_addCell μ r hadd

lemma WalkCountFormula.iterU_emptyBasis_support_card (i : ℕ) (lam : YoungDiagram)
    (hlam : lam.card ≠ i) :
    (WalkCountFormula.iterU i WalkCountFormula.emptyBasis) lam = 0 := by
  induction i generalizing lam with
  | zero =>
    have : lam ≠ ⊥ := by
      intro h; subst h; exact hlam (by simp [YoungDiagram.card])
    simp [WalkCountFormula.iterU_zero, WalkCountFormula.emptyBasis, this]
  | succ n ih =>
    rw [WalkCountFormula.iterU_succ, LinearMap.comp_apply,
      WalkCountFormula.iterU_liftU_comm]


    set f := WalkCountFormula.iterU n WalkCountFormula.emptyBasis with hf_def
    simp only [WalkCountFormula.liftU, Finsupp.lsum_apply]


    unfold Finsupp.sum
    rw [Finset.sum_apply']
    apply Finset.sum_eq_zero; intro μ _
    simp only [LinearMap.smulRight_apply, LinearMap.id_apply,
      Finsupp.smul_apply, smul_eq_mul, WalkCountFormula.raisingOp_apply,
      mul_ite, mul_one, mul_zero]
    split_ifs with hcov
    · have hcovBy := YoungDiagram.covBy_of_mem_coversUp hcov
      have hcard_eq := HasseWalks.card_covBy_succ hcovBy
      have hμ_card : μ.card ≠ n := by omega
      exact ih μ hμ_card
    · rfl

def HasseWalkFormula.UpWalkType (n : ℕ) (lam : YoungDiagram) :=
  { walk : Fin (n + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨n, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin n,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

lemma HasseWalkFormula.upWalkCount_eq_card (n : ℕ) (lam : YoungDiagram) :
    HasseWalkFormula.upWalkCount n lam = Nat.card (HasseWalkFormula.UpWalkType n lam) := by
  unfold HasseWalkFormula.upWalkCount HasseWalkFormula.UpWalkType
  simp only [Nat.card]

lemma HasseWalkFormula.upWalkType_cells_subset {m : ℕ} {mu : YoungDiagram}
    (w : Fin (m + 1) → YoungDiagram)
    (_h0 : w ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hs : ∀ i : Fin m, w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
      w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    (he : w ⟨m, Nat.lt_succ_of_le le_rfl⟩ = mu)
    (k : Fin (m + 1)) : (w k).cells ⊆ mu.cells := by
  obtain ⟨k, hk⟩ := k
  have hle : ∀ (i : ℕ) (hi : i < m + 1) (j : ℕ) (hj : j < m + 1),
      i ≤ j → (w ⟨i, hi⟩).cells ⊆ (w ⟨j, hj⟩).cells := by
    intro i hi j hj hij
    induction hij with
    | refl => exact Finset.Subset.refl _
    | step _ ih =>
      rename_i j' _
      exact Finset.Subset.trans (ih (by omega)) ((hs ⟨j', by omega⟩).lt.le)
  have : (w ⟨k, hk⟩).cells ⊆ (w ⟨m, Nat.lt_succ_of_le le_rfl⟩).cells :=
    hle k hk m (Nat.lt_succ_of_le le_rfl) (by omega)
  rw [he] at this; exact this

instance HasseWalkFormula.upWalkType_finite (m : ℕ) (mu : YoungDiagram) :
    Finite (HasseWalkFormula.UpWalkType m mu) :=
  Finite.of_injective
    (fun ⟨w, h0, he, hs⟩ (i : Fin (m + 1)) =>
      (⟨(w ⟨i.val, i.isLt⟩).cells,
        Finset.mem_powerset.mpr
          (HasseWalkFormula.upWalkType_cells_subset w h0 hs he ⟨i.val, i.isLt⟩)⟩ :
        ↑(mu.cells.powerset)))
    (fun ⟨w1, h01, he1, hs1⟩ ⟨w2, h02, he2, hs2⟩ heq => by
      apply Subtype.ext; funext ⟨i, hi⟩
      have := congr_fun heq ⟨i, hi⟩
      simp at this
      exact YoungDiagram.ext_iff.mpr this)

open Classical in
theorem HasseWalkFormula.upWalkCount_succ_eq_finset_sum
    (n : ℕ) (lam : YoungDiagram) (hlam : n + 1 = lam.card)
    (ih : ∀ μ : YoungDiagram, n = μ.card →
      (HasseWalkFormula.upWalkCount n μ : ℤ) =
        (WalkCountFormula.iterU n WalkCountFormula.emptyBasis) μ) :
    (HasseWalkFormula.upWalkCount (n + 1) lam : ℤ) =
      ∑ μ ∈ (WalkCountFormula.iterU n WalkCountFormula.emptyBasis).support,
        if μ ⋖ lam then (HasseWalkFormula.upWalkCount n μ : ℤ) else 0 := by
  set f := WalkCountFormula.iterU n WalkCountFormula.emptyBasis with hf_def

  have huf : ∀ μ : YoungDiagram, (HasseWalkFormula.upWalkCount n μ : ℤ) = f μ := by
    intro μ
    by_cases hμ : n = μ.card
    · exact ih μ hμ
    · simp only [HasseWalkFormula.upWalkCount_eq_zero_of_ne n μ hμ, Nat.cast_zero, hf_def,
        WalkCountFormula.iterU_emptyBasis_support_card n μ (Ne.symm hμ)]

  conv_rhs =>
    arg 2; ext μ
    rw [show (if μ ⋖ lam then (HasseWalkFormula.upWalkCount n μ : ℤ) else 0) =
      (if μ ⋖ lam then f μ else 0) from by split_ifs <;> simp [huf]]
  rw [← Finset.sum_filter]
  set S := f.support.filter (· ⋖ lam) with hS_def

  rw [HasseWalkFormula.upWalkCount_eq_card]
  conv_rhs =>
    arg 2; ext μ
    rw [show f μ = (HasseWalkFormula.upWalkCount n μ : ℤ) from (huf μ).symm]
  rw [← Nat.cast_sum, ← HasseWalkFormula.upWalkCount_eq_card]
  norm_cast

  have hmem_S : ∀ μ : YoungDiagram, μ ⋖ lam → HasseWalkFormula.upWalkCount n μ ≠ 0 → μ ∈ S := by
    intro μ hcov hne
    rw [hS_def, Finset.mem_filter]
    refine ⟨Finsupp.mem_support_iff.mpr (fun hf0 => ?_), hcov⟩
    exact hne (Nat.cast_eq_zero.mp (by rw [huf]; exact hf0))
  rw [HasseWalkFormula.upWalkCount_eq_card]
  simp_rw [HasseWalkFormula.upWalkCount_eq_card]

  let fwd : HasseWalkFormula.UpWalkType (n + 1) lam →
      (μ : ↑S) × HasseWalkFormula.UpWalkType n μ := fun ⟨w, h0, he, hs⟩ =>
    let μ := w ⟨n, by omega⟩
    have hcov : μ ⋖ lam := by
      have h1 := hs ⟨n, by omega⟩; simp only [μ]; rw [he] at h1; exact h1
    let g : Fin (n + 1) → YoungDiagram := fun i => w ⟨i.val, by omega⟩
    have hg0 : g ⟨0, Nat.zero_lt_succ _⟩ = ⊥ := h0
    have hgn : g ⟨n, Nat.lt_succ_of_le le_rfl⟩ = μ := rfl
    have hgs : ∀ i : Fin n, g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
      intro ⟨i, hi⟩
      have := hs ⟨i, by omega⟩
      convert this using 2
    have hne : HasseWalkFormula.upWalkCount n μ ≠ 0 := by
      rw [HasseWalkFormula.upWalkCount_eq_card, Nat.card_ne_zero]
      exact ⟨⟨⟨g, hg0, hgn, hgs⟩⟩, inferInstance⟩
    (⟨⟨μ, hmem_S μ hcov hne⟩, ⟨g, hg0, hgn, hgs⟩⟩)
  let bwd : ((μ : ↑S) × HasseWalkFormula.UpWalkType n μ) →
      HasseWalkFormula.UpWalkType (n + 1) lam := fun ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩ =>
    have hcov : μ ⋖ lam := by rw [hS_def, Finset.mem_filter] at hμ; exact hμ.2
    let w : Fin (n + 2) → YoungDiagram := fun i =>
      if h : i.val ≤ n then g ⟨i.val, by omega⟩ else lam
    have hw0 : w ⟨0, Nat.zero_lt_succ _⟩ = ⊥ := by
      simp only [w, show (0 : ℕ) ≤ n from Nat.zero_le n, dite_true]; exact hg0
    have hwn : w ⟨n + 1, Nat.lt_succ_of_le le_rfl⟩ = lam := by
      simp only [w, show ¬(n + 1 ≤ n) from by omega, dite_false]
    have hws : ∀ i : Fin (n + 1), w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
      intro ⟨i, hi⟩; simp only [w]
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
      · subst heq
        simp only [show i ≤ i from le_rfl, dite_true, show ¬(i + 1 ≤ i) from by omega, dite_false]
        rw [hgn]; exact hcov
      · simp only [show i ≤ n from by omega, dite_true, show i + 1 ≤ n from by omega, dite_true]
        exact hgs ⟨i, by omega⟩
    ⟨w, hw0, hwn, hws⟩
  have hfwd_bwd : ∀ x, fwd (bwd x) = x := by
    intro ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩
    show fwd (bwd ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩) = ⟨⟨μ, hμ⟩, ⟨g, hg0, hgn, hgs⟩⟩
    simp only [fwd, bwd]
    have h1 : (fun (i : Fin (n + 1)) =>
        (if h : (i : ℕ) ≤ n then g ⟨i, by omega⟩ else lam)) = g :=
      funext fun ⟨i, hi⟩ => dif_pos (by omega)
    have h2 : (if h : n ≤ n then g ⟨n, by omega⟩ else lam) = μ := by
      rw [dif_pos le_rfl]; exact hgn
    exact Sigma.ext (Subtype.ext h2) (by subst h2; exact heq_of_eq (Subtype.ext h1))
  have hbwd_fwd : ∀ x, bwd (fwd x) = x := by
    intro ⟨w, h0, he, hs⟩
    simp only [fwd, bwd]
    apply Subtype.ext; funext ⟨i, hi⟩
    show (if h : i ≤ n then w ⟨i, _⟩ else lam) = w ⟨i, hi⟩
    split_ifs with h
    · rfl
    · have hi_eq : i = n + 1 := by omega
      subst hi_eq; exact he.symm
  have equiv : HasseWalkFormula.UpWalkType (n + 1) lam ≃
      ((μ : ↑S) × HasseWalkFormula.UpWalkType n μ) :=
    { toFun := fwd, invFun := bwd, left_inv := hbwd_fwd, right_inv := hfwd_bwd }
  rw [Nat.card_congr equiv, Nat.card_sigma]
  exact Finset.sum_coe_sort S (fun μ => Nat.card (HasseWalkFormula.UpWalkType n μ))

theorem HasseWalkFormula.upWalkCount_eq_iterU_apply
    (i : ℕ) (lam : YoungDiagram) :
    (HasseWalkFormula.upWalkCount i lam : ℤ) =
      (WalkCountFormula.iterU i WalkCountFormula.emptyBasis) lam := by
  classical
  by_cases hi : i = lam.card
  · revert lam; induction i with
    | zero =>
      intro lam hlam
      have hlam_bot : lam = ⊥ := by
        rw [YoungDiagram.ext_iff]; ext ⟨a, b⟩
        simp only [YoungDiagram.card] at hlam; constructor
        · intro h; exact absurd (Finset.card_pos.mpr ⟨_, h⟩) (by omega)
        · intro h; simp at h
      subst hlam_bot
      simp [WalkCountFormula.iterU_zero, WalkCountFormula.emptyBasis]
      unfold HasseWalkFormula.upWalkCount
      norm_cast
      apply Nat.card_eq_one_iff_unique.mpr
      exact ⟨⟨fun ⟨f, hf1, _, _⟩ ⟨g, hg1, _, _⟩ => by
        apply Subtype.ext; funext ⟨j, hj⟩
        have hj0 : j = 0 := by omega
        subst hj0; exact hf1.trans hg1.symm⟩,
        ⟨⟨fun _ => ⊥, rfl, rfl, fun j => absurd j.isLt (by omega)⟩⟩⟩
    | succ n ih_n =>
      intro lam hlam
      rw [WalkCountFormula.iterU_succ, LinearMap.comp_apply,
        WalkCountFormula.iterU_liftU_comm]
      simp only [WalkCountFormula.liftU, Finsupp.lsum_apply]
      unfold Finsupp.sum
      rw [Finset.sum_apply']
      simp only [LinearMap.smulRight_apply, LinearMap.id_apply,
        Finsupp.smul_apply, smul_eq_mul, WalkCountFormula.raisingOp_apply,
        mul_ite, mul_one, mul_zero]
      simp_rw [← YoungDiagram.covBy_iff_mem_coversUp]
      have hrw : ∀ μ ∈ (WalkCountFormula.iterU n WalkCountFormula.emptyBasis).support,
          ite (μ ⋖ lam) ((WalkCountFormula.iterU n WalkCountFormula.emptyBasis) μ) (0 : ℤ) =
          ite (μ ⋖ lam) (HasseWalkFormula.upWalkCount n μ : ℤ) 0 := by
        intro μ _; split_ifs with hcov
        · exact (ih_n μ (by have := HasseWalks.card_covBy_succ hcov; omega)).symm
        · rfl
      rw [Finset.sum_congr rfl hrw]
      exact HasseWalkFormula.upWalkCount_succ_eq_finset_sum n lam hlam
        (fun μ hμ => ih_n μ hμ)
  · have hLHS := HasseWalkFormula.upWalkCount_eq_zero_of_ne i lam hi
    have hRHS := WalkCountFormula.iterU_emptyBasis_support_card i lam (Ne.symm hi)
    simp [hLHS, hRHS]


theorem HasseWalkFormula.DplusU_pow_emptyBasis_eq_sum_bijCoeff_iterU
    (ell : ℕ) (lam : YoungDiagram) :
    ((((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ ell)
        WalkCountFormula.emptyBasis) lam : ℚ) =
      ∑ i ∈ Finset.range (ell + 1),
        NormalOrderCoeff.bijCoeff i 0 ell *
          ((WalkCountFormula.iterU i WalkCountFormula.emptyBasis) lam : ℚ) :=
  WalkCountBridge.DplusU_pow_emptyBasis_eq_sum_bijCoeff_iterU ell lam


theorem HasseWalkFormula.hasseWalkCount_eq_sum_bijCoeff_upWalkCount
    (ell : ℕ) (lam : YoungDiagram) :
    (HasseWalkFormula.hasseWalkCount ell lam : ℚ) =
      ∑ i ∈ Finset.range (ell + 1),
        NormalOrderCoeff.bijCoeff i 0 ell *
          (HasseWalkFormula.upWalkCount i lam : ℚ) := by

  have hF2 := hasseWalkCount_eq_DplusU_pow_apply ell lam

  have hNO := DplusU_pow_emptyBasis_eq_sum_bijCoeff_iterU ell lam


  calc (hasseWalkCount ell lam : ℚ)
      = ((((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ ell)
            WalkCountFormula.emptyBasis) lam : ℚ) := by exact_mod_cast hF2
    _ = ∑ i ∈ Finset.range (ell + 1),
          NormalOrderCoeff.bijCoeff i 0 ell *
            ((WalkCountFormula.iterU i WalkCountFormula.emptyBasis) lam : ℚ) := hNO
    _ = ∑ i ∈ Finset.range (ell + 1),
          NormalOrderCoeff.bijCoeff i 0 ell *
            (upWalkCount i lam : ℚ) := by
        apply Finset.sum_congr rfl; intro i _
        congr 1; exact_mod_cast (upWalkCount_eq_iterU_apply i lam).symm

theorem HasseWalkFormula.hasseWalkCount_eq_bijCoeff_mul_upWalkCount
    (ell : ℕ) (lam : YoungDiagram) :
    (HasseWalkFormula.hasseWalkCount ell lam : ℚ) =
      NormalOrderCoeff.bijCoeff lam.card 0 ell *
        (HasseWalkFormula.upWalkCount lam.card lam : ℚ) := by
  rw [hasseWalkCount_eq_sum_bijCoeff_upWalkCount]
  have hvanish : ∀ i ∈ Finset.range (ell + 1), i ≠ lam.card →
      NormalOrderCoeff.bijCoeff i 0 ell * (upWalkCount i lam : ℚ) = 0 := by
    intro i _ hi
    rw [upWalkCount_eq_zero_of_ne i lam hi]
    simp
  by_cases hmem : lam.card ∈ Finset.range (ell + 1)
  · rw [← Finset.add_sum_erase _ _ hmem]
    suffices h : ∑ x ∈ (Finset.range (ell + 1)).erase lam.card,
        NormalOrderCoeff.bijCoeff x 0 ell * (upWalkCount x lam : ℚ) = 0 by
      rw [h, add_zero]
    apply Finset.sum_eq_zero
    intro i hi
    exact hvanish i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  · have hlt : ell < lam.card := by
      simp only [Finset.mem_range, not_lt] at hmem; omega
    rw [NormalOrderCoeff.bijCoeff_eq_zero_of_gt (by omega : ell < lam.card + 0)]
    simp only [zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    exact hvanish i hi (by simp only [Finset.mem_range] at hi; omega)


theorem HasseWalkFormula.hasseWalkCount_eq_bijCoeff_mul_numSYT
    (ell : ℕ) (lam : YoungDiagram) :
    (HasseWalkFormula.hasseWalkCount ell lam : ℚ) =
      NormalOrderCoeff.bijCoeff lam.card 0 ell *
        (HasseWalkFormula.numSYT lam : ℚ) := by
  rw [HasseWalkFormula.hasseWalkCount_eq_bijCoeff_mul_upWalkCount,
      HasseWalkFormula.upWalkCount_eq_numSYT]

noncomputable section

namespace HasseWalkFormula

theorem bijCoeff_n_0_eq {n ell : ℕ} (hn : n ≤ ell) (heven : (ell - n) % 2 = 0) :
    NormalOrderCoeff.bijCoeff n 0 ell =
      (ell.choose n : ℚ) * ((ell - n - 1).doubleFactorial : ℚ) := by
  rw [NormalOrderCoeff.bijCoeff_of_valid (show n + 0 ≤ ell by omega)
    (show (ell - n - 0) % 2 = 0 by omega)]
  set m := (ell - n - 0) / 2 with hm_def
  have hm_rel : ell - n = 2 * m := by omega
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [Nat.cast_choose ℚ hn]
  by_cases hm0 : m = 0
  ·
    have h_en : ell - n = 0 := by omega
    simp [hm0, h_en]
  ·
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have h_dfact_arg : ell - n - 1 = 2 * m - 1 := by omega
    rw [h_dfact_arg, hm_rel]
    have h_nfact : (n.factorial : ℚ) ≠ 0 := by positivity
    have h_mfact : (m.factorial : ℚ) ≠ 0 := by positivity
    have h_pow2 : (2 : ℚ) ^ m ≠ 0 := by positivity
    have h_dfact_ne : ((2 * m - 1).doubleFactorial : ℚ) ≠ 0 := by positivity
    have key : (2 * m).factorial = 2 ^ m * m.factorial * (2 * m - 1).doubleFactorial := by
      have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * m - 1)
      rw [show 2 * m - 1 + 1 = 2 * m from by omega] at h1
      rw [Nat.doubleFactorial_two_mul] at h1
      exact h1
    rw [show (↑((2 * m).factorial) : ℚ) =
      (2 : ℚ) ^ m * ↑m.factorial * ↑(2 * m - 1).doubleFactorial from by exact_mod_cast key]
    field_simp

theorem hasseWalkCount_formula {ell n : ℕ} (lam : YoungDiagram)
    (hn : lam.card = n) (hle : n ≤ ell) (heven : (ell - n) % 2 = 0) :
    (hasseWalkCount ell lam : ℚ) =
      (ell.choose n : ℚ) * ((ell - n - 1).doubleFactorial : ℚ) * (numSYT lam : ℚ) := by
  rw [hasseWalkCount_eq_bijCoeff_mul_numSYT, hn, bijCoeff_n_0_eq hle heven, mul_assoc]

lemma bot_card : (⊥ : YoungDiagram).card = 0 := by
  simp [YoungDiagram.card]

theorem numSYT_bot : numSYT ⊥ = 1 := by


  have hcard : (⊥ : YoungDiagram).card = 0 := bot_card
  unfold numSYT


  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  ·
    constructor
    intro ⟨f, hf1, hf2, hf3⟩ ⟨g, hg1, hg2, hg3⟩
    apply Subtype.ext
    funext ⟨i, hi⟩
    have hi' : i < (⊥ : YoungDiagram).card + 1 := hi
    rw [hcard] at hi'
    have : i = 0 := by omega
    subst this
    exact hf1.trans hg1.symm
  ·
    refine ⟨⟨fun _ => ⊥, rfl, rfl, fun i => ?_⟩⟩
    exact absurd i.isLt (by simp [hcard])

theorem closedWalkCount_eq_doubleFactorial (m : ℕ) :
    (hasseWalkCount (2 * m) ⊥ : ℚ) = ((2 * m - 1).doubleFactorial : ℚ) := by
  have hcard : (⊥ : YoungDiagram).card = 0 := bot_card
  rw [hasseWalkCount_formula ⊥ hcard (by omega) (by simp)]
  simp [Nat.choose_zero_right, numSYT_bot]

theorem closedWalkCount_eq_doubleFactorial_nat (m : ℕ) :
    hasseWalkCount (2 * m) ⊥ = (2 * m - 1).doubleFactorial := by
  have h := closedWalkCount_eq_doubleFactorial m
  exact_mod_cast h

end HasseWalkFormula

end
