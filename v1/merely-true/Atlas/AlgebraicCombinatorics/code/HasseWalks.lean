/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith

namespace HasseWalks

inductive HStep : Type where
  | U : HStep
  | D : HStep
  deriving DecidableEq, Repr

def HStep.toInt : HStep → ℤ
  | HStep.U => 1
  | HStep.D => -1

def expandBlock (p : ℕ × ℕ) : List HStep :=
  List.replicate p.1 HStep.U ++ List.replicate p.2 HStep.D

def expandBlocks (w : List (ℕ × ℕ)) : List HStep :=
  w.flatMap expandBlock

def displacement (w : List (ℕ × ℕ)) : ℤ :=
  (w.map fun p => (p.1 : ℤ) - (p.2 : ℤ)).sum

def partialDisplacement (w : List (ℕ × ℕ)) (j : ℕ) : ℤ :=
  displacement (w.take j)

def IsValidWord (w : List (ℕ × ℕ)) (n : ℕ) : Prop :=
  displacement w = (n : ℤ) ∧
  ∀ j, 1 ≤ j → j ≤ w.length → 0 ≤ partialDisplacement w j

structure HasseWalk (steps : List HStep) (start target : YoungDiagram) : Type where
  diagram : Fin (steps.length + 1) → YoungDiagram
  start_eq : diagram ⟨0, Nat.zero_lt_succ _⟩ = start
  target_eq : diagram ⟨steps.length, Nat.lt_succ_of_le le_rfl⟩ = target
  step_up : ∀ (i : Fin steps.length), steps[i] = HStep.U →
    diagram ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
    diagram ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  step_down : ∀ (i : Fin steps.length), steps[i] = HStep.D →
    diagram ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
    diagram ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

lemma isLowerSet_insert_minimal {μ ν : YoungDiagram}
    (m : ℕ × ℕ) (hm_ν : m ∈ ν.cells) (hm_nμ : m ∉ μ.cells)
    (h_below : ∀ c : ℕ × ℕ, c ∈ ν.cells → c.1 ≤ m.1 → c.2 ≤ m.2 → c ≠ m → c ∈ μ.cells) :
    IsLowerSet ((↑(Finset.cons m μ.cells hm_nμ)) : Set (ℕ × ℕ)) := by
  intro x y hle hx_mem
  have hx : x ∈ Finset.cons m μ.cells hm_nμ := hx_mem
  rw [Finset.mem_cons] at hx
  suffices y ∈ Finset.cons m μ.cells hm_nμ from this
  rcases hx with hx_eq | hx_μ
  · have hle' : y ≤ m := hx_eq ▸ hle
    by_cases hy_eq : y = m
    · rw [hy_eq]; exact Finset.mem_cons_self m μ.cells
    · exact Finset.mem_cons.mpr (Or.inr
        (h_below y (ν.isLowerSet hle' hm_ν) hle'.1 hle'.2 hy_eq))
  · exact Finset.mem_cons.mpr (Or.inr (μ.isLowerSet hle hx_μ))

theorem card_covBy_succ {μ ν : YoungDiagram} (h : μ ⋖ ν) :
    ν.card = μ.card + 1 := by
  have hsub : μ.cells ⊆ ν.cells := h.lt.le
  have hne : μ ≠ ν := ne_of_lt h.lt
  have hsdiff_nonempty : (ν.cells \ μ.cells).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    exact fun hsub' => hne (le_antisymm h.lt.le hsub')
  suffices h1 : (ν.cells \ μ.cells).card = 1 by
    have h2 := Finset.card_sdiff_add_card_eq_card hsub
    simp only [YoungDiagram.card]; omega
  by_contra h_ne1
  exfalso
  have hcard_ge1 := hsdiff_nonempty.card_pos
  set sdiff := ν.cells \ μ.cells with sdiff_def
  have img_ne : (sdiff.image (fun p : ℕ × ℕ => p.1 + p.2)).Nonempty :=
    hsdiff_nonempty.image _
  obtain ⟨m, hm_sdiff, hm_eq⟩ : ∃ m ∈ sdiff, m.1 + m.2 =
      (sdiff.image (fun p : ℕ × ℕ => p.1 + p.2)).min' img_ne := by
    have := Finset.min'_mem _ img_ne
    rw [Finset.mem_image] at this
    obtain ⟨m, hm, hmeq⟩ := this
    exact ⟨m, hm, hmeq⟩
  have hm_ν := (Finset.mem_sdiff.mp hm_sdiff).1
  have hm_nμ := (Finset.mem_sdiff.mp hm_sdiff).2
  have h_min_le : ∀ c ∈ sdiff, m.1 + m.2 ≤ c.1 + c.2 := by
    intro c hc
    rw [hm_eq]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have h_below : ∀ c : ℕ × ℕ, c ∈ ν.cells → c.1 ≤ m.1 → c.2 ≤ m.2 → c ≠ m →
      c ∈ μ.cells := by
    intro c hc_ν hc1 hc2 hc_ne
    by_contra hc_nμ
    have hc_sdiff : c ∈ sdiff := Finset.mem_sdiff.mpr ⟨hc_ν, hc_nμ⟩
    have := h_min_le c hc_sdiff
    have hle12 : c.1 + c.2 ≤ m.1 + m.2 := Nat.add_le_add hc1 hc2
    have : c.1 = m.1 := le_antisymm hc1 (by omega)
    have : c.2 = m.2 := le_antisymm hc2 (by omega)
    exact hc_ne (Prod.ext ‹c.1 = m.1› ‹c.2 = m.2›)
  set ξ : YoungDiagram := ⟨Finset.cons m μ.cells hm_nμ,
    isLowerSet_insert_minimal m hm_ν hm_nμ h_below⟩
  have hμ_lt_ξ : μ < ξ := by
    rw [show (μ < ξ) = (μ.cells ⊂ ξ.cells) from rfl]
    exact Finset.ssubset_cons hm_nμ
  have hξ_lt_ν : ξ < ν := by
    rw [show (ξ < ν) = (ξ.cells ⊂ ν.cells) from rfl]
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [show ξ.cells = Finset.cons m μ.cells hm_nμ from rfl, Finset.mem_cons] at hx
      rcases hx with rfl | hx_μ
      · exact hm_ν
      · exact hsub hx_μ
    · intro h_eq
      have : ξ.cells.card = μ.cells.card + 1 := by
        rw [show ξ.cells = Finset.cons m μ.cells hm_nμ from rfl]
        exact Finset.card_cons hm_nμ
      have hν_card : ν.cells.card = μ.cells.card + 1 := by
        rw [← h_eq]; exact this
      have h_sdiff_card := Finset.card_sdiff_add_card_eq_card hsub
      rw [sdiff_def] at h_ne1 hcard_ge1
      omega
  exact (h.2 hμ_lt_ξ) hξ_lt_ν

lemma expandBlock_toInt_sum (p : ℕ × ℕ) :
    ((expandBlock p).map HStep.toInt).sum = (p.1 : ℤ) - (p.2 : ℤ) := by
  simp only [expandBlock, HStep.toInt, List.map_append, List.sum_append,
    List.map_replicate, List.sum_replicate, nsmul_eq_mul, mul_one]
  omega

lemma expandBlocks_toInt_sum (w : List (ℕ × ℕ)) :
    ((expandBlocks w).map HStep.toInt).sum = displacement w := by
  induction w with
  | nil => simp [expandBlocks, displacement]
  | cons p w ih =>
    simp only [expandBlocks, displacement]
    simp only [List.flatMap_cons, List.map_append, List.sum_append, expandBlock_toInt_sum,
      List.map_cons, List.sum_cons]
    have : (List.flatMap expandBlock w).map HStep.toInt = (expandBlocks w).map HStep.toInt := rfl
    rw [this, ih, displacement]

lemma expandBlocks_append (w₁ w₂ : List (ℕ × ℕ)) :
    expandBlocks (w₁ ++ w₂) = expandBlocks w₁ ++ expandBlocks w₂ := by
  simp only [expandBlocks, List.flatMap_append]

lemma walk_card_step {steps : List HStep} {start target : YoungDiagram}
    (walk : HasseWalk steps start target) (i : Fin steps.length) :
    ((walk.diagram ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).card : ℤ) =
    ((walk.diagram ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).card : ℤ) +
    (steps[i]).toInt := by
  cases h_step : steps[i] with
  | U =>
    have := card_covBy_succ (walk.step_up i h_step)
    simp only [HStep.toInt]; omega
  | D =>
    have := card_covBy_succ (walk.step_down i h_step)
    simp only [HStep.toInt]; omega

lemma walk_card_eq {steps : List HStep} {start target : YoungDiagram}
    (walk : HasseWalk steps start target) (k : ℕ) (hk : k ≤ steps.length) :
    ((walk.diagram ⟨k, Nat.lt_succ_of_le hk⟩).card : ℤ) =
    (start.card : ℤ) + ((steps.take k).map HStep.toInt).sum := by
  induction k with
  | zero =>
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero]
    exact congrArg (fun d => (d.card : ℤ)) walk.start_eq
  | succ n ih =>
    have hn_lt : n < steps.length := Nat.lt_of_succ_le hk
    have h_step := walk_card_step walk ⟨n, hn_lt⟩
    rw [h_step, ih (Nat.le_of_lt hn_lt)]
    rw [← List.take_concat_get' steps n hn_lt]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, add_assoc, Fin.getElem_fin]

theorem walk_exists_necessity (w : List (ℕ × ℕ)) (lam : YoungDiagram) (n : ℕ)
    (hn : lam.card = n) (walk : HasseWalk (expandBlocks w) ⊥ lam) :
    IsValidWord w n := by
  have h_bot_card : (⊥ : YoungDiagram).card = 0 := by simp [YoungDiagram.card]
  constructor
  · have h_end := walk_card_eq walk (expandBlocks w).length le_rfl
    simp only [walk.target_eq, List.take_length] at h_end
    rw [hn, h_bot_card, Nat.cast_zero, zero_add, expandBlocks_toInt_sum] at h_end
    exact h_end.symm
  · intro j _ hj_le
    set pos := (expandBlocks (w.take j)).length
    have hpos_le : pos ≤ (expandBlocks w).length := by
      have : expandBlocks w = expandBlocks (w.take j) ++ expandBlocks (w.drop j) := by
        rw [← expandBlocks_append, List.take_append_drop]
      rw [this]; simp only [List.length_append, pos]; omega
    have h_pos := walk_card_eq walk pos hpos_le
    rw [h_bot_card, Nat.cast_zero, zero_add] at h_pos
    have h_take : (expandBlocks w).take pos = expandBlocks (w.take j) := by
      conv_lhs => rw [← List.take_append_drop j w, expandBlocks_append]
      exact List.take_left
    rw [h_take, expandBlocks_toInt_sum] at h_pos
    show 0 ≤ partialDisplacement w j
    rw [show partialDisplacement w j = displacement (w.take j) from rfl, ← h_pos]
    exact Int.natCast_nonneg _

lemma card_zero_eq_bot {μ : YoungDiagram} (h : μ.card = 0) : μ = ⊥ := by
  ext ⟨i, j⟩; constructor
  · intro hmem; exact absurd h (Finset.card_ne_zero_of_mem hmem)
  · intro hmem; exact absurd hmem (YoungDiagram.notMem_bot _)

lemma exists_removable_cell (ν : YoungDiagram) (hne : ν.cells.Nonempty) :
    ∃ c ∈ ν.cells, (c.1 + 1, c.2) ∉ ν.cells ∧ (c.1, c.2 + 1) ∉ ν.cells := by
  set f : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have img_ne := hne.image f
  obtain ⟨c, hc, hc_max⟩ : ∃ c ∈ ν.cells, f c =
      (ν.cells.image f).max' img_ne := by
    have := Finset.max'_mem _ img_ne
    rw [Finset.mem_image] at this
    obtain ⟨c, hc, hceq⟩ := this
    exact ⟨c, hc, hceq⟩
  refine ⟨c, hc, ?_, ?_⟩
  · intro h
    have hle := Finset.le_max' (ν.cells.image f) (f (c.1 + 1, c.2))
      (Finset.mem_image.mpr ⟨(c.1 + 1, c.2), h, rfl⟩)
    simp only [f] at hle hc_max; omega
  · intro h
    have hle := Finset.le_max' (ν.cells.image f) (f (c.1, c.2 + 1))
      (Finset.mem_image.mpr ⟨(c.1, c.2 + 1), h, rfl⟩)
    simp only [f] at hle hc_max; omega

lemma isLowerSet_erase_corner (ν : YoungDiagram)
    (c : ℕ × ℕ) (hc : c ∈ ν.cells)
    (h1 : (c.1 + 1, c.2) ∉ ν.cells) (h2 : (c.1, c.2 + 1) ∉ ν.cells) :
    IsLowerSet ((ν.cells.erase c : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro a b hab ha_mem
  rw [Finset.mem_coe, Finset.mem_erase] at ha_mem ⊢
  obtain ⟨ha_ne, ha_ν⟩ := ha_mem
  refine ⟨?_, ν.isLowerSet hab ha_ν⟩
  intro hb_eq; rw [hb_eq] at hab
  have ha1 : c.1 ≤ a.1 := hab.1
  have ha2 : c.2 ≤ a.2 := hab.2
  rcases Nat.lt_or_eq_of_le ha1 with ha1_lt | ha1_eq
  · exact h1 (ν.isLowerSet (show (c.1 + 1, c.2) ≤ a from ⟨ha1_lt, ha2⟩) ha_ν)
  · rcases Nat.lt_or_eq_of_le ha2 with ha2_lt | ha2_eq
    · exact h2 (ν.isLowerSet (show (c.1, c.2 + 1) ≤ a from ⟨ha1, ha2_lt⟩) ha_ν)
    · exact ha_ne (Prod.ext ha1_eq.symm ha2_eq.symm)

lemma covBy_erase_corner (ν : YoungDiagram)
    (c : ℕ × ℕ) (hc : c ∈ ν.cells)
    (h1 : (c.1 + 1, c.2) ∉ ν.cells) (h2 : (c.1, c.2 + 1) ∉ ν.cells) :
    (⟨ν.cells.erase c, isLowerSet_erase_corner ν c hc h1 h2⟩ : YoungDiagram) ⋖ ν := by
  constructor
  · show (⟨ν.cells.erase c, _⟩ : YoungDiagram) < ν
    exact Finset.erase_ssubset hc
  · intro ξ hlt hξν
    have h_sub_ν : ξ.cells ⊆ ν.cells := hξν.le
    have : (ν.cells.erase c).card + 1 ≤ ξ.cells.card := Finset.card_lt_card hlt
    have : ξ.cells = ν.cells :=
      Finset.eq_of_subset_of_card_le h_sub_ν (by
        rw [Finset.card_erase_of_mem hc] at *; omega)
    exact absurd (YoungDiagram.ext_iff.mpr this) (ne_of_lt hξν)

lemma exists_covBy_below {ν : YoungDiagram} (hν : 0 < ν.card) :
    ∃ μ : YoungDiagram, μ ⋖ ν := by
  have hne : ν.cells.Nonempty := Finset.card_pos.mp hν
  obtain ⟨c, hc, h1, h2⟩ := exists_removable_cell ν hne
  exact ⟨⟨ν.cells.erase c, isLowerSet_erase_corner ν c hc h1 h2⟩,
    covBy_erase_corner ν c hc h1 h2⟩

lemma exists_covBy_above (μ : YoungDiagram) :
    ∃ ν : YoungDiagram, μ ⋖ ν := by
  set c := (0, μ.rowLen 0) with hc_def
  have hc_not_mem : c ∉ μ.cells := by
    simp only [YoungDiagram.mem_cells, hc_def]
    rw [YoungDiagram.mem_iff_lt_rowLen]; omega
  set ν : YoungDiagram := ⟨Finset.cons c μ.cells hc_not_mem,
    by
      intro a b hab hb_mem
      rw [Finset.mem_coe, Finset.mem_cons] at hb_mem ⊢
      rcases hb_mem with hb_eq | hb_μ
      · subst hb_eq
        have ha1_eq : b.1 = 0 := Nat.le_zero.mp hab.1
        rcases Nat.lt_or_eq_of_le hab.2 with ha2_lt | ha2_eq
        · right; rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, ha1_eq]
          exact ha2_lt
        · left; exact Prod.ext ha1_eq ha2_eq
      · right; exact μ.isLowerSet hab hb_μ⟩ with hν_def
  refine ⟨ν, ?_⟩
  constructor
  · show μ < ν
    exact Finset.ssubset_cons hc_not_mem
  · intro ξ hμ_lt_ξ hξ_lt_ν
    have hξ_le_ν : ξ.cells ⊆ ν.cells := hξ_lt_ν.le
    have : μ.cells.card + 1 ≤ ξ.cells.card := Finset.card_lt_card hμ_lt_ξ
    have hν_card : ν.cells.card = μ.cells.card + 1 := by
      show (Finset.cons c μ.cells hc_not_mem).card = μ.cells.card + 1
      exact Finset.card_cons hc_not_mem
    have : ξ.cells = ν.cells := by
      apply Finset.eq_of_subset_of_card_le hξ_le_ν; omega
    exact absurd (YoungDiagram.ext_iff.mpr this) (ne_of_lt hξ_lt_ν)

lemma nonempty_walk_extend {s : List HStep} {a : HStep} {mid target : YoungDiagram}
    (hw : Nonempty (HasseWalk s ⊥ mid))
    (hU : a = HStep.U → mid ⋖ target) (hD : a = HStep.D → target ⋖ mid) :
    Nonempty (HasseWalk (s ++ [a]) ⊥ target) := by
  obtain ⟨w⟩ := hw
  refine ⟨⟨fun ⟨i, hi⟩ => if h : i < s.length + 1 then w.diagram ⟨i, h⟩ else target,
    ?_, ?_, ?_, ?_⟩⟩
  · dsimp only; rw [dif_pos (by omega : 0 < s.length + 1)]; exact w.start_eq
  · dsimp only; exact dif_neg (by simp)
  · intro ⟨i, hi_orig⟩ hstep
    dsimp only
    have hlen_eq : (s ++ [a]).length = s.length + 1 := by simp
    have hi : i < s.length + 1 := by omega
    by_cases hi' : i + 1 < s.length + 1
    · rw [dif_pos (show i < s.length + 1 from hi), dif_pos hi']
      have hi_s : i < s.length := by omega
      have hstep' : s[i]'hi_s = HStep.U := by
        have h := @List.getElem_append _ s [a] i hi_orig
        rw [dif_pos hi_s] at h; rw [← h]; exact hstep
      exact w.step_up ⟨i, hi_s⟩ hstep'
    · rw [dif_pos (show i < s.length + 1 from hi), dif_neg hi']
      have hi_eq : i = s.length := by omega
      subst hi_eq; rw [w.target_eq]; apply hU
      have h := @List.getElem_append _ s [a] s.length hi_orig
      rw [dif_neg (by omega : ¬ s.length < s.length)] at h
      simp only [Nat.sub_self, List.getElem_cons_zero] at h
      rw [← h]; exact hstep
  · intro ⟨i, hi_orig⟩ hstep
    dsimp only
    have hlen_eq : (s ++ [a]).length = s.length + 1 := by simp
    have hi : i < s.length + 1 := by omega
    by_cases hi' : i + 1 < s.length + 1
    · rw [dif_pos (show i < s.length + 1 from hi), dif_pos hi']
      have hi_s : i < s.length := by omega
      have hstep' : s[i]'hi_s = HStep.D := by
        have h := @List.getElem_append _ s [a] i hi_orig
        rw [dif_pos hi_s] at h; rw [← h]; exact hstep
      exact w.step_down ⟨i, hi_s⟩ hstep'
    · rw [dif_pos (show i < s.length + 1 from hi), dif_neg hi']
      have hi_eq : i = s.length := by omega
      subst hi_eq; rw [w.target_eq]; apply hD
      have h := @List.getElem_append _ s [a] s.length hi_orig
      rw [dif_neg (by omega : ¬ s.length < s.length)] at h
      simp only [Nat.sub_self, List.getElem_cons_zero] at h
      rw [← h]; exact hstep

lemma walk_from_bot_exists (s : List HStep) (target : YoungDiagram)
    (hcard : (target.card : ℤ) = ((s.map HStep.toInt).sum))
    (hpartial : ∀ k, k ≤ s.length → 0 ≤ ((s.take k).map HStep.toInt).sum) :
    Nonempty (HasseWalk s ⊥ target) := by
  induction s using List.reverseRecOn generalizing target with
  | nil =>
    have hcard0 : target.card = 0 := by
      have : (target.card : ℤ) = 0 := by convert hcard using 1
      exact_mod_cast this
    have := card_zero_eq_bot hcard0; subst this
    exact ⟨⟨fun _ => ⊥, rfl, rfl, fun i => i.elim0, fun i => i.elim0⟩⟩
  | append_singleton s a ih =>
    cases a with
    | U =>
      have hsum_s : ((s.map HStep.toInt).sum) = (target.card : ℤ) - 1 := by
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_cons,
          List.sum_nil, add_zero, HStep.toInt] at hcard; linarith
      have htgt_pos : 0 < target.card := by
        have h := hpartial s.length (by simp)
        rw [List.take_append_of_le_length (by omega), List.take_length] at h; linarith
      obtain ⟨mid, hmid⟩ := exists_covBy_below htgt_pos
      have hccs := card_covBy_succ hmid
      have hcard_mid : (mid.card : ℤ) = (s.map HStep.toInt).sum := by omega
      have hpartial_s : ∀ k, k ≤ s.length → 0 ≤ ((s.take k).map HStep.toInt).sum := by
        intro k hk
        have h := hpartial k (by simp; omega)
        rwa [List.take_append_of_le_length (by omega)] at h
      exact nonempty_walk_extend (ih mid hcard_mid hpartial_s)
        (fun _ => hmid) (fun h => absurd h (by decide))
    | D =>
      have hsum_s : ((s.map HStep.toInt).sum) = (target.card : ℤ) + 1 := by
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_cons,
          List.sum_nil, add_zero, HStep.toInt] at hcard; linarith
      obtain ⟨mid, hmid⟩ := exists_covBy_above target
      have hccs := card_covBy_succ hmid
      have hcard_mid : (mid.card : ℤ) = (s.map HStep.toInt).sum := by omega
      have hpartial_s : ∀ k, k ≤ s.length → 0 ≤ ((s.take k).map HStep.toInt).sum := by
        intro k hk
        have h := hpartial k (by simp; omega)
        rwa [List.take_append_of_le_length (by omega)] at h
      exact nonempty_walk_extend (ih mid hcard_mid hpartial_s)
        (fun h => absurd h (by decide)) (fun _ => hmid)

lemma expandBlocks_partial_nonneg_aux
    (w : List (ℕ × ℕ)) (base : ℤ) (hbase : 0 ≤ base)
    (hpartial : ∀ j, 1 ≤ j → j ≤ w.length →
      0 ≤ base + partialDisplacement w j)
    (k : ℕ) (hk : k ≤ (expandBlocks w).length) :
    0 ≤ base + (((expandBlocks w).take k).map HStep.toInt).sum := by
  induction w generalizing k base with
  | nil =>
    simp only [expandBlocks, List.flatMap_nil, List.length_nil] at hk
    have : k = 0 := Nat.le_zero.mp hk
    subst this; simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero]; exact hbase
  | cons p w' ih =>
    simp only [expandBlocks, List.flatMap_cons] at hk ⊢
    by_cases hk' : k ≤ (expandBlock p).length
    · rw [List.take_append_of_le_length hk']
      simp only [expandBlock, List.length_append, List.length_replicate] at hk'
      by_cases hk_u : k ≤ p.1
      · have htake : (List.replicate p.1 HStep.U ++ List.replicate p.2 HStep.D).take k =
            (List.replicate p.1 HStep.U).take k :=
          List.take_append_of_le_length (by simp; omega)
        simp only [expandBlock, htake, List.take_replicate, List.map_replicate,
          HStep.toInt, List.sum_replicate, nsmul_eq_mul, mul_one, Nat.min_eq_left hk_u]
        linarith [Int.natCast_nonneg k]
      · push Not at hk_u
        have htake : (List.replicate p.1 HStep.U ++ List.replicate p.2 HStep.D).take k =
            List.replicate p.1 HStep.U ++
            (List.replicate p.2 HStep.D).take (k - p.1) := by
          rw [List.take_append, List.take_replicate]
          simp only [List.length_replicate, Nat.min_eq_right (by omega : p.1 ≤ k)]
        simp only [expandBlock, htake, List.map_append, List.sum_append,
          List.map_replicate, HStep.toInt, List.sum_replicate, nsmul_eq_mul, mul_one,
          List.take_replicate]
        have hdisp := hpartial 1 (by omega) (by simp)
        simp only [partialDisplacement, displacement, List.take_succ_cons,
          List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero] at hdisp
        have hmin : (↑(min (k - p.1) p.2) : ℤ) ≤ (p.2 : ℤ) := by
          exact_mod_cast Nat.min_le_right _ _
        linarith
    · push Not at hk'
      rw [List.take_append, List.map_append, List.sum_append,
        List.take_of_length_le (by omega)]
      rw [expandBlock_toInt_sum]
      have hbase' : 0 ≤ base + ((p.1 : ℤ) - (p.2 : ℤ)) := by
        have hdisp := hpartial 1 (by omega) (by simp)
        simp only [partialDisplacement, displacement, List.take_succ_cons,
          List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero] at hdisp
        linarith
      have hpartial' : ∀ j, 1 ≤ j → j ≤ w'.length →
          0 ≤ (base + ((p.1 : ℤ) - (p.2 : ℤ))) + partialDisplacement w' j := by
        intro j hj1 hj2
        have := hpartial (j + 1) (by omega) (by simp; omega)
        simp only [partialDisplacement, List.take_succ_cons] at this ⊢
        simp only [displacement, List.map_cons, List.sum_cons] at this
        rw [displacement]; linarith
      have hk_tail : k - (expandBlock p).length ≤ (expandBlocks w').length := by
        change k - _ ≤ (List.flatMap expandBlock w').length
        have : (expandBlock p ++ List.flatMap expandBlock w').length =
            (expandBlock p).length + (List.flatMap expandBlock w').length :=
          List.length_append
        omega
      have ih_applied := ih (base + ((p.1 : ℤ) - (p.2 : ℤ))) hbase' hpartial'
        (k - (expandBlock p).length) hk_tail
      have : expandBlocks w' = List.flatMap expandBlock w' := rfl
      rw [this] at ih_applied
      linarith

theorem walk_exists_sufficiency
    (w : List (ℕ × ℕ)) (lam : YoungDiagram) (n : ℕ)
    (hn : lam.card = n) (hvalid : IsValidWord w n) :
    Nonempty (HasseWalk (expandBlocks w) ⊥ lam) := by
  apply walk_from_bot_exists
  · rw [expandBlocks_toInt_sum, hn]; exact hvalid.1.symm
  · intro k hk
    have := expandBlocks_partial_nonneg_aux w 0 (le_refl _)
      (fun j hj1 hj2 => by simp only [zero_add]; exact hvalid.2 j hj1 hj2) k hk
    simp only [zero_add] at this; exact this

theorem valid_word_iff_walk_exists (w : List (ℕ × ℕ)) (lam : YoungDiagram) (n : ℕ)
    (hn : lam.card = n) :
    Nonempty (HasseWalk (expandBlocks w) ⊥ lam) ↔ IsValidWord w n :=
  ⟨fun ⟨walk⟩ => walk_exists_necessity w lam n hn walk,
   fun hvalid => walk_exists_sufficiency w lam n hn hvalid⟩

end HasseWalks
