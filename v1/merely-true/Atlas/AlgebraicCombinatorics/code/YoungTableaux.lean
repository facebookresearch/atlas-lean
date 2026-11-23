/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic

noncomputable section

open scoped Classical
open Finset

namespace YoungDiagram

theorem rowLen_eq_zero_of_colLen_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  have hpos : 0 < μ.rowLen i := Nat.pos_of_ne_zero h
  have : (i, 0) ∈ μ := mem_iff_lt_rowLen.mpr hpos
  rw [mem_iff_lt_colLen] at this
  omega

theorem rowLen_pos_of_lt_colLen (μ : YoungDiagram) {i : ℕ} (hi : i < μ.colLen 0) :
    0 < μ.rowLen i := by
  have : (i, 0) ∈ μ := mem_iff_lt_colLen.mpr hi
  exact mem_iff_lt_rowLen.mp this

lemma rowLen_antitone (μ : YoungDiagram) : Antitone μ.rowLen := by
  intro i j hij
  by_contra hc; push Not at hc
  have h1 : (j, μ.rowLen i) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
  have h2 : (i, μ.rowLen i) ∈ μ :=
    μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hij, le_rfl⟩) h1
  rw [mem_iff_lt_rowLen] at h2; omega

lemma rowLen_gt_of_lt_addable (μ : YoungDiagram) {i : ℕ}
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) {c : ℕ} (hc : c < i) :
    μ.rowLen c > μ.rowLen i := by
  rcases hadd with rfl | h
  · omega
  · exact lt_of_lt_of_le h (rowLen_antitone μ (by omega))

def addableRows (μ : YoungDiagram) : Finset ℕ :=
  (Finset.range (μ.colLen 0 + 1)).filter
    (fun i => i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i)

def removableRows (μ : YoungDiagram) : Finset ℕ :=
  (Finset.range (μ.colLen 0)).filter
    (fun i => i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1))

theorem removableRow_succ_addable (μ : YoungDiagram) {i : ℕ}
    (hi : i ∈ μ.removableRows) : i + 1 ∈ μ.addableRows := by
  simp only [removableRows, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hlt, hstep⟩ := hi
  simp only [addableRows, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, ?_⟩
  right
  simp only [Nat.add_sub_cancel]
  rcases hstep with heq | hgt
  · rw [heq, rowLen_eq_zero_of_colLen_le μ (le_refl _)]
    exact rowLen_pos_of_lt_colLen μ hlt
  · exact hgt

theorem zero_mem_addableRows (μ : YoungDiagram) : 0 ∈ μ.addableRows := by
  unfold addableRows
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Or.inl rfl⟩

theorem addableRow_pos_of_removable (μ : YoungDiagram) {i : ℕ}
    (hi : i ∈ μ.addableRows) (hpos : 0 < i) : i - 1 ∈ μ.removableRows := by
  simp only [addableRows, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨_, hstep⟩ := hi
  rcases hstep with heq | hgt
  · omega
  · simp only [removableRows, Finset.mem_filter, Finset.mem_range]
    have hrowpos : 0 < μ.rowLen (i - 1) := by omega
    have hlt2 : i - 1 < μ.colLen 0 := by
      have : (i - 1, 0) ∈ μ := mem_iff_lt_rowLen.mpr hrowpos
      exact mem_iff_lt_colLen.mp this
    refine ⟨hlt2, Or.inr ?_⟩
    rwa [Nat.sub_add_cancel hpos]

theorem addableRows_eq (μ : YoungDiagram) :
    μ.addableRows = {0} ∪ μ.removableRows.image (· + 1) := by
  ext i
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
  constructor
  · intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · left; rfl
    · right
      exact ⟨i - 1, addableRow_pos_of_removable μ hi hpos, by omega⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact zero_mem_addableRows μ
    · exact removableRow_succ_addable μ hj

theorem disjoint_zero_image_succ_removable (μ : YoungDiagram) :
    Disjoint ({0} : Finset ℕ) (μ.removableRows.image (· + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_singleton] at hx
  subst hx
  simp only [Finset.mem_image] at hx'
  obtain ⟨_, _, h⟩ := hx'
  omega

theorem injOn_succ_removableRows (μ : YoungDiagram) :
    Set.InjOn (· + 1 : ℕ → ℕ) (μ.removableRows : Set ℕ) := by
  intro a _ b _ hab
  simpa using hab

theorem card_addableRows_eq_card_removableRows_succ (μ : YoungDiagram) :
    μ.addableRows.card = μ.removableRows.card + 1 := by
  rw [addableRows_eq,
    Finset.card_union_of_disjoint (disjoint_zero_image_succ_removable μ),
    Finset.card_singleton,
    Finset.card_image_of_injOn (injOn_succ_removableRows μ)]
  omega

noncomputable def addCell (μ : YoungDiagram) (i : ℕ)
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) : YoungDiagram :=
  ⟨μ.cells ∪ {(i, μ.rowLen i)}, by
    intro ⟨a, b⟩ ⟨c, d⟩ hle hmem
    simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
               Finset.mem_coe] at hmem ⊢
    rcases hmem with h | h
    · left; exact μ.isLowerSet hle (Finset.mem_coe.mpr h)
    · rw [h] at hle; simp only [Prod.le_def] at hle; obtain ⟨hci, hdi⟩ := hle
      by_cases hc_lt : c < i
      · left; exact Finset.mem_coe.mpr (mem_iff_lt_rowLen.mpr
          (lt_of_le_of_lt hdi (rowLen_gt_of_lt_addable μ hadd hc_lt)))
      · by_cases hd_lt : d < μ.rowLen i
        · left; exact Finset.mem_coe.mpr (mem_iff_lt_rowLen.mpr
            (lt_of_lt_of_le hd_lt (rowLen_antitone μ (by omega))))
        · right; exact Prod.mk_inj.mpr ⟨by omega, by omega⟩⟩

noncomputable def removeCell (μ : YoungDiagram) (i : ℕ)
    (hrem : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1)) : YoungDiagram :=
  ⟨μ.cells.erase (i, μ.rowLen i - 1), by
    intro ⟨a, b⟩ ⟨c, d⟩ hle hmem
    simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe] at hmem ⊢
    obtain ⟨hmem_in, hmem_ne⟩ := hmem
    refine ⟨μ.isLowerSet hle (Finset.mem_coe.mpr hmem_in), fun heq => ?_⟩
    rw [heq] at hle; simp only [Prod.le_def] at hle; obtain ⟨hia, hrlb⟩ := hle
    have hmem_mu := (μ.mem_cells (a, b)).mp hmem_in
    rw [mem_iff_lt_rowLen] at hmem_mu
    have ha_eq : a = i := by
      by_contra ha_ne
      have h1 : μ.rowLen a ≤ μ.rowLen (i + 1) := rowLen_antitone μ (by omega)
      rcases hrem with h | h
      · have := rowLen_eq_zero_of_colLen_le μ (by omega : μ.colLen 0 ≤ i + 1); omega
      · omega
    rw [ha_eq] at hmem_mu
    exact hmem_ne (Prod.mk_inj.mpr ⟨ha_eq, by omega⟩)⟩

noncomputable def coversUp (μ : YoungDiagram) : Finset YoungDiagram :=
  μ.addableRows.image (fun i =>
    if h : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i then μ.addCell i h else μ)

noncomputable def coversDown (μ : YoungDiagram) : Finset YoungDiagram :=
  μ.removableRows.image (fun i =>
    if h : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1) then μ.removeCell i h else μ)

noncomputable def raisingOp (lam : YoungDiagram) : YoungDiagram →₀ ℤ :=
  lam.coversUp.sum (fun σ => Finsupp.single σ 1)

noncomputable def loweringOp (lam : YoungDiagram) : YoungDiagram →₀ ℤ :=
  lam.coversDown.sum (fun ν => Finsupp.single ν 1)

noncomputable def DU_apply (lam mu : YoungDiagram) : ℤ :=
  lam.coversUp.sum (fun σ => (loweringOp σ) mu)

noncomputable def UD_apply (lam mu : YoungDiagram) : ℤ :=
  lam.coversDown.sum (fun ν => (raisingOp ν) mu)

noncomputable def DUCoeff (lam mu : YoungDiagram) : ℕ :=
  (lam.coversUp.filter (fun σ => mu ∈ σ.coversDown)).card

noncomputable def UDCoeff (lam mu : YoungDiagram) : ℕ :=
  (lam.coversDown.filter (fun ρ => mu ∈ ρ.coversUp)).card

def DUCoeff_cases (lam mu : YoungDiagram) : ℕ :=
  if lam = mu then lam.addableRows.card
  else if (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 then 1
  else 0

def UDCoeff_cases (lam mu : YoungDiagram) : ℕ :=
  if lam = mu then lam.removableRows.card
  else if (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 then 1
  else 0


lemma addCell_cells (μ : YoungDiagram) (i : ℕ) (h : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) :
    (μ.addCell i h).cells = μ.cells ∪ {(i, μ.rowLen i)} :=
  rfl


lemma mem_addableRows_of_mem (μ : YoungDiagram) {i : ℕ} (hi : i ∈ μ.addableRows) :
    i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i := by
  simp only [addableRows, Finset.mem_filter, Finset.mem_range] at hi; exact hi.2


lemma mem_addCell_iff (μ : YoungDiagram) (i : ℕ) (h : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i)
    (a b : ℕ) : (a, b) ∈ μ.addCell i h ↔ (a, b) ∈ μ ∨ (a = i ∧ b = μ.rowLen i) := by
  simp only [addCell, mem_mk, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq, mem_cells]

lemma rowLen_addCell_same (μ : YoungDiagram) (i : ℕ) (h : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) :
    (μ.addCell i h).rowLen i = μ.rowLen i + 1 := by
  have h1 : (i, μ.rowLen i) ∈ μ.addCell i h := by
    rw [mem_addCell_iff]; right; exact ⟨rfl, rfl⟩
  have h2 : (i, μ.rowLen i + 1) ∉ μ.addCell i h := by
    rw [mem_addCell_iff]; intro h; rcases h with h | ⟨_, h⟩
    · rw [mem_iff_lt_rowLen] at h; omega
    · omega
  rw [mem_iff_lt_rowLen] at h1
  have h3 : ¬ (μ.rowLen i + 1 < (μ.addCell i h).rowLen i) := by
    intro hlt; exact h2 (mem_iff_lt_rowLen.mpr hlt)
  omega

lemma rowLen_addCell_ne (μ : YoungDiagram) (i j : ℕ) (h : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i)
    (hne : j ≠ i) : (μ.addCell i h).rowLen j = μ.rowLen j := by
  apply le_antisymm
  · by_contra hlt; simp only [not_le] at hlt
    have hc : (j, μ.rowLen j) ∈ μ.addCell i h := mem_iff_lt_rowLen.mpr (by omega)
    rw [mem_addCell_iff] at hc
    rcases hc with hc | ⟨rfl, _⟩
    · rw [mem_iff_lt_rowLen] at hc; omega
    · exact absurd rfl hne
  · by_contra hlt; simp only [not_le] at hlt
    have hc : (j, (μ.addCell i h).rowLen j) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
    have hc2 : (j, (μ.addCell i h).rowLen j) ∈ μ.addCell i h := by
      rw [mem_addCell_iff]; left; exact hc
    rw [mem_iff_lt_rowLen] at hc2; omega


lemma removeCell_addCell_same (μ : YoungDiagram) (i : ℕ)
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i)
    (hrem : i + 1 = (μ.addCell i hadd).colLen 0 ∨
            (μ.addCell i hadd).rowLen i > (μ.addCell i hadd).rowLen (i + 1)) :
    (μ.addCell i hadd).removeCell i hrem = μ := by
  ext ⟨a, b⟩
  simp only [removeCell, Finset.mem_erase, mem_cells,
             addCell_cells, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, hmem | hmem⟩
    · exact hmem
    · exfalso
      rw [Prod.mk.injEq] at hmem; obtain ⟨rfl, rfl⟩ := hmem
      apply hne
      rw [Prod.mk.injEq]
      exact ⟨rfl, by rw [rowLen_addCell_same]; omega⟩
  · intro hmem
    refine ⟨?_, Or.inl hmem⟩
    intro hne
    rw [Prod.mk.injEq] at hne; obtain ⟨rfl, hb⟩ := hne
    rw [rowLen_addCell_same] at hb
    have := (mem_iff_lt_rowLen).mp hmem; omega


lemma removableRow_of_addCell (μ : YoungDiagram) (i : ℕ)
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) :
    i ∈ (μ.addCell i hadd).removableRows := by
  simp only [removableRows, Finset.mem_filter, Finset.mem_range]
  constructor
  · rw [← mem_iff_lt_colLen]; rw [mem_addCell_iff]
    by_cases hrl : 0 < μ.rowLen i
    · left; exact mem_iff_lt_rowLen.mpr hrl
    · right; exact ⟨rfl, by omega⟩
  · right; rw [rowLen_addCell_same, rowLen_addCell_ne μ i (i + 1) hadd (by omega)]
    have hanti : μ.rowLen (i + 1) ≤ μ.rowLen i := rowLen_antitone μ (Nat.le_succ i)
    omega


lemma mem_removableRows_of_mem (μ : YoungDiagram) {i : ℕ} (hi : i ∈ μ.removableRows) :
    i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1) := by
  simp only [removableRows, Finset.mem_filter, Finset.mem_range] at hi; exact hi.2


lemma self_mem_coversDown_addCell (μ : YoungDiagram) (i : ℕ)
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) :
    μ ∈ (μ.addCell i hadd).coversDown := by
  unfold coversDown; rw [Finset.mem_image]
  exact ⟨i, removableRow_of_addCell μ i hadd, by
    have hrem := mem_removableRows_of_mem _ (removableRow_of_addCell μ i hadd)
    simp only [dif_pos hrem]; exact removeCell_addCell_same μ i hadd hrem⟩


lemma addCell_injective (μ : YoungDiagram) {i j : ℕ}
    (hi : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i)
    (hj : j = 0 ∨ μ.rowLen (j - 1) > μ.rowLen j)
    (heq : μ.addCell i hi = μ.addCell j hj) : i = j := by
  by_contra hne
  have h1 : (i, μ.rowLen i) ∈ (μ.addCell j hj).cells := by
    rw [← heq, addCell_cells]; exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
  rw [addCell_cells] at h1
  simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at h1
  rcases h1 with hmem | ⟨rfl, _⟩
  · rw [mem_cells, mem_iff_lt_rowLen] at hmem; omega
  · exact hne rfl


lemma DUCoeff_self_eq_card_coversUp (lam : YoungDiagram) :
    (lam.coversUp.filter (fun σ => lam ∈ σ.coversDown)).card = lam.coversUp.card := by
  congr 1; ext σ; simp only [Finset.mem_filter, and_iff_left_iff_imp]
  intro hσ; unfold coversUp at hσ; rw [Finset.mem_image] at hσ
  obtain ⟨i, hi, hσ_eq⟩ := hσ
  have hadd := mem_addableRows_of_mem lam hi
  simp only [dif_pos hadd] at hσ_eq
  rw [← hσ_eq]; exact self_mem_coversDown_addCell lam i hadd


lemma card_coversUp_eq_card_addableRows (μ : YoungDiagram) :
    μ.coversUp.card = μ.addableRows.card := by
  unfold coversUp; rw [Finset.card_image_of_injOn]
  intro i hi j hj heq
  have hadd_i := mem_addableRows_of_mem μ hi
  have hadd_j := mem_addableRows_of_mem μ hj
  simp only [dif_pos hadd_i, dif_pos hadd_j] at heq
  exact addCell_injective μ hadd_i hadd_j heq


lemma removeCell_cells_eq (μ : YoungDiagram) (i : ℕ)
    (h : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1)) :
    (μ.removeCell i h).cells = μ.cells.erase (i, μ.rowLen i - 1) := rfl


lemma mem_removeCell_iff (μ : YoungDiagram) (i : ℕ)
    (h : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1))
    (a b : ℕ) : (a, b) ∈ μ.removeCell i h ↔ (a, b) ∈ μ ∧ (a, b) ≠ (i, μ.rowLen i - 1) := by
  simp only [removeCell, mem_mk, Finset.mem_erase, mem_cells, ne_eq, and_comm]

lemma rowLen_removeCell_same (μ : YoungDiagram) (i : ℕ)
    (h : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1)) :
    (μ.removeCell i h).rowLen i = μ.rowLen i - 1 := by
  have hpos : 0 < μ.rowLen i := by
    rcases h with h | h
    · exact rowLen_pos_of_lt_colLen μ (by omega)
    · omega
  have h2 : (i, μ.rowLen i - 1) ∉ μ.removeCell i h := by
    rw [mem_removeCell_iff]; push Not; intro _; rfl
  have h_upper : ¬ (μ.rowLen i - 1 < (μ.removeCell i h).rowLen i) := by
    intro hlt; exact h2 (mem_iff_lt_rowLen.mpr hlt)
  by_cases hrl : μ.rowLen i - 1 = 0
  · have h3 : (μ.removeCell i h).rowLen i = 0 := by
      by_contra hne
      have hmem : (i, 0) ∈ μ.removeCell i h := mem_iff_lt_rowLen.mpr (by omega)
      rw [mem_removeCell_iff] at hmem
      obtain ⟨_, hne2⟩ := hmem
      apply hne2; rw [Prod.mk.injEq]; exact ⟨rfl, by omega⟩
    omega
  · have h1 : (i, μ.rowLen i - 1 - 1) ∈ μ.removeCell i h := by
      rw [mem_removeCell_iff]; constructor
      · exact mem_iff_lt_rowLen.mpr (by omega)
      · intro heq; rw [Prod.mk.injEq] at heq; omega
    rw [mem_iff_lt_rowLen] at h1; omega

lemma rowLen_removeCell_ne (μ : YoungDiagram) (i j : ℕ)
    (h : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1))
    (hne : j ≠ i) : (μ.removeCell i h).rowLen j = μ.rowLen j := by
  apply le_antisymm
  · by_contra hlt; simp only [not_le] at hlt
    have hc : (j, μ.rowLen j) ∈ μ.removeCell i h := mem_iff_lt_rowLen.mpr (by omega)
    rw [mem_removeCell_iff] at hc
    obtain ⟨hc1, _⟩ := hc
    rw [mem_iff_lt_rowLen] at hc1; omega
  · by_contra hlt; simp only [not_le] at hlt
    have hc : (j, (μ.removeCell i h).rowLen j) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
    have hc2 : (j, (μ.removeCell i h).rowLen j) ∈ μ.removeCell i h := by
      rw [mem_removeCell_iff]; refine ⟨hc, ?_⟩
      intro heq; rw [Prod.mk.injEq] at heq; exact absurd heq.1 hne
    rw [mem_iff_lt_rowLen] at hc2; omega


lemma addCell_removeCell_same (μ : YoungDiagram) (i : ℕ)
    (hrem : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1))
    (hadd : i = 0 ∨ (μ.removeCell i hrem).rowLen (i - 1) > (μ.removeCell i hrem).rowLen i) :
    (μ.removeCell i hrem).addCell i hadd = μ := by
  ext ⟨a, b⟩
  simp only [mem_addCell_iff, mem_removeCell_iff, mem_cells]
  rw [rowLen_removeCell_same]
  constructor
  · rintro (⟨hmem, _⟩ | ⟨rfl, rfl⟩)
    · exact hmem
    · exact mem_iff_lt_rowLen.mpr (by
        rcases hrem with h | h
        · exact Nat.sub_lt (rowLen_pos_of_lt_colLen μ (by omega)) Nat.one_pos
        · omega)

  · intro hmem
    by_cases heq : a = i ∧ b = μ.rowLen i - 1
    · obtain ⟨rfl, rfl⟩ := heq; right; exact ⟨rfl, rfl⟩
    · left; refine ⟨hmem, ?_⟩
      intro habs; rw [Prod.mk.injEq] at habs; exact heq habs


lemma addableRow_of_removeCell (μ : YoungDiagram) (i : ℕ)
    (hrem : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1)) :
    i ∈ (μ.removeCell i hrem).addableRows := by
  simp only [addableRows, Finset.mem_filter, Finset.mem_range]
  constructor
  ·
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · omega
    · have hrowpos : 0 < μ.rowLen (i - 1) := by
        rcases hrem with h | h
        · exact rowLen_pos_of_lt_colLen μ (by omega)
        · have := rowLen_antitone μ (show i - 1 ≤ i by omega); omega
      have hmem : (i - 1, 0) ∈ μ.removeCell i hrem := by
        rw [mem_removeCell_iff]; constructor
        · exact mem_iff_lt_rowLen.mpr hrowpos
        · intro heq; rw [Prod.mk.injEq] at heq; omega
      have : i - 1 < (μ.removeCell i hrem).colLen 0 := mem_iff_lt_colLen.mp hmem
      omega
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · left; rfl
    · right
      rw [rowLen_removeCell_ne μ i (i - 1) hrem (by omega),
          rowLen_removeCell_same μ i hrem]
      have := rowLen_antitone μ (show i - 1 ≤ i by omega)
      have hpos2 : 0 < μ.rowLen i := by
        rcases hrem with h | h
        · exact rowLen_pos_of_lt_colLen μ (by omega)
        · omega
      omega


lemma self_mem_coversUp_removeCell (μ : YoungDiagram) (i : ℕ)
    (hrem : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1)) :
    μ ∈ (μ.removeCell i hrem).coversUp := by
  unfold coversUp; rw [Finset.mem_image]
  exact ⟨i, addableRow_of_removeCell μ i hrem, by
    have hadd := mem_addableRows_of_mem _ (addableRow_of_removeCell μ i hrem)
    simp only [dif_pos hadd]; exact addCell_removeCell_same μ i hrem hadd⟩


lemma removeCell_injective (μ : YoungDiagram) {i j : ℕ}
    (hi : i + 1 = μ.colLen 0 ∨ μ.rowLen i > μ.rowLen (i + 1))
    (hj : j + 1 = μ.colLen 0 ∨ μ.rowLen j > μ.rowLen (j + 1))
    (heq : μ.removeCell i hi = μ.removeCell j hj) : i = j := by
  by_contra hne

  have hpos : 0 < μ.rowLen i := by
    rcases hi with h | h
    · exact rowLen_pos_of_lt_colLen μ (by omega)
    · omega

  have hmem_j : (i, μ.rowLen i - 1) ∈ μ.removeCell j hj := by
    rw [mem_removeCell_iff]; constructor
    · exact mem_iff_lt_rowLen.mpr (by omega)
    · intro heq2; rw [Prod.mk.injEq] at heq2; exact hne heq2.1

  have hnmem_i : (i, μ.rowLen i - 1) ∉ μ.removeCell i hi := by
    rw [mem_removeCell_iff]; push Not; intro _; rfl
  rw [heq] at hnmem_i
  exact hnmem_i hmem_j


end YoungDiagram

theorem YoungDiagram.symm_diff_of_intermediate (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (σ : YoungDiagram) (hσ_up : σ ∈ lam.coversUp) (hmu_down : mu ∈ σ.coversDown) :
    (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 := by
  open YoungDiagram in

  unfold coversUp at hσ_up; rw [Finset.mem_image] at hσ_up
  obtain ⟨j, hj_mem, hσ_eq⟩ := hσ_up
  have hadd_j := mem_addableRows_of_mem lam hj_mem
  simp only [dif_pos hadd_j] at hσ_eq

  unfold coversDown at hmu_down; rw [Finset.mem_image] at hmu_down
  obtain ⟨k, hk_mem, hmu_eq⟩ := hmu_down
  have hrem_k := mem_removableRows_of_mem σ hk_mem
  simp only [dif_pos hrem_k] at hmu_eq

  subst hσ_eq

  have hjk : j ≠ k := by
    intro hjk_eq; subst hjk_eq
    have := removeCell_addCell_same lam j hadd_j hrem_k
    rw [this] at hmu_eq
    exact hne hmu_eq

  have hrlk_eq : (lam.addCell j hadd_j).rowLen k = lam.rowLen k :=
    rowLen_addCell_ne lam j k hadd_j (Ne.symm hjk)

  have hk_mem_rem : k ∈ (lam.addCell j hadd_j).removableRows := hk_mem
  have hrowk_pos : 0 < lam.rowLen k := by
    have : 0 < (lam.addCell j hadd_j).rowLen k := by
      simp only [removableRows, Finset.mem_filter, Finset.mem_range] at hk_mem_rem
      exact rowLen_pos_of_lt_colLen _ hk_mem_rem.1
    rwa [hrlk_eq] at this

  have hj_not_in_lam : (j, lam.rowLen j) ∉ lam.cells := by
    rw [mem_cells]; intro h
    rw [mem_iff_lt_rowLen] at h; omega

  have hk_in_lam : (k, lam.rowLen k - 1) ∈ lam.cells := by
    rw [mem_cells, mem_iff_lt_rowLen]; omega

  have mu_cells_eq : mu.cells = (lam.cells ∪ {(j, lam.rowLen j)}).erase (k, lam.rowLen k - 1) := by
    rw [← hmu_eq]; simp only [removeCell, addCell_cells]
    congr 1
    rw [hrlk_eq]

  have sdiff1 : mu.cells \ lam.cells = {(j, lam.rowLen j)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    rw [mu_cells_eq]
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, hmem | ⟨rfl, rfl⟩⟩, hnot⟩
      · exact absurd hmem hnot
      · exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨fun h => ?_, Or.inr ⟨rfl, rfl⟩⟩, hj_not_in_lam⟩
      rw [Prod.mk.injEq] at h; obtain ⟨rfl, hb⟩ := h
      exact absurd rfl hjk

  have sdiff2 : lam.cells \ mu.cells = {(k, lam.rowLen k - 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    rw [mu_cells_eq]
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hmem, hnot⟩


      by_contra h_ne
      apply hnot
      refine ⟨fun heq => h_ne ?_, Or.inl hmem⟩
      exact (Prod.mk.inj heq).elim And.intro

    · rintro ⟨rfl, rfl⟩
      refine ⟨hk_in_lam, ?_⟩
      intro ⟨hne_cell, _⟩
      exact hne_cell rfl

  rw [sdiff1, sdiff2]
  exact ⟨Finset.card_singleton _, Finset.card_singleton _⟩

namespace YoungDiagram

lemma sdiff_singleton_of_card_one (lam mu : YoungDiagram)
    (h : (mu.cells \ lam.cells).card = 1) :
    ∃ j, (mu.cells \ lam.cells) = {(j, lam.rowLen j)} ∧
      j ∈ lam.addableRows := by

  rw [Finset.card_eq_one] at h
  obtain ⟨⟨r, s⟩, hrs⟩ := h

  have hmem : (r, s) ∈ mu.cells \ lam.cells := by rw [hrs]; exact Finset.mem_singleton_self _
  rw [Finset.mem_sdiff] at hmem
  obtain ⟨hmu, hlam⟩ := hmem

  have hs_ge : lam.rowLen r ≤ s := by
    by_contra hlt
    push Not at hlt
    rw [mem_cells] at hlam
    exact hlam (mem_iff_lt_rowLen.mpr hlt)

  have hs_eq : s = lam.rowLen r := by
    rcases Nat.eq_or_lt_of_le hs_ge with h | h
    · exact h.symm
    ·

      have hmem_prev : (r, s - 1) ∈ mu.cells := by
        rw [mem_cells, mem_iff_lt_rowLen]
        rw [mem_cells] at hmu
        have := mem_iff_lt_rowLen.mp hmu
        omega

      have hne : (r, s - 1) ≠ (r, s) := by
        intro heq; rw [Prod.mk.injEq] at heq; omega
      have hnotin : (r, s - 1) ∉ mu.cells \ lam.cells := by
        rw [hrs]; simp only [Finset.mem_singleton]; exact hne

      rw [Finset.mem_sdiff, not_and_or] at hnotin
      rcases hnotin with h2 | h2
      · exact absurd hmem_prev h2
      · push Not at h2
        have := mem_iff_lt_rowLen.mp h2
        omega

  subst hs_eq
  refine ⟨r, hrs, ?_⟩

  simp only [addableRows, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, ?_⟩
  ·


    by_contra hge
    push Not at hge


    have hrl0 : lam.rowLen r = 0 := rowLen_eq_zero_of_colLen_le lam (by omega)

    have hmu_mem : (r, 0) ∈ mu := by
      rw [mem_cells] at hmu
      have hlt := mem_iff_lt_rowLen.mp hmu
      rw [hrl0] at hlt
      exact mem_iff_lt_rowLen.mpr (by omega)


    have hcol_in_mu : (lam.colLen 0, 0) ∈ mu := by
      rw [mem_iff_lt_rowLen]
      have : 0 < mu.rowLen r := mem_iff_lt_rowLen.mp hmu_mem
      exact lt_of_lt_of_le this (rowLen_antitone mu (by omega))

    have hcol_notin_lam : (lam.colLen 0, 0) ∉ lam.cells := by
      intro hmem2
      rw [mem_cells] at hmem2
      rw [mem_iff_lt_colLen] at hmem2
      omega

    have hcol_sdiff : (lam.colLen 0, 0) ∈ mu.cells \ lam.cells := by
      rw [Finset.mem_sdiff]
      exact ⟨(mem_cells _).mpr hcol_in_mu, hcol_notin_lam⟩


    rw [hrl0] at hrs


    have hne_r : (lam.colLen 0, (0 : ℕ)) ≠ (r, (0 : ℕ)) := by
      intro heq; rw [Prod.mk.injEq] at heq; omega

    rw [hrs] at hcol_sdiff
    rw [Finset.mem_singleton] at hcol_sdiff
    exact hne_r hcol_sdiff
  ·
    rcases Nat.eq_zero_or_pos r with rfl | hr_pos
    · left; rfl
    · right

      have hmem_above : (r - 1, lam.rowLen r) ∈ mu.cells := by
        rw [mem_cells, mem_iff_lt_rowLen]
        rw [mem_cells] at hmu
        have := mem_iff_lt_rowLen.mp hmu
        exact lt_of_lt_of_le this (rowLen_antitone mu (by omega))

      have hne2 : (r - 1, lam.rowLen r) ≠ (r, lam.rowLen r) := by
        intro heq; rw [Prod.mk.injEq] at heq; omega

      have hnotin2 : (r - 1, lam.rowLen r) ∉ mu.cells \ lam.cells := by
        rw [hrs]; simp only [Finset.mem_singleton]; exact hne2

      rw [Finset.mem_sdiff, not_and_or] at hnotin2
      rcases hnotin2 with h2 | h2
      · exact absurd hmem_above h2
      · push Not at h2
        exact mem_iff_lt_rowLen.mp h2

lemma addCell_mem_intermediate_filter (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hsymm : (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1)
    (j : ℕ) (hj : (mu.cells \ lam.cells) = {(j, lam.rowLen j)})
    (hjadd : j ∈ lam.addableRows) :
    lam.addCell j (mem_addableRows_of_mem lam hjadd) ∈
      lam.coversUp.filter (fun σ => mu ∈ σ.coversDown) := by
  have hadd := mem_addableRows_of_mem lam hjadd
  rw [Finset.mem_filter]
  constructor
  · simp only [coversUp, Finset.mem_image]
    exact ⟨j, hjadd, by simp only [dif_pos hadd]⟩
  ·
    obtain ⟨⟨k, t⟩, hkt⟩ := Finset.card_eq_one.mp hsymm.2
    have hkt_mem : (k, t) ∈ lam.cells \ mu.cells := by
      rw [hkt]; exact Finset.mem_singleton_self _
    rw [Finset.mem_sdiff] at hkt_mem
    obtain ⟨hklam, hkmu⟩ := hkt_mem
    have ht_eq : t = lam.rowLen k - 1 := by
      rw [mem_cells] at hklam
      have hlt := mem_iff_lt_rowLen.mp hklam
      rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hlt) with h | h
      · exact h
      · have hmem_next : (k, t + 1) ∈ lam.cells := by
          rw [mem_cells, mem_iff_lt_rowLen]; omega
        have hne_cell : (k, t + 1) ≠ (k, t) := by
          intro heq; rw [Prod.mk.injEq] at heq; omega
        have : (k, t + 1) ∉ lam.cells \ mu.cells := by
          rw [hkt]; simp only [Finset.mem_singleton]; exact hne_cell
        rw [Finset.mem_sdiff, not_and_or] at this
        rcases this with h2 | h2
        · exact absurd hmem_next h2
        · push Not at h2; rw [mem_cells] at h2
          have : (k, t) ∈ mu := by
            rw [mem_iff_lt_rowLen]; have := mem_iff_lt_rowLen.mp h2; omega
          exact absurd ((mem_cells _).mpr this) hkmu
    subst ht_eq
    have hjk : j ≠ k := by
      intro hjk_eq; subst hjk_eq
      have h1 : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
        rw [hj]; exact Finset.mem_singleton_self _
      rw [Finset.mem_sdiff] at h1
      have hj_mu : (j, lam.rowLen j) ∈ mu.cells := h1.1
      have : (j, lam.rowLen j - 1) ∈ mu := by
        rw [mem_iff_lt_rowLen]
        rw [mem_cells] at hj_mu; have := mem_iff_lt_rowLen.mp hj_mu; omega
      exact absurd ((mem_cells _).mpr this) hkmu
    have hrlk_eq : (lam.addCell j hadd).rowLen k = lam.rowLen k :=
      rowLen_addCell_ne lam j k hadd (Ne.symm hjk)
    have hrowk_pos : 0 < lam.rowLen k := by
      rw [mem_cells] at hklam
      have := mem_iff_lt_rowLen.mp hklam; omega
    have hk_rem : k ∈ (lam.addCell j hadd).removableRows := by
      simp only [removableRows, Finset.mem_filter, Finset.mem_range]
      constructor
      · have : (k, 0) ∈ lam.addCell j hadd := by
          rw [mem_addCell_iff]; left; exact mem_iff_lt_rowLen.mpr hrowk_pos
        exact mem_iff_lt_colLen.mp this
      · right; rw [hrlk_eq]
        by_cases hjk1 : j = k + 1
        · subst hjk1
          rw [rowLen_addCell_same]
          rcases hadd with h0 | hadd_drop
          · omega
          · simp only [Nat.add_sub_cancel] at hadd_drop
            by_contra hle
            push Not at hle
            have hcell_eq : lam.rowLen k - 1 = lam.rowLen (k + 1) := by omega
            have hj_in_mu : (k + 1, lam.rowLen (k + 1)) ∈ mu.cells := by
              have : (k + 1, lam.rowLen (k + 1)) ∈ mu.cells \ lam.cells := by
                rw [hj]; exact Finset.mem_singleton_self _
              exact (Finset.mem_sdiff.mp this).1
            have hk_in_mu : (k, lam.rowLen (k + 1)) ∈ mu := by
              rw [mem_iff_lt_rowLen]; rw [mem_cells] at hj_in_mu
              exact lt_of_lt_of_le (mem_iff_lt_rowLen.mp hj_in_mu) (rowLen_antitone mu (by omega))
            rw [hcell_eq] at hkmu
            exact hkmu ((mem_cells _).mpr hk_in_mu)
        · rw [rowLen_addCell_ne lam j (k + 1) hadd (Ne.symm hjk1)]
          by_contra hle
          push Not at hle
          have hmem_next : (k + 1, lam.rowLen k - 1) ∈ lam := by
            rw [mem_iff_lt_rowLen]; omega
          have hne_cell : (k + 1, lam.rowLen k - 1) ≠ (k, lam.rowLen k - 1) := by
            intro heq; rw [Prod.mk.injEq] at heq; omega
          have hnotin : (k + 1, lam.rowLen k - 1) ∉ lam.cells \ mu.cells := by
            rw [hkt]; simp only [Finset.mem_singleton]; exact hne_cell
          rw [Finset.mem_sdiff, not_and_or] at hnotin
          rcases hnotin with h2 | h2
          · exact absurd ((mem_cells _).mpr hmem_next) h2
          · push Not at h2; rw [mem_cells] at h2
            have : (k, lam.rowLen k - 1) ∈ mu := by
              rw [mem_iff_lt_rowLen]
              exact lt_of_lt_of_le (mem_iff_lt_rowLen.mp h2) (rowLen_antitone mu (by omega))
            exact absurd ((mem_cells _).mpr this) hkmu
    have hrem := mem_removableRows_of_mem _ hk_rem
    have mu_cells_eq : mu.cells =
        (lam.cells ∪ {(j, lam.rowLen j)}).erase (k, lam.rowLen k - 1) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro hmem
        refine ⟨fun heq => ?_, ?_⟩
        · rw [Prod.mk.injEq] at heq
          exact absurd hmem (heq.1 ▸ heq.2 ▸ hkmu)
        · by_cases hlam_ab : (a, b) ∈ lam.cells
          · left; exact hlam_ab
          · right
            have : (a, b) ∈ mu.cells \ lam.cells := Finset.mem_sdiff.mpr ⟨hmem, hlam_ab⟩
            rw [hj, Finset.mem_singleton] at this
            exact this
      · rintro ⟨hne_cell, hmem_lam | hab_eq⟩
        · by_contra hab_mu
          have : (a, b) ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hmem_lam, hab_mu⟩
          rw [hkt, Finset.mem_singleton] at this
          exact hne_cell this
        · rw [hab_eq]
          have : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
            rw [hj]; exact Finset.mem_singleton_self _
          exact (Finset.mem_sdiff.mp this).1
    simp only [coversDown, Finset.mem_image]
    refine ⟨k, hk_rem, ?_⟩
    simp only [dif_pos hrem]
    rw [YoungDiagram.ext_iff]
    rw [removeCell_cells_eq, addCell_cells, hrlk_eq]
    exact mu_cells_eq.symm

lemma intermediate_filter_unique (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hsymm : (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1)
    (j : ℕ) (hj : (mu.cells \ lam.cells) = {(j, lam.rowLen j)})
    (hjadd : j ∈ lam.addableRows)
    (σ : YoungDiagram)
    (hσ : σ ∈ lam.coversUp.filter (fun σ => mu ∈ σ.coversDown)) :
    σ = lam.addCell j (mem_addableRows_of_mem lam hjadd) := by
  have hadd := mem_addableRows_of_mem lam hjadd
  rw [Finset.mem_filter] at hσ
  obtain ⟨hσ_up, hmu_down⟩ := hσ

  simp only [coversUp, Finset.mem_image] at hσ_up
  obtain ⟨i, hi_mem, hσ_eq⟩ := hσ_up
  have hadd_i := mem_addableRows_of_mem lam hi_mem
  simp only [dif_pos hadd_i] at hσ_eq

  subst hσ_eq


  have hi_sdiff : (i, lam.rowLen i) ∈ mu.cells \ lam.cells := by


    simp only [coversDown, Finset.mem_image] at hmu_down
    obtain ⟨k, hk_mem, hmu_eq⟩ := hmu_down
    have hrem_k := mem_removableRows_of_mem _ hk_mem
    simp only [dif_pos hrem_k] at hmu_eq


    have hik : i ≠ k := by
      intro hik_eq; subst hik_eq
      have := removeCell_addCell_same lam i hadd_i hrem_k
      rw [this] at hmu_eq; exact hne hmu_eq

    have hi_in_sigma : (i, lam.rowLen i) ∈ (lam.addCell i hadd_i).cells := by
      rw [addCell_cells]; exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
    have hi_not_lam : (i, lam.rowLen i) ∉ lam.cells := by
      rw [mem_cells]; intro h
      rw [mem_iff_lt_rowLen] at h; omega

    have hi_in_mu : (i, lam.rowLen i) ∈ mu.cells := by
      rw [← hmu_eq, removeCell_cells_eq]
      rw [Finset.mem_erase]
      refine ⟨fun heq => ?_, hi_in_sigma⟩
      rw [Prod.mk.injEq] at heq; exact hik heq.1
    exact Finset.mem_sdiff.mpr ⟨hi_in_mu, hi_not_lam⟩

  rw [hj, Finset.mem_singleton, Prod.mk.injEq] at hi_sdiff
  obtain ⟨rfl, _⟩ := hi_sdiff

  rfl

end YoungDiagram

open YoungDiagram in
theorem YoungDiagram.intermediate_unique_of_symm_diff (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hsymm : (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1) :
    (lam.coversUp.filter (fun σ => mu ∈ σ.coversDown)).card = 1 := by

  obtain ⟨j, hj, hjadd⟩ := sdiff_singleton_of_card_one lam mu hsymm.1

  have hmem := addCell_mem_intermediate_filter lam mu hne hsymm j hj hjadd

  rw [Finset.card_eq_one]
  exact ⟨lam.addCell j (mem_addableRows_of_mem lam hjadd), Finset.ext fun σ => ⟨
    fun hσ => Finset.mem_singleton.mpr (intermediate_filter_unique lam mu hne hsymm j hj hjadd σ hσ),
    fun hσ => Finset.mem_singleton.mp hσ ▸ hmem⟩⟩

namespace YoungDiagram
open Finset


lemma no_intermediate_of_no_symm_diff (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hnsymm : ¬((mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1)) :
    (lam.coversUp.filter (fun σ => mu ∈ σ.coversDown)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ hσ hmu
  exact hnsymm (symm_diff_of_intermediate lam mu hne σ hσ hmu)


theorem DUCoeff_eq_cases (lam mu : YoungDiagram) :
    DUCoeff lam mu = DUCoeff_cases lam mu := by
  unfold DUCoeff DUCoeff_cases
  by_cases heq : lam = mu
  · subst heq; rw [if_pos rfl]
    rw [DUCoeff_self_eq_card_coversUp, card_coversUp_eq_card_addableRows]
  · rw [if_neg heq]
    split_ifs with hsymm
    · exact intermediate_unique_of_symm_diff lam mu heq hsymm
    · exact no_intermediate_of_no_symm_diff lam mu heq hsymm


lemma UDCoeff_self_eq_card_coversDown (lam : YoungDiagram) :
    (lam.coversDown.filter (fun ρ => lam ∈ ρ.coversUp)).card = lam.coversDown.card := by
  congr 1; ext ρ; simp only [Finset.mem_filter, and_iff_left_iff_imp]
  intro hρ; unfold coversDown at hρ; rw [Finset.mem_image] at hρ
  obtain ⟨i, hi, hρ_eq⟩ := hρ
  have hrem := mem_removableRows_of_mem lam hi
  simp only [dif_pos hrem] at hρ_eq
  rw [← hρ_eq]; exact self_mem_coversUp_removeCell lam i hrem


lemma card_coversDown_eq_card_removableRows (μ : YoungDiagram) :
    μ.coversDown.card = μ.removableRows.card := by
  unfold coversDown; rw [Finset.card_image_of_injOn]
  intro i hi j hj heq
  have hrem_i := mem_removableRows_of_mem μ hi
  have hrem_j := mem_removableRows_of_mem μ hj
  simp only [dif_pos hrem_i, dif_pos hrem_j] at heq
  exact removeCell_injective μ hrem_i hrem_j heq

end YoungDiagram


theorem YoungDiagram.symm_diff_of_intermediate_UD (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (ρ : YoungDiagram) (hρ_down : ρ ∈ lam.coversDown) (hmu_up : mu ∈ ρ.coversUp) :
    (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 := by
  open YoungDiagram in

  unfold coversDown at hρ_down; rw [Finset.mem_image] at hρ_down
  obtain ⟨k, hk_mem, hρ_eq⟩ := hρ_down
  have hrem_k := mem_removableRows_of_mem lam hk_mem
  simp only [dif_pos hrem_k] at hρ_eq

  unfold coversUp at hmu_up; rw [Finset.mem_image] at hmu_up
  obtain ⟨j, hj_mem, hmu_eq⟩ := hmu_up
  have hadd_j := mem_addableRows_of_mem ρ hj_mem
  simp only [dif_pos hadd_j] at hmu_eq

  subst hρ_eq

  have hjk : j ≠ k := by
    intro hjk_eq; subst hjk_eq
    have := addCell_removeCell_same lam j hrem_k hadd_j
    rw [this] at hmu_eq
    exact hne hmu_eq


  have hrlj_eq : (lam.removeCell k hrem_k).rowLen j = lam.rowLen j :=
    rowLen_removeCell_ne lam k j hrem_k hjk

  have hrowk_pos : 0 < lam.rowLen k := by
    rcases hrem_k with h | h
    · exact rowLen_pos_of_lt_colLen lam (by omega)
    · omega

  have hk_in_lam : (k, lam.rowLen k - 1) ∈ lam.cells := by
    rw [mem_cells, mem_iff_lt_rowLen]; omega

  have hj_not_in_lam : (j, lam.rowLen j) ∉ lam.cells := by
    rw [mem_cells]; intro h
    rw [mem_iff_lt_rowLen] at h; omega


  have mu_cells_eq : mu.cells = (lam.cells.erase (k, lam.rowLen k - 1)) ∪ {(j, lam.rowLen j)} := by
    rw [← hmu_eq]; simp only [addCell_cells, removeCell_cells_eq]
    congr 1
    simp only [hrlj_eq]

  have sdiff1 : mu.cells \ lam.cells = {(j, lam.rowLen j)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    rw [mu_cells_eq]
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, hmem⟩ | ⟨rfl, rfl⟩, hnot⟩
      · exact absurd hmem hnot
      · exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inr ⟨rfl, rfl⟩, hj_not_in_lam⟩

  have sdiff2 : lam.cells \ mu.cells = {(k, lam.rowLen k - 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    rw [mu_cells_eq]
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hmem, hnot⟩


      by_contra h_ne
      apply hnot
      by_cases hab : a = j ∧ b = lam.rowLen j
      · exact Or.inr hab
      · left
        refine ⟨?_, hmem⟩
        intro heq; rw [Prod.mk.injEq] at heq
        exact h_ne heq
    · rintro ⟨rfl, rfl⟩
      refine ⟨hk_in_lam, ?_⟩
      intro hmem
      rcases hmem with ⟨hne_cell, _⟩ | ⟨rfl, hb⟩
      · exact hne_cell rfl
      · exact hjk rfl
  rw [sdiff1, sdiff2]
  exact ⟨Finset.card_singleton _, Finset.card_singleton _⟩

namespace YoungDiagram
open Finset

lemma sdiff_singleton_of_card_one_UD (lam mu : YoungDiagram)
    (h : (lam.cells \ mu.cells).card = 1) :
    ∃ k, (lam.cells \ mu.cells) = {(k, lam.rowLen k - 1)} ∧
      k ∈ lam.removableRows := by
  rw [Finset.card_eq_one] at h
  obtain ⟨⟨r, s⟩, hrs⟩ := h
  have hmem : (r, s) ∈ lam.cells \ mu.cells := by rw [hrs]; exact Finset.mem_singleton_self _
  rw [Finset.mem_sdiff] at hmem
  obtain ⟨hlam, hmu⟩ := hmem

  have hs_lt : s < lam.rowLen r := by
    rw [mem_cells] at hlam; exact mem_iff_lt_rowLen.mp hlam
  have hs_eq : s = lam.rowLen r - 1 := by
    rcases Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt hs_lt) with h | h
    · exact h
    ·
      have hmem_next : (r, s + 1) ∈ lam.cells := by
        rw [mem_cells, mem_iff_lt_rowLen]; omega
      have hne_cell : (r, s + 1) ≠ (r, s) := by
        intro heq; rw [Prod.mk.injEq] at heq; omega
      have : (r, s + 1) ∉ lam.cells \ mu.cells := by
        rw [hrs]; simp only [Finset.mem_singleton]; exact hne_cell
      rw [Finset.mem_sdiff, not_and_or] at this
      rcases this with h2 | h2
      · exact absurd hmem_next h2
      · push Not at h2; rw [mem_cells] at h2
        have : (r, s) ∈ mu := by
          rw [mem_iff_lt_rowLen]; have := mem_iff_lt_rowLen.mp h2; omega
        exact absurd ((mem_cells _).mpr this) hmu
  subst hs_eq
  refine ⟨r, hrs, ?_⟩
  simp only [removableRows, Finset.mem_filter, Finset.mem_range]
  constructor
  ·
    rw [← mem_iff_lt_colLen]; rw [mem_cells] at hlam
    have := mem_iff_lt_rowLen.mp hlam
    exact mem_iff_lt_rowLen.mpr (by omega)
  ·

    by_contra habs
    push Not at habs
    obtain ⟨hne_col, hle⟩ := habs

    have hle' : lam.rowLen r ≤ lam.rowLen (r + 1) := by omega
    have hrlr_sub_lt : lam.rowLen r - 1 < lam.rowLen r := by
      rw [mem_cells] at hlam; exact mem_iff_lt_rowLen.mp hlam

    have hmem_below : (r + 1, lam.rowLen r - 1) ∈ lam := by
      rw [mem_iff_lt_rowLen]; omega
    have hne_cell : (r + 1, lam.rowLen r - 1) ≠ (r, lam.rowLen r - 1) := by
      intro heq; rw [Prod.mk.injEq] at heq; omega

    have hnotin : (r + 1, lam.rowLen r - 1) ∉ lam.cells \ mu.cells := by
      rw [hrs]; simp only [Finset.mem_singleton]; exact hne_cell
    rw [Finset.mem_sdiff, not_and_or] at hnotin
    rcases hnotin with h2 | h2
    · exact absurd ((mem_cells _).mpr hmem_below) h2
    ·
      push Not at h2; rw [mem_cells] at h2

      have : (r, lam.rowLen r - 1) ∈ mu := by
        rw [mem_iff_lt_rowLen]
        exact lt_of_lt_of_le (mem_iff_lt_rowLen.mp h2) (rowLen_antitone mu (by omega))
      exact absurd ((mem_cells _).mpr this) hmu

lemma removeCell_mem_intermediate_filter_UD (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hsymm : (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1)
    (k : ℕ) (hk : (lam.cells \ mu.cells) = {(k, lam.rowLen k - 1)})
    (hkrem : k ∈ lam.removableRows) :
    lam.removeCell k (mem_removableRows_of_mem lam hkrem) ∈
      lam.coversDown.filter (fun ρ => mu ∈ ρ.coversUp) := by
  have hrem := mem_removableRows_of_mem lam hkrem
  rw [Finset.mem_filter]
  constructor
  ·
    simp only [coversDown, Finset.mem_image]
    exact ⟨k, hkrem, by simp only [dif_pos hrem]⟩
  ·

    obtain ⟨j, hjt, hjadd_lam⟩ := sdiff_singleton_of_card_one lam mu hsymm.1

    have hjk : j ≠ k := by
      intro hjk_eq
      have h1 : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
        rw [hjt]; exact Finset.mem_singleton_self _
      rw [Finset.mem_sdiff] at h1
      have hj_mu : (j, lam.rowLen j) ∈ mu.cells := h1.1
      have : (j, lam.rowLen j - 1) ∈ mu := by
        rw [mem_iff_lt_rowLen]
        rw [mem_cells] at hj_mu; have := mem_iff_lt_rowLen.mp hj_mu; omega
      have hk_sdiff : (k, lam.rowLen k - 1) ∈ lam.cells \ mu.cells := by
        rw [hk]; exact Finset.mem_singleton_self _
      rw [Finset.mem_sdiff] at hk_sdiff
      rw [hjk_eq] at this
      exact hk_sdiff.2 ((mem_cells _).mpr this)

    have hrlj_eq : (lam.removeCell k hrem).rowLen j = lam.rowLen j :=
      rowLen_removeCell_ne lam k j hrem hjk

    have hj_add : j ∈ (lam.removeCell k hrem).addableRows := by
      simp only [addableRows, Finset.mem_filter, Finset.mem_range]
      constructor
      ·
        rcases Nat.eq_zero_or_pos j with rfl | hj_pos
        · omega
        · suffices (j - 1, 0) ∈ lam.removeCell k hrem by
            have := mem_iff_lt_colLen.mp this; omega
          rw [mem_removeCell_iff]
          constructor
          · have : j - 1 < lam.colLen 0 := by
              simp only [addableRows, Finset.mem_filter, Finset.mem_range] at hjadd_lam
              omega
            exact mem_iff_lt_rowLen.mpr (rowLen_pos_of_lt_colLen lam this)
          · intro heq; rw [Prod.mk.injEq] at heq
            obtain ⟨hjk1, h0eq⟩ := heq
            have hrlk_pos : 0 < lam.rowLen k := by
              rcases hrem with h | h
              · exact rowLen_pos_of_lt_colLen lam (by omega)
              · omega
            have hrlk1 : lam.rowLen k = 1 := by omega
            have hj_in_mu : (j, lam.rowLen j) ∈ mu.cells := by
              have : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
                rw [hjt]; exact Finset.mem_singleton_self _
              exact (Finset.mem_sdiff.mp this).1
            have hk_in_mu : (k, lam.rowLen j) ∈ mu := by
              rw [mem_iff_lt_rowLen]
              rw [mem_cells] at hj_in_mu
              exact lt_of_lt_of_le (mem_iff_lt_rowLen.mp hj_in_mu) (rowLen_antitone mu (by omega))
            have hrlj_le : lam.rowLen j ≤ 1 := by
              have := rowLen_antitone lam (show k ≤ j by omega); omega
            rcases Nat.eq_zero_or_pos (lam.rowLen j) with hrlj0 | hrlj_pos
            · rw [hrlj0] at hk_in_mu
              have hk0_not_mu : (k, lam.rowLen k - 1) ∉ mu.cells := by
                have : (k, lam.rowLen k - 1) ∈ lam.cells \ mu.cells := by
                  rw [hk]; exact Finset.mem_singleton_self _
                exact (Finset.mem_sdiff.mp this).2
              rw [hrlk1] at hk0_not_mu
              exact absurd ((mem_cells _).mpr hk_in_mu) hk0_not_mu
            · have hrlj1 : lam.rowLen j = 1 := by omega
              simp only [addableRows, Finset.mem_filter, Finset.mem_range] at hjadd_lam
              rcases hjadd_lam.2 with rfl | hdrop
              · omega
              · rw [hjk1, hrlk1, hrlj1] at hdrop; omega
      ·
        rcases Nat.eq_zero_or_pos j with rfl | hj_pos
        · left; rfl
        · right
          rw [hrlj_eq]
          by_cases hjk1 : j - 1 = k
          ·
            rw [hjk1, rowLen_removeCell_same lam k hrem]
            have hj_in_mu : (j, lam.rowLen j) ∈ mu.cells := by
              have : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
                rw [hjt]; exact Finset.mem_singleton_self _
              exact (Finset.mem_sdiff.mp this).1
            have hk_in_mu : (k, lam.rowLen j) ∈ mu := by
              rw [mem_iff_lt_rowLen]; rw [mem_cells] at hj_in_mu
              exact lt_of_lt_of_le (mem_iff_lt_rowLen.mp hj_in_mu) (rowLen_antitone mu (by omega))
            have hk_not_mu : (k, lam.rowLen k - 1) ∉ mu.cells := by
              have : (k, lam.rowLen k - 1) ∈ lam.cells \ mu.cells := by
                rw [hk]; exact Finset.mem_singleton_self _
              exact (Finset.mem_sdiff.mp this).2
            have : ¬ (lam.rowLen k - 1 < mu.rowLen k) := by
              intro hlt; exact hk_not_mu ((mem_cells _).mpr (mem_iff_lt_rowLen.mpr hlt))
            have : lam.rowLen j < mu.rowLen k := mem_iff_lt_rowLen.mp hk_in_mu
            omega
          ·
            rw [rowLen_removeCell_ne lam k (j - 1) hrem hjk1]
            have hj_in_mu : (j, lam.rowLen j) ∈ mu.cells := by
              have : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
                rw [hjt]; exact Finset.mem_singleton_self _
              exact (Finset.mem_sdiff.mp this).1
            have hmem_above : (j - 1, lam.rowLen j) ∈ mu := by
              rw [mem_iff_lt_rowLen]; rw [mem_cells] at hj_in_mu
              exact lt_of_lt_of_le (mem_iff_lt_rowLen.mp hj_in_mu) (rowLen_antitone mu (by omega))
            have hne' : (j - 1, lam.rowLen j) ≠ (j, lam.rowLen j) := by
              intro heq; rw [Prod.mk.injEq] at heq; omega
            have hnotin : (j - 1, lam.rowLen j) ∉ mu.cells \ lam.cells := by
              rw [hjt]; simp only [Finset.mem_singleton]; exact hne'
            rw [Finset.mem_sdiff, not_and_or] at hnotin
            rcases hnotin with h2 | h2
            · exact absurd ((mem_cells _).mpr hmem_above) h2
            · push Not at h2; exact mem_iff_lt_rowLen.mp h2
    have hadd_j := mem_addableRows_of_mem _ hj_add
    have mu_cells_eq : mu.cells =
        (lam.cells.erase (k, lam.rowLen k - 1)) ∪ {(j, lam.rowLen j)} := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro hmem
        by_cases hlam_ab : (a, b) ∈ lam.cells
        · left; refine ⟨fun heq => ?_, hlam_ab⟩
          have hk_sdiff : (k, lam.rowLen k - 1) ∈ lam.cells \ mu.cells := by
            rw [hk]; exact Finset.mem_singleton_self _
          rw [Finset.mem_sdiff] at hk_sdiff
          rw [heq] at hmem
          exact absurd hmem hk_sdiff.2
        · right
          have : (a, b) ∈ mu.cells \ lam.cells := Finset.mem_sdiff.mpr ⟨hmem, hlam_ab⟩
          rw [hjt, Finset.mem_singleton] at this
          exact this
      · rintro (⟨hne_cell, hmem_lam⟩ | hab_eq)
        · by_contra hab_mu
          have : (a, b) ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hmem_lam, hab_mu⟩
          rw [hk, Finset.mem_singleton] at this
          exact hne_cell this
        · rw [hab_eq]
          have : (j, lam.rowLen j) ∈ mu.cells \ lam.cells := by
            rw [hjt]; exact Finset.mem_singleton_self _
          exact (Finset.mem_sdiff.mp this).1
    simp only [coversUp, Finset.mem_image]
    refine ⟨j, hj_add, ?_⟩
    simp only [dif_pos hadd_j]
    rw [YoungDiagram.ext_iff]
    rw [addCell_cells, removeCell_cells_eq, hrlj_eq]
    exact mu_cells_eq.symm

lemma intermediate_filter_unique_UD (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hsymm : (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1)
    (k : ℕ) (hk : (lam.cells \ mu.cells) = {(k, lam.rowLen k - 1)})
    (hkrem : k ∈ lam.removableRows)
    (ρ : YoungDiagram)
    (hρ : ρ ∈ lam.coversDown.filter (fun ρ => mu ∈ ρ.coversUp)) :
    ρ = lam.removeCell k (mem_removableRows_of_mem lam hkrem) := by
  have hrem := mem_removableRows_of_mem lam hkrem
  rw [Finset.mem_filter] at hρ
  obtain ⟨hρ_down, hmu_up⟩ := hρ

  simp only [coversDown, Finset.mem_image] at hρ_down
  obtain ⟨i, hi_mem, hρ_eq⟩ := hρ_down
  have hrem_i := mem_removableRows_of_mem lam hi_mem
  simp only [dif_pos hrem_i] at hρ_eq
  subst hρ_eq


  have hi_sdiff : (i, lam.rowLen i - 1) ∈ lam.cells \ mu.cells := by
    simp only [coversUp, Finset.mem_image] at hmu_up
    obtain ⟨j, hj_mem, hmu_eq⟩ := hmu_up
    have hadd_j := mem_addableRows_of_mem _ hj_mem
    simp only [dif_pos hadd_j] at hmu_eq

    have hij : i ≠ j := by
      intro hij_eq; subst hij_eq
      have := addCell_removeCell_same lam i hrem_i hadd_j
      rw [this] at hmu_eq; exact hne hmu_eq

    have hi_in_lam : (i, lam.rowLen i - 1) ∈ lam.cells := by
      rw [mem_cells, mem_iff_lt_rowLen]
      have : 0 < lam.rowLen i := by
        rcases hrem_i with h | h
        · exact rowLen_pos_of_lt_colLen lam (by omega)
        · omega
      omega

    have hi_not_rem : (i, lam.rowLen i - 1) ∉ (lam.removeCell i hrem_i).cells := by
      rw [removeCell_cells_eq]; exact Finset.notMem_erase _ _

    have hi_not_mu : (i, lam.rowLen i - 1) ∉ mu.cells := by
      rw [← hmu_eq, addCell_cells]
      intro hmem
      rw [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with hmem | ⟨rfl, heq⟩
      · exact hi_not_rem hmem
      · exact hij rfl
    exact Finset.mem_sdiff.mpr ⟨hi_in_lam, hi_not_mu⟩

  rw [hk, Finset.mem_singleton, Prod.mk.injEq] at hi_sdiff
  obtain ⟨rfl, _⟩ := hi_sdiff
  rfl


theorem intermediate_unique_of_symm_diff_UD (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hsymm : (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1) :
    (lam.coversDown.filter (fun ρ => mu ∈ ρ.coversUp)).card = 1 := by
  obtain ⟨k, hk, hkrem⟩ := sdiff_singleton_of_card_one_UD lam mu hsymm.2
  have hmem := removeCell_mem_intermediate_filter_UD lam mu hne hsymm k hk hkrem
  rw [Finset.card_eq_one]
  exact ⟨lam.removeCell k (mem_removableRows_of_mem lam hkrem), Finset.ext fun ρ => ⟨
    fun hρ => Finset.mem_singleton.mpr (intermediate_filter_unique_UD lam mu hne hsymm k hk hkrem ρ hρ),
    fun hρ => Finset.mem_singleton.mp hρ ▸ hmem⟩⟩


lemma no_intermediate_of_no_symm_diff_UD (lam mu : YoungDiagram) (hne : lam ≠ mu)
    (hnsymm : ¬((mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1)) :
    (lam.coversDown.filter (fun ρ => mu ∈ ρ.coversUp)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ρ hρ hmu
  exact hnsymm (symm_diff_of_intermediate_UD lam mu hne ρ hρ hmu)


theorem UDCoeff_eq_cases (lam mu : YoungDiagram) :
    UDCoeff lam mu = UDCoeff_cases lam mu := by
  unfold UDCoeff UDCoeff_cases
  by_cases heq : lam = mu
  · subst heq; rw [if_pos rfl]
    rw [UDCoeff_self_eq_card_coversDown, card_coversDown_eq_card_removableRows]
  · rw [if_neg heq]
    split_ifs with hsymm
    · exact intermediate_unique_of_symm_diff_UD lam mu heq hsymm
    · exact no_intermediate_of_no_symm_diff_UD lam mu heq hsymm

@[simp]
theorem DUCoeff_self (lam : YoungDiagram) : DUCoeff lam lam = lam.addableRows.card := by
  rw [DUCoeff_eq_cases]; unfold DUCoeff_cases; exact if_pos rfl

@[simp]
theorem UDCoeff_self (lam : YoungDiagram) : UDCoeff lam lam = lam.removableRows.card := by
  rw [UDCoeff_eq_cases]; unfold UDCoeff_cases; exact if_pos rfl

theorem DUCoeff_eq_UDCoeff_of_ne (lam mu : YoungDiagram) (hne : lam ≠ mu) :
    DUCoeff lam mu = UDCoeff lam mu := by
  rw [DUCoeff_eq_cases, UDCoeff_eq_cases]
  have hDU : DUCoeff_cases lam mu =
      if (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 then 1 else 0 := by
    unfold DUCoeff_cases; exact if_neg hne
  have hUD : UDCoeff_cases lam mu =
      if (mu.cells \ lam.cells).card = 1 ∧ (lam.cells \ mu.cells).card = 1 then 1 else 0 := by
    unfold UDCoeff_cases; exact if_neg hne
  rw [hDU, hUD]

theorem young_commutation_coeff (lam mu : YoungDiagram) :
    (DUCoeff lam mu : ℤ) - (UDCoeff lam mu : ℤ) = if lam = mu then 1 else 0 := by
  by_cases heq : lam = mu
  ·
    subst heq
    rw [if_pos rfl, DUCoeff_self, UDCoeff_self]
    have h := card_addableRows_eq_card_removableRows_succ lam
    omega
  ·
    rw [if_neg heq]
    have h := DUCoeff_eq_UDCoeff_of_ne lam mu heq
    simp [h]

end YoungDiagram

end
