/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.OrderRaising
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

open Finset

set_option autoImplicit false

namespace BooleanCommutator

variable {n : ℕ}

def DU_coeff (i : ℕ) (x z : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun y : Finset (Fin n) =>
    y.card = i + 1 ∧ x ⊆ y ∧ z ⊆ y)).card

def UD_coeff (i : ℕ) (x z : Finset (Fin n)) : ℕ :=
  match i with
  | 0 => 0
  | i + 1 => (Finset.univ.filter (fun w : Finset (Fin n) =>
      w.card = i ∧ w ⊆ x ∧ w ⊆ z)).card

lemma card_supersets_insert (x : Finset (Fin n)) :
    (Finset.univ.filter (fun y : Finset (Fin n) =>
      y.card = x.card + 1 ∧ x ⊆ y)).card = n - x.card := by
  classical

  symm
  calc n - x.card
      = xᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]
    _ = (Finset.univ.filter (fun y : Finset (Fin n) =>
          y.card = x.card + 1 ∧ x ⊆ y)).card := by
        apply Finset.card_bij (fun a _ => insert a x)
        ·
          intro a ha
          simp only [mem_filter, mem_univ, true_and]
          rw [Finset.mem_compl] at ha
          exact ⟨Finset.card_insert_of_notMem ha, Finset.subset_insert a x⟩
        ·
          intro a₁ ha₁ a₂ _ h
          rw [Finset.mem_compl] at ha₁
          exact (Finset.insert_inj ha₁).mp h
        ·
          intro y hy
          simp only [mem_filter, mem_univ, true_and] at hy
          obtain ⟨hycard, hxy⟩ := hy
          have hsdiff_card : (y \ x).card = 1 := by
            rw [Finset.card_sdiff_of_subset hxy, hycard]; omega
          rw [Finset.card_eq_one] at hsdiff_card
          obtain ⟨a, ha⟩ := hsdiff_card
          have ha_mem : a ∈ y \ x := ha ▸ Finset.mem_singleton_self a
          rw [Finset.mem_sdiff] at ha_mem
          refine ⟨a, Finset.mem_compl.mpr ha_mem.2, ?_⟩
          ext c; simp only [mem_insert]
          constructor
          · intro hc; rcases hc with rfl | hc
            · exact ha_mem.1
            · exact hxy hc
          · intro hc
            by_cases hcx : c ∈ x
            · right; exact hcx
            · left
              have : c ∈ y \ x := Finset.mem_sdiff.mpr ⟨hc, hcx⟩
              rw [ha, Finset.mem_singleton] at this; exact this

lemma DU_coeff_diag (i : ℕ) (x : Finset (Fin n)) (hx : x.card = i) :
    DU_coeff i x x = n - i := by
  unfold DU_coeff
  have : (Finset.univ.filter (fun y : Finset (Fin n) =>
      y.card = i + 1 ∧ x ⊆ y ∧ x ⊆ y)) =
    (Finset.univ.filter (fun y : Finset (Fin n) =>
      y.card = i + 1 ∧ x ⊆ y)) := by
    ext y; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [this, ← hx, card_supersets_insert, hx]

lemma UD_coeff_diag (i : ℕ) (x : Finset (Fin n)) (hx : x.card = i) :
    UD_coeff i x x = i := by
  classical
  cases i with
  | zero => simp [UD_coeff]
  | succ k =>
    simp only [UD_coeff]
    have : (Finset.univ.filter (fun w : Finset (Fin n) =>
        w.card = k ∧ w ⊆ x ∧ w ⊆ x)) =
      (Finset.univ.filter (fun w : Finset (Fin n) =>
        w.card = k ∧ w ⊆ x)) := by
      ext w; simp only [mem_filter, mem_univ, true_and]; tauto
    rw [this]
    have h_eq : (Finset.univ.filter (fun w : Finset (Fin n) =>
        w.card = k ∧ w ⊆ x)) = x.powersetCard k := by
      ext w; simp only [mem_filter, mem_univ, true_and, mem_powersetCard]; tauto
    rw [h_eq, card_powersetCard, hx, Nat.choose_succ_self_right]

lemma DU_UD_coeff_off_diag (i : ℕ) (x z : Finset (Fin n))
    (hx : x.card = i) (hz : z.card = i) (hne : x ≠ z) :
    DU_coeff i x z = UD_coeff i x z := by
  classical
  set k := (x ∩ z).card with hk_def
  have hk_le : k ≤ i := by
    rw [hk_def]; exact (Finset.card_le_card Finset.inter_subset_left).trans hx.le
  have hk_lt : k < i := by
    rcases hk_le.lt_or_eq with h | h
    · exact h
    · exfalso; apply hne
      have hxz_eq : x ∩ z = x := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by rw [hx]; exact h.symm.le)
      have hxz_eq' : x ∩ z = z := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by rw [hz]; exact h.symm.le)
      rw [← hxz_eq, hxz_eq']
  have hunion : (x ∪ z).card = 2 * i - k := by
    have h1 := Finset.card_union_add_card_inter x z
    rw [hx, hz] at h1; omega
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [DU_coeff, UD_coeff]
  by_cases hk_eq : k = i'
  ·
    have hunion_card : (x ∪ z).card = i' + 1 + 1 := by rw [hunion, hk_eq]; omega
    have hDU : (Finset.univ.filter (fun y : Finset (Fin n) =>
        y.card = i' + 1 + 1 ∧ x ⊆ y ∧ z ⊆ y)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨x ∪ z, ?_⟩
      ext y; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hycard, hxy, hzy⟩
        exact Finset.eq_of_superset_of_card_ge (Finset.union_subset hxy hzy)
          (by rw [hunion_card]; omega)
      · rintro rfl
        exact ⟨hunion_card, Finset.subset_union_left, Finset.subset_union_right⟩
    have hinter_card : (x ∩ z).card = i' := by omega
    have hUD : (Finset.univ.filter (fun w : Finset (Fin n) =>
        w.card = i' ∧ w ⊆ x ∧ w ⊆ z)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨x ∩ z, ?_⟩
      ext w; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hwcard, hwx, hwz⟩
        exact Finset.eq_of_subset_of_card_le (Finset.subset_inter hwx hwz)
          (by rw [hinter_card]; omega)
      · rintro rfl
        exact ⟨hinter_card, Finset.inter_subset_left, Finset.inter_subset_right⟩
    rw [hDU, hUD]
  ·
    have hk_small : k < i' := by omega
    have hDU : (Finset.univ.filter (fun y : Finset (Fin n) =>
        y.card = i' + 1 + 1 ∧ x ⊆ y ∧ z ⊆ y)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y _
      rintro ⟨hycard, hxy, hzy⟩
      have : (x ∪ z).card ≤ y.card := Finset.card_le_card (Finset.union_subset hxy hzy)
      rw [hunion, hycard] at this; omega
    have hUD : (Finset.univ.filter (fun w : Finset (Fin n) =>
        w.card = i' ∧ w ⊆ x ∧ w ⊆ z)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _
      rintro ⟨hwcard, hwx, hwz⟩
      have : w.card ≤ (x ∩ z).card := Finset.card_le_card (Finset.subset_inter hwx hwz)
      rw [hwcard] at this; omega
    rw [hDU, hUD]

theorem boolean_DU_UD_commutator (i : ℕ) (x z : Finset (Fin n))
    (hx : x.card = i) (hz : z.card = i) (hi : i ≤ n) :
    (DU_coeff i x z : ℤ) - (UD_coeff i x z : ℤ) =
      if z = x then ((n : ℤ) - 2 * i) else 0 := by
  by_cases hzx : z = x
  · rw [hzx, DU_coeff_diag i x hx, UD_coeff_diag i x hx, if_pos rfl]; omega
  · rw [DU_UD_coeff_off_diag i x z hx hz (Ne.symm hzx), if_neg hzx, sub_self]

end BooleanCommutator
