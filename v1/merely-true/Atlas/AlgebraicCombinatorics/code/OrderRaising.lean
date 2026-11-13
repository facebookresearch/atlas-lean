/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SetFamily.Shadow

open Finset SpernerProperty
open scoped FinsetFamily

namespace SpernerProperty

section UpwardLYM

variable {α : Type*}

lemma upward_local_LYM [DecidableEq α] [Fintype α]
    {𝒜 : Finset (Finset α)} {i : ℕ}
    (h𝒜 : (𝒜 : Set (Finset α)).Sized i) :
    𝒜.card * (Fintype.card α - i) ≤ (∂⁺ 𝒜).card * (i + 1) := by
  refine card_mul_le_card_mul (· ⊆ ·) (fun a ha => ?_) (fun b hb => ?_)
  ·
    rw [← h𝒜 ha, ← card_compl]
    apply card_le_card_of_injOn (fun j => insert j a)
    · intro j hj
      simp only [mem_coe, mem_compl] at hj
      simp only [mem_coe, Finset.mem_bipartiteAbove]
      exact ⟨insert_mem_upShadow ha hj, subset_insert _ _⟩
    · exact insert_inj_on' a
  ·
    have hb_card : b.card = i + 1 := h𝒜.upShadow hb
    calc (bipartiteBelow (· ⊆ ·) 𝒜 b).card
        ≤ (b.powersetCard i).card := by
          apply card_le_card; intro a ha
          simp only [mem_bipartiteBelow] at ha
          rw [mem_powersetCard]; exact ⟨ha.2, h𝒜 ha.1⟩
      _ = (i + 1).choose i := by rw [card_powersetCard, hb_card]
      _ = i + 1 := Nat.choose_succ_self_right i

lemma boolean_hall_condition {n i : ℕ} (hn : 2 * i + 1 ≤ n)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized i) :
    𝒜.card ≤ (∂⁺ 𝒜).card := by
  by_cases h𝒜_empty : 𝒜 = ∅
  · simp [h𝒜_empty]
  have hlym := upward_local_LYM (α := Fin n) h𝒜
  rw [Fintype.card_fin] at hlym
  have hni : i + 1 ≤ n - i := by omega
  have : 𝒜.card * (i + 1) ≤ (∂⁺ 𝒜).card * (i + 1) :=
    le_trans (Nat.mul_le_mul_left _ hni) hlym
  exact Nat.le_of_mul_le_mul_right this (by omega)

end UpwardLYM

section BooleanMatching

noncomputable def upNbhd (n i : ℕ) (s : {s : Finset (Fin n) // s.card = i}) :
    Finset {t : Finset (Fin n) // t.card = i + 1} :=
  Finset.univ.filter fun t => s.val ⊂ t.val

lemma biUnion_upNbhd_image_eq {n i : ℕ}
    (A : Finset {s : Finset (Fin n) // s.card = i}) :
    (A.biUnion (upNbhd n i)).image Subtype.val = ∂⁺ (A.image Subtype.val) := by
  ext t
  simp only [mem_image, mem_biUnion, upNbhd, mem_filter, mem_univ, true_and,
             mem_upShadow_iff_exists_sdiff]
  constructor
  · rintro ⟨⟨t', ht'_card⟩, ⟨s, hs, hst⟩, rfl⟩
    exact ⟨s.val, ⟨s, hs, rfl⟩, hst.subset, by
      rw [card_sdiff_of_subset hst.subset, ht'_card, s.prop]; omega⟩
  · rintro ⟨s_val, ⟨s, hs, rfl⟩, hsub, hcard⟩
    have ht_card : t.card = i + 1 := by
      have := Finset.card_sdiff_add_card_eq_card hsub
      rw [hcard, s.prop] at this; omega
    refine ⟨⟨t, ht_card⟩, ⟨s, hs, ?_⟩, rfl⟩
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hsub, by intro h; rw [h, sdiff_self] at hcard; simp at hcard⟩

lemma hall_condition_subtypes {n i : ℕ} (hn : 2 * i + 1 ≤ n) :
    ∀ A : Finset {s : Finset (Fin n) // s.card = i},
      A.card ≤ (A.biUnion (upNbhd n i)).card := by
  intro A
  have h1 : A.card = (A.image Subtype.val).card :=
    (card_image_of_injective A Subtype.val_injective).symm
  have h2 : (A.biUnion (upNbhd n i)).card = (∂⁺ (A.image Subtype.val)).card := by
    rw [← biUnion_upNbhd_image_eq]
    exact (card_image_of_injective _ Subtype.val_injective).symm
  have h3 : (↑(A.image Subtype.val) : Set (Finset (Fin n))).Sized i := by
    intro s hs
    simp only [Finset.mem_coe, mem_image] at hs
    obtain ⟨⟨s', hs'⟩, _, rfl⟩ := hs; exact hs'
  rw [h1, h2]
  exact boolean_hall_condition hn _ h3

theorem boolean_order_raising_matching_exists {n i : ℕ} (hn : 2 * i + 1 ≤ n) :
    ∃ f : {s : Finset (Fin n) // s.card = i} → {t : Finset (Fin n) // t.card = i + 1},
      Function.Injective f ∧ ∀ s, s.val ⊂ (f s).val := by
  have hall := hall_condition_subtypes hn
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (upNbhd n i)).mp hall
  refine ⟨f, hf_inj, fun s => ?_⟩
  have := hf_mem s
  simp only [upNbhd, mem_filter, mem_univ, true_and] at this
  exact this

set_option maxHeartbeats 1600000 in
theorem booleanPoset_hasOrderRaisingMatching (n i : ℕ) (hn : 2 * i + 1 ≤ n) :
    HasOrderRaisingMatching (α := BooleanPoset n) i := by
  classical
  obtain ⟨f, hf_inj, hf_ss⟩ := boolean_order_raising_matching_exists hn

  let φ : Finset (Fin n) → Finset (Fin n) := fun x =>
    if hx : x.card = i then (f ⟨x, hx⟩).val else x
  refine ⟨φ, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxc : x.card = i := by rwa [Finset.grade_eq] at hx
    simp only [φ, dif_pos hxc, Finset.grade_eq]
    exact (f ⟨x, hxc⟩).prop
  ·
    intro x hx
    have hxc : x.card = i := by rwa [Finset.grade_eq] at hx
    simp only [φ, dif_pos hxc]
    exact hf_ss ⟨x, hxc⟩
  ·
    intro x y hx hy hxy
    have hxc : x.card = i := by rwa [Finset.grade_eq] at hx
    have hyc : y.card = i := by rwa [Finset.grade_eq] at hy
    simp only [φ, dif_pos hxc, dif_pos hyc] at hxy
    have := hf_inj (Subtype.val_injective hxy)
    exact congrArg Subtype.val this

end BooleanMatching

end SpernerProperty
