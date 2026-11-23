/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.OrderRaising
import Mathlib.Data.Finset.Card

open Finset

namespace SpernerProperty

section BooleanSperner

variable (n : ℕ)

def booleanComplement (s : BooleanPoset n) : BooleanPoset n :=
  Finset.univ \ s

lemma booleanComplement_card (s : BooleanPoset n) :
    (booleanComplement n s).card = n - s.card := by
  unfold booleanComplement
  rw [card_sdiff_of_subset (subset_univ s), card_univ, Fintype.card_fin]

lemma booleanComplement_involutive : Function.Involutive (booleanComplement n) := by
  intro s
  unfold booleanComplement
  exact _root_.sdiff_sdiff_eq_self (subset_univ s)

lemma booleanComplement_antitone : Antitone (booleanComplement n) := by
  intro a b hab
  exact sdiff_subset_sdiff Subset.rfl hab

lemma booleanComplement_grade (s : BooleanPoset n) :
    grade ℕ (booleanComplement n s) = n - grade ℕ s := by
  rw [grade_eq, booleanComplement_card, grade_eq]

set_option maxHeartbeats 400000 in
theorem booleanPoset_hasOrderLoweringMatching (i : ℕ) (hi : n + 1 ≤ 2 * i) (hin : i ≤ n) :
    HasOrderLoweringMatching (α := BooleanPoset n) i := by

  have hn_raise : 2 * (n - i) + 1 ≤ n := by omega
  obtain ⟨φ, hφ_grade, hφ_lt, hφ_inj⟩ := booleanPoset_hasOrderRaisingMatching n (n - i) hn_raise

  let ψ := fun (x : BooleanPoset n) => booleanComplement n (φ (booleanComplement n x))
  refine ⟨ψ, ?_, ?_, ?_⟩
  ·
    intro x hx
    simp only [ψ]
    rw [booleanComplement_grade]
    have hcx : grade ℕ (booleanComplement n x) = n - i := by
      rw [booleanComplement_grade, hx]
    rw [hφ_grade _ hcx]
    omega
  ·
    intro x hx
    simp only [ψ]
    have hcx : grade ℕ (booleanComplement n x) = n - i := by
      rw [booleanComplement_grade, hx]
    have hlt := hφ_lt _ hcx
    have h_le := booleanComplement_antitone n (le_of_lt hlt)
    rw [booleanComplement_involutive] at h_le
    have hne : booleanComplement n (φ (booleanComplement n x)) ≠ x := by
      intro heq

      have : φ (booleanComplement n x) = booleanComplement n x := by
        have := congr_arg (booleanComplement n) heq
        rwa [booleanComplement_involutive] at this
      exact absurd this (ne_of_gt hlt)
    exact lt_of_le_of_ne h_le hne
  ·
    intro x y hx hy hxy
    simp only [ψ] at hxy
    have hcx : grade ℕ (booleanComplement n x) = n - i := by
      rw [booleanComplement_grade, hx]
    have hcy : grade ℕ (booleanComplement n y) = n - i := by
      rw [booleanComplement_grade, hy]
    have hinj := (booleanComplement_involutive n).injective
    have hφeq := hφ_inj _ _ hcx hcy (hinj hxy)
    exact hinj hφeq

theorem booleanPoset_hasOrderMatchings :
    HasOrderMatchings (α := BooleanPoset n) (n / 2) := by
  refine ⟨Nat.div_le_self n 2, ?_, ?_⟩
  ·
    intro i hi
    exact booleanPoset_hasOrderRaisingMatching n i (by omega)
  ·
    intro i hi hin
    exact booleanPoset_hasOrderLoweringMatching n i (by omega) hin

theorem boolean_sperner :
    HasSpernerProperty (α := BooleanPoset n) :=
  orderMatchings_imp_sperner (n / 2) (booleanPoset_hasOrderMatchings n)

end BooleanSperner

end SpernerProperty
