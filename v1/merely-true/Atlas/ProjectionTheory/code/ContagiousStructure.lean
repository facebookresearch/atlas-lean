/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Pointwise

namespace ContagiousStructure

/--
Contagious structure lemma (multiplicative form). For a commutative domain `Z`,
a finite set `A ⊆ Z`, and nonzero scalars `t₁, t₂`, if `|A − t₁·A| ≤ K|A|` and
`|A − t₂·A| ≤ K|A|`, then `|A − (t₁ · t₂)·A| ≤ K² |A|`. This says that having
small dilated difference sets is "contagious" under products of the dilation
parameter.
-/
theorem contagious_structure_mul {Z : Type*} [CommRing Z] [IsDomain Z] [DecidableEq Z]
    (A : Finset Z) (t₁ t₂ : Z) (K : ℝ) (hK : 0 ≤ K)
    (ht₁ : t₁ ≠ 0)
    (h₁ : ((A - t₁ • A).card : ℝ) ≤ K * ↑(A.card))
    (h₂ : ((A - t₂ • A).card : ℝ) ≤ K * ↑(A.card)) :
    ((A - (t₁ * t₂) • A).card : ℝ) ≤ K ^ 2 * ↑(A.card) := by
  have ht₁_inj : Function.Injective (HSMul.hSMul t₁ : Z → Z) :=
    mul_right_injective₀ ht₁
  rcases A.eq_empty_or_nonempty with hA | hA
  · simp [hA]
  have hApos : (0 : ℝ) < ↑(A.card) := by
    exact_mod_cast Finset.card_pos.mpr hA

  have card_smul : ∀ S : Finset Z, (t₁ • S).card = S.card := fun S => by
    simp only [Finset.smul_finset_def]
    exact Finset.card_image_of_injective S ht₁_inj

  have hmul_smul : (t₁ * t₂) • A = t₁ • (t₂ • A) := by
    ext x; simp [Finset.mem_smul_finset, mul_assoc]

  have hdiff : (t₁ * t₂) • A - t₁ • A = t₁ • (t₂ • A - A) := by
    rw [hmul_smul]; ext x
    simp only [Finset.mem_sub, Finset.mem_smul_finset]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a - b, ⟨a, ha, b, hb, rfl⟩, by rw [smul_sub]⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨t₁ • a, ⟨a, ha, rfl⟩, t₁ • b, ⟨b, hb, rfl⟩, by rw [smul_sub]⟩

  have hcard_sym : (t₂ • A - A).card = (A - t₂ • A).card := by
    rw [← Finset.card_neg (t₂ • A - A)]; congr 1; ext x; simp [Finset.mem_sub]

  have hbound : ((((t₁ * t₂) • A - t₁ • A).card : ℝ) ≤ K * ↑(A.card)) := by
    rw [hdiff, card_smul, hcard_sym]; exact h₂

  have ruzsa := Finset.ruzsa_triangle_inequality_sub_sub_sub A (t₁ • A) ((t₁ * t₂) • A)

  have ruzsa_real : ((A - (t₁ * t₂) • A).card : ℝ) * ↑(A.card) ≤
      ↑((A - t₁ • A).card) * ↑(((t₁ * t₂) • A - t₁ • A).card) := by
    have h := ruzsa
    rw [card_smul] at h
    exact_mod_cast h

  suffices h : ((A - (t₁ * t₂) • A).card : ℝ) * ↑(A.card) ≤ K ^ 2 * ↑(A.card) * ↑(A.card) from
    le_of_mul_le_mul_right (by linarith) hApos
  calc ((A - (t₁ * t₂) • A).card : ℝ) * ↑(A.card)
      _ ≤ ↑((A - t₁ • A).card) * ↑(((t₁ * t₂) • A - t₁ • A).card) := ruzsa_real
      _ ≤ (K * ↑(A.card)) * (K * ↑(A.card)) := by
            apply mul_le_mul h₁ hbound (by exact_mod_cast Nat.zero_le _) (by positivity)
      _ = K ^ 2 * ↑(A.card) * ↑(A.card) := by ring

end ContagiousStructure
