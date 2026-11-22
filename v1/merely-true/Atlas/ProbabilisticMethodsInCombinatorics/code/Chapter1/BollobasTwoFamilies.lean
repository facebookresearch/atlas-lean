/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Order.Field.Basic

open Finset Nat BigOperators

namespace BollobasTwoFamilies

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `goodPerms S T` is the set of permutations `σ` of `α` such that every element of `S`
appears before every element of `T` in the linear ordering induced by `σ`. -/
noncomputable def goodPerms (S T : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun σ =>
    ∀ s ∈ S, ∀ t ∈ T, (Fintype.equivFin α (σ s) : ℕ) < (Fintype.equivFin α (σ t) : ℕ))

/-- If `S₁ ∩ T₂` and `S₂ ∩ T₁` are both nonempty, the sets of good permutations
for `(S₁, T₁)` and `(S₂, T₂)` are disjoint, since a common permutation would force a
cyclic ordering contradiction. -/
lemma disjoint_goodPerms {S₁ T₁ S₂ T₂ : Finset α}
    (h₁ : (S₁ ∩ T₂).Nonempty) (h₂ : (S₂ ∩ T₁).Nonempty) :
    Disjoint (goodPerms S₁ T₁) (goodPerms S₂ T₂) := by
  simp only [goodPerms]
  apply Finset.disjoint_filter.mpr
  intro σ _ hσ₁ hσ₂
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  rw [Finset.mem_inter] at hx hy
  have hxy := hσ₁ x hx.1 y hy.2
  have hyx := hσ₂ y hy.1 x hx.2
  exact absurd (lt_trans hxy hyx) (lt_irrefl _)


/-- The binomial coefficient $\binom{a+b}{a}$ is positive. -/
lemma choose_pos_of_add (a b : ℕ) : 0 < (a + b).choose a :=
  Nat.choose_pos (Nat.le_add_right a b)



end BollobasTwoFamilies
