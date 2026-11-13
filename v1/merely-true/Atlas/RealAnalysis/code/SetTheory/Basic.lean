/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Set

namespace SetTheory

variable {α : Type*} (A B C : Set α)

/-- **De Morgan's Laws.** For sets `A`, `B`, `C`:
the complement of a union is the intersection of complements,
the complement of an intersection is the union of complements,
and the analogous identities for set differences:
`A \ (B ∪ C) = (A \ B) ∩ (A \ C)` and `A \ (B ∩ C) = (A \ B) ∪ (A \ C)`. -/
theorem de_morgan_laws :
    (B ∪ C)ᶜ = Bᶜ ∩ Cᶜ ∧
    (B ∩ C)ᶜ = Bᶜ ∪ Cᶜ ∧
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) ∧
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) :=
  ⟨compl_union B C, compl_inter B C, diff_inter_diff.symm, Set.diff_inter⟩

/-- **Well-ordering of `ℕ`.** Every nonempty subset `S ⊆ ℕ` contains a least element,
that is, there exists `x ∈ S` such that `x ≤ y` for all `y ∈ S`. -/
theorem well_ordering_nat (S : Set ℕ) (hS : S.Nonempty) : ∃ x ∈ S, ∀ y ∈ S, x ≤ y := by
  classical
  have ⟨n, hn⟩ := hS
  exact ⟨Nat.find ⟨n, hn⟩, Nat.find_spec ⟨n, hn⟩, fun y hy => Nat.find_min' ⟨n, hn⟩ hy⟩

/-- **Principle of mathematical induction (starting at 1).** If `P 1` holds and
`P m → P (m + 1)` for all `m`, then `P n` holds for every natural number `n ≥ 1`. -/
theorem induction_principle (P : ℕ → Prop) (base : P 1)
    (step : ∀ m : ℕ, P m → P (m + 1)) : ∀ n : ℕ, n ≥ 1 → P n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => exact base
    | succ k' => exact step _ (ih (by omega))

end SetTheory

namespace SetTheory

variable {α : Type*} (A B : Set α)

/-- **Basic set relations.** `A ⊆ B` means every element of `A` lies in `B`;
`A = B` is equivalent to mutual inclusion `A ⊆ B` and `B ⊆ A`; and
`A ⊂ B` (proper subset) is equivalent to `A ⊆ B` together with `A ≠ B`. -/
theorem set_relations :
    (A ⊆ B ↔ ∀ a, a ∈ A → a ∈ B) ∧
    (A = B ↔ A ⊆ B ∧ B ⊆ A) ∧
    (A ⊂ B ↔ A ⊆ B ∧ A ≠ B) :=
  ⟨Iff.rfl, Set.Subset.antisymm_iff, Set.ssubset_iff_subset_ne⟩

end SetTheory
