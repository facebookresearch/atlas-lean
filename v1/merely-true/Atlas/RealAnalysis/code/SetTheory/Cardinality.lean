/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace SetTheory.Cardinality

/-- Corollary to Cantor's theorem: for every natural number `n`, `n < 2 ^ n`. -/
theorem n_lt_two_pow_n (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ n ≥ 1 := Nat.one_le_two_pow
    calc n + 1
      _ < 2 ^ n + 1 := by omega
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- `SameCardinality A B` states that `A` and `B` have the same cardinality, i.e. there exists
a bijection between them (`A ≃ B`). -/
def SameCardinality (A B : Type*) : Prop := Nonempty (A ≃ B)

/-- Cantor's theorem: for every type `α`, the cardinality of `α` is strictly less than the
cardinality of its power set `Set α`. -/
theorem cantor_cardinal (α : Type*) : Cardinal.mk α < Cardinal.mk (Set α) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor (Cardinal.mk α)

/-- Cantor-Schröder-Bernstein theorem: if there are injections `f : α → β` and `g : β → α`,
then there exists a bijection between `α` and `β`; equivalently, `|α| ≤ |β|` and `|β| ≤ |α|`
imply `|α| = |β|`. -/
theorem cantor_schroeder_bernstein {α β : Type*} (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Nonempty (α ≃ β) :=
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

end SetTheory.Cardinality
