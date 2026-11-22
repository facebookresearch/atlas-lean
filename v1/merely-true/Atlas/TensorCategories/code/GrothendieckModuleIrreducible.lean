/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 800000

/-- A combinatorial `ℤ₊`-ring on the basis `ι`: nonnegative structure constants `N`, a
distinguished set `I₀` whose sum is the unit, and associativity. -/
structure ZPlusRingIrr (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A `ℤ₊`-module over a `ZPlusRingIrr`, indexed by a basis `κ`, with nonnegative action
constants compatible with the unit and with the multiplication of `R`. -/
structure ZPlusModuleIrr (R : ZPlusRingIrr ι) (κ : Type*) [DecidableEq κ] [Fintype κ] where
  act : ι → κ → κ → ℕ
  act_unit : ∀ l k, ∑ s ∈ R.I₀, act s l k = if l = k then 1 else 0
  act_compat : ∀ i j l k,
    ∑ m : ι, R.N i j m * act m l k = ∑ n : κ, act j l n * act i n k

variable {R : ZPlusRingIrr ι} {κ : Type*} [DecidableEq κ] [Fintype κ]

namespace ZPlusModuleIrr

variable (M : ZPlusModuleIrr R κ)

/-- A subset `S ⊆ κ` is a proper nontrivial `ℤ₊`-submodule of `M` if it is nonempty,
not all of `κ`, and closed under the action of every basis element of the ring. -/
structure IsZPlusSubmodule (S : Finset κ) : Prop where
  nonempty : S.Nonempty
  proper : S ≠ Finset.univ
  closed : ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- The `ℤ₊`-module `M` is irreducible if it admits no proper `ℤ₊`-submodule. -/
def IsIrreducible : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule S

/-- The `ℤ₊`-module `M` is indecomposable if `κ` cannot be partitioned into two nonempty
disjoint subsets each closed under the action. -/
def IsIndecomposable : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- The `ℤ₊`-module `M` is exact if whenever some basis element of the ring sends `l` to
`k` with nonzero coefficient, there is also a basis element sending `k` back to `l`. -/
def IsExact : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

/-- Lemma 2.8.5: An indecomposable exact `ℤ₊`-module is irreducible — any proper
closed subset would give a partition of `κ` violating indecomposability. -/
theorem Lemma_2_8_5 (hindec : M.IsIndecomposable) (hexact : M.IsExact) :
    M.IsIrreducible := by
  intro S hS

  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hS.proper
    have : S = Finset.univ \ (Finset.univ \ S) := by simp
    rw [this, h]; simp

  have hdisj : Disjoint S (Finset.univ \ S) := disjoint_sdiff_self_right
  have hunion : S ∪ (Finset.univ \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ S)

  have hSc_closed : ∀ (i : ι) (l : κ), l ∈ Finset.univ \ S → ∀ (k : κ),
      M.act i l k ≠ 0 → k ∈ Finset.univ \ S := by
    intro i l hl k hact
    rw [Finset.mem_sdiff] at hl ⊢
    exact ⟨Finset.mem_univ k, fun hk_in_S => by


      obtain ⟨j, hj⟩ := hexact i l k hact
      exact hl.2 (hS.closed j k hk_in_S l hj)⟩


  exact hindec S (Finset.univ \ S) hS.nonempty hSc_ne hdisj hunion hS.closed hSc_closed

end ZPlusModuleIrr
