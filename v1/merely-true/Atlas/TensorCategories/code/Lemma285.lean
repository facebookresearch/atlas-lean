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

/-- Auxiliary, "primed" version of a `ℤ₊`-ring used by the standalone development of
Lemma 2.8.5. Mirrors `ZPlusRing` with structure constants `N : ι → ι → ι → ℕ`, a unit
support `I₀ : Finset ι` and the usual unit and associativity axioms. -/
structure ZPlusRing' (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Auxiliary, "primed" version of a `ℤ₊`-module over a `ZPlusRing'`, used by the standalone
development of Lemma 2.8.5. Records action constants `act : ι → κ → κ → ℕ` and the usual unit
and compatibility axioms. -/
structure ZPlusModule' (R : ZPlusRing' ι) (κ : Type*) [DecidableEq κ] [Fintype κ] where
  act : ι → κ → κ → ℕ
  act_unit : ∀ l k, ∑ s ∈ R.I₀, act s l k = if l = k then 1 else 0
  act_compat : ∀ i j l k,
    ∑ m : ι, R.N i j m * act m l k = ∑ n : κ, act j l n * act i n k

variable {R : ZPlusRing' ι} {κ : Type*} [DecidableEq κ] [Fintype κ]

namespace ZPlusModule'

variable (M : ZPlusModule' R κ)

/-- A nonempty proper subset `S` of basis elements that is closed under the `ℤ₊`-module
action constitutes a `ℤ₊`-submodule of `M` (primed variant). -/
structure IsZPlusSubmodule' (S : Finset κ) : Prop where
  nonempty : S.Nonempty
  proper : S ≠ Finset.univ
  closed : ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- `M` is irreducible (primed variant) if it has no nontrivial `ℤ₊`-submodule. -/
def IsIrreducible' : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule' S

/-- `M` is indecomposable (primed variant) if there is no partition of its basis into two
nonempty disjoint subsets, each closed under the action. -/
def IsIndecomposable' : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- `M` is exact (primed variant) if whenever `act i l k ≠ 0` there is some `j` such that
`act j k l ≠ 0`; this is the combinatorial analogue of exactness from EGNO. -/
def IsExact' : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

/-- Lemma 2.8.5 (EGNO), primed/standalone version. An indecomposable exact `ℤ₊`-module is
irreducible: the complement of any proper closed subset cannot fail to also be closed by
exactness, contradicting indecomposability. -/
theorem lemma_2_8_5' (hindec : M.IsIndecomposable') (hexact : M.IsExact') :
    M.IsIrreducible' := by
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

end ZPlusModule'
