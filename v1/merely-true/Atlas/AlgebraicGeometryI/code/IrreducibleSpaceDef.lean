/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Irreducible

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- Irreducible space (Def 7, Lec 3): `X` is irreducible iff the whole space `⊤` is
irreducible as a subset. -/
theorem irreducibleSpace_def' :
    IrreducibleSpace X ↔ IsIrreducible (⊤ : Set X) :=
  irreducibleSpace_def X

section Equivalences

variable [IrreducibleSpace X]

/-- In an irreducible space, any two nonempty open sets meet (Def 7, Lec 3). -/
theorem IrreducibleSpace.nonempty_inter_of_open {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hU' : U.Nonempty) (hV' : V.Nonempty) :
    (U ∩ V).Nonempty :=
  nonempty_preirreducible_inter hU hV hU' hV'

/-- Dual form: if `X` is irreducible and `X = Z₁ ∪ Z₂` with `Zᵢ` closed, then one of
the `Zᵢ` is the whole space. -/
theorem IrreducibleSpace.eq_univ_of_isClosed_union {Z₁ Z₂ : Set X}
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (h : Z₁ ∪ Z₂ = univ) :
    Z₁ = univ ∨ Z₂ = univ := by
  have hirr := PreirreducibleSpace.isPreirreducible_univ (X := X)
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  have hsub : (univ : Set X) ⊆ Z₁ ∪ Z₂ := h ▸ le_refl _
  cases hirr Z₁ Z₂ hZ₁ hZ₂ hsub with
  | inl h => exact Or.inl (eq_univ_of_univ_subset h)
  | inr h => exact Or.inr (eq_univ_of_univ_subset h)

/-- In an irreducible space, every nonempty open set is dense. -/
theorem IrreducibleSpace.dense_of_isOpen {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : Dense U :=
  hU.dense hne

end Equivalences

/-- Converse: a nonempty space in which any two nonempty opens intersect is irreducible. -/
theorem irreducibleSpace_of_nonempty_inter [Nonempty X]
    (h : ∀ ⦃U V : Set X⦄, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty → (U ∩ V).Nonempty) :
    IrreducibleSpace X where
  toPreirreducibleSpace := PreirreducibleSpace.of_forall_nonempty_inter h
  toNonempty := ‹_›
