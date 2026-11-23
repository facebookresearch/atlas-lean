/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Irreducible

section IrreducibleComponent

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- Irreducible component (Def 8, Lec 3): a subset `s ⊆ X` is an irreducible component
if it is a maximal irreducible closed subset of `X`. -/
def IsIrreducibleComponentOf (s : Set X) : Prop :=
  s ∈ irreducibleComponents X

/-- Characterization: `s` is an irreducible component iff `s` is maximal among
closed irreducible subsets. -/
theorem isIrreducibleComponentOf_iff_maximal_closed_irreducible (s : Set X) :
    IsIrreducibleComponentOf s ↔
      Maximal (fun t => IsClosed t ∧ IsIrreducible t) s := by
  unfold IsIrreducibleComponentOf
  constructor
  · intro hs
    rw [irreducibleComponents_eq_maximals_closed] at hs
    exact hs
  · intro hs
    rw [irreducibleComponents_eq_maximals_closed]
    exact hs

/-- An irreducible component is irreducible. -/
theorem IsIrreducibleComponentOf.isIrreducible {s : Set X} (hs : IsIrreducibleComponentOf s) :
    IsIrreducible s :=
  hs.1

/-- An irreducible component is closed. -/
theorem IsIrreducibleComponentOf.isClosed {s : Set X} (hs : IsIrreducibleComponentOf s) :
    IsClosed s :=
  isClosed_of_mem_irreducibleComponents s hs

/-- Every irreducible subset is contained in some irreducible component. -/
theorem exists_irreducibleComponent_superset {s : Set X} (hs : IsIrreducible s) :
    ∃ t, IsIrreducibleComponentOf t ∧ s ⊆ t := by
  obtain ⟨t, ht, hst⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible s hs
  exact ⟨t, ht, hst⟩

/-- Every point of `X` is contained in some irreducible component. -/
theorem exists_irreducibleComponent_of_mem (x : X) :
    ∃ s, IsIrreducibleComponentOf s ∧ x ∈ s :=
  ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

end IrreducibleComponent
