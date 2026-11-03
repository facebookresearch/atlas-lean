/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Irreducible

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X]

/-- A subset `s` of a topological space is an *irreducible component* if it is closed, irreducible,
and maximal among closed irreducible subsets containing it. -/
def IsIrreducibleComponent (s : Set X) : Prop :=
  IsClosed s ∧ IsIrreducible s ∧ ∀ t : Set X, IsClosed t → IsIrreducible t → s ⊆ t → t = s

/-- Our `IsIrreducibleComponent` predicate agrees with membership in Mathlib's
`irreducibleComponents X`. -/
theorem isIrreducibleComponent_iff_mem (s : Set X) :
    IsIrreducibleComponent s ↔ s ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_maximals_closed]
  simp only [Maximal, Set.mem_setOf_eq]
  constructor
  · intro ⟨hc, hi, hmax⟩
    exact ⟨⟨hc, hi⟩, fun t ⟨htc, hti⟩ hst => (hmax t htc hti hst).le⟩
  · intro ⟨⟨hc, hi⟩, hmax⟩
    exact ⟨hc, hi, fun t htc hti hst => le_antisymm (hmax ⟨htc, hti⟩ hst) hst⟩

/-- An irreducible component is closed. -/
theorem IsIrreducibleComponent.isClosed {s : Set X} (h : IsIrreducibleComponent s) :
    IsClosed s :=
  h.1

/-- An irreducible component is irreducible. -/
theorem IsIrreducibleComponent.isIrreducible {s : Set X} (h : IsIrreducibleComponent s) :
    IsIrreducible s :=
  h.2.1

/-- Maximality of an irreducible component: any closed irreducible superset coincides with it. -/
theorem IsIrreducibleComponent.eq_of_subset {s t : Set X} (h : IsIrreducibleComponent s)
    (htc : IsClosed t) (hti : IsIrreducible t) (hst : s ⊆ t) : t = s :=
  h.2.2 t htc hti hst

/-- Every point of a topological space is contained in some irreducible component. -/
theorem exists_isIrreducibleComponent_of_mem (x : X) :
    ∃ s : Set X, IsIrreducibleComponent s ∧ x ∈ s :=
  ⟨irreducibleComponent x,
    (isIrreducibleComponent_iff_mem _).mpr (irreducibleComponent_mem_irreducibleComponents x),
    mem_irreducibleComponent⟩
