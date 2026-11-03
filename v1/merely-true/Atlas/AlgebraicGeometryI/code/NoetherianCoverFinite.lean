/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.NoetherianSpace

open TopologicalSpace Set

/-- Every open cover of a Noetherian topological space admits a finite subcover.
This underlies the fact that a variety has a finite open affine cover. -/
theorem noetherian_open_cover_finite (X : Type*) [TopologicalSpace X] [NoetherianSpace X]
    (U : Set (Set X)) (hU : ∀ u ∈ U, IsOpen u) (hcover : ⋃₀ U = Set.univ) :
    ∃ F ⊆ U, F.Finite ∧ ⋃₀ F = Set.univ := by
  have hcompact : IsCompact (Set.univ : Set X) := NoetherianSpace.isCompact Set.univ
  rw [sUnion_eq_biUnion] at hcover
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i ∈ U, i := hcover.ge
  obtain ⟨F, hFU, hFfin, hFcover⟩ := hcompact.elim_finite_subcover_image hU hcover'
  refine ⟨F, hFU, hFfin, ?_⟩
  rw [sUnion_eq_biUnion, eq_univ_iff_forall]
  exact fun x => hFcover (mem_univ x)
