/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Link
import Atlas.Buildings.code.Building.Basic

open scoped Classical

variable {V : Type} [DecidableEq V]

open SimplicialComplex in
/-- If $C$ is maximal in the link complex $\mathrm{lk}_\sigma(\mathcal{B})$,
then $\sigma \cup C$ is a chamber (maximal face) of the ambient building. -/
theorem linkComplex_maximal_union_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (C : Finset V)
    (hC : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C) :
    b.toChamberComplex.toSimplicialComplex.IsMaximal (σ ∪ C) := by
  set K := b.toChamberComplex.toSimplicialComplex
  have hC_link := hC.1
  rw [mem_linkComplex_iff] at hC_link
  refine ⟨hC_link.2.2, fun w hw h_sub => ?_⟩
  have hσw : σ ⊆ w := Finset.subset_union_left.trans h_sub
  by_cases hne : (w \ σ).Nonempty
  · have hw_link := mem_linkComplex_of_sdiff K σ hσ w hw hσw hne
    have hC_sub : C ⊆ w \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨h_sub (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hC_link.2.1 hv⟩
    rw [hC.2 (w \ σ) hw_link hC_sub, Finset.union_sdiff_of_subset hσw]
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exfalso
    obtain ⟨v, hv⟩ := hC_link.1
    exact Finset.disjoint_right.mp hC_link.2.1 hv (hne (h_sub (Finset.mem_union_right σ hv)))


/-- If $C, D$ are each disjoint from $\sigma$ and $C \neq D$, then
$\sigma \cup C \neq \sigma \cup D$. -/
lemma union_ne_of_disjoint_ne (σ C D : Finset V)
    (hC_disj : Disjoint σ C) (hD_disj : Disjoint σ D) (hne : C ≠ D) :
    σ ∪ C ≠ σ ∪ D := by
  intro h
  apply hne
  have hC' : C = (σ ∪ C) \ σ := (Finset.union_sdiff_cancel_left hC_disj).symm
  have hD' : D = (σ ∪ D) \ σ := (Finset.union_sdiff_cancel_left hD_disj).symm
  rw [hC', hD', h]

