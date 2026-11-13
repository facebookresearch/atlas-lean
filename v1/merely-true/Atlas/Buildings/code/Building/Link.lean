/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Labels

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace SimplicialComplex

/-- The *link complex* $\mathrm{lk}_K(\sigma)$ of a face $\sigma$ as a simplicial complex: its
faces are the nonempty $\tau$ disjoint from $\sigma$ such that $\sigma \cup \tau \in K$. -/
def linkComplex (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) : SimplicialComplex V where
  faces := K.link σ hσ
  nonempty_of_mem := by
    intro s hs
    exact hs.1
  down_closed := by
    intro s t hs hts ht_ne

    obtain ⟨_, hsdisj, hsunion⟩ := hs
    refine ⟨ht_ne, ?_, ?_⟩
    ·
      exact Disjoint.mono_right hts hsdisj
    ·
      have h_sub : σ ∪ t ⊆ σ ∪ s := Finset.union_subset_union_right hts
      have h_ne : (σ ∪ t).Nonempty := by
        exact Finset.Nonempty.mono (Finset.subset_union_left) (K.nonempty_of_mem σ hσ)
      exact K.down_closed hsunion h_sub h_ne

/-- Every face $\tau$ of $\mathrm{lk}_K(\sigma)$ is disjoint from $\sigma$. -/
theorem linkComplex_disjoint (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (τ : Finset V) (hτ : τ ∈ (K.linkComplex σ hσ).faces) :
    Disjoint σ τ :=
  hτ.2.1

/-- For each face $\tau \in \mathrm{lk}_K(\sigma)$, the union $\sigma \cup \tau$ is a face of
$K$. -/
theorem linkComplex_union_mem (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (τ : Finset V) (hτ : τ ∈ (K.linkComplex σ hσ).faces) :
    σ ∪ τ ∈ K.faces :=
  hτ.2.2

/-- Membership characterisation of $\mathrm{lk}_K(\sigma)$: $\tau$ lies in the link iff $\tau$ is
nonempty, disjoint from $\sigma$, and $\sigma \cup \tau$ is a face. -/
theorem mem_linkComplex_iff (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (τ : Finset V) :
    τ ∈ (K.linkComplex σ hσ).faces ↔
      τ.Nonempty ∧ Disjoint σ τ ∧ (σ ∪ τ) ∈ K.faces :=
  Iff.rfl

/-- Every face of $\mathrm{lk}_K(\sigma)$ is itself a face of $K$. -/
theorem linkComplex_face_mem_faces (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (τ : Finset V) (hτ : τ ∈ (K.linkComplex σ hσ).faces) :
    τ ∈ K.faces := by
  have h_union := linkComplex_union_mem K σ hσ τ hτ
  have h_ne := (K.linkComplex σ hσ).nonempty_of_mem τ hτ
  exact K.down_closed h_union Finset.subset_union_right h_ne

/-- For a face $w$ properly containing $\sigma$, the complement $w \setminus \sigma$ is a face of
$\mathrm{lk}_K(\sigma)$. -/
theorem mem_linkComplex_of_sdiff (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (w : Finset V) (hw : w ∈ K.faces) (hσw : σ ⊆ w)
    (hne : (w \ σ).Nonempty) :
    (w \ σ) ∈ (K.linkComplex σ hσ).faces := by
  rw [mem_linkComplex_iff]
  refine ⟨hne, ?_, ?_⟩
  · exact disjoint_sdiff_self_right
  · rw [Finset.union_sdiff_of_subset hσw]
    exact hw

end SimplicialComplex
