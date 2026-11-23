/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
open Set Topology

namespace CompactnessArgument

/-- Compactness argument (Lemma 6.2.7): if every finite subfamily of bad events can be jointly
avoided by some assignment $f : (v : V) \to \alpha\,v$ on a product of finite spaces, then the
entire (possibly infinite) family can be jointly avoided. -/
theorem compactness_argument
    {V : Type*} {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, TopologicalSpace (α v)]
    [∀ v, DiscreteTopology (α v)]
    (events : Set (Set ((v : V) → α v)))
    (hclosed : ∀ A ∈ events, IsClosed Aᶜ)
    (hfin : ∀ F ⊆ events, F.Finite →
      ∃ f : (v : V) → α v, ∀ A ∈ F, f ∉ A) :
    ∃ f : (v : V) → α v, ∀ A ∈ events, f ∉ A := by


  set goods := compl '' events with hgoods_def

  have hgclosed : ∀ G ∈ goods, IsClosed G := by
    rintro G ⟨A, hA, rfl⟩
    exact hclosed A hA

  have hgfip : ∀ F ⊆ goods, F.Finite → (⋂₀ F).Nonempty := by
    intro F hFsub hFfin


    let eventsF := compl '' F
    have heFsub : eventsF ⊆ events := by
      rintro A ⟨G, hG, rfl⟩
      obtain ⟨B, hB, rfl⟩ := hFsub hG
      simpa using hB
    have heFfin : eventsF.Finite := hFfin.image _
    obtain ⟨f, hf⟩ := hfin eventsF heFsub heFfin
    refine ⟨f, mem_sInter.mpr (fun G hG => ?_)⟩
    obtain ⟨A, hA, rfl⟩ := hFsub hG
    simp only [mem_compl_iff]
    exact hf A (by exact ⟨Aᶜ, hG, compl_compl A⟩)

  have hne : (⋂₀ goods).Nonempty := CompactSpace.nonempty_sInter hgclosed hgfip
  obtain ⟨f, hf⟩ := hne
  exact ⟨f, fun A hA => by
    have : f ∈ Aᶜ := mem_sInter.mp hf (Aᶜ) ⟨A, hA, rfl⟩
    exact this⟩

end CompactnessArgument
