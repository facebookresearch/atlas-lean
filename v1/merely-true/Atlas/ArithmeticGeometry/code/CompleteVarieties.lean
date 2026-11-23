/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.KrullDimension.Zero

universe u

/-- A variety is a topological space that is Noetherian (every descending chain of closed subsets stabilizes). -/
abbrev IsVariety (X : Type u) [TopologicalSpace X] : Prop :=
  TopologicalSpace.NoetherianSpace X

/-- A complete variety: a variety $X$ such that the second projection $X \times Y \to Y$ is a closed map for every variety $Y$ (the topological analog of properness). -/
class IsCompleteVariety (X : Type u) [TopologicalSpace X] : Prop where
  isVariety : IsVariety X
  isClosedMap_snd : ∀ (Y : Type u) [TopologicalSpace Y] [IsVariety Y],
    IsClosedMap (Prod.snd : X × Y → Y)


/-- A complete variety is in particular a Noetherian topological space. -/
instance (priority := 100) IsCompleteVariety.toNoetherianSpace
    {X : Type u} [TopologicalSpace X] [h : IsCompleteVariety X] :
    TopologicalSpace.NoetherianSpace X := h.isVariety

namespace IsCompleteVariety

variable {X : Type u} [TopologicalSpace X]

/-- Any compact Noetherian space is a complete variety, since the projection $X \times Y \to Y$ from a compact space is automatically closed. -/
instance of_compactSpace [CompactSpace X] [TopologicalSpace.NoetherianSpace X] :
    IsCompleteVariety X where
  isVariety := inferInstance
  isClosedMap_snd _ := isClosedMap_snd_of_compactSpace


/-- (Lemma 16.12) If $X$ is a complete variety and $\varphi : X \to Y$ is a continuous map with closed graph, then $\varphi$ is a closed map and its image is a complete variety. -/
theorem lemma_16_12 [hX : IsCompleteVariety X]
    {Y : Type u} [TopologicalSpace Y] [IsVariety Y]
    {φ : X → Y} (hφ : Continuous φ)
    (hgraph : IsClosed {p : X × Y | p.2 = φ p.1}) :
    IsClosedMap φ ∧ IsCompleteVariety (Set.range φ) := by
  constructor
  ·
    intro Z hZ
    have hZuniv : IsClosed (Z ×ˢ (Set.univ : Set Y)) := hZ.prod isClosed_univ
    have hinter : IsClosed ({p : X × Y | p.2 = φ p.1} ∩ (Z ×ˢ Set.univ)) :=
      hgraph.inter hZuniv
    have hproj := hX.isClosedMap_snd Y _ hinter
    suffices h : φ '' Z = Prod.snd '' ({p : X × Y | p.2 = φ p.1} ∩ (Z ×ˢ Set.univ)) from
      h ▸ hproj
    ext y
    constructor
    · rintro ⟨x, hxZ, rfl⟩
      exact ⟨(x, φ x), ⟨rfl, hxZ, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨x, y'⟩, ⟨hy', hxZ, _⟩, rfl⟩
      exact ⟨x, hxZ, hy'.symm⟩
  ·
    exact {
      isVariety := TopologicalSpace.NoetherianSpace.range φ hφ
      isClosedMap_snd := by
        intro Z _inst _var S hS
        let ψ : X × Z → (Set.range φ) × Z := Prod.map (Set.rangeFactorization φ) id
        have hψ : Continuous ψ := (hφ.rangeFactorization).prodMap continuous_id
        have hpreimage : IsClosed (ψ ⁻¹' S) := hS.preimage hψ
        have hproj := hX.isClosedMap_snd Z _ hpreimage
        convert hproj using 1
        ext z
        constructor
        · rintro ⟨⟨⟨y, hy⟩, z'⟩, hS', rfl⟩
          obtain ⟨x, rfl⟩ := hy
          exact ⟨(x, z'), hS', rfl⟩
        · rintro ⟨⟨x, z'⟩, hS', rfl⟩
          exact ⟨(⟨φ x, x, rfl⟩, z'), hS', rfl⟩
    }


/-- A closed subset of a complete variety is itself a complete variety. -/
theorem isCompleteVariety_of_isClosed [hX : IsCompleteVariety X] {V : Set X} (hV : IsClosed V) :
    IsCompleteVariety V where
  isVariety := TopologicalSpace.NoetherianSpace.set V
  isClosedMap_snd := by
    intro Z _inst _noeth
    have h_eq : (Prod.snd : V × Z → Z) = (Prod.snd : X × Z → Z) ∘ Prod.map Subtype.val id := by
      ext ⟨v, z⟩; simp
    rw [h_eq]
    have h_incl : Topology.IsClosedEmbedding (Prod.map (Subtype.val : V → X) (id : Z → Z)) := by
      constructor
      · exact (Topology.IsClosedEmbedding.subtypeVal hV).isEmbedding.prodMap .id
      · rw [Set.range_prodMap, Subtype.range_val, Set.range_id]
        exact hV.prod isClosed_univ
    exact (hX.isClosedMap_snd Z).comp h_incl.isClosedMap

end IsCompleteVariety

open AlgebraicGeometry

/-- A complete affine integral variety over a field $K$ is a single point: if $X$ is affine, integral, and $X \to \mathrm{Spec}(K)$ is proper, then $X$ is a subsingleton. -/
theorem complete_affine_variety_subsingleton
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K))
    [IsAffine X] [IsIntegral X] [IsProper f] :
    Subsingleton X := by


  have hfield : IsField Γ(X, ⊤) := isField_of_universallyClosed K f


  have hsub : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := by
    rwa [PrimeSpectrum.subsingleton_iff_isField_of_isReduced]

  have : Subsingleton (Spec Γ(X, ⊤)) := hsub

  exact X.isoSpec.hom.homeomorph.toEquiv.subsingleton
