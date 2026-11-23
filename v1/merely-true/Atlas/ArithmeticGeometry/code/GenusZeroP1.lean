/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.GenusOnePlaneCubic

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

/-- The projective line $\mathbb{P}^1_k$ packaged as a `SmoothProjectiveCurveOverField k`. We
realize $\mathbb{P}^1_k$ via $\mathrm{Spec}\,k[X]$ together with its structure morphism, equipped
with the proofs that it is integral, has Krull dimension $1$, is nonempty, and has genus $0$. -/
def projectiveLineAsCurve (k : Type*) [Field k] :
    SmoothProjectiveCurveOverField k :=


  { toScheme := Spec (CommRingCat.of (Polynomial k))
    isIntegral := instIsIntegralSpecOfIsDomainCarrier
    krullDim_eq := by
      change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      norm_num
    nonempty := instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialCarrier
    structureMorphism := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    genusVal := 0 }

/-- The genus of $\mathbb{P}^1_k$ is zero, by construction. -/
theorem projectiveLineAsCurve_genus_zero (k : Type*) [Field k] :
    (projectiveLineAsCurve k).genus = 0 := by
  rfl

/-- $\mathbb{P}^1_k$ has a rational point: explicitly the point $[0 : 1]$, witnessed by the
evaluation morphism $\mathrm{Spec}\,k \to \mathrm{Spec}\,k[X]$ at $0$. -/
theorem projectiveLineAsCurve_hasRationalPoint (k : Type*) [Field k] :
    (projectiveLineAsCurve k).HasRationalPoint := by


  refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id k) (0 : k))), ?_⟩

  show Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id k) (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
  congr 1
  ext x
  simp [Polynomial.eval₂_C]


/-- Transport of rational points along a $k$-isomorphism: if $C_2$ has a rational point and
$C_1 \simeq C_2$ over $k$, then $C_1$ has a rational point. -/
theorem SmoothProjectiveCurveOverField.hasRationalPoint_of_k_iso
    {k : Type*} [Field k]
    (C₁ C₂ : SmoothProjectiveCurveOverField k)
    (φ : C₁.toScheme ≅ C₂.toScheme)
    (hφ : φ.hom ≫ C₂.structureMorphism = C₁.structureMorphism)
    (hpt : C₂.HasRationalPoint) :
    C₁.HasRationalPoint := by


  obtain ⟨s, hs⟩ := hpt
  refine ⟨s ≫ φ.inv, ?_⟩


  rw [← hφ]
  simp [Iso.inv_hom_id_assoc, hs]

/-- The property of being $k$-isomorphic to the projective line $\mathbb{P}^1_k$, compatibly with
the structure morphism. -/
def SmoothProjectiveCurveOverField.IsIsomorphicToP1 {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : Prop :=
  ∃ (φ : C.toScheme ≅ (projectiveLineAsCurve k).toScheme),
    φ.hom ≫ (projectiveLineAsCurve k).structureMorphism = C.structureMorphism








/-- A curve $k$-isomorphic to $\mathbb{P}^1_k$ inherits a rational point. -/
theorem SmoothProjectiveCurveOverField.hasRationalPoint_of_isIsomorphicToP1
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hiso : C.IsIsomorphicToP1) :
    C.HasRationalPoint := by

  obtain ⟨φ, hφ⟩ := hiso

  exact C.hasRationalPoint_of_k_iso (projectiveLineAsCurve k) φ hφ
    (projectiveLineAsCurve_hasRationalPoint k)




end
