/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Cotangent

set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory KaehlerDifferential

noncomputable section

universe u

section ConormalPart1

/-- For a closed immersion `i : Z → X`, the induced map on stalks `𝒪_{X,i(z)} → 𝒪_{Z,z}` is
surjective at every point. -/
theorem closedImmersion_stalkMap_surjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Function.Surjective (i.stalkMap z).hom :=
  SurjectiveOnStalks.stalkMap_surjective i z

/-- Proposition 33 / 35 (Lecture 20, conormal sequence — exactness at the middle term).
For a surjection `A → B` of `R`-algebras, the image of `I/I² → B ⊗_A Ω_{A/R}` equals the
kernel of `B ⊗_A Ω_{A/R} → Ω_{B/R}`. -/
theorem conormalSequence_exact
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    LinearMap.range (kerCotangentToTensor R A B) =
      (LinearMap.ker (mapBaseChange R A B)).restrictScalars A :=
  range_kerCotangentToTensor R A B hsurj

/-- The natural map `Ω_{A/R} ⊗_A B → Ω_{B/R}` (equivalently, surjectivity at the right of
the conormal/Jacobi–Zariski sequence) is surjective. -/
theorem conormalSequence_surjective
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    Function.Surjective (KaehlerDifferential.map R A B B) :=
  KaehlerDifferential.map_surjective R A B

/-- Exactness of the Jacobi–Zariski sequence in the middle:
`B ⊗_A Ω_{A/R} → Ω_{B/R}` is exact at `Ω_{B/R}` in the sense that the kernel coincides with
the image of the conormal map. -/
theorem jacobiZariski_exact
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    Function.Exact (mapBaseChange R A B) (KaehlerDifferential.map R A B B) :=
  exact_mapBaseChange_map R A B

end ConormalPart1

section ConormalPart2

/-- For a formally smooth `R`-algebra `A` and a surjection `A → B`, the conormal map
`I/I² → B ⊗_A Ω_{A/R}` is injective iff the first cotangent cohomology `H¹(L_{B/R})`
vanishes. -/
theorem conormalSequence_injective_iff_h1Cotangent_subsingleton
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Function.Injective (kerCotangentToTensor R A B) ↔
      Subsingleton (Algebra.H1Cotangent R B) :=
  Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj

/-- For a formally smooth `R`-algebra `A` with a formally smooth presentation `P`, the
cotangent complex map `P.cotangentComplex` is injective. -/
theorem conormalSequence_injective_of_formallySmooth
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A] (P : Algebra.Extension R A)
    [Algebra.FormallySmooth R P.Ring] :
    Function.Injective P.cotangentComplex := by
  rw [P.cotangentComplex_injective_iff]
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

/-- For a closed immersion `i : Z → X` and a smooth morphism `f : X → S`, the stalk of
`i ∘ f` at `z` is formally smooth iff `z` lies in the smooth locus of `i ∘ f`. -/
theorem conormalSequence_ses_iff_smooth
    {X Z S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) [Smooth f] [IsNoetherian X] (z : Z) :
    ((i ≫ f).stalkMap z).hom.FormallySmooth ↔
      z ∈ (i ≫ f).smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus]

end ConormalPart2

section ConormalPart3

/-- The smooth locus of `i ∘ f : Z → S` is an open subset of `Z`. -/
theorem conormalSequence_smoothLocus_isOpen
    {X Z S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) [Smooth f] [IsNoetherian X] :
    IsOpen {z : Z | ((i ≫ f).stalkMap z).hom.FormallySmooth} :=
  Scheme.Hom.isOpen_smoothLocus (i ≫ f)

/-- Smoothness propagates to a neighbourhood: a smooth point of `i ∘ f` has an open
neighbourhood of smooth points. -/
theorem conormalSequence_smoothness_propagates
    {X Z S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) [Smooth f] [IsNoetherian X]
    (z₀ : Z) (hz₀ : ((i ≫ f).stalkMap z₀).hom.FormallySmooth) :
    ∃ (U : TopologicalSpace.Opens Z), z₀ ∈ U ∧
      ∀ z ∈ U, ((i ≫ f).stalkMap z).hom.FormallySmooth := by
  have hopen := conormalSequence_smoothLocus_isOpen i f
  exact ⟨⟨{z | ((i ≫ f).stalkMap z).hom.FormallySmooth}, hopen⟩, hz₀, fun z hz => hz⟩

end ConormalPart3

end
