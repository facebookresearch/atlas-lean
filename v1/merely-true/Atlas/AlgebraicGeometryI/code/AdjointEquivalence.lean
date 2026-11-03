/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.Torsion.Basic

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry

universe u v

section AdjointFullyFaithful

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- If `F ⊣ G` is an adjunction with `F` fully faithful and `G` conservative, then the counit is
a natural isomorphism. This is a standard criterion for an adjunction to give an equivalence. -/
theorem adjunction_counit_isIso_of_conservative (adj : F ⊣ G) [F.Full] [F.Faithful]
    [G.ReflectsIsomorphisms] (X : D) : IsIso (adj.counit.app X) := by
  have : IsIso (G.map (adj.counit.app X)) :=
    NatIso.isIso_app_of_isIso (whiskerRight adj.counit G) X
  exact isIso_of_reflects_iso (adj.counit.app X) G

end AdjointFullyFaithful

section AffineMorphisms

/-- `Spec R` is an affine scheme. Convenience wrapper around `isAffine_Spec`. -/
theorem Spec_isAffine' (R : CommRingCat) : IsAffine (Spec R) :=
  isAffine_Spec R

end AffineMorphisms

section RestrictScalarsFull

/-- If `f : R →+* S` is surjective, then the restriction of scalars functor on module categories
is full: every `R`-linear map between restricted `S`-modules lifts to an `S`-linear map. -/
theorem restrictScalars_full_of_surjective {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars f).Full where
  map_surjective {M N} g := by


    refine ⟨ModuleCat.ofHom ⟨g.hom.toAddHom, fun s m => ?_⟩, ?_⟩
    · obtain ⟨r, rfl⟩ := hf s


      change g.hom (f r • m) = f r • g.hom m
      have := g.hom.map_smul r m
      simp only [ModuleCat.restrictScalars.smul_def] at this
      exact this
    · rfl

end RestrictScalarsFull

section RestrictScalarsEssImage

/-- If an `R`-module `M` is in the essential image of restriction along `R → R/I`, then `I`
annihilates `M`. -/
theorem restrictScalars_essImage_annihilated {R : Type*} [CommRing R] (I : Ideal R)
    (M : ModuleCat R)
    (h : ∃ (N : ModuleCat (R ⧸ I)),
      Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N ≅ M)) :
    ∀ (r : R) (m : M), r ∈ I → r • m = 0 := by
  rintro r m hr
  obtain ⟨N, ⟨iso⟩⟩ := h
  have key : r • (iso.inv.hom m) =
      (0 : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) := by
    change (Ideal.Quotient.mk I r) • (iso.inv.hom m : N) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  have h1 := iso.hom.hom.map_smul r (iso.inv.hom m)
  rw [key, map_zero] at h1
  have h2 : iso.hom.hom (iso.inv.hom m) = m := by
    change (iso.inv ≫ iso.hom).hom m = m
    simp [iso.inv_hom_id]
  rw [h2] at h1; exact h1.symm

/-- Conversely, an `R`-module annihilated by `I` is the restriction of scalars of some
`R/I`-module; this characterizes the essential image of restriction along `R → R/I`. -/
theorem restrictScalars_essImage_of_annihilated {R : Type*} [CommRing R] (I : Ideal R)
    (M : ModuleCat R)
    (hann : ∀ (r : R) (m : M), r ∈ I → r • m = 0) :
    ∃ (N : ModuleCat (R ⧸ I)),
      Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N ≅ M) := by
  have htors : Module.IsTorsionBySet R M (I : Set R) := by
    intro m ⟨a, ha⟩; exact hann a m ha
  letI := htors.module
  let N : ModuleCat (R ⧸ I) := ModuleCat.of (R ⧸ I) M
  exact ⟨N, ⟨{
    hom := ModuleCat.ofHom LinearMap.id
    inv := ModuleCat.ofHom LinearMap.id
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }⟩⟩

end RestrictScalarsEssImage
