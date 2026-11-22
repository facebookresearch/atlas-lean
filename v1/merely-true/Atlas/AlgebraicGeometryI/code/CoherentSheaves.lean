/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Atlas.AlgebraicGeometryI.code.IsFiniteTypeOfCoversTop
import Atlas.AlgebraicGeometryI.code.PushforwardPreservesKernel
import Atlas.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
import Atlas.AlgebraicGeometryI.code.Prop19PushforwardEmbedding

namespace CoherentSheaves

/-- An `R`-module `M` is *coherent* (in the textbook sense for affine schemes) iff it is
finitely generated. -/
def IsCoherentModule (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M

/-- Over a Noetherian ring, coherence is equivalent to finite presentation. -/
theorem noetherian_coherent_iff_fp
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsCoherentModule R M ↔ Module.FinitePresentation R M :=
  (Module.finitePresentation_iff_finite R M).symm

universe u

open CategoryTheory Limits AlgebraicGeometry in
/-- A sheaf of modules `F` on a scheme `X` is *coherent* if it is quasi-coherent and of
finite type. -/
class IsCoherentSheaf {X : Scheme.{u}} (F : X.Modules) : Prop where
  isQC : (F : SheafOfModules.{u} X.ringCatSheaf).IsQuasicoherent
  isFT : (F : SheafOfModules.{u} X.ringCatSheaf).IsFiniteType

open CategoryTheory Limits AlgebraicGeometry in
/-- The category of `O_X`-modules on a scheme `X` is abelian. -/
noncomputable instance oX_modules_abelian (X : Scheme.{u}) :
    CategoryTheory.Abelian X.Modules :=
  inferInstanceAs <| Abelian (SheafOfModules.{u} X.ringCatSheaf)

section kernel_coherent_sheaf_section
open CategoryTheory Limits AlgebraicGeometry






end kernel_coherent_sheaf_section





/-- The category of `R`-modules is abelian, for any commutative ring `R`. -/
instance coherent_sheaves_abelian (R : Type*) [CommRing R] :
    CategoryTheory.Abelian (ModuleCat R) :=
  inferInstance


/-- Lemma 23 (Lec 12): on `Spec A`, the sheaf `M̃` is coherent if and only if the module `M` is
finitely generated, i.e. locally finitely generated equals finitely generated. -/
theorem lemma23_coherent_iff_fg_affine
    (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] :
    CoherentSpecFinitelyGenerated.IsLocallyFinitelyGenerated R M ↔ Module.Finite R M :=
  CoherentSpecFinitelyGenerated.lemma23_coherent_tilde_iff_fg R M

/-- Any element of the localized module `M_f` can be represented as `m / f^n` for some
`m ∈ M` and `n ∈ ℕ`. -/
theorem extension_of_sections
    {R : Type*} [CommRing R] (f : R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (σ : LocalizedModule (Submonoid.powers f) M) :
    ∃ (m : M) (s : Submonoid.powers f), σ = LocalizedModule.mk m s :=
  LocalizedModule.induction_on (fun m s => ⟨m, s, rfl⟩) σ

end CoherentSheaves
