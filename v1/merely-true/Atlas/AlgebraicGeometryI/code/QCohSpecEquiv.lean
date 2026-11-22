/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- The adjunction `tilde ⊣ Γ` between modules over `R` and sheaves of modules
on `Spec R`. -/
def tildeΓAdjunction : tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- The tilde functor is fully faithful, the categorical input to the
equivalence `Mod R ≃ QCoh(Spec R)`. -/
def tildeFullyFaithful : (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

/-- For every `R`-module `M`, the sheaf `M̃` on `Spec R` is quasi-coherent. -/
theorem tilde_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

/-- The unit of the `tilde ⊣ Γ` adjunction is an isomorphism (the affine
reconstruction `Γ(M̃) ≅ M`). -/
instance tilde_unit_isIso : IsIso (tilde.adjunction (R := R)).unit :=
  tilde.adjunction.isIso_unit_of_iso (tilde.toTildeΓNatIso (R := R)).symm

/-- Equivalence of categories between `Mod R` and the essential image of the
tilde functor, packaging the fully-faithful corestriction. -/
def tildeEssImageEquiv :
    ModuleCat.{u} R ≌ (tilde.functor R).EssImageSubcategory :=
  (tilde.functor R).toEssImage.asEquivalence

/-- A sheaf `M` on `Spec R` lies in the essential image of the tilde functor iff
the affine counit `fromTildeΓ M` is an isomorphism. -/
theorem tilde_essImage_iff_isIso_counit (M : (Spec (.of R)).Modules) :
    (tilde.functor R).essImage M ↔ IsIso M.fromTildeΓ :=
  isIso_fromTildeΓ_iff.symm

/-- If a sheaf of modules on `Spec R` admits a presentation, then the
affine counit `fromTildeΓ` is an isomorphism. -/
theorem tilde_counit_isIso_of_presentation (M : (Spec R).Modules)
    (P : M.Presentation) : IsIso M.fromTildeΓ :=
  isIso_fromTildeΓ_of_presentation M P
