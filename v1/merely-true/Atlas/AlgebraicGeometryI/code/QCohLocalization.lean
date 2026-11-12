/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Atlas.AlgebraicGeometryI.code.Lec14QCohProjective

namespace QCohLocalization

open LocalizedModule

/-- The localized module `M_f := S^{-1} M` at the powers of `f`, encoding the
value `Γ(D(f), M̃)` of the tilde sheaf on a principal open. -/
abbrev ModuleTilde (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (f : R) : Type _ :=
  LocalizedModule (Submonoid.powers f) M

/-- Localization is left exact: it preserves injectivity of module maps. -/
theorem localization_preserves_injective {R : Type*} [CommRing R]
    (S : Submonoid R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (LocalizedModule.map S f) :=
  LocalizedModule.map_injective S f hf

/-- Localization is right exact: it preserves surjectivity of module maps. -/
theorem localization_preserves_surjective {R : Type*} [CommRing R]
    (S : Submonoid R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (LocalizedModule.map S f) :=
  LocalizedModule.map_surjective S f hf

/-- Localization is exact in the middle: it preserves exactness of a pair `f, g`
of consecutive linear maps. -/
theorem localization_exact_middle {R : Type*} [CommRing R]
    (S : Submonoid R) {M' M M'' : Type*}
    [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hex : Function.Exact f g) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
  LocalizedModule.map_exact S f g hex

/-- Localization functor `S^{-1}(−)` is exact: it preserves exact sequences,
the key property powering the tilde-functor proofs. -/
theorem localization_preserves_exactness {R : Type*} [CommRing R] (S : Submonoid R)
    {M N P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
  LocalizedModule.map_exact S f g hfg

end QCohLocalization

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {R : CommRingCat.{u}}


/-- Global sections of a sheaf of modules on `Spec R`, viewed as an `R`-module
through the natural `Γ` functor. -/
noncomputable def tildeSpec_globalSectionsModule (F : (Spec R).Modules) :
    ModuleCat.{u} R :=
  moduleSpecΓFunctor.obj F

/-- The unit of the `tilde ⊣ Γ` adjunction is an isomorphism, expressing
the identity `Γ(M̃) ≅ M`. -/
instance tildeSpec_unitIso : IsIso (tilde.adjunction (R := R)).unit :=
  inferInstance

/-- The sheaf `M̃` on `Spec R` is quasi-coherent for any `R`-module `M`. -/
instance tildeSpec_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

section Prop20Projective

open AlgebraicGeometry CategoryTheory

universe v

variable {A : Type v} [CommRing A] {σ : Type v} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

end Prop20Projective
