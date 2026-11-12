/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.AlgebraicGeometry.Modules.Tilde

set_option maxHeartbeats 4000000

namespace QCohEquivalenceProof

open Submodule

/-- Construct an inverse linear map from `N` to `M` assuming `η : M → N`
becomes bijective after localization at every maximal ideal — used to invert
maps via local data. -/
noncomputable def inverse_from_local_data {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (η : M →ₗ[R] N)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (LocalizedModule.map P.primeCompl η)) :
    N →ₗ[R] M :=
  (LinearEquiv.ofBijective η (bijective_of_localized_maximal η h)).symm

open CategoryTheory AlgebraicGeometry

/-- Restricting the tilde functor to its essential image yields an equivalence
`Mod R ≃ EssImage(tilde)`, a step toward the equivalence with `QCoh(Spec R)`. -/
noncomputable def qcoh_mod_equivalence (R : CommRingCat.{u}) :
    ModuleCat.{u} R ≌ (tilde.functor R).EssImageSubcategory :=
  (tilde.functor R).toEssImage.asEquivalence

/-- `M̃` is quasi-coherent for every `R`-module `M` (Cor 16). -/
instance qcoh_tilde_isQuasicoherent {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

/-- Reconstructs the equivalence-of-adjunction identity from local (stalkwise)
data: maps that are inverse at every maximal localization are globally inverse. -/
theorem adjunction_equivalence_from_stalks {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (η : M →ₗ[R] N) (ε : N →ₗ[R] M)
    (h_comp_unit : ∀ (P : Ideal R) [P.IsMaximal],
      LocalizedModule.map P.primeCompl (ε ∘ₗ η) = LinearMap.id)
    (h_comp_counit : ∀ (P : Ideal R) [P.IsMaximal],
      LocalizedModule.map P.primeCompl (η ∘ₗ ε) = LinearMap.id) :
    ε ∘ₗ η = LinearMap.id ∧ η ∘ₗ ε = LinearMap.id := by
  constructor
  · ext m
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    refine @Module.eq_of_localization_maximal R M _ _ _
      (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => inferInstance) (fun P _ => inferInstance)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      (fun P _ => inferInstance)
      (ε (η m)) m (fun P _ => ?_)
    have h1 := congr_fun (congr_arg DFunLike.coe (h_comp_unit P))
                          (LocalizedModule.mkLinearMap P.primeCompl M m)
    simp only [LinearMap.id_coe, id_eq] at h1
    rw [show (LocalizedModule.map P.primeCompl (ε ∘ₗ η))
            (LocalizedModule.mkLinearMap P.primeCompl M m) =
         LocalizedModule.mkLinearMap P.primeCompl M ((ε ∘ₗ η) m) from
      IsLocalizedModule.map_apply P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M)
        (LocalizedModule.mkLinearMap P.primeCompl M) (ε ∘ₗ η) m] at h1
    exact h1
  · ext n
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    refine @Module.eq_of_localization_maximal R N _ _ _
      (fun P _ => LocalizedModule P.primeCompl N)
      (fun P _ => inferInstance) (fun P _ => inferInstance)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl N)
      (fun P _ => inferInstance)
      (η (ε n)) n (fun P _ => ?_)
    have h1 := congr_fun (congr_arg DFunLike.coe (h_comp_counit P))
                          (LocalizedModule.mkLinearMap P.primeCompl N n)
    simp only [LinearMap.id_coe, id_eq] at h1
    rw [show (LocalizedModule.map P.primeCompl (η ∘ₗ ε))
            (LocalizedModule.mkLinearMap P.primeCompl N n) =
         LocalizedModule.mkLinearMap P.primeCompl N ((η ∘ₗ ε) n) from
      IsLocalizedModule.map_apply P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl N)
        (LocalizedModule.mkLinearMap P.primeCompl N) (η ∘ₗ ε) n] at h1
    exact h1

end QCohEquivalenceProof
