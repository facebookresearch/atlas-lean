/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

universe u

lemma mapRange_linearMap_add_apply {k : Type u} [CommRing k] {α M N : Type u}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f g : M →ₗ[k] N) (x : α →₀ M) :
    Finsupp.mapRange.linearMap (f + g) x =
    Finsupp.mapRange.linearMap f x + Finsupp.mapRange.linearMap g x := by
  ext i
  simp [Finsupp.mapRange.linearMap]

instance chainsFunctor_additive (k G : Type u) [CommRing k] [Group G] :
    (groupHomology.chainsFunctor k G).Additive where
  map_add {X Y f g} := by
    ext n : 1
    show (groupHomology.chainsMap (MonoidHom.id G) (f + g)).f n =
      ((groupHomology.chainsMap (MonoidHom.id G) f) +
        (groupHomology.chainsMap (MonoidHom.id G) g)).f n
    have key : ∀ (φ : X ⟶ Y), (groupHomology.chainsMap (MonoidHom.id G) φ).f n =
      ModuleCat.ofHom (Finsupp.mapRange.linearMap (Rep.Hom.hom φ).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun x => (MonoidHom.id G) ∘ x) := fun φ =>
      groupHomology.chainsMap_f (MonoidHom.id G) φ n
    rw [key (f + g)]
    conv_rhs =>
      rw [show (groupHomology.chainsMap (MonoidHom.id G) f +
        groupHomology.chainsMap (MonoidHom.id G) g).f n =
        (groupHomology.chainsMap (MonoidHom.id G) f).f n +
        (groupHomology.chainsMap (MonoidHom.id G) g).f n from rfl, key f, key g]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show ((Finsupp.mapRange.linearMap (Rep.Hom.hom (f + g)).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x) =
      ((Finsupp.mapRange.linearMap (Rep.Hom.hom f).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x) +
      ((Finsupp.mapRange.linearMap (Rep.Hom.hom g).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x)
    simp only [LinearMap.comp_apply]
    rw [show (Rep.Hom.hom (f + g)).toLinearMap =
      (Rep.Hom.hom f).toLinearMap + (Rep.Hom.hom g).toLinearMap from rfl]
    exact mapRange_linearMap_add_apply _ _ _

noncomputable def homology_biprod_iso (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    groupHomology (A ⊞ B) n ≅
    groupHomology A n ⊞ groupHomology B n := by
  open CategoryTheory Limits in
  let F := groupHomology.chainsFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n
  haveI : F.Additive := inferInstance
  haveI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  haveI : PreservesBiproductsOfShape WalkingPair F := PreservesFiniteBiproducts.preserves
  haveI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod A B
