/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Spec

open AlgebraicGeometry CategoryTheory

/-- Lemma 27 (Lec 13): a morphism of schemes `f : X → Y` is affine iff the preimage of
every affine open of `Y` is an affine open of `X`. -/
theorem lemma27_affine_morphism_iff {X Y : Scheme} (f : X ⟶ Y) :
    IsAffineHom f ↔ ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U) :=
  isAffineHom_iff f

/-- Forward direction of Lemma 27: if `f` is affine, then preimages of affine opens
are affine opens. -/
theorem lemma27_affine_preimage {X Y : Scheme} (f : X ⟶ Y)
    [IsAffineHom f] (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  (isAffineHom_iff f).mp inferInstance U hU

/-- Converse direction of Lemma 27: if preimages of all affine opens are affine,
then `f` is an affine morphism. -/
theorem lemma27_affineHom_of_preimages_affine {X Y : Scheme} (f : X ⟶ Y)
    (h : ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)) :
    IsAffineHom f :=
  (isAffineHom_iff f).mpr h

/-- A morphism `f : X → Y` is finite iff it is affine and, for every affine open `U`
of `Y`, the induced ring map `Γ(U, O_Y) → Γ(f⁻¹U, O_X)` is finite. -/
theorem lemma27_finite_morphism_iff {X Y : Scheme} (f : X ⟶ Y) :
    IsFinite f ↔ IsAffineHom f ∧
      ∀ (U : Y.Opens), IsAffineOpen U → (f.app U).hom.Finite :=
  isFinite_iff f

/-- Every finite morphism is affine. -/
theorem lemma27_finite_is_affine {X Y : Scheme} (f : X ⟶ Y) [hf : IsFinite f] :
    IsAffineHom f :=
  ((isFinite_iff f).mp hf).1

/-- If `f` is finite then, on every affine open of `Y`, the corresponding map of
section rings is a finite ring map. -/
theorem lemma27_finite_ringHom_of_finite {X Y : Scheme} (f : X ⟶ Y) [hf : IsFinite f]
    (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.Finite :=
  ((isFinite_iff f).mp hf).2 U hU

/-- Converse: an affine morphism whose induced ring maps on affine opens are all
finite is itself a finite morphism. -/
theorem lemma27_finite_of_affine_and_finite_ringHom {X Y : Scheme} (f : X ⟶ Y)
    (hAff : IsAffineHom f)
    (hFin : ∀ (U : Y.Opens), IsAffineOpen U → (f.app U).hom.Finite) :
    IsFinite f :=
  (isFinite_iff f).mpr ⟨hAff, hFin⟩

/-- Affine case: `Spec.map f : Spec S → Spec R` is finite iff the underlying ring
map `f : R → S` is finite. -/
theorem lemma27_finite_specMap_iff {R S : CommRingCat} (f : R ⟶ S) :
    IsFinite (Spec.map f) ↔ f.hom.Finite :=
  IsFinite.SpecMap_iff f

/-- A morphism is finite iff it is both integral and locally of finite type. -/
theorem lemma27_finite_iff_integral_and_finiteType {X Y : Scheme} (f : X ⟶ Y) :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f :=
  IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f
