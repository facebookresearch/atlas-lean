/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

/-- A morphism between varieties, defined here as a scheme morphism `X ⟶ Y`. -/
abbrev VarietyMorphism (X Y : Scheme.{u}) : Type u := X ⟶ Y

namespace VarietyMorphism

variable {X Y Z : Scheme.{u}}

section ContinuousMap

/-- The underlying map of a morphism of varieties is continuous. -/
lemma continuous_base (f : VarietyMorphism X Y) : Continuous (f : X → Y) :=
  f.continuous

end ContinuousMap

section PullbackRegular

/-- Pullback of regular sections along a morphism: a function on `U ⊆ Y` pulls back to a function
on the preimage `f⁻¹(U) ⊆ X`. -/
def pullbackSections (f : VarietyMorphism X Y) (U : Y.Opens) :
    Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.app U

/-- Pullback of global regular sections along a morphism of varieties. -/
def pullbackGlobal (f : VarietyMorphism X Y) :
    Γ(Y, ⊤) ⟶ Γ(X, ⊤) :=
  f.appTop

end PullbackRegular

section Functoriality

/-- Pullback along the identity morphism is the identity. -/
lemma pullback_id (U : X.Opens) :
    pullbackSections (𝟙 X : VarietyMorphism X X) U = 𝟙 Γ(X, U) :=
  Scheme.Hom.id_app U

/-- Pullback of sections is contravariantly functorial: pullback along `f ≫ g` equals pullback
along `g` followed by pullback along `f`. -/
lemma pullback_comp (f : VarietyMorphism X Y) (g : VarietyMorphism Y Z) (U : Z.Opens) :
    pullbackSections (f ≫ g) U =
      pullbackSections g U ≫ pullbackSections f (g ⁻¹ᵁ U) :=
  Scheme.Hom.comp_app f g U

end Functoriality

section LocallyRingedSpace

/-- The underlying morphism of locally ringed spaces of a morphism of varieties. -/
def toLocallyRingedSpaceHom (f : VarietyMorphism X Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom

end LocallyRingedSpace

end VarietyMorphism
