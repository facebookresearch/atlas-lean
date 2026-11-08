/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits ZeroObject

universe v u

noncomputable section

namespace TensorNondegen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- The right-tensor functor `- ⊗ Y` in a preadditive monoidal category preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms (Y : C) :
    (tensorRight Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.zero_whiskerRight

/-- The left-tensor functor `Y ⊗ -` in a preadditive monoidal category preserves zero morphisms. -/
instance tensorLeft_preservesZeroMorphisms (Y : C) :
    (tensorLeft Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.whiskerLeft_zero

/-- In a rigid braided abelian preadditive monoidal category, if `X ⊗ X` is zero then `X` is zero. -/
theorem isZero_of_tensorSelf_isZero (X : C) (h : IsZero (X ⊗ X)) : IsZero X := by

  have h1 : IsZero ((X ⊗ X) ⊗ HasRightDual.rightDual X) :=
    (tensorRight _).map_isZero h

  have h2 : IsZero (X ⊗ (X ⊗ HasRightDual.rightDual X)) :=
    h1.of_iso (α_ X X (HasRightDual.rightDual X)).symm


  have h3 : IsZero (X ⊗ (HasRightDual.rightDual X ⊗ X)) :=
    h2.of_iso ((tensorLeft X).mapIso (β_ (HasRightDual.rightDual X) X))

  have h4 : IsZero ((X ⊗ HasRightDual.rightDual X) ⊗ X) :=
    h3.of_iso (α_ X (HasRightDual.rightDual X) X)


  have hz : η_ X (HasRightDual.rightDual X) ▷ X = 0 :=
    h4.eq_of_tgt _ _


  have zigzag := ExactPairing.evaluation_coevaluation X (HasRightDual.rightDual X)

  rw [hz, zero_comp] at zigzag


  have hlam : (λ_ X).hom = 0 := by
    have : (λ_ X).hom = ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by simp
    rw [this, zigzag.symm, zero_comp]

  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

/-- Corollary: an object whose tensor square is isomorphic to the zero object is itself
isomorphic to zero. -/
def iso_zero_of_tensorSelf_iso_zero (X : C) (e : X ⊗ X ≅ (0 : C)) : X ≅ (0 : C) :=
  (isZero_of_tensorSelf_isZero X (e.isZero_iff.mpr (isZero_zero C))).iso (isZero_zero C)

end TensorNondegen
