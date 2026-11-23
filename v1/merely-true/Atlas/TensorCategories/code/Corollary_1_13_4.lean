/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Functor.EpiMono

open CategoryTheory MonoidalCategory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Abelian C]

/-- Image-tensor isomorphism: in a rigid abelian monoidal category, `Im(f₁) ⊗ Im(f₂)` is
canonically isomorphic to `Im(f₁ ⊗ f₂)`. -/
noncomputable def image_tensor_iso
    {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    image f₁ ⊗ image f₂ ≅ image (f₁ ⊗ₘ f₂) := by

  have fac : (factorThruImage f₁ ⊗ₘ factorThruImage f₂) ≫
      (image.ι f₁ ⊗ₘ image.ι f₂) = f₁ ⊗ₘ f₂ := by
    rw [tensorHom_comp_tensorHom, image.fac, image.fac]


  haveI : StrongEpi (factorThruImage f₁ ⊗ₘ factorThruImage f₂) := by
    rw [MonoidalCategory.tensorHom_def]
    haveI : (tensorRight X₂).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction (tensorRightAdjunction X₂ (X₂ᘁ))
    haveI : (tensorRight (X₂ᘁ)).PreservesMonomorphisms :=
      Functor.preservesMonomorphisms_of_adjunction (tensorRightAdjunction (ᘁ(X₂ᘁ)) (X₂ᘁ))
    haveI : StrongEpi ((factorThruImage f₁) ▷ X₂) := by
      show StrongEpi ((tensorRight X₂).map (factorThruImage f₁))
      exact Adjunction.strongEpi_map_of_strongEpi (tensorRightAdjunction X₂ (X₂ᘁ)) _
    haveI : (tensorLeft (image f₁)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        (tensorLeftAdjunction (ᘁ(image f₁)) (image f₁))
    haveI : (tensorLeft (ᘁ(image f₁))).PreservesMonomorphisms :=
      Functor.preservesMonomorphisms_of_adjunction
        (tensorLeftAdjunction (ᘁ(image f₁)) ((ᘁ(image f₁))ᘁ))
    haveI : StrongEpi ((image f₁) ◁ (factorThruImage f₂)) := by
      show StrongEpi ((tensorLeft (image f₁)).map (factorThruImage f₂))
      exact Adjunction.strongEpi_map_of_strongEpi
        (tensorLeftAdjunction (ᘁ(image f₁)) (image f₁)) _
    exact strongEpi_comp _ _

  haveI : Mono (image.ι f₁ ⊗ₘ image.ι f₂) := by
    rw [MonoidalCategory.tensorHom_def]
    haveI : (tensorRight (image f₂)).PreservesMonomorphisms :=
      Functor.preservesMonomorphisms_of_adjunction
        (tensorRightAdjunction (ᘁ(image f₂)) (image f₂))
    haveI : Mono ((image.ι f₁) ▷ (image f₂)) := by
      show Mono ((tensorRight (image f₂)).map (image.ι f₁))
      infer_instance
    haveI : (tensorLeft Y₁).PreservesMonomorphisms :=
      Functor.preservesMonomorphisms_of_adjunction (tensorLeftAdjunction Y₁ (Y₁ᘁ))
    haveI : Mono (Y₁ ◁ (image.ι f₂)) := by
      show Mono ((tensorLeft Y₁).map (image.ι f₂))
      infer_instance
    exact mono_comp _ _

  exact image.isoStrongEpiMono _ _ fac

/-- Corollary 1.13.4 (EGNO): for any pair of morphisms `f₁, f₂` in a multiring category `C`
one has `Im(f₁ ⊗ f₂) = Im(f₁) ⊗ Im(f₂)`. -/
noncomputable def Corollary_1_13_4
    {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    image f₁ ⊗ image f₂ ≅ image (f₁ ⊗ₘ f₂) :=
  image_tensor_iso f₁ f₂

/-- Corollary 1.13.4 (EGNO): for any pair of morphisms `f₁, f₂` in a multiring category `C`
one has `Im(f₁ ⊗ f₂) = Im(f₁) ⊗ Im(f₂)`. -/
noncomputable def corollary_1_13_4
    {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    image f₁ ⊗ image f₂ ≅ image (f₁ ⊗ₘ f₂) :=
  image_tensor_iso f₁ f₂

end CategoryTheory
