/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive

open CategoryTheory MonoidalCategory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

/-- In a preadditive monoidal category, an object whose right dual is zero is itself zero. -/
theorem isZero_of_isZero_rightDual {X : C} [HasRightDual X] (h : IsZero (Xᘁ)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  have hid : 𝟙 (Xᘁ) = 0 := (IsZero.iff_id_eq_zero _).mp h
  have hXY_zero : 𝟙 (X ⊗ Xᘁ) = 0 := by
    rw [← whiskerLeft_id X Xᘁ, hid, MonoidalPreadditive.whiskerLeft_zero]
  have heta : η_ X Xᘁ = 0 := by
    calc η_ X Xᘁ = η_ X Xᘁ ≫ 𝟙 (X ⊗ Xᘁ) := (Category.comp_id _).symm
      _ = η_ X Xᘁ ≫ 0 := by rw [hXY_zero]
      _ = 0 := comp_zero
  have htri := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [show η_ X Xᘁ ▷ X = 0 from by rw [heta, MonoidalPreadditive.zero_whiskerRight],
      zero_comp] at htri

  have hrho_inv : (ρ_ X).inv = 0 := by
    calc (ρ_ X).inv = (λ_ X).inv ≫ ((λ_ X).hom ≫ (ρ_ X).inv) := by rw [Iso.inv_hom_id_assoc]
      _ = (λ_ X).inv ≫ 0 := by rw [htri]
      _ = 0 := comp_zero
  calc 𝟙 X = (ρ_ X).inv ≫ (ρ_ X).hom := (Iso.inv_hom_id _).symm
    _ = 0 ≫ (ρ_ X).hom := by rw [hrho_inv]
    _ = 0 := zero_comp

/-- In a preadditive monoidal category, the right dual of a zero object is zero. -/
theorem isZero_rightDual_of_isZero {X : C} [HasRightDual X] (h : IsZero X) : IsZero (Xᘁ) := by
  rw [IsZero.iff_id_eq_zero]
  have hid : 𝟙 X = 0 := (IsZero.iff_id_eq_zero X).mp h
  have hYX_zero : 𝟙 (Xᘁ ⊗ X) = 0 := by
    rw [← whiskerLeft_id Xᘁ X, hid, MonoidalPreadditive.whiskerLeft_zero]
  have heps : ε_ X Xᘁ = 0 := by
    calc ε_ X Xᘁ = 𝟙 _ ≫ ε_ X Xᘁ := (Category.id_comp _).symm
      _ = 0 ≫ ε_ X Xᘁ := by rw [hYX_zero]
      _ = 0 := zero_comp
  have htri := ExactPairing.coevaluation_evaluation X Xᘁ
  rw [show ε_ X Xᘁ ▷ Xᘁ = 0 from by rw [heps, MonoidalPreadditive.zero_whiskerRight],
      comp_zero, comp_zero] at htri

  have hlambda_inv : (λ_ Xᘁ).inv = 0 := by
    calc (λ_ Xᘁ).inv = (ρ_ Xᘁ).inv ≫ ((ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv) := by
          rw [Iso.inv_hom_id_assoc]
      _ = (ρ_ Xᘁ).inv ≫ 0 := by rw [htri]
      _ = 0 := comp_zero
  calc 𝟙 Xᘁ = (λ_ Xᘁ).inv ≫ (λ_ Xᘁ).hom := (Iso.inv_hom_id _).symm
    _ = 0 ≫ (λ_ Xᘁ).hom := by rw [hlambda_inv]
    _ = 0 := zero_comp

/-- In a preadditive monoidal category, an object whose left dual is zero is itself zero. -/
theorem isZero_of_isZero_leftDual {X : C} [HasLeftDual X] (h : IsZero (ᘁX : C)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  have hid : 𝟙 (ᘁX : C) = 0 := (IsZero.iff_id_eq_zero _).mp h
  have hYX_zero : 𝟙 ((ᘁX : C) ⊗ X) = 0 := by
    rw [← id_whiskerRight (ᘁX : C) X, hid, MonoidalPreadditive.zero_whiskerRight]
  have heta : η_ (ᘁX : C) X = 0 := by
    calc η_ (ᘁX : C) X = η_ (ᘁX : C) X ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = η_ (ᘁX : C) X ≫ 0 := by rw [hYX_zero]
      _ = 0 := comp_zero
  have h_whisker : X ◁ η_ (ᘁX : C) X = 0 := by
    rw [heta, MonoidalPreadditive.whiskerLeft_zero]
  have htri := ExactPairing.coevaluation_evaluation (ᘁX : C) X
  rw [h_whisker, zero_comp] at htri

  have hlambda_inv : (λ_ X).inv = 0 := by
    calc (λ_ X).inv = (ρ_ X).inv ≫ ((ρ_ X).hom ≫ (λ_ X).inv) := by rw [Iso.inv_hom_id_assoc]
      _ = (ρ_ X).inv ≫ 0 := by rw [htri]
      _ = 0 := comp_zero
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := (Iso.inv_hom_id _).symm
    _ = 0 ≫ (λ_ X).hom := by rw [hlambda_inv]
    _ = 0 := zero_comp

/-- In a preadditive monoidal category, the left dual of a zero object is zero. -/
theorem isZero_leftDual_of_isZero {X : C} [HasLeftDual X] (h : IsZero X) : IsZero (ᘁX : C) := by
  rw [IsZero.iff_id_eq_zero]
  have hid : 𝟙 X = 0 := (IsZero.iff_id_eq_zero X).mp h
  have hXY_zero : 𝟙 (X ⊗ (ᘁX : C)) = 0 := by
    rw [← id_whiskerRight X (ᘁX : C), hid, MonoidalPreadditive.zero_whiskerRight]
  have heps : ε_ (ᘁX : C) X = 0 := by
    calc ε_ (ᘁX : C) X = 𝟙 _ ≫ ε_ (ᘁX : C) X := (Category.id_comp _).symm
      _ = 0 ≫ ε_ (ᘁX : C) X := by rw [hXY_zero]
      _ = 0 := zero_comp
  have h_whisker : (ᘁX : C) ◁ ε_ (ᘁX : C) X = 0 := by
    rw [heps, MonoidalPreadditive.whiskerLeft_zero]
  have htri := ExactPairing.evaluation_coevaluation (ᘁX : C) X
  rw [h_whisker, comp_zero, comp_zero] at htri

  have hrho_inv : (ρ_ (ᘁX : C)).inv = 0 := by
    calc (ρ_ (ᘁX : C)).inv
        = (λ_ (ᘁX : C)).inv ≫ ((λ_ (ᘁX : C)).hom ≫ (ρ_ (ᘁX : C)).inv) := by
          rw [Iso.inv_hom_id_assoc]
      _ = (λ_ (ᘁX : C)).inv ≫ 0 := by rw [htri]
      _ = 0 := comp_zero
  calc 𝟙 (ᘁX : C) = (ρ_ (ᘁX : C)).inv ≫ (ρ_ (ᘁX : C)).hom := (Iso.inv_hom_id _).symm
    _ = 0 ≫ (ρ_ (ᘁX : C)).hom := by rw [hrho_inv]
    _ = 0 := zero_comp

end CategoryTheory
