/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive

open CategoryTheory MonoidalCategory Limits

universe u v

section Corollary_1_15_9

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RightRigidCategory C]

/-- For any nonzero object `X` in an abelian rigid monoidal category, the coevaluation
morphism `η_X : 1 → X ⊗ X*` is nonzero. -/
lemma coevaluation_ne_zero {X : C} (hX : ¬ IsZero X) :
    η_ X (Xᘁ) ≠ 0 := by
  intro h
  apply hX
  rw [IsZero.iff_id_eq_zero]
  have triangle := ExactPairing.evaluation_coevaluation X (Xᘁ)
  rw [h, MonoidalPreadditive.zero_whiskerRight] at triangle
  simp only [zero_comp] at triangle
  have heq : (λ_ X).hom ≫ (ρ_ X).inv = 0 := triangle.symm
  have h1 : (ρ_ X).inv = 0 := by
    have := congr_arg ((λ_ X).inv ≫ ·) heq
    simp only [Iso.inv_hom_id_assoc, comp_zero] at this
    exact this
  calc 𝟙 X = (ρ_ X).inv ≫ (ρ_ X).hom := by simp
    _ = 0 ≫ (ρ_ X).hom := by rw [h1]
    _ = 0 := by simp

/-- For any nonzero object `X`, the evaluation morphism `ε_X : X* ⊗ X → 1` is nonzero. -/
lemma evaluation_ne_zero {X : C} (hX : ¬ IsZero X) :
    ε_ X (Xᘁ) ≠ 0 := by
  intro h
  apply hX
  rw [IsZero.iff_id_eq_zero]
  have triangle := ExactPairing.evaluation_coevaluation X (Xᘁ)
  rw [h, MonoidalPreadditive.whiskerLeft_zero] at triangle
  simp only [comp_zero] at triangle
  have heq : (λ_ X).hom ≫ (ρ_ X).inv = 0 := triangle.symm
  have h1 : (ρ_ X).inv = 0 := by
    have := congr_arg ((λ_ X).inv ≫ ·) heq
    simp only [Iso.inv_hom_id_assoc, comp_zero] at this
    exact this
  calc 𝟙 X = (ρ_ X).inv ≫ (ρ_ X).hom := by simp
    _ = 0 ≫ (ρ_ X).hom := by rw [h1]
    _ = 0 := by simp

variable [Simple (𝟙_ C)]

/-- Half of Corollary 1.15.9: in a ring category with right duals and simple unit, the
evaluation morphism is an epimorphism. -/
theorem Corollary_1_15_9_evaluation_epi {X : C} (hX : ¬ IsZero X) :
    Epi (ε_ X (Xᘁ)) :=
  epi_of_nonzero_to_simple (evaluation_ne_zero C hX)

/-- Half of Corollary 1.15.9: in a ring category with right duals and simple unit, the
coevaluation morphism is a monomorphism. -/
theorem Corollary_1_15_9_coevaluation_mono {X : C} (hX : ¬ IsZero X) :
    Mono (η_ X (Xᘁ)) :=
  mono_of_nonzero_from_simple (coevaluation_ne_zero C hX)

/-- Corollary 1.15.9 (EGNO): in a ring category with right duals (and simple unit), the
evaluation morphisms are surjective and the coevaluation morphisms are injective. -/
theorem Corollary_1_15_9 {X : C} (hX : ¬ IsZero X) :
    Epi (ε_ X (Xᘁ)) ∧ Mono (η_ X (Xᘁ)) :=
  ⟨Corollary_1_15_9_evaluation_epi C hX, Corollary_1_15_9_coevaluation_mono C hX⟩

end Corollary_1_15_9
