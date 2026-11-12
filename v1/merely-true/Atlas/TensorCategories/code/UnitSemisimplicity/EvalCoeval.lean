/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Abelian.Basic
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u

noncomputable section

namespace TensorCategories

/-- The evaluation morphism `ε_ X Xᘁ : X ⊗ X* → 𝟙` is nonzero whenever `X` is
nonzero, in a preadditive right-rigid monoidal category. -/
lemma evaluation_ne_zero_of_nonzero_obj {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Preadditive C] [RightRigidCategory C]
    [MonoidalPreadditive C] (X : C) (hX : ¬ IsZero X) : ε_ X Xᘁ ≠ 0 := by
  intro h
  apply hX; rw [IsZero.iff_id_eq_zero]
  have zig := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [h] at zig
  simp [MonoidalPreadditive.whiskerLeft_zero] at zig
  have hlam : (λ_ X).hom = 0 := by rw [← cancel_mono (ρ_ X).inv]; simp [zig]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

end TensorCategories
