/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.Projective
import Atlas.TensorCategories.code.TensorProjective.TensorSummand
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits

open CategoryTheory MonoidalCategory

universe v u

namespace Formalization.TensorProjective.Proposition_1_13_6

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Part of Proposition 1.13.6: if `P` is projective and `X` has a right dual, and tensoring
on the right preserves epimorphisms, then `P ⊗ X` is projective. -/
theorem projective_tensor_of_hasRightDual
    {P X : C} [Projective P] [HasRightDual X]
    (hEpi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
    Projective (P ⊗ X) where
  factors := by
    intro E Y f e he
    haveI := he
    let f' : P ⟶ Y ⊗ (Xᘁ : C) := (tensorRightHomEquiv P X (Xᘁ : C) Y) f
    haveI : Epi (e ▷ (Xᘁ : C)) := hEpi e (Xᘁ : C)
    obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ (Xᘁ : C))
    use (tensorRightHomEquiv P X (Xᘁ : C) E).symm g'
    apply (tensorRightHomEquiv P X (Xᘁ : C) Y).injective
    rw [tensorRightHomEquiv_naturality]
    change (tensorRightHomEquiv P X (Xᘁ : C) E)
      ((tensorRightHomEquiv P X (Xᘁ : C) E).symm g') ≫ e ▷ (Xᘁ : C) = f'
    rw [Equiv.apply_symm_apply]
    exact hg'

end Formalization.TensorProjective.Proposition_1_13_6
