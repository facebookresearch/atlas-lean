/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
import Atlas.TensorCategories.code.TensorNondegen.DualZero
import Atlas.TensorCategories.code.TensorNondegen.EvalCoevalArg

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u

noncomputable section

/-- Nondegeneracy of the tensor product in an abelian monoidal category: tensoring with self
detects zero, and the right dual is zero iff the object is zero. -/
class TensorNondegenerate (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Abelian C] : Prop where
  isZero_of_tensor_self_isZero : ∀ (X : C), IsZero (X ⊗ X) → IsZero X
  isZero_rightDual_of_isZero : ∀ (X : C) [HasRightDual X], IsZero X → IsZero (Xᘁ)
  isZero_of_isZero_rightDual : ∀ (X : C) [HasRightDual X], IsZero (Xᘁ) → IsZero X

section Instance

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- Any rigid braided abelian monoidal preadditive category has a nondegenerate tensor product. -/
instance tensorNondegenerate_of_rigidCategory : TensorNondegenerate C where
  isZero_of_tensor_self_isZero := TensorNondegen.isZero_of_tensorSelf_isZero
  isZero_rightDual_of_isZero := fun _ _ h => CategoryTheory.isZero_rightDual_of_isZero h
  isZero_of_isZero_rightDual := fun _ _ h => CategoryTheory.isZero_of_isZero_rightDual h

end Instance

section FullNondegeneracy

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C]

end FullNondegeneracy
