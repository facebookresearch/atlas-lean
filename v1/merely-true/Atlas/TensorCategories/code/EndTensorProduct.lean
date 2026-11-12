/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

set_option maxHeartbeats 400000

noncomputable section

open CategoryTheory MonoidalCategory

namespace EndTensorProduct

universe u

variable (k : Type u) [Field k]

/-- The external tensor product of two functors `F₁ : C₁ ⥤ FGModuleCat k` and
`F₂ : C₂ ⥤ FGModuleCat k`, taking `(X, Y)` to `F₁(X) ⊗ F₂(Y)`. -/
def functorExternalTensor
    {C₁ : Type u} [Category.{u} C₁]
    {C₂ : Type u} [Category.{u} C₂]
    (F₁ : C₁ ⥤ FGModuleCat.{u} k) (F₂ : C₂ ⥤ FGModuleCat.{u} k) :
    (C₁ × C₂) ⥤ FGModuleCat.{u} k where
  obj XY := F₁.obj XY.1 ⊗ F₂.obj XY.2
  map f := F₁.map f.1 ⊗ₘ F₂.map f.2
  map_id XY := by
    change F₁.map (𝟙 XY.1) ⊗ₘ F₂.map (𝟙 XY.2) = 𝟙 _
    rw [F₁.map_id, F₂.map_id, id_tensorHom_id]
  map_comp f g := by
    change F₁.map (f.1 ≫ g.1) ⊗ₘ F₂.map (f.2 ≫ g.2) = _
    rw [F₁.map_comp, F₂.map_comp, tensorHom_comp_tensorHom]

/-- Semiring structure on the tensor product `End(F₁) ⊗[k] End(F₂)` coming from the
`k`-algebra tensor product. -/
instance endFunctorTensorSemiring
    {C₁ : Type u} [Category.{u} C₁]
    {C₂ : Type u} [Category.{u} C₂]
    (F₁ : C₁ ⥤ FGModuleCat.{u} k) (F₂ : C₂ ⥤ FGModuleCat.{u} k) :
    Semiring (TensorProduct k (End F₁) (End F₂)) :=
  Algebra.TensorProduct.instSemiring

/-- `k`-algebra structure on the tensor product `End(F₁) ⊗[k] End(F₂)`. -/
instance endFunctorTensorAlgebra
    {C₁ : Type u} [Category.{u} C₁]
    {C₂ : Type u} [Category.{u} C₂]
    (F₁ : C₁ ⥤ FGModuleCat.{u} k) (F₂ : C₂ ⥤ FGModuleCat.{u} k) :
    Algebra k (TensorProduct k (End F₁) (End F₂)) :=
  Algebra.TensorProduct.instAlgebra



end EndTensorProduct

end
