/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctorDefs

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- Lemma 2.13.2 (EGNO). Composition with a module functor between exact module categories
preserves both monomorphisms and epimorphisms of module natural transformations: post-composition
with `G` preserves mono/epi pointwise, and pre-composition with `F` reflects mono/epi on
objects of the form `F(A)`. -/
theorem Lemma_2_13_2
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [FiniteMultitensorBase C]
    {M₁ : Type u₂} [Category.{v₂} M₁] [ExactModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [ExactModuleCategory C M₂]
    [ExactModuleInfra C M₂]
    {M₃ : Type u₄} [Category.{v₄} M₃] [ExactModuleCategory C M₃] :


    (∀ (G : ModuleFunctor C M₂ M₃) {F₁ F₂ : ModuleFunctor C M₁ M₂}
      (η : F₁ ⟶ F₂),
      (∀ (A : M₁), Mono (η.natTrans.app A) → Mono (G.toFunctor.map (η.natTrans.app A))) ∧
      (∀ (A : M₁), Epi (η.natTrans.app A) → Epi (G.toFunctor.map (η.natTrans.app A)))) ∧


    (∀ (F : ModuleFunctor C M₁ M₂) {G₁ G₂ : ModuleFunctor C M₂ M₃}
      (η : G₁ ⟶ G₂),
      ((∀ (B : M₂), Mono (η.natTrans.app B)) →
        ∀ (A : M₁), Mono (η.natTrans.app (F.toFunctor.obj A))) ∧
      ((∀ (B : M₂), Epi (η.natTrans.app B)) →
        ∀ (A : M₁), Epi (η.natTrans.app (F.toFunctor.obj A)))) := by
  constructor
  ·

    intro G F₁ F₂ η
    have hG := proposition_2_7_8 G
    exact ⟨fun A hm => hG.preserves_mono (η.natTrans.app A) hm,
           fun A he => hG.preserves_epi (η.natTrans.app A) he⟩
  ·

    intro F G₁ G₂ η
    exact ⟨fun hm A => hm (F.toFunctor.obj A), fun he A => he (F.toFunctor.obj A)⟩

end CategoryTheory
