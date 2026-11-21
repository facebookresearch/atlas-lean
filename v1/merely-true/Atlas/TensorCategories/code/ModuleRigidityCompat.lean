/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace ExactModuleCategory

open Category MonoidalCategory LeftModCat

/-- Data of evaluation and coevaluation morphisms compatible with a module action on `M`,
together with the zigzag identities relating them to the module structure on `M`. -/
class ModuleEvalCoeval
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] where
  modEval : ∀ (P : C), HasLeftDual.leftDual P ⊗ P ⟶ 𝟙_ C
  modCoeval : ∀ (P : C), 𝟙_ C ⟶ P ⊗ HasLeftDual.leftDual P
  zigzag_left : ∀ (P : C) (N A : M) (g : (ᘁP : C) ⊗ᵐ A ⟶ N),
    (ᘁP : C) ◁ᵐ ((actℓ_ A).inv ≫ (modCoeval P) ▷ᵐ A ≫
      (actμ_ P (ᘁP : C) A).hom ≫ P ◁ᵐ g) ≫
      (actμ_ (ᘁP : C) P N).inv ≫ (modEval P) ▷ᵐ N ≫ (actℓ_ N).hom = g
  zigzag_right : ∀ (P : C) (N A : M) (f : A ⟶ P ⊗ᵐ N),
    (actℓ_ A).inv ≫ (modCoeval P) ▷ᵐ A ≫ (actμ_ P (ᘁP : C) A).hom ≫
      P ◁ᵐ ((ᘁP : C) ◁ᵐ f ≫ (actμ_ (ᘁP : C) P N).inv ≫
        (modEval P) ▷ᵐ N ≫ (actℓ_ N).hom) = f

section AuxLemmas

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
         {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

omit [LeftRigidCategory C] in
/-- Left whiskering of a module action distributes over composition of morphisms in `M`. -/
theorem actWhiskerLeft_comp (X : C) {N₁ N₂ N₃ : M} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
  have h := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
  simp only [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight,
    id_comp, comp_id] at h
  exact h.symm

end AuxLemmas

section Construction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
         {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
         [hMEC : ModuleEvalCoeval C M]

/-- Shorthand for the evaluation morphism `(ᘁP) ⊗ P ⟶ 𝟙_ C` supplied by `ModuleEvalCoeval`. -/
abbrev ev (P : C) : (ᘁP : C) ⊗ P ⟶ 𝟙_ C :=
  hMEC.modEval P

/-- Shorthand for the coevaluation morphism `𝟙_ C ⟶ P ⊗ (ᘁP)` supplied by `ModuleEvalCoeval`. -/
abbrev coev (P : C) : 𝟙_ C ⟶ P ⊗ (ᘁP : C) :=
  hMEC.modCoeval P

/-- A `ModuleEvalCoeval` structure on `(C, M)` produces a `ModuleRigidityCompat` instance,
using the supplied evaluation/coevaluation and zigzag identities. -/
noncomputable instance ofEvalCoeval :
    ModuleRigidityCompat C M where
  modRigidForward P N A f :=
    (ᘁP : C) ◁ᵐ f ≫ (actμ_ (ᘁP : C) P N).inv ≫
      (ev P) ▷ᵐ N ≫ (actℓ_ N).hom
  modRigidBackward P N A g :=
    (actℓ_ A).inv ≫ (coev P) ▷ᵐ A ≫
      (actμ_ P (ᘁP : C) A).hom ≫ P ◁ᵐ g
  modRigid_left_inv P N A g := hMEC.zigzag_left P N A g
  modRigid_right_inv P N A f := hMEC.zigzag_right P N A f
  modRigidForward_natural P N e g := by
    intro e' g'
    rw [actWhiskerLeft_comp, assoc]

end Construction

section BraidedConstruction

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
         [BraidedCategory C] [LeftRigidCategory C]
         (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M]




end BraidedConstruction

end ExactModuleCategory

end CategoryTheory
