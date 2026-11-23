/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section TensorLeftExact

/-- In a rigid category, the left-tensor functor `X ⊗ -` preserves all limits, as it is the
right adjoint of `Xᘁ ⊗ -`. -/
noncomputable instance tensorLeft_preservesLimitsOfSize (X : C) :
    PreservesLimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction X (Xᘁ)).rightAdjoint_preservesLimits

/-- In a rigid category, the left-tensor functor `X ⊗ -` preserves all colimits, as it is the
left adjoint of `ᘁX ⊗ -`. -/
noncomputable instance tensorLeft_preservesColimitsOfSize (X : C) :
    PreservesColimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

/-- The left-tensor functor `X ⊗ -` in a rigid category preserves finite limits. -/
noncomputable instance tensorLeft_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorLeft X) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The left-tensor functor `X ⊗ -` in a rigid category preserves finite colimits. -/
noncomputable instance tensorLeft_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorLeft X) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end TensorLeftExact

section TensorRightExact

/-- In a rigid category, the right-tensor functor `- ⊗ X` preserves all limits, as it is the
right adjoint of `- ⊗ ᘁX`. -/
noncomputable instance tensorRight_preservesLimitsOfSize (X : C) :
    PreservesLimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction (ᘁX) X).rightAdjoint_preservesLimits

/-- In a rigid category, the right-tensor functor `- ⊗ X` preserves all colimits, as it is the
left adjoint of `- ⊗ Xᘁ`. -/
noncomputable instance tensorRight_preservesColimitsOfSize (X : C) :
    PreservesColimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction X (Xᘁ)).leftAdjoint_preservesColimits

/-- The right-tensor functor `- ⊗ X` in a rigid category preserves finite limits. -/
noncomputable instance tensorRight_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorRight X) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The right-tensor functor `- ⊗ X` in a rigid category preserves finite colimits. -/
noncomputable instance tensorRight_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorRight X) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end TensorRightExact

section ExactFunctors

/-- The left-tensor functor `X ⊗ -` in a rigid category is exact, packaged as an `exactFunctor`. -/
noncomputable def tensorLeft_exact (X : C) :
    exactFunctor C C (tensorLeft X) :=
  ⟨tensorLeft_preservesFiniteLimits X, tensorLeft_preservesFiniteColimits X⟩

/-- The right-tensor functor `- ⊗ X` in a rigid category is exact, packaged as an `exactFunctor`. -/
noncomputable def tensorRight_exact (X : C) :
    exactFunctor C C (tensorRight X) :=
  ⟨tensorRight_preservesFiniteLimits X, tensorRight_preservesFiniteColimits X⟩

/-- In a rigid category, both `X ⊗ -` and `- ⊗ X` are exact functors. -/
theorem tensor_biexact (X : C) :
    exactFunctor C C (tensorLeft X) ∧ exactFunctor C C (tensorRight X) :=
  ⟨tensorLeft_exact X, tensorRight_exact X⟩

/-- Proposition 1.13.1: in a rigid monoidal category, both left and right tensoring with any
object are exact functors. -/
theorem proposition_1_13_1 (X : C) :
    exactFunctor C C (tensorLeft X) ∧ exactFunctor C C (tensorRight X) :=
  tensor_biexact X

end ExactFunctors

section DualizationExact

/-- The right dualization functor `Cᵒᵖ ⥤ C` sending `X ↦ Xᘁ` and a morphism to its right adjoint mate. -/
noncomputable def rightDualizationFunctor : Cᵒᵖ ⥤ C where
  obj X := (X.unop)ᘁ
  map f := (f.unop)ᘁ
  map_id X := by simp [rightAdjointMate_id]
  map_comp f g := by simp [comp_rightAdjointMate]

/-- The left dualization functor `Cᵒᵖ ⥤ C` sending `X ↦ ᘁX` and a morphism to its left adjoint mate. -/
noncomputable def leftDualizationFunctor : Cᵒᵖ ⥤ C where
  obj X := ᘁ(X.unop)
  map f := ᘁ(f.unop)
  map_id X := by simp [leftAdjointMate_id]
  map_comp f g := by simp [comp_leftAdjointMate]

/-- The right adjoint mate is a bijection `Hom(X, Y) ≃ Hom(Yᘁ, Xᘁ)` induced by the rigid structure. -/
noncomputable def rightAdjointMateEquiv (X Y : C) : (X ⟶ Y) ≃ (Yᘁ ⟶ Xᘁ) :=
  ((Equiv.mk (fun f => f ≫ (ρ_ Y).inv) (fun f => f ≫ (ρ_ Y).hom)
      (by intro f; simp) (by intro f; simp)).trans
  (((tensorLeftHomEquiv X Y (Yᘁ) (𝟙_ C)).symm).trans
  (((tensorRightHomEquiv (Yᘁ) X (Xᘁ) (𝟙_ C))).trans
  (Equiv.mk (fun f => f ≫ (λ_ (Xᘁ)).hom) (fun f => f ≫ (λ_ (Xᘁ)).inv)
      (by intro f; simp) (by intro f; simp)))))

/-- Computation: `rightAdjointMateEquiv` applied to `f` agrees with the underlying right adjoint mate. -/
theorem rightAdjointMateEquiv_apply (X Y : C) (f : X ⟶ Y) :
    rightAdjointMateEquiv X Y f = rightAdjointMate f := by
  simp only [rightAdjointMateEquiv, Equiv.trans_apply]
  dsimp [Equiv.mk]
  simp only [rightAdjointMate, tensorLeftHomEquiv, tensorRightHomEquiv]
  dsimp
  monoidal

/-- The left adjoint mate is a bijection `Hom(X, Y) ≃ Hom(ᘁY, ᘁX)` induced by the rigid structure. -/
noncomputable def leftAdjointMateEquiv (X Y : C) : (X ⟶ Y) ≃ ((ᘁY : C) ⟶ (ᘁX : C)) :=
  ((Equiv.mk (fun f => f ≫ (λ_ Y).inv) (fun f => f ≫ (λ_ Y).hom)
      (by intro f; simp) (by intro f; simp)).trans
  (((tensorRightHomEquiv X (ᘁY : C) Y (𝟙_ C)).symm).trans
  (((tensorLeftHomEquiv (ᘁY : C) (ᘁX : C) X (𝟙_ C))).trans
  (Equiv.mk (fun f => f ≫ (ρ_ (ᘁX : C)).hom) (fun f => f ≫ (ρ_ (ᘁX : C)).inv)
      (by intro f; simp) (by intro f; simp)))))

/-- Computation: `leftAdjointMateEquiv` applied to `f` agrees with the underlying left adjoint mate. -/
theorem leftAdjointMateEquiv_apply (X Y : C) (f : X ⟶ Y) :
    leftAdjointMateEquiv X Y f = leftAdjointMate f := by
  simp only [leftAdjointMateEquiv, Equiv.trans_apply]
  dsimp [Equiv.mk]
  simp only [leftAdjointMate, tensorLeftHomEquiv, tensorRightHomEquiv]
  dsimp
  monoidal

/-- The right dualization functor `Cᵒᵖ ⥤ C` is faithful, as the right adjoint mate is injective. -/
instance rightDualizationFunctor_faithful :
    (rightDualizationFunctor (C := C)).Faithful where
  map_injective {X Y f₁ f₂} h := by
    apply Quiver.Hom.unop_inj
    apply (rightAdjointMateEquiv Y.unop X.unop).injective
    simp only [rightAdjointMateEquiv_apply]
    exact h

/-- The right dualization functor `Cᵒᵖ ⥤ C` is full, as the right adjoint mate is surjective. -/
instance rightDualizationFunctor_full :
    (rightDualizationFunctor (C := C)).Full where
  map_surjective {X Y} g := by
    obtain ⟨h, hh⟩ := (rightAdjointMateEquiv Y.unop X.unop).surjective g
    exact ⟨h.op, by simp [rightDualizationFunctor, ← rightAdjointMateEquiv_apply, hh]⟩

/-- The right dualization functor `Cᵒᵖ ⥤ C` is essentially surjective: every `Z` is `(ᘁZ)ᘁ`. -/
instance rightDualizationFunctor_essSurj :
    (rightDualizationFunctor (C := C)).EssSurj where
  mem_essImage Z := by
    refine ⟨op (ᘁZ), ⟨?_⟩⟩
    change rightDualizationFunctor.obj (op (ᘁZ)) ≅ Z
    simp only [rightDualizationFunctor]


    exact rightDualIso (RightRigidCategory.rightDual (ᘁZ)).exact hasRightDualLeftDual.exact

/-- The right dualization functor `Cᵒᵖ ⥤ C` is an equivalence of categories. -/
noncomputable instance rightDualizationFunctor_isEquivalence :
    (rightDualizationFunctor (C := C)).IsEquivalence where

/-- The right dualization functor preserves all limits, since it is an equivalence. -/
noncomputable instance rightDualizationFunctor_preservesLimits :
    PreservesLimitsOfSize.{v, v} (rightDualizationFunctor (C := C)) :=
  inferInstance

/-- The right dualization functor preserves all colimits, since it is an equivalence. -/
noncomputable instance rightDualizationFunctor_preservesColimits :
    PreservesColimitsOfSize.{v, v} (rightDualizationFunctor (C := C)) :=
  inferInstance

/-- The right dualization functor preserves finite limits. -/
noncomputable instance rightDualizationFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (rightDualizationFunctor (C := C)) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The right dualization functor preserves finite colimits. -/
noncomputable instance rightDualizationFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (rightDualizationFunctor (C := C)) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The left dualization functor `Cᵒᵖ ⥤ C` is faithful, as the left adjoint mate is injective. -/
instance leftDualizationFunctor_faithful :
    (leftDualizationFunctor (C := C)).Faithful where
  map_injective {X Y f₁ f₂} h := by
    apply Quiver.Hom.unop_inj
    apply (leftAdjointMateEquiv Y.unop X.unop).injective
    simp only [leftAdjointMateEquiv_apply]
    exact h

/-- The left dualization functor `Cᵒᵖ ⥤ C` is full, as the left adjoint mate is surjective. -/
instance leftDualizationFunctor_full :
    (leftDualizationFunctor (C := C)).Full where
  map_surjective {X Y} g := by
    obtain ⟨h, hh⟩ := (leftAdjointMateEquiv Y.unop X.unop).surjective g
    exact ⟨h.op, by simp [leftDualizationFunctor, ← leftAdjointMateEquiv_apply, hh]⟩

/-- The left dualization functor `Cᵒᵖ ⥤ C` is essentially surjective: every `Z` is `ᘁ(Zᘁ)`. -/
instance leftDualizationFunctor_essSurj :
    (leftDualizationFunctor (C := C)).EssSurj where
  mem_essImage Z := by
    refine ⟨op (Zᘁ), ⟨?_⟩⟩
    change leftDualizationFunctor.obj (op (Zᘁ)) ≅ Z
    simp only [leftDualizationFunctor]


    exact leftDualIso (LeftRigidCategory.leftDual (Zᘁ)).exact hasLeftDualRightDual.exact

/-- The left dualization functor `Cᵒᵖ ⥤ C` is an equivalence of categories. -/
noncomputable instance leftDualizationFunctor_isEquivalence :
    (leftDualizationFunctor (C := C)).IsEquivalence where

/-- The left dualization functor preserves all limits, since it is an equivalence. -/
noncomputable instance leftDualizationFunctor_preservesLimits :
    PreservesLimitsOfSize.{v, v} (leftDualizationFunctor (C := C)) :=
  inferInstance

/-- The left dualization functor preserves all colimits, since it is an equivalence. -/
noncomputable instance leftDualizationFunctor_preservesColimits :
    PreservesColimitsOfSize.{v, v} (leftDualizationFunctor (C := C)) :=
  inferInstance

/-- The left dualization functor preserves finite limits. -/
noncomputable instance leftDualizationFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (leftDualizationFunctor (C := C)) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The left dualization functor preserves finite colimits. -/
noncomputable instance leftDualizationFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (leftDualizationFunctor (C := C)) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The right dualization functor `Cᵒᵖ ⥤ C` is exact, packaged as an `exactFunctor`. -/
noncomputable def rightDualizationFunctor_exact :
    exactFunctor Cᵒᵖ C (rightDualizationFunctor (C := C)) :=
  ⟨rightDualizationFunctor_preservesFiniteLimits,
   rightDualizationFunctor_preservesFiniteColimits⟩

/-- The left dualization functor `Cᵒᵖ ⥤ C` is exact, packaged as an `exactFunctor`. -/
noncomputable def leftDualizationFunctor_exact :
    exactFunctor Cᵒᵖ C (leftDualizationFunctor (C := C)) :=
  ⟨leftDualizationFunctor_preservesFiniteLimits,
   leftDualizationFunctor_preservesFiniteColimits⟩

/-- Both dualization functors `Cᵒᵖ ⥤ C` are exact in a rigid category. -/
theorem dualization_exact :
    exactFunctor Cᵒᵖ C (rightDualizationFunctor (C := C)) ∧
    exactFunctor Cᵒᵖ C (leftDualizationFunctor (C := C)) :=
  ⟨rightDualizationFunctor_exact, leftDualizationFunctor_exact⟩

/-- Proposition 1.13.5: in a rigid monoidal category, both dualization functors
`Cᵒᵖ ⥤ C` are exact. -/
theorem prop_1_13_5 :
    exactFunctor Cᵒᵖ C (rightDualizationFunctor (C := C)) ∧
    exactFunctor Cᵒᵖ C (leftDualizationFunctor (C := C)) :=
  dualization_exact

end DualizationExact

end CategoryTheory
