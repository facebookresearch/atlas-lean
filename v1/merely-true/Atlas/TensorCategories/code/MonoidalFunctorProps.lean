/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

set_option maxHeartbeats 800000

namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- EGNO Definition 1.4.1: a monoidal functor `F : C ⥤ D`, expressed as the existence of
a `Functor.Monoidal` structure on `F`. -/
abbrev Definition_1_4_1_MonoidalFunctor (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] (F : C ⥤ D) := F.Monoidal

/-- EGNO Definition 1.4.1 (natural transformations): a monoidal natural transformation
between lax monoidal functors. -/
abbrev def_1_4_1_MonoidalNatTrans
    {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (η : F ⟶ G) := NatTrans.IsMonoidal η

/-- EGNO Proposition 1.4.3 (left unitality): for a lax monoidal functor `F`, the left
unitor of `F X` factors through `ε ▷ F X` and `μ (𝟙_ C) X` followed by `F (λ_ X).hom`. -/
theorem Prop_1_4_3_left (F : C ⥤ D) [F.LaxMonoidal] (X : C) :
    (λ_ (F.obj X)).hom =
      LaxMonoidal.ε F ▷ F.obj X ≫ LaxMonoidal.μ F (𝟙_ C) X ≫ F.map (λ_ X).hom :=
  LaxMonoidal.left_unitality F X

/-- EGNO Definition 1.4.5: a monoidal natural transformation between lax monoidal
functors. -/
abbrev def_1_4_5_MonoidalNatTrans
    {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (η : F ⟶ G) := NatTrans.IsMonoidal η

/-- A monoidal functor preserves exact pairings: if `(X, Y)` is an exact pairing in `C`,
then `(F X, F Y)` is an exact pairing in `D`, with evaluation and coevaluation conjugated
by the monoidal structure isomorphisms. -/
noncomputable instance monoidalFunctor_exactPairing
    (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' :=
    (Monoidal.εIso F).hom ≫ F.map (ExactPairing.coevaluation X Y) ≫ (Monoidal.μIso F X Y).inv
  evaluation' :=
    (Monoidal.μIso F Y X).hom ≫ F.map (ExactPairing.evaluation X Y) ≫ (Monoidal.εIso F).inv
  coevaluation_evaluation' := by
    simp only [Monoidal.εIso_hom, Monoidal.εIso_inv, Monoidal.μIso_hom, Monoidal.μIso_inv,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [Monoidal.map_associator_inv' F Y X Y]
    simp only [Category.assoc, Monoidal.whiskerLeft_δ_μ_assoc, Monoidal.whiskerRight_δ_μ_assoc]
    rw [LaxMonoidal.μ_natural_right_assoc F Y (ExactPairing.coevaluation X Y)]
    rw [OplaxMonoidal.δ_natural_left_assoc F (ExactPairing.evaluation X Y) Y]
    slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp]
    rw [ExactPairing.coevaluation_evaluation, F.map_comp]
    simp only [Category.assoc]
    rw [LaxMonoidal.right_unitality F Y]
    simp only [Category.assoc]
    rw [Monoidal.map_leftUnitor_inv F Y]
    simp only [Category.assoc, Monoidal.μ_δ_assoc, Monoidal.whiskerRight_ε_η, Category.comp_id]
  evaluation_coevaluation' := by
    simp only [Monoidal.εIso_hom, Monoidal.εIso_inv, Monoidal.μIso_hom, Monoidal.μIso_inv,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [Monoidal.map_associator' F X Y X]
    simp only [Category.assoc, Monoidal.whiskerRight_δ_μ_assoc, Monoidal.whiskerLeft_δ_μ_assoc]
    rw [LaxMonoidal.μ_natural_left_assoc F (ExactPairing.coevaluation X Y) X]
    rw [OplaxMonoidal.δ_natural_right_assoc F X (ExactPairing.evaluation X Y)]
    slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp]
    rw [ExactPairing.evaluation_coevaluation, F.map_comp]
    simp only [Category.assoc]
    rw [LaxMonoidal.left_unitality F X]
    simp only [Category.assoc]
    rw [Monoidal.map_rightUnitor_inv F X]
    simp only [Category.assoc, Monoidal.μ_δ_assoc, Monoidal.whiskerLeft_ε_η, Category.comp_id]

section Exercise_1_10_15

open Category

/-- Part of EGNO Exercise 1.10.15: a monoidal natural transformation between strong
monoidal functors has invertible component at the unit object. -/
noncomputable instance monoidalNatTrans_isIso_unit
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal] :
    IsIso (α.app (𝟙_ C)) := by
  have h := NatTrans.IsMonoidal.unit (τ := α)
  have hcomp : IsIso (LaxMonoidal.ε F ≫ α.app (𝟙_ C)) := h ▸ (Monoidal.εIso G).isIso_hom
  exact IsIso.of_isIso_comp_left (LaxMonoidal.ε F) (α.app (𝟙_ C))

/-- Part of EGNO Exercise 1.10.15: a monoidal natural transformation between strong
monoidal functors has invertible component at a tensor product whenever it has invertible
components at the factors. -/
noncomputable instance monoidalNatTrans_isIso_tensor
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X Y : C) [IsIso (α.app X)] [IsIso (α.app Y)] :
    IsIso (α.app (X ⊗ Y)) := by
  have h := NatTrans.IsMonoidal.tensor (τ := α) X Y
  have hrhs : IsIso ((α.app X ⊗ₘ α.app Y) ≫ LaxMonoidal.μ G X Y) := by
    apply IsIso.comp_isIso
  have hcomp : IsIso (LaxMonoidal.μ F X Y ≫ α.app (X ⊗ Y)) := h ▸ hrhs
  exact IsIso.of_isIso_comp_left (LaxMonoidal.μ F X Y) (α.app (X ⊗ Y))

/-- Candidate inverse of `α.app X` at a right-dualizable object `X`, built from the
evaluation/coevaluation of the right dual together with the inverse component `α.app Xᘁ`. -/
noncomputable def monoidalNatTrans_inv
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X : C) [HasRightDual X] : G.obj X ⟶ F.obj X :=
  (λ_ (G.obj X)).inv
  ≫ (ExactPairing.coevaluation (F.obj X) (F.obj Xᘁ) ▷ G.obj X)
  ≫ (α_ (F.obj X) (F.obj Xᘁ) (G.obj X)).hom
  ≫ (F.obj X ◁ (α.app Xᘁ ▷ G.obj X))
  ≫ (F.obj X ◁ ExactPairing.evaluation (G.obj X) (G.obj Xᘁ))
  ≫ (ρ_ (F.obj X)).hom

/-- Compatibility of a monoidal natural transformation with the evaluation of an exact
pairing transported through `F` and `G`. -/
lemma monoidalNatTrans_tensorHom_comp_eval
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X Y : C) [ExactPairing X Y] :
    (α.app Y ⊗ₘ α.app X) ≫
      @ExactPairing.evaluation D _ _ (G.obj X) (G.obj Y) (monoidalFunctor_exactPairing G X Y) =
      @ExactPairing.evaluation D _ _ (F.obj X) (F.obj Y) (monoidalFunctor_exactPairing F X Y) := by

  show (α.app Y ⊗ₘ α.app X) ≫
    ((Monoidal.μIso G Y X).hom ≫ G.map (ExactPairing.evaluation X Y) ≫ (Monoidal.εIso G).inv) =
    (Monoidal.μIso F Y X).hom ≫ F.map (ExactPairing.evaluation X Y) ≫ (Monoidal.εIso F).inv
  simp only [Monoidal.μIso_hom, Monoidal.εIso_inv]

  rw [← NatTrans.IsMonoidal.tensor_assoc (τ := α) Y X]
  congr 1

  rw [← α.naturality_assoc (ε_ X Y)]
  congr 1

  rw [← cancel_epi (LaxMonoidal.ε F)]
  rw [NatTrans.IsMonoidal.unit_assoc (τ := α)]
  simp

/-- Compatibility of a monoidal natural transformation with the coevaluation of an exact
pairing transported through `F` and `G`. -/
lemma monoidalNatTrans_coev_comp_tensorHom
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation D _ _ (F.obj X) (F.obj Y) (monoidalFunctor_exactPairing F X Y) ≫
      (α.app X ⊗ₘ α.app Y) =
      @ExactPairing.coevaluation D _ _ (G.obj X) (G.obj Y) (monoidalFunctor_exactPairing G X Y) := by

  show ((Monoidal.εIso F).hom ≫ F.map (ExactPairing.coevaluation X Y) ≫ (Monoidal.μIso F X Y).inv) ≫
      (α.app X ⊗ₘ α.app Y) =
    (Monoidal.εIso G).hom ≫ G.map (ExactPairing.coevaluation X Y) ≫ (Monoidal.μIso G X Y).inv
  simp only [Monoidal.εIso_hom, Monoidal.μIso_inv, assoc]

  rw [← cancel_mono (LaxMonoidal.μ G X Y)]
  simp only [assoc]
  rw [Monoidal.δ_μ, comp_id]
  rw [← NatTrans.IsMonoidal.tensor (τ := α) X Y]
  rw [Monoidal.δ_μ_assoc]

  slice_lhs 2 3 => rw [α.naturality]

  rw [reassoc_of% (NatTrans.IsMonoidal.unit (τ := α))]

/-- Part of EGNO Exercise 1.10.15: a monoidal natural transformation between strong
monoidal functors has invertible component at any right-dualizable object. -/
noncomputable instance monoidalNatTrans_isIso_of_hasRightDual
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X : C) [HasRightDual X] : IsIso (α.app X) := by
  refine ⟨⟨monoidalNatTrans_inv F G α X, ?_, ?_⟩⟩
  ·
    simp only [monoidalNatTrans_inv]

    rw [leftUnitor_inv_naturality_assoc]

    slice_lhs 2 3 => rw [whisker_exchange]
    try simp only [assoc]

    slice_lhs 3 4 => rw [associator_naturality_right]
    try simp only [assoc]

    slice_lhs 4 5 => rw [← MonoidalCategory.whiskerLeft_comp]

    rw [← tensorHom_def']

    slice_lhs 4 5 => rw [← MonoidalCategory.whiskerLeft_comp]

    rw [monoidalNatTrans_tensorHom_comp_eval]

    slice_lhs 2 4 => rw [ExactPairing.evaluation_coevaluation]
    simp
  ·
    simp only [monoidalNatTrans_inv, assoc]

    slice_lhs 6 7 => rw [← rightUnitor_naturality]
    try simp only [assoc]

    slice_lhs 5 6 => rw [whisker_exchange]
    try simp only [assoc]

    slice_lhs 4 5 => rw [whisker_exchange]
    try simp only [assoc]

    slice_lhs 3 4 => rw [← associator_naturality_left]
    try simp only [assoc]

    slice_lhs 2 3 => rw [← comp_whiskerRight]
    try simp only [assoc]

    rw [show (η_ (F.obj X) (F.obj Xᘁ) ≫ α.app X ▷ F.obj Xᘁ) ▷ G.obj X =
      η_ (F.obj X) (F.obj Xᘁ) ▷ G.obj X ≫ (α.app X ▷ F.obj Xᘁ) ▷ G.obj X
      from comp_whiskerRight _ _ _]
    try simp only [assoc]

    slice_lhs 3 4 => rw [associator_naturality_left]
    try simp only [assoc]

    slice_lhs 4 5 => rw [← whisker_exchange]
    try simp only [assoc]

    slice_lhs 3 4 => rw [← associator_naturality_middle]
    try simp only [assoc]

    slice_lhs 4 5 => rw [← associator_naturality_left]
    try simp only [assoc]

    slice_lhs 3 4 => rw [← comp_whiskerRight]
    try simp only [assoc]

    rw [← tensorHom_def']

    slice_lhs 2 3 => rw [← comp_whiskerRight]

    rw [monoidalNatTrans_coev_comp_tensorHom]

    slice_lhs 2 4 => rw [ExactPairing.evaluation_coevaluation]
    simp

/-- EGNO Exercise 1.10.15 (rigid case): when both `C` and `D` are right-rigid, every
monoidal natural transformation between strong monoidal functors is a natural
isomorphism. -/
noncomputable instance monoidalNatTrans_isIso_of_rigid
    [RightRigidCategory C] [RightRigidCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X : C) : IsIso (α.app X) :=
  monoidalNatTrans_isIso_of_hasRightDual F G α X

end Exercise_1_10_15

end TensorCategories.MonoidalFunctorProps
