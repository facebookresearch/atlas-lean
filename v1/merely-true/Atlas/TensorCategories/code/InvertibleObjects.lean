/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An object `X` of a monoidal category `C` is invertible if there exists an object
`tensorInverse` together with isomorphisms `X ⊗ tensorInverse ≅ 𝟙_ C` and
`tensorInverse ⊗ X ≅ 𝟙_ C` (cf. Definition 1.11.1). -/
class IsInvertibleObject (X : C) where
  tensorInverse : C
  compIso : X ⊗ tensorInverse ≅ 𝟙_ C
  invCompIso : tensorInverse ⊗ X ≅ 𝟙_ C

/-- The unit object `𝟙_ C` is invertible, with itself as tensor inverse and the left
unitor as both compositional isomorphisms. -/
@[reducible]
def unit_invertible : IsInvertibleObject (𝟙_ C) where
  tensorInverse := 𝟙_ C
  compIso := λ_ (𝟙_ C)
  invCompIso := λ_ (𝟙_ C)

variable [RigidCategory C]

/-- Definition 1.11.1: in a rigid category, an object `X` is invertible iff both the
evaluation `ε_ X Xᘁ` and the coevaluation `η_ X Xᘁ` are isomorphisms. -/
def Definition_1_11_1_InvertibleObject (X : C) : Prop :=
  IsIso (ε_ X (Xᘁ)) ∧ IsIso (η_ X (Xᘁ))

/-- Construct an `IsInvertibleObject` instance for `X` from its right dual `Xᘁ` together
with isomorphisms `X ⊗ Xᘁ ≅ 𝟙_ C` and `Xᘁ ⊗ X ≅ 𝟙_ C`. -/
@[reducible]
def IsInvertibleObject.ofRightDual (X : C) [HasRightDual X]
    (h1 : X ⊗ (Xᘁ) ≅ 𝟙_ C) (h2 : (Xᘁ) ⊗ X ≅ 𝟙_ C) : IsInvertibleObject X where
  tensorInverse := Xᘁ
  compIso := h1
  invCompIso := h2

/-- The tensor inverse of an invertible object is itself invertible, with `X` as its
inverse. -/
@[reducible]
def IsInvertibleObject.inverseInvertible (X : C) [h : IsInvertibleObject X] :
    IsInvertibleObject h.tensorInverse where
  tensorInverse := X
  compIso := h.invCompIso
  invCompIso := h.compIso

/-- If the tensor inverse of an invertible object `X` equals its right dual `Xᘁ`, then
`Xᘁ` is itself invertible. -/
@[reducible]
def rightDual_invertible (X : C) [HasRightDual X]
    (hX : IsInvertibleObject X) (h : hX.tensorInverse = Xᘁ) :
    IsInvertibleObject (Xᘁ : C) :=
  h ▸ hX.inverseInvertible

/-- Given inverse isomorphisms `X ⊗ Xi ≅ 𝟙_ C` and `Y ⊗ Yi ≅ 𝟙_ C`, build the
isomorphism `(X ⊗ Y) ⊗ (Yi ⊗ Xi) ≅ 𝟙_ C` via the associators and unitors. -/
noncomputable def tensorCompIso {X Y Xi Yi : C}
    (hX : X ⊗ Xi ≅ 𝟙_ C) (hY : Y ⊗ Yi ≅ 𝟙_ C) :
    (X ⊗ Y) ⊗ (Yi ⊗ Xi) ≅ 𝟙_ C :=
  (α_ X Y (Yi ⊗ Xi)) ≪≫
  (tensorLeft X).mapIso (α_ Y Yi Xi).symm ≪≫
  (tensorLeft X).mapIso (tensorIso hY (Iso.refl Xi)) ≪≫
  (tensorLeft X).mapIso (λ_ Xi) ≪≫
  hX

/-- Given inverse isomorphisms `Xi ⊗ X ≅ 𝟙_ C` and `Yi ⊗ Y ≅ 𝟙_ C`, build the
isomorphism `(Yi ⊗ Xi) ⊗ (X ⊗ Y) ≅ 𝟙_ C` via the associators and unitors. -/
noncomputable def tensorInvCompIso {X Y Xi Yi : C}
    (hX : Xi ⊗ X ≅ 𝟙_ C) (hY : Yi ⊗ Y ≅ 𝟙_ C) :
    (Yi ⊗ Xi) ⊗ (X ⊗ Y) ≅ 𝟙_ C :=
  (α_ Yi Xi (X ⊗ Y)) ≪≫
  (tensorLeft Yi).mapIso (α_ Xi X Y).symm ≪≫
  (tensorLeft Yi).mapIso (tensorIso hX (Iso.refl Y)) ≪≫
  (tensorLeft Yi).mapIso (λ_ Y) ≪≫
  hY

/-- The tensor product `X ⊗ Y` of two invertible objects is invertible, with tensor
inverse `Y⁻¹ ⊗ X⁻¹`. -/
@[reducible]
noncomputable def tensor_invertible (X Y : C)
    [hX : IsInvertibleObject X] [hY : IsInvertibleObject Y] :
    IsInvertibleObject (X ⊗ Y) where
  tensorInverse := hY.tensorInverse ⊗ hX.tensorInverse
  compIso := tensorCompIso hX.compIso hY.compIso
  invCompIso := tensorInvCompIso hX.invCompIso hY.invCompIso

section LeftDualIsoRightDual

variable (X : C) [HasRightDual X] [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))]

omit [RigidCategory C] in
/-- Zigzag identity for the inverses of evaluation and coevaluation morphisms (one of
the two compatibility laws used to upgrade `Xᘁ` to a left dual when `ε`, `η` are iso). -/
lemma zigzag_inv_eval_coeval :
    (inv (ε_ X Xᘁ) ▷ Xᘁ) ≫ (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ inv (η_ X Xᘁ)) =
    (λ_ Xᘁ).hom ≫ (ρ_ Xᘁ).inv := by
  have h : (Xᘁ ◁ η_ X Xᘁ) ≫ (α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ) =
      (ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv :=
    ExactPairing.coevaluation_evaluation' (X := X) (Y := Xᘁ)
  have cancel : ((Xᘁ ◁ η_ X Xᘁ) ≫ (α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ)) ≫
      ((inv (ε_ X Xᘁ) ▷ Xᘁ) ≫ (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ inv (η_ X Xᘁ))) =
      𝟙 (Xᘁ ⊗ 𝟙_ C) := by
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight]
    simp [Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp]
  rw [h] at cancel
  rw [← cancel_epi ((ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv), cancel]
  simp

omit [RigidCategory C] in
/-- Dual zigzag identity for the inverses of coevaluation and evaluation, completing the
exact-pairing axioms for the pair `(Xᘁ, X)`. -/
lemma zigzag_inv_coeval_eval :
    (X ◁ inv (ε_ X Xᘁ)) ≫ (α_ X Xᘁ X).inv ≫ (inv (η_ X Xᘁ) ▷ X) =
    (ρ_ X).hom ≫ (λ_ X).inv := by
  have h : (η_ X Xᘁ ▷ X) ≫ (α_ X Xᘁ X).hom ≫ (X ◁ ε_ X Xᘁ) =
      (λ_ X).hom ≫ (ρ_ X).inv :=
    ExactPairing.evaluation_coevaluation' (X := X) (Y := Xᘁ)
  have cancel : ((η_ X Xᘁ ▷ X) ≫ (α_ X Xᘁ X).hom ≫ (X ◁ ε_ X Xᘁ)) ≫
      ((X ◁ inv (ε_ X Xᘁ)) ≫ (α_ X Xᘁ X).inv ≫ (inv (η_ X Xᘁ) ▷ X)) =
      𝟙 (𝟙_ C ⊗ X) := by
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [← MonoidalCategory.whiskerLeft_comp, IsIso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id]
    simp [Iso.hom_inv_id_assoc, ← comp_whiskerRight]
  rw [h] at cancel
  rw [← cancel_epi ((λ_ X).hom ≫ (ρ_ X).inv), cancel]
  simp

/-- When the evaluation and coevaluation of `X` and `Xᘁ` are both isomorphisms, `Xᘁ`
together with `X` forms an exact pairing using their inverses. -/
@[reducible]
noncomputable def exactPairingDualObj : ExactPairing (Xᘁ) X where
  coevaluation' := inv (ε_ X Xᘁ)
  evaluation' := inv (η_ X Xᘁ)
  coevaluation_evaluation' := zigzag_inv_coeval_eval X
  evaluation_coevaluation' := zigzag_inv_eval_coeval X

/-- For an invertible object `X` in a rigid category, the left dual is canonically
isomorphic to the right dual. -/
noncomputable def leftDualIsoRightDual_of_invertible : HasLeftDual.leftDual X ≅ Xᘁ :=
  leftDualIso (inferInstance : ExactPairing (HasLeftDual.leftDual X) X) (exactPairingDualObj X)

end LeftDualIsoRightDual

/-- Proposition 1.11.3: for an invertible object `X` in a rigid category, (i) the left
dual is isomorphic to the right dual, (ii) the tensor inverse is invertible, and (iii)
the tensor product of invertibles is invertible. -/
noncomputable def Proposition_1_11_3
    (X : C) [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))] :

    (HasLeftDual.leftDual X ≅ Xᘁ) ×

    (∀ [IsInvertibleObject X], IsInvertibleObject (IsInvertibleObject.tensorInverse X)) ×

    (∀ (Y : C) [IsInvertibleObject X] [IsInvertibleObject Y],
      IsInvertibleObject (X ⊗ Y)) :=
  ⟨leftDualIsoRightDual_of_invertible X,
   IsInvertibleObject.inverseInvertible X,
   fun Y => tensor_invertible X Y⟩

section InvertibleSubcategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The object property of being invertible, packaged as an `ObjectProperty C` for use
when forming the monoidal subcategory of invertible objects. -/
def IsInvertibleObjectProp : ObjectProperty C := fun X => Nonempty (IsInvertibleObject X)

/-- The collection of invertible objects in a rigid monoidal category is closed under
the monoidal unit and tensor product, hence forms a monoidal subcategory. -/
noncomputable instance : (IsInvertibleObjectProp (C := C)).IsMonoidal where
  prop_unit := ⟨unit_invertible⟩
  prop_tensor := fun X Y ⟨hX⟩ ⟨hY⟩ => ⟨tensor_invertible X Y (hX := hX) (hY := hY)⟩

end InvertibleSubcategory

end CategoryTheory
