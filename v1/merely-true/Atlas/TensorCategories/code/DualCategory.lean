/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory
import Atlas.TensorCategories.code.ExactModuleCategory
import Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

/-- Underlying type of the dual category `C*_M`: module endofunctors of the module
category `M` over `C`. -/
def DualCatObj := ModuleFunctor C M M

/-- Definition 2.14.1: the dual category `C*_M` of `C` with respect to a module category
`M`, realised as the category of module endofunctors of `M`. -/
abbrev Definition_2_14_1 := @DualCatObj

namespace DualCatObj

variable {C M}

/-- A morphism in the dual category `C*_M`: a natural transformation between the
underlying functors compatible with the module structure isomorphisms. -/
structure Hom (F G : DualCatObj C M) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  comm : ∀ (X : C) (N : M),
    natTrans.app (X ⊗ᵐ N) ≫ (G.strIso X N).hom =
      (F.strIso X N).hom ≫ X ◁ᵐ (natTrans.app N)

attribute [reassoc] Hom.comm

/-- Two morphisms in `DualCatObj C M` are equal whenever their underlying natural
transformations agree. -/
@[ext]
theorem Hom.ext' {F G : DualCatObj C M} {f g : Hom F G}
    (h : f.natTrans = g.natTrans) : f = g := by
  cases f; cases g; congr

/-- Identity morphism on `F` in the dual category, given by the identity natural
transformation. -/
def Hom.id (F : DualCatObj C M) : Hom F F where
  natTrans := NatTrans.id F.toFunctor
  comm X N := by
    simp [NatTrans.id_app', LeftModuleCategory.actWhiskerLeft_id]

/-- Composition of morphisms in the dual category, given by the vertical composition of
the underlying natural transformations. -/
def Hom.comp {F G H : DualCatObj C M} (α : Hom F G) (β : Hom G H) :
    Hom F H where
  natTrans := α.natTrans ≫ β.natTrans
  comm X N := by
    simp only [NatTrans.comp_app, assoc]
    rw [β.comm, ← assoc, α.comm, assoc]
    congr 1

    have ha : X ◁ᵐ α.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (α.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hb : X ◁ᵐ β.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hab : X ◁ᵐ (α.natTrans.app N ≫ β.natTrans.app N) =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (α.natTrans.app N ≫ β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    rw [ha, hb, hab, LeftModuleCategory.actTensorHom_comp, comp_id]

/-- Category structure on `DualCatObj C M` whose morphisms are the module-compatible
natural transformations between module endofunctors of `M`. -/
instance categoryInstance : Category (DualCatObj C M) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext' (by ext x; simp [Hom.comp, Hom.id])
  comp_id f := Hom.ext' (by ext x; simp [Hom.comp, Hom.id])
  assoc f g h := Hom.ext' (by ext x; simp [Hom.comp])

/-- The underlying natural transformation of the identity morphism in `DualCatObj C M`
is the identity natural transformation. -/
@[simp]
theorem id_natTrans (F : DualCatObj C M) :
    (𝟙 F : Hom F F).natTrans = NatTrans.id F.toFunctor := rfl

/-- The underlying natural transformation of a composition in `DualCatObj C M` is the
composition of the underlying natural transformations. -/
@[simp]
theorem comp_natTrans {F G H : DualCatObj C M} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).natTrans = f.natTrans ≫ g.natTrans := rfl

/-- The identity module endofunctor of `M`, which serves as the monoidal unit of the
dual category. -/
def idModuleFunctor : DualCatObj C M :=
  { toFunctor := 𝟭 M
    strIso := fun _ _ => Iso.refl _
    strIso_natural := fun f g => by
      dsimp [Iso.refl]
      simp
    strIso_assoc := fun X Y N => by
      dsimp [Iso.refl]
      simp
    strIso_unit := fun N => by
      dsimp [Iso.refl]
      simp }

/-- Composition of two module endofunctors of `M`, giving the tensor product in the
dual category `C*_M`. -/
def compModuleFunctor (F₁ F₂ : DualCatObj C M) : DualCatObj C M :=
  { toFunctor := F₁.toFunctor ⋙ F₂.toFunctor
    strIso := fun X N =>
      (F₂.toFunctor.mapIso (F₁.strIso X N)).trans (F₂.strIso X (F₁.toFunctor.obj N))
    strIso_natural := fun {X₁ X₂ N₁ N₂} f g => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]
      rw [← F₂.toFunctor.map_comp_assoc, F₁.strIso_natural,
          F₂.toFunctor.map_comp, assoc, F₂.strIso_natural]
    strIso_assoc := fun X Y N => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]


      have whisker_comp : X ◁ᵐ (F₂.toFunctor.map (F₁.strIso Y N).hom ≫
          (F₂.strIso Y (F₁.toFunctor.obj N)).hom) =
        X ◁ᵐ F₂.toFunctor.map (F₁.strIso Y N).hom ≫
          X ◁ᵐ (F₂.strIso Y (F₁.toFunctor.obj N)).hom := by
        have h := LeftModuleCategory.actTensorHom_comp (𝟙 X)
          (F₂.toFunctor.map (F₁.strIso Y N).hom) (𝟙 X)
          ((F₂.strIso Y (F₁.toFunctor.obj N)).hom)
        simp [LeftModuleCategory.actTensorHom_def,
              LeftModuleCategory.actId_whiskerRight] at h
        exact h.symm
      rw [whisker_comp]

      have nat_s₂ : (F₂.strIso X (F₁.toFunctor.obj (Y ⊗ᵐ N))).hom ≫
          X ◁ᵐ F₂.toFunctor.map (F₁.strIso Y N).hom =
        F₂.toFunctor.map (X ◁ᵐ (F₁.strIso Y N).hom) ≫
          (F₂.strIso X (Y ⊗ᵐ F₁.toFunctor.obj N)).hom := by
        have := F₂.strIso_natural (𝟙 X) (F₁.strIso Y N).hom
        simp [LeftModuleCategory.actId_whiskerRight] at this
        exact this.symm
      slice_lhs 3 4 => rw [nat_s₂]
      simp only [assoc]

      rw [← F₂.toFunctor.map_comp_assoc, ← F₂.toFunctor.map_comp_assoc]

      have inner : (F₁.toFunctor.map (actμ_ X Y N).hom ≫ (F₁.strIso X (Y ⊗ᵐ N)).hom) ≫
          X ◁ᵐ (F₁.strIso Y N).hom =
        (F₁.strIso (X ⊗ Y) N).hom ≫ (actμ_ X Y (F₁.toFunctor.obj N)).hom := by
        rw [assoc]; exact F₁.strIso_assoc X Y N
      rw [show F₂.toFunctor.map ((F₁.toFunctor.map (actμ_ X Y N).hom ≫
          (F₁.strIso X (Y ⊗ᵐ N)).hom) ≫ X ◁ᵐ (F₁.strIso Y N).hom) =
        F₂.toFunctor.map ((F₁.strIso (X ⊗ Y) N).hom ≫
          (actμ_ X Y (F₁.toFunctor.obj N)).hom) from congr_arg F₂.toFunctor.map inner]
      rw [F₂.toFunctor.map_comp, assoc]
      congr 1
      exact F₂.strIso_assoc X Y (F₁.toFunctor.obj N)
    strIso_unit := fun N => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]
      rw [F₁.strIso_unit, F₂.toFunctor.map_comp]
      congr 1
      exact F₂.strIso_unit (F₁.toFunctor.obj N) }

/-- Left whiskering of a morphism `α : G₁ ⟶ G₂` by a module endofunctor `F`, giving a
morphism `F ⊗ G₁ ⟶ F ⊗ G₂` in `DualCatObj C M`. -/
def dualWhiskerLeft (F : DualCatObj C M) {G₁ G₂ : DualCatObj C M} (α : G₁ ⟶ G₂) :
    compModuleFunctor F G₁ ⟶ compModuleFunctor F G₂ where
  natTrans :=
    { app := fun N => α.natTrans.app (F.toFunctor.obj N)
      naturality := fun N₁ N₂ f => α.natTrans.naturality (F.toFunctor.map f) }
  comm X N := by
    simp only [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, assoc]
    rw [← α.natTrans.naturality_assoc, α.comm]

/-- Right whiskering of a morphism `α : F₁ ⟶ F₂` by a module endofunctor `G`, giving a
morphism `F₁ ⊗ G ⟶ F₂ ⊗ G` in `DualCatObj C M`. -/
def dualWhiskerRight {F₁ F₂ : DualCatObj C M} (α : F₁ ⟶ F₂) (G : DualCatObj C M) :
    compModuleFunctor F₁ G ⟶ compModuleFunctor F₂ G where
  natTrans :=
    { app := fun N => G.toFunctor.map (α.natTrans.app N)
      naturality := fun N₁ N₂ f => by
        dsimp [compModuleFunctor]
        rw [← G.toFunctor.map_comp, ← G.toFunctor.map_comp]
        congr 1; exact α.natTrans.naturality f }
  comm X N := by
    simp only [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, assoc]


    rw [← G.toFunctor.map_comp_assoc, α.comm, G.toFunctor.map_comp, assoc]


    congr 1

    have := G.strIso_natural (𝟙 X) (α.natTrans.app N)
    simp [LeftModuleCategory.actId_whiskerRight] at this
    exact this

/-- Reducible alias for the category structure on `DualCatObj C M`. -/
@[reducible]
def dualCategory : Category (DualCatObj C M) := categoryInstance

/-- The module-structure isomorphisms of the two ways of bracketing a triple composition
of module endofunctors agree on objects. -/
lemma compModuleFunctor_assoc_strIso (F₁ F₂ F₃ : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor (compModuleFunctor F₁ F₂) F₃).strIso X N =
    (compModuleFunctor F₁ (compModuleFunctor F₂ F₃)).strIso X N := by
  ext
  simp [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj,
        Functor.comp_map]

/-- Associator isomorphism for the monoidal structure on `DualCatObj C M` induced by
composition of module endofunctors. -/
def dualAssociator (F₁ F₂ F₃ : DualCatObj C M) :
    compModuleFunctor (compModuleFunctor F₁ F₂) F₃ ≅
    compModuleFunctor F₁ (compModuleFunctor F₂ F₃) where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_assoc_strIso]
      dsimp [compModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_assoc_strIso]
      dsimp [compModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor]; simp)

/-- Composing on the left with the identity module endofunctor does not change the
structure isomorphism. -/
lemma compModuleFunctor_left_id_strIso (F : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor idModuleFunctor F).strIso X N = F.strIso X N := by
  ext
  simp [compModuleFunctor, idModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Iso.refl]

/-- Left unitor for the monoidal structure on `DualCatObj C M`, witnessing
`𝟙 ⊗ F ≅ F`. -/
def dualLeftUnitor (F : DualCatObj C M) :
    compModuleFunctor idModuleFunctor F ≅ F where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_left_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_left_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)

/-- Composing on the right with the identity module endofunctor does not change the
structure isomorphism. -/
lemma compModuleFunctor_right_id_strIso (F : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor F idModuleFunctor).strIso X N = F.strIso X N := by
  ext
  simp [compModuleFunctor, idModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Iso.refl]

/-- Right unitor for the monoidal structure on `DualCatObj C M`, witnessing
`F ⊗ 𝟙 ≅ F`. -/
def dualRightUnitor (F : DualCatObj C M) :
    compModuleFunctor F idModuleFunctor ≅ F where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_right_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_right_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)

/-- Monoidal category structure data on `DualCatObj C M`: tensor product is functor
composition, the unit is the identity module endofunctor, and the coherence
isomorphisms are the canonical ones. -/
instance dualMonoidalCategoryStruct : MonoidalCategoryStruct (DualCatObj C M) where
  tensorObj := compModuleFunctor
  whiskerLeft := dualWhiskerLeft
  whiskerRight := fun f G => dualWhiskerRight f G
  tensorUnit := idModuleFunctor
  associator := dualAssociator
  leftUnitor := dualLeftUnitor
  rightUnitor := dualRightUnitor


/-- Tensor product in `DualCatObj C M` is functor composition. -/
@[simp] lemma tensorObj_eq (F G : DualCatObj C M) : F ⊗ G = compModuleFunctor F G := rfl
/-- The monoidal unit of `DualCatObj C M` is the identity module endofunctor. -/
@[simp] lemma tensorUnit_eq : (𝟙_ (DualCatObj C M)) = idModuleFunctor := rfl
/-- Left whiskering in `DualCatObj C M` agrees with `dualWhiskerLeft`. -/
@[simp] lemma whiskerLeft_eq (F : DualCatObj C M) {G₁ G₂ : DualCatObj C M} (f : G₁ ⟶ G₂) :
    F ◁ f = dualWhiskerLeft F f := rfl
/-- Right whiskering in `DualCatObj C M` agrees with `dualWhiskerRight`. -/
@[simp] lemma whiskerRight_eq {F₁ F₂ : DualCatObj C M} (f : F₁ ⟶ F₂) (G : DualCatObj C M) :
    f ▷ G = dualWhiskerRight f G := rfl
/-- The associator in `DualCatObj C M` agrees with `dualAssociator`. -/
@[simp] lemma associator_eq (F₁ F₂ F₃ : DualCatObj C M) :
    α_ F₁ F₂ F₃ = dualAssociator F₁ F₂ F₃ := rfl
/-- The left unitor in `DualCatObj C M` agrees with `dualLeftUnitor`. -/
@[simp] lemma leftUnitor_eq (F : DualCatObj C M) : λ_ F = dualLeftUnitor F := rfl
/-- The right unitor in `DualCatObj C M` agrees with `dualRightUnitor`. -/
@[simp] lemma rightUnitor_eq (F : DualCatObj C M) : ρ_ F = dualRightUnitor F := rfl

/-- Monoidal category structure on `DualCatObj C M` packaging together the data of
`dualMonoidalCategoryStruct` with the coherence axioms (pentagon, triangle, etc.). -/
instance dualMonoidalCategory : MonoidalCategory (DualCatObj C M) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun F G => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        tensorObj_eq, id_natTrans, comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp [Functor.map_id])
    (id_tensorHom := fun F {G₁ G₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp)
    (tensorHom_id := fun {F₁ F₂} f G => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp)
    (tensorHom_comp_tensorHom := fun {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor, Hom.comp]


      have nat := f₂.natTrans.naturality (g₁.natTrans.app N)

      slice_lhs 2 3 => rw [← nat]
      simp only [assoc]
      rw [← X₂.toFunctor.map_comp_assoc])
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualWhiskerLeft, dualWhiskerRight, compModuleFunctor, Hom.comp]
      simp only [id_comp, comp_id]
      rw [X₃.toFunctor.map_comp, assoc])
    (leftUnitor_naturality := fun {X₁ X₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualLeftUnitor, dualWhiskerLeft, dualWhiskerRight,
             compModuleFunctor, idModuleFunctor]
      simp)
    (rightUnitor_naturality := fun {X₁ X₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualRightUnitor, dualWhiskerLeft, dualWhiskerRight,
             compModuleFunctor, idModuleFunctor]
      simp)

    (pentagon := fun W X Y Z => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualWhiskerLeft, dualWhiskerRight, Hom.comp, compModuleFunctor]
      simp [Functor.map_id])
    (triangle := fun X Y => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom, comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualLeftUnitor, dualRightUnitor,
             dualWhiskerLeft, dualWhiskerRight, Hom.comp, compModuleFunctor, idModuleFunctor]
      simp [Functor.map_id])

/-- Evaluation of a module endofunctor `F ∈ DualCatObj C M` at an object `N ∈ M`. -/
def evalObj (F : DualCatObj C M) (N : M) : M := F.toFunctor.obj N

/-- Evaluation of a module endofunctor `F` on a morphism of `M`. -/
def evalMap (F : DualCatObj C M) {N₁ N₂ : M} (f : N₁ ⟶ N₂) :
    evalObj F N₁ ⟶ evalObj F N₂ :=
  F.toFunctor.map f

/-- Evaluation of a morphism `α : F₁ ⟶ F₂` of `DualCatObj C M` at an object `N ∈ M`. -/
def evalNatApp {F₁ F₂ : DualCatObj C M} (α : F₁ ⟶ F₂) (N : M) :
    evalObj F₁ N ⟶ evalObj F₂ N :=
  α.natTrans.app N








/-- Functoriality of left whiskering on `M`: `X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g`. -/
theorem actWhiskerLeft_comp (X : C) {A B D : M} (f : A ⟶ B) (g : B ⟶ D) :
    X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
  have := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
  simp only [LeftModuleCategory.actTensorHom_def,
    LeftModuleCategory.actId_whiskerRight, id_comp, comp_id] at this
  exact this.symm

/-- Left whiskering preserves isomorphisms: if `f : A ⟶ B` is an isomorphism in `M` then
so is `X ◁ᵐ f`. -/
instance actWhiskerLeft_isIso (X : C) {A B : M} (f : A ⟶ B) [IsIso f] :
    IsIso (X ◁ᵐ f) where
  out := ⟨X ◁ᵐ inv f, by
    constructor
    · rw [← actWhiskerLeft_comp, IsIso.hom_inv_id,
          LeftModuleCategory.actWhiskerLeft_id]
    · rw [← actWhiskerLeft_comp, IsIso.inv_hom_id,
          LeftModuleCategory.actWhiskerLeft_id]⟩

/-- Construct an inverse morphism `𝟙 ⟶ F` from a morphism `α : F ⟶ 𝟙` whose components
are isomorphisms at every object of `M`. -/
noncomputable def Hom.mkInverse
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom (idModuleFunctor (C := C) (M := M)) F where
  natTrans := {
    app := fun N => @inv _ _ _ _ (α.natTrans.app N) (hiso N)
    naturality := fun {N₁ N₂} f => by
      haveI := hiso N₁
      haveI := hiso N₂
      have hnat := α.natTrans.naturality f
      rw [← cancel_epi (α.natTrans.app N₁)]
      simp only [assoc, IsIso.hom_inv_id_assoc]
      rw [← assoc]
      rw [← hnat]
      simp [IsIso.hom_inv_id]

  }
  comm := fun X N => by
    haveI := hiso N
    haveI := hiso (X ⊗ᵐ N)
    have hcomm := α.comm X N
    show inv (α.natTrans.app (X ⊗ᵐ N)) ≫ (F.strIso X N).hom =
      (idModuleFunctor.strIso X N).hom ≫ X ◁ᵐ inv (α.natTrans.app N)
    rw [IsIso.inv_comp_eq]
    rw [← assoc, ← hcomm.symm, assoc, ← actWhiskerLeft_comp, IsIso.hom_inv_id,
        LeftModuleCategory.actWhiskerLeft_id, comp_id]

/-- The constructed inverse from `Hom.mkInverse` is a left inverse to `α`. -/
theorem Hom.mkInverse_comp
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom.comp (Hom.mkInverse α hiso) α =
      Hom.id (idModuleFunctor (C := C) (M := M)) := by
  apply Hom.ext'
  ext N
  simp only [Hom.comp, Hom.mkInverse, Hom.id, NatTrans.comp_app, NatTrans.id_app']
  haveI := hiso N
  exact IsIso.inv_hom_id (α.natTrans.app N)

/-- The constructed inverse from `Hom.mkInverse` is a right inverse to `α`. -/
theorem Hom.comp_mkInverse
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom.comp α (Hom.mkInverse α hiso) = Hom.id F := by
  apply Hom.ext'
  ext N
  simp only [Hom.comp, Hom.mkInverse, Hom.id, NatTrans.comp_app, NatTrans.id_app']
  haveI := hiso N
  exact IsIso.hom_inv_id (α.natTrans.app N)




/-- The endofunctor of `M` given by tensoring with a fixed object `X ∈ C` on the left. -/
def actionFunctor (X : C) : M ⥤ M where
  obj := fun N => X ⊗ᵐ N
  map := fun f => X ◁ᵐ f
  map_id := fun N => by simp [LeftModuleCategory.actWhiskerLeft_id]
  map_comp := fun f g => by
    have h1 := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
    simp [LeftModuleCategory.actTensorHom_def,
          LeftModuleCategory.actId_whiskerRight] at h1
    exact h1.symm





/-- The "double dual" category `(C*_M)*_M`: module endofunctors of `M` viewed as a
module category over `C*_M`. -/
def DoubleDualObj (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [LeftModuleCategory (DualCatObj C M) M] :=
  ModuleFunctor (DualCatObj C M) M M

/-- A morphism in the double-dual category `(C*_M)*_M`: a natural transformation
between the underlying functors compatible with the `C*_M`-module structures. -/
structure DoubleDualHom [inst : LeftModuleCategory (DualCatObj C M) M]
    (F G : DoubleDualObj C M) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  comm : ∀ (P : DualCatObj C M) (N : M),
    natTrans.app (P ⊗ᵐ N) ≫ (G.strIso P N).hom =
      (F.strIso P N).hom ≫ P ◁ᵐ (natTrans.app N)

/-- Two double-dual morphisms are equal whenever their underlying natural
transformations agree. -/
@[ext]
theorem DoubleDualHom.ext' [inst : LeftModuleCategory (DualCatObj C M) M]
    {F G : DoubleDualObj C M} {f g : DoubleDualHom F G}
    (h : f.natTrans = g.natTrans) : f = g := by
  cases f; cases g; congr

/-- Identity morphism on `F` in the double-dual category, given by the identity natural
transformation. -/
def DoubleDualHom.id [inst : LeftModuleCategory (DualCatObj C M) M]
    (F : DoubleDualObj C M) : DoubleDualHom F F where
  natTrans := NatTrans.id F.toFunctor
  comm P N := by
    simp [NatTrans.id_app', LeftModuleCategory.actWhiskerLeft_id]

/-- Composition of morphisms in the double-dual category, given by the vertical
composition of the underlying natural transformations. -/
def DoubleDualHom.comp [inst : LeftModuleCategory (DualCatObj C M) M]
    {F G H : DoubleDualObj C M}
    (α : DoubleDualHom F G) (β : DoubleDualHom G H) :
    DoubleDualHom F H where
  natTrans := α.natTrans ≫ β.natTrans
  comm P N := by
    simp only [NatTrans.comp_app, assoc]
    rw [β.comm, ← assoc, α.comm, assoc]
    congr 1
    have ha : P ◁ᵐ α.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (α.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hb : P ◁ᵐ β.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hab : P ◁ᵐ (α.natTrans.app N ≫ β.natTrans.app N) =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (α.natTrans.app N ≫ β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    rw [ha, hb, hab, LeftModuleCategory.actTensorHom_comp, comp_id]

/-- Category structure on the double-dual category `DoubleDualObj C M`, with
`DoubleDualHom` as morphisms. -/
instance doubleDualCategoryInstance [inst : LeftModuleCategory (DualCatObj C M) M] :
    Category (DoubleDualObj C M) where
  Hom := DoubleDualHom
  id := DoubleDualHom.id
  comp := DoubleDualHom.comp
  id_comp f := DoubleDualHom.ext' (by ext x; simp [DoubleDualHom.comp, DoubleDualHom.id])
  comp_id f := DoubleDualHom.ext' (by ext x; simp [DoubleDualHom.comp, DoubleDualHom.id])
  assoc f g h := DoubleDualHom.ext' (by ext x; simp [DoubleDualHom.comp])



section Lemma_2_14_7

/-- Multiplication on the dual-tensor algebra `ᘁA ⊗ A` formed using the evaluation map
of the left duality on `A`. -/
noncomputable def dualAlg_mul (A : C) [HasLeftDual A] :
    ((ᘁA : C) ⊗ A) ⊗ ((ᘁA : C) ⊗ A) ⟶ (ᘁA : C) ⊗ A :=
  (α_ (ᘁA : C) A ((ᘁA : C) ⊗ A)).hom ≫
  (ᘁA : C) ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)

open MonObj in
/-- A left module over an algebra object `B ∈ C`: an object `Y` together with an action
`B ⊗ Y ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure LeftModObj (B : C) [MonObj B] (Y : C) where
  act : B ⊗ Y ⟶ Y
  act_one : (λ_ Y).inv ≫ (MonObj.one ▷ Y) ≫ act = 𝟙 Y
  act_assoc : (α_ B B Y).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ Y) ≫ act

open MonObj in
/-- A right module over an algebra object `B ∈ C`: an object `Y` together with an
action `Y ⊗ B ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure RightModObj (B : C) [MonObj B] (Y : C) where
  act : Y ⊗ B ⟶ Y
  act_one : (ρ_ Y).inv ≫ (Y ◁ MonObj.one) ≫ act = 𝟙 Y
  act_assoc : (α_ Y B B).inv ≫ (act ▷ B) ≫ act = (Y ◁ MonObj.mul) ≫ act







end Lemma_2_14_7














end DualCatObj








/-- An object of the Drinfeld center expressed in half-braiding form: an object `X ∈ C`
together with a family of half-braiding isomorphisms `V ⊗ X ≅ X ⊗ V` satisfying
naturality and a hexagon-style tensor compatibility. -/
structure DrinfeldCenterHalfBraidingObj (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  X : C
  halfBraiding : ∀ (V : C), (V ⊗ X) ≅ (X ⊗ V)
  halfBraiding_natural : ∀ {V₁ V₂ : C} (f : V₁ ⟶ V₂),
    (f ▷ X) ≫ (halfBraiding V₂).hom = (halfBraiding V₁).hom ≫ (X ◁ f)
  halfBraiding_tensor : ∀ (V W : C),
    (halfBraiding (V ⊗ W)).hom =
      (α_ V W X).hom ≫ (V ◁ (halfBraiding W).hom) ≫ (α_ V X W).inv ≫
        ((halfBraiding V).hom ▷ W) ≫ (α_ X V W).hom

/-- A morphism between half-braiding objects of the Drinfeld center: a morphism of the
underlying objects compatible with the half-braiding isomorphisms. -/
structure DrinfeldCenterHalfBraidingHom {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P Q : DrinfeldCenterHalfBraidingObj C) where
  hom : P.X ⟶ Q.X
  comm : ∀ (V : C),
    (V ◁ hom) ≫ (Q.halfBraiding V).hom = (P.halfBraiding V).hom ≫ (hom ▷ V)

attribute [reassoc] DrinfeldCenterHalfBraidingHom.comm

/-- Two half-braiding morphisms are equal whenever their underlying morphisms in `C`
agree. -/
@[ext]
theorem DrinfeldCenterHalfBraidingHom.ext {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q : DrinfeldCenterHalfBraidingObj C} {f g : DrinfeldCenterHalfBraidingHom P Q}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; congr

/-- Identity morphism on a half-braiding object of the Drinfeld center. -/
def DrinfeldCenterHalfBraidingHom.id {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P : DrinfeldCenterHalfBraidingObj C) : DrinfeldCenterHalfBraidingHom P P where
  hom := 𝟙 P.X
  comm V := by simp

/-- Composition of half-braiding morphisms in the Drinfeld center. -/
def DrinfeldCenterHalfBraidingHom.comp {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q R : DrinfeldCenterHalfBraidingObj C}
    (f : DrinfeldCenterHalfBraidingHom P Q) (g : DrinfeldCenterHalfBraidingHom Q R) :
    DrinfeldCenterHalfBraidingHom P R where
  hom := f.hom ≫ g.hom
  comm V := by
    simp only [MonoidalCategory.whiskerLeft_comp, assoc]
    rw [g.comm]
    simp only [← assoc]
    rw [f.comm]
    simp only [assoc, comp_whiskerRight]

/-- Category structure on the type of half-braiding objects of the Drinfeld center. -/
instance drinfeldCenterHalfBraidingCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    Category (DrinfeldCenterHalfBraidingObj C) where
  Hom := DrinfeldCenterHalfBraidingHom
  id := DrinfeldCenterHalfBraidingHom.id
  comp := DrinfeldCenterHalfBraidingHom.comp
  id_comp f := DrinfeldCenterHalfBraidingHom.ext (by simp [DrinfeldCenterHalfBraidingHom.comp, DrinfeldCenterHalfBraidingHom.id])
  comp_id f := DrinfeldCenterHalfBraidingHom.ext (by simp [DrinfeldCenterHalfBraidingHom.comp, DrinfeldCenterHalfBraidingHom.id])
  assoc f g h := DrinfeldCenterHalfBraidingHom.ext (by simp [DrinfeldCenterHalfBraidingHom.comp])

section BasicIdentity

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {M : Type u} [Category.{v} M] [LeftModuleCategory C M]







end BasicIdentity

end CategoryTheory
