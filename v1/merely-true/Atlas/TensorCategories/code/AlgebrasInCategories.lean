/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_

import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Atlas.TensorCategories.code.ModuleCategory

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section MonoidObjectExamples

end MonoidObjectExamples

variable (A : C) [MonObj A]

/-- The data of a right `A`-module structure on an object `M : C`: a right action
`act : M ⊗ A → M` compatible with the unit and multiplication of the algebra `A`. -/
structure RightModObj (M : C) where
  act : M ⊗ A ⟶ M
  act_unit : (M ◁ η[A]) ≫ act = (ρ_ M).hom := by aesop_cat
  act_assoc : (act ▷ A) ≫ act = (α_ M A A).hom ≫ (M ◁ μ[A]) ≫ act := by aesop_cat

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

/-- A right module over an algebra `(A, m, u)` is a pair `(M, p)` with `M : C` and
`p : M ⊗ A → M` satisfying the unit and associativity axioms. -/
abbrev Definition_2_9_5_RightModule (M : C) := RightModObj A M

/-- A right module over the algebra `A` packaged as a bundled structure: an underlying
object `X : C` together with a right action `mod : RightModObj A X`. -/
structure RightMod_ where
  X : C
  mod : RightModObj A X

variable {A}

/-- A morphism `l : M₁ → M₂` between right `A`-modules `(M₁, p₁)` and `(M₂, p₂)` is an
`A`-module homomorphism if it intertwines the right actions. -/
def IsRightModHom {M₁ M₂ : C} (p₁ : RightModObj A M₁) (p₂ : RightModObj A M₂)
    (l : M₁ ⟶ M₂) : Prop :=
  p₁.act ≫ l = (l ▷ A) ≫ p₂.act

/-- A morphism in the category of right `A`-modules: an underlying morphism `hom` in `C`
that intertwines the right `A`-actions on the source and target. -/
@[ext]
structure RightMod_.Hom (M N : RightMod_ A) where
  hom : M.X ⟶ N.X
  comm : M.mod.act ≫ hom = (hom ▷ A) ≫ N.mod.act := by aesop_cat

attribute [reassoc (attr := simp)] RightMod_.Hom.comm

namespace RightMod_

/-- The identity morphism on a right `A`-module `M`. -/
@[simps]
def id (M : RightMod_ A) : Hom M M where
  hom := 𝟙 M.X

/-- Composition of two right `A`-module morphisms. -/
@[simps]
def comp {M N K : RightMod_ A} (f : Hom M N) (g : Hom N K) : Hom M K where
  hom := f.hom ≫ g.hom
  comm := by simp [comp_whiskerRight, reassoc_of% f.comm]

/-- The category structure on right `A`-modules, with morphisms `RightMod_.Hom`,
identities and composition as defined above. -/
instance : Category (RightMod_ A) where
  Hom := Hom
  id := id
  comp := comp

/-- Two morphisms of right `A`-modules are equal iff their underlying morphisms in `C`
are equal. -/
@[ext]
lemma hom_ext {M N : RightMod_ A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) : f₁ = f₂ :=
  Hom.ext h

/-- The underlying morphism of the identity in `RightMod_ A` is the identity in `C`. -/
@[simp] lemma id_hom' (M : RightMod_ A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := rfl

/-- The underlying morphism of a composition `f ≫ g` of right `A`-module morphisms is the
composition of the underlying morphisms. -/
@[simp] lemma comp_hom' {M N K : RightMod_ A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The right regular `A`-module, namely the algebra `A` viewed as a right module over
itself via its multiplication. -/
@[simps]
def regular (A : C) [MonObj A] : RightMod_ (A := A) where
  X := A
  mod := { act := μ[A] }

/-- The forgetful functor from right `A`-modules to `C`, sending a module to its
underlying object. -/
@[simps]
def forget : RightMod_ (A := A) ⥤ C where
  obj M := M.X
  map f := f.hom

/-- For `X : C` and a right `A`-module `M`, the object `X ⊗ M.X` carries a right
`A`-module structure with action `(α_).hom ≫ X ◁ M.mod.act`. -/
def tensorModObj (X : C) (M : RightMod_ A) : RightModObj A (X ⊗ M.X) where
  act := (α_ X M.X A).hom ≫ X ◁ M.mod.act
  act_unit := by
    calc (X ⊗ M.X) ◁ η ≫ (α_ X M.X A).hom ≫ X ◁ M.mod.act
        = (α_ X M.X _).hom ≫ X ◁ (M.X ◁ η) ≫ X ◁ M.mod.act := by simp [assoc]
      _ = (α_ X M.X _).hom ≫ X ◁ ((M.X ◁ η) ≫ M.mod.act) := by rw [whiskerLeft_comp]
      _ = (α_ X M.X _).hom ≫ X ◁ (ρ_ M.X).hom := by rw [M.mod.act_unit]
      _ = (ρ_ (X ⊗ M.X)).hom := (rightUnitor_tensor_hom X M.X).symm
  act_assoc := by
    rw [comp_whiskerRight, assoc]
    slice_lhs 2 3 => simp
    slice_lhs 3 4 => rw [← whiskerLeft_comp, M.mod.act_assoc]
    simp only [whiskerLeft_comp]
    slice_lhs 1 3 => rw [pentagon]
    simp [assoc]

/-- Right whiskering of `f : X₁ ⟶ X₂` by a right `A`-module `M`, viewed as a morphism
in `RightMod_ A` between the modules `X₁ ⊗ M` and `X₂ ⊗ M`. -/
def actWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (M : RightMod_ A) :
    (⟨X₁ ⊗ M.X, tensorModObj X₁ M⟩ : RightMod_ A) ⟶
    ⟨X₂ ⊗ M.X, tensorModObj X₂ M⟩ where
  hom := f ▷ M.X
  comm := by
    simp only [tensorModObj, assoc]
    rw [whisker_exchange]
    simp

/-- Left whiskering of a right `A`-module morphism `g : M ⟶ N` by an object `X : C`,
giving a morphism `X ⊗ M ⟶ X ⊗ N` in `RightMod_ A`. -/
def actWhiskerLeft (X : C) {M N : RightMod_ A} (g : M ⟶ N) :
    (⟨X ⊗ M.X, tensorModObj X M⟩ : RightMod_ A) ⟶
    ⟨X ⊗ N.X, tensorModObj X N⟩ where
  hom := X ◁ g.hom
  comm := by
    simp only [tensorModObj, assoc]
    rw [← whiskerLeft_comp, g.comm, whiskerLeft_comp]
    simp [assoc]

/-- The associator isomorphism `(X ⊗ Y) ⊗ M ≅ X ⊗ (Y ⊗ M)` in `RightMod_ A` for the
`C`-action on right `A`-modules. -/
def actAssociator (X Y : C) (M : RightMod_ A) :
    (⟨(X ⊗ Y) ⊗ M.X, tensorModObj (X ⊗ Y) M⟩ : RightMod_ A) ≅
    ⟨X ⊗ (Y ⊗ M.X), tensorModObj X ⟨Y ⊗ M.X, tensorModObj Y M⟩⟩ where
  hom := {
    hom := (α_ X Y M.X).hom
    comm := by
      simp only [tensorModObj, assoc, whiskerLeft_comp]
      slice_lhs 2 3 => rw [associator_naturality_right]
      rw [← pentagon_assoc]
  }
  inv := {
    hom := (α_ X Y M.X).inv
    comm := by
      simp only [tensorModObj, assoc, whiskerLeft_comp]
      rw [← cancel_mono (α_ X Y M.X).hom]
      simp only [assoc, Iso.inv_hom_id, comp_id]
      rw [associator_naturality_right (f := M.mod.act)]
      rw [show (α_ X Y M.X).inv ▷ A ≫ (α_ (X ⊗ Y) M.X A).hom ≫
        (α_ X Y (M.X ⊗ A)).hom ≫ X ◁ Y ◁ M.mod.act =
        (α_ X Y M.X).inv ▷ A ≫ ((α_ X Y M.X).hom ▷ A ≫
        (α_ X (Y ⊗ M.X) A).hom ≫ X ◁ (α_ Y M.X A).hom) ≫
        X ◁ Y ◁ M.mod.act from by rw [pentagon]; simp [assoc]]
      simp [assoc]
  }

/-- The left unitor isomorphism `𝟙_ C ⊗ M ≅ M` in `RightMod_ A` for the `C`-action. -/
def actLeftUnitor (M : RightMod_ A) :
    (⟨(𝟙_ C) ⊗ M.X, tensorModObj (𝟙_ C) M⟩ : RightMod_ A) ≅
    M where
  hom := {
    hom := (λ_ M.X).hom
    comm := by
      simp only [tensorModObj, assoc]
      rw [show (λ_ M.X).hom ▷ A ≫ M.mod.act =
        (α_ (𝟙_ C) M.X A).hom ≫ (𝟙_ C) ◁ M.mod.act ≫ (λ_ M.X).hom from by simp]
  }
  inv := {
    hom := (λ_ M.X).inv
    comm := by
      rw [← cancel_mono (λ_ M.X).hom]
      simp only [tensorModObj, assoc, Iso.inv_hom_id]
      simp
  }

/-- The tensor of a morphism `f : X₁ ⟶ X₂` in `C` with a morphism `g : M₁ ⟶ M₂` of right
`A`-modules, giving a morphism `X₁ ⊗ M₁ ⟶ X₂ ⊗ M₂` in `RightMod_ A`. -/
def actTensorHom {X₁ X₂ : C} {M₁ M₂ : RightMod_ A}
    (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
    (⟨X₁ ⊗ M₁.X, tensorModObj X₁ M₁⟩ : RightMod_ A) ⟶
    ⟨X₂ ⊗ M₂.X, tensorModObj X₂ M₂⟩ where
  hom := f ▷ M₁.X ≫ X₂ ◁ g.hom
  comm := by
    dsimp only [tensorModObj]
    simp only [assoc]
    rw [whisker_exchange_assoc]
    rw [← whiskerLeft_comp X₂ M₁.mod.act g.hom, g.comm, whiskerLeft_comp]
    rw [comp_whiskerRight_assoc, associator_naturality_middle_assoc,
        associator_naturality_left_assoc]

/-- The category `RightMod_ A` of right `A`-modules carries a canonical structure of a
left `C`-module category, with action `(X, M) ↦ X ⊗ M` and the natural associativity and
unit constraints. -/
instance actLeftModuleCategory :
    LeftModuleCategory C (RightMod_ (A := A)) where
  actObj X M := ⟨X ⊗ M.X, tensorModObj X M⟩
  actWhiskerLeft X {_ _} f := actWhiskerLeft X f
  actWhiskerRight {_ _} f N := actWhiskerRight f N
  actTensorHom f g := actTensorHom f g
  actAssociator X Y N := actAssociator X Y N
  actLeftUnitor N := actLeftUnitor N
  actTensorHom_def f g := by
    apply hom_ext
    simp [actTensorHom, actWhiskerRight, actWhiskerLeft]
  actWhiskerLeft_id X N := by
    apply hom_ext
    simp [actWhiskerLeft]
  actId_whiskerRight X N := by
    apply hom_ext
    simp [actWhiskerRight]
  actId_tensorHom_id X N := by
    apply hom_ext
    simp [actTensorHom]
  actTensorHom_comp f₁ g₁ f₂ g₂ := by
    apply hom_ext
    simp [actTensorHom, comp_whiskerRight, whiskerLeft_comp, whisker_exchange_assoc]
  actAssociator_naturality {X₁ X₂ Y₁ Y₂} {M₁ M₂} f g h := by
    apply hom_ext
    show ((f ⊗ₘ g) ▷ M₁.X ≫ (X₂ ⊗ Y₂) ◁ h.hom) ≫ (α_ X₂ Y₂ M₂.X).hom =
      (α_ X₁ Y₁ M₁.X).hom ≫ (f ▷ (Y₁ ⊗ M₁.X) ≫ X₂ ◁ (g ▷ M₁.X ≫ Y₂ ◁ h.hom))
    rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def,
        ← MonoidalCategory.tensorHom_def]
    exact associator_naturality f g h.hom
  actLeftUnitor_naturality f := by
    apply hom_ext
    simp [actWhiskerLeft, actLeftUnitor]
  actPentagon X Y Z N := by
    apply hom_ext
    dsimp only [comp_hom', actWhiskerRight, actAssociator, actWhiskerLeft]
    exact pentagon X Y Z N.X
  actTriangle X N := by
    apply hom_ext
    dsimp only [comp_hom', actWhiskerRight, actAssociator, actWhiskerLeft, actLeftUnitor]
    exact triangle X N.X

/-- Proposition 2.9.10: the category `Mod_C(A)` together with the functor `⊗̃` and the
associativity and unit constraints `ã`, `l̃` is a left module category over `C`. -/
def Proposition_2_9_10 : LeftModuleCategory C (RightMod_ (A := A)) :=
  RightMod_.actLeftModuleCategory

/-- Lemma 2.9.12: for any `X ∈ C`, the canonical isomorphism
`Hom_A(X ⊗ A, M) ≃ Hom(X, M)` exhibits `· ⊗ A` as left adjoint to the forgetful functor. -/
noncomputable def Lemma_2_9_12 (X : C) (M : RightMod_ A) :
    Hom ⟨X ⊗ A, tensorModObj X (regular A)⟩ M ≃ (X ⟶ M.X) where
  toFun f := (ρ_ X).inv ≫ (X ◁ η[A]) ≫ f.hom
  invFun g := {
    hom := (g ▷ A) ≫ M.mod.act
    comm := by
      simp only [tensorModObj, regular, assoc, comp_whiskerRight]
      rw [M.mod.act_assoc]
      slice_lhs 2 3 => rw [whisker_exchange g μ[A]]
      slice_lhs 1 2 => rw [← associator_naturality_left]
      simp [assoc]
  }
  left_inv f := by
    ext
    simp only [comp_whiskerRight, assoc]
    have hc : f.hom ▷ A ≫ M.mod.act = (α_ X A A).hom ≫ X ◁ μ[A] ≫ f.hom := by
      have := f.comm
      simp only [tensorModObj, regular] at this
      rw [← assoc, ← this]
    rw [hc]
    have h : (ρ_ X).inv ▷ A ≫ (X ◁ η[A]) ▷ A ≫ (α_ X A A).hom ≫ X ◁ μ[A] = 𝟙 (X ⊗ A) := by
      slice_lhs 2 3 => rw [associator_naturality_middle]
      slice_lhs 3 4 => rw [← whiskerLeft_comp, MonObj.one_mul]
      rw [triangle]; simp
    calc (ρ_ X).inv ▷ A ≫ (X ◁ η[A]) ▷ A ≫ (α_ X A A).hom ≫ X ◁ μ[A] ≫ f.hom
        = ((ρ_ X).inv ▷ A ≫ (X ◁ η[A]) ▷ A ≫ (α_ X A A).hom ≫ X ◁ μ[A]) ≫ f.hom := by
          simp [assoc]
      _ = 𝟙 (X ⊗ A) ≫ f.hom := by rw [h]
      _ = f.hom := by simp
  right_inv g := by
    simp only
    rw [whisker_exchange_assoc]
    simp

end RightMod_

/-- Two algebras `A` and `B` in `C` are Morita equivalent if there is a module equivalence
between their categories of right modules `RightMod_ A` and `RightMod_ B`. -/
def MoritaEquivalent (A B : C) [MonObj A] [MonObj B] : Prop :=
  Nonempty (ModuleEquivalence C (RightMod_ (C := C) (A := A)) (RightMod_ (C := C) (A := B)))

section TensorOverAlgebra

variable [Limits.HasCoequalizers C]

/-- Tensor product over an algebra `A`: for a right `A`-module `(M, actR)` and a left
`A`-module `(N, actL)`, the object `M ⊗_A N` is the coequalizer of the two natural maps
`M ⊗ A ⊗ N ⇒ M ⊗ N`. -/
noncomputable def TensorOverAlgebra {A M N : C}
    (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  Limits.coequalizer
    ((α_ M A N).inv ≫ (actR ▷ N))
    (M ◁ actL)

/-- The canonical projection `M ⊗ N ⟶ M ⊗_A N` exhibiting `M ⊗_A N` as the coequalizer. -/
noncomputable def TensorOverAlgebra.π {A M N : C}
    (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) :
    M ⊗ N ⟶ TensorOverAlgebra actR actL :=
  Limits.coequalizer.π _ _

end TensorOverAlgebra

end CategoryTheory
