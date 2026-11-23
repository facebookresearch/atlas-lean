/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w

namespace TensorCategories

/-- Definition 1.14.1 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-tensor functor
between abelian monoidal categories `C` and `D` over a field `k`. It consists of an
exact (mono- and epi-preserving) faithful functor `F` equipped with natural
isomorphisms `J X Y : F X ⊗ F Y ≅ F (X ⊗ Y)` and a unit isomorphism
`F (𝟙_ C) ≅ 𝟙_ D`. -/
structure QuasiTensorFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  faithful : F.Faithful
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms
  J : ∀ (X Y : C), F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  J_natural_left : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
    (F.map f ▷ F.obj Y) ≫ (J X' Y).hom = (J X Y).hom ≫ F.map (f ▷ Y)
  J_natural_right : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
    (F.obj X ◁ F.map g) ≫ (J X Y').hom = (J X Y).hom ≫ F.map (X ◁ g)
  unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D

/-- Definition 1.14.1 (Etingof–Gelaki–Nikshych–Ostrik): A tensor functor between
abelian monoidal categories `C` and `D` over a field `k` is an exact faithful
functor `F` equipped with a monoidal structure (coherent associativity and unit
isomorphisms). -/
structure TensorFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  faithful : F.Faithful
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms
  monoidal : F.Monoidal

/-- Every tensor functor is in particular a quasi-tensor functor: the monoidal
structure provides the natural isomorphisms `J` and the unit isomorphism. -/
def TensorFunctor.toQuasiTensorFunctor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    (TF : TensorFunctor k C D) : QuasiTensorFunctor k C D where
  F := TF.F
  faithful := TF.faithful
  preservesMono := TF.preservesMono
  preservesEpi := TF.preservesEpi
  J X Y := @Functor.Monoidal.μIso _ _ _ _ _ _ TF.F TF.monoidal X Y
  J_natural_left := by
    intro X X' f Y
    have := TF.monoidal
    simp [Functor.Monoidal.μIso, Functor.LaxMonoidal.μ_natural_left]
  J_natural_right := by
    intro X Y Y' g
    have := TF.monoidal
    simp [Functor.Monoidal.μIso, Functor.LaxMonoidal.μ_natural_right]
  unitIso := (@Functor.Monoidal.εIso _ _ _ _ _ _ TF.F TF.monoidal).symm

/-- Reference abbreviation for Definition 1.14.1: a quasi-tensor functor. -/
abbrev Definition_1_14_1_QuasiTensorFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] :=
  QuasiTensorFunctor k C D

/-- Reference abbreviation for Definition 1.14.1: a tensor functor. -/
abbrev Definition_1_14_1_TensorFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] :=
  TensorFunctor k C D

section QuasiTensorExactness

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]

/-- A quasi-tensor functor is left exact: its underlying functor preserves monomorphisms. -/
theorem QuasiTensorFunctor.isLeftExact
    (QTF : QuasiTensorFunctor k C D) : QTF.F.PreservesMonomorphisms :=
  QTF.preservesMono

/-- A quasi-tensor functor is right exact: its underlying functor preserves epimorphisms. -/
theorem QuasiTensorFunctor.isRightExact
    (QTF : QuasiTensorFunctor k C D) : QTF.F.PreservesEpimorphisms :=
  QTF.preservesEpi

/-- A quasi-tensor functor is faithful. -/
theorem QuasiTensorFunctor.isFaithful
    (QTF : QuasiTensorFunctor k C D) : QTF.F.Faithful :=
  QTF.faithful

/-- A quasi-tensor functor preserves the unit object, as recorded by its unit isomorphism. -/
def QuasiTensorFunctor.preservesUnit
    (QTF : QuasiTensorFunctor k C D) : QTF.F.obj (𝟙_ C) ≅ 𝟙_ D :=
  QTF.unitIso

end QuasiTensorExactness

section TensorFunctorProps

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]

/-- A tensor functor is left exact: its underlying functor preserves monomorphisms. -/
theorem TensorFunctor.isLeftExact
    (TF : TensorFunctor k C D) : TF.F.PreservesMonomorphisms :=
  TF.preservesMono

/-- A tensor functor is right exact: its underlying functor preserves epimorphisms. -/
theorem TensorFunctor.isRightExact
    (TF : TensorFunctor k C D) : TF.F.PreservesEpimorphisms :=
  TF.preservesEpi

/-- A tensor functor is faithful. -/
theorem TensorFunctor.isFaithful
    (TF : TensorFunctor k C D) : TF.F.Faithful :=
  TF.faithful

/-- The unit isomorphism of a tensor functor, derived from its monoidal structure. -/
def TensorFunctor.preservesUnit
    (TF : TensorFunctor k C D) : TF.F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (@Functor.Monoidal.εIso _ _ _ _ _ _ TF.F TF.monoidal).symm

/-- A quasi-tensor functor whose underlying functor carries a monoidal structure
upgrades to a tensor functor. -/
def QuasiTensorFunctor.toTensorFunctor_of_monoidal
    (QTF : QuasiTensorFunctor k C D)
    (hmon : QTF.F.Monoidal) : TensorFunctor k C D where
  F := QTF.F
  faithful := QTF.faithful
  preservesMono := QTF.preservesMono
  preservesEpi := QTF.preservesEpi
  monoidal := hmon

end TensorFunctorProps

/-- Definition 1.19.1 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-fiber functor on an
abelian monoidal category `C` over a field `k` is a quasi-tensor functor from `C`
to the category of `k`-modules. -/
structure QuasiFiberFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    extends QuasiTensorFunctor k C (ModuleCat.{w} k)

/-- Definition 1.19.1 (Etingof–Gelaki–Nikshych–Ostrik): A fiber functor on an
abelian monoidal category `C` over a field `k` is a tensor functor from `C` to the
category of `k`-modules. -/
structure FiberFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] where
  F : C ⥤ ModuleCat.{w} k
  faithful : F.Faithful
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms
  monoidal : F.Monoidal

/-- Reference abbreviation for Definition 1.19.1: a quasi-fiber functor. -/
abbrev Definition_1_19_1_QuasiFiberFunctor := @QuasiFiberFunctor

/-- Reference abbreviation for Definition 1.19.1: a fiber functor. -/
abbrev Definition_1_19_1_FiberFunctor := @FiberFunctor

/-- A fiber functor on `C` is in particular a tensor functor from `C` to the
category of `k`-modules. -/
def FiberFunctor.toTensorFunctor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF : FiberFunctor k C) : TensorFunctor k C (ModuleCat.{w} k) where
  F := FF.F
  faithful := FF.faithful
  preservesMono := FF.preservesMono
  preservesEpi := FF.preservesEpi
  monoidal := FF.monoidal

/-- A fiber functor is in particular a quasi-fiber functor, via its monoidal structure. -/
def FiberFunctor.toQuasiFiberFunctor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF : FiberFunctor k C) : QuasiFiberFunctor k C :=
  ⟨FF.toTensorFunctor.toQuasiTensorFunctor⟩

/-- A tensor functor from `C` to the category of `k`-modules is a fiber functor on `C`. -/
def FiberFunctor.ofTensorFunctorToVec
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (TF : TensorFunctor k C (ModuleCat.{w} k)) :
    FiberFunctor k C where
  F := TF.F
  faithful := TF.faithful
  preservesMono := TF.preservesMono
  preservesEpi := TF.preservesEpi
  monoidal := TF.monoidal

/-- Exhibit a quasi-fiber functor as a quasi-tensor functor into the category of
`k`-modules. -/
def QuasiFiberFunctor.toQuasiTensorFunctorToVec
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF : QuasiFiberFunctor k C) : QuasiTensorFunctor k C (ModuleCat.{w} k) :=
  QFF.toQuasiTensorFunctor

/-- Definition 1.34.1 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-fiber functor `QFF`
is normalized when the natural isomorphisms `J` are compatible with the left and
right unit constraints via the unit isomorphism. -/
def QuasiFiberFunctor.IsNormalized
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF : QuasiFiberFunctor k C) : Prop :=
  (∀ X : C,
    (QFF.J (𝟙_ C) X).hom ≫ QFF.F.map (λ_ X).hom =
      (QFF.unitIso.hom ▷ QFF.F.obj X) ≫ (λ_ (QFF.F.obj X)).hom) ∧
  (∀ X : C,
    (QFF.J X (𝟙_ C)).hom ≫ QFF.F.map (ρ_ X).hom =
      (QFF.F.obj X ◁ QFF.unitIso.hom) ≫ (ρ_ (QFF.F.obj X)).hom)

/-- Reference abbreviation for Definition 1.34.1: a normalized quasi-fiber functor. -/
abbrev Definition_1_34_1_IsNormalized := @QuasiFiberFunctor.IsNormalized

/-- Reference abbreviation for Definition 1.34.1. -/
abbrev Definition_1_34_1 := @QuasiFiberFunctor.IsNormalized

/-- Definition 1.34.2 (Etingof–Gelaki–Nikshych–Ostrik): Two quasi-fiber functors
on `C` are twist-equivalent if they share the same underlying functor. -/
def QuasiFiberFunctor.TwistEquivalent
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF₁ QFF₂ : QuasiFiberFunctor k C) : Prop :=
  QFF₁.F = QFF₂.F

/-- The twist isomorphism on `QFF₁.F X ⊗ QFF₁.F Y` obtained from a twist-equivalence
`h : QFF₁.TwistEquivalent QFF₂`, comparing the two natural isomorphisms `J` on
the same underlying functor. -/
noncomputable def QuasiFiberFunctor.twist
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF₁ QFF₂ : QuasiFiberFunctor k C)
    (h : QFF₁.TwistEquivalent QFF₂) (X Y : C) :
    QFF₁.F.obj X ⊗ QFF₁.F.obj Y ≅ QFF₁.F.obj X ⊗ QFF₁.F.obj Y := by
  have hobj : ∀ Z : C, QFF₁.F.obj Z = QFF₂.F.obj Z := fun Z => by rw [h]


  exact eqToIso (by simp [hobj]) ≪≫ QFF₂.J X Y ≪≫ eqToIso (by simp [hobj]) ≪≫
    (QFF₁.J X Y).symm

/-- Reference abbreviation for Definition 1.34.2: twist-equivalence of quasi-fiber functors. -/
abbrev Definition_1_34_2 := @QuasiFiberFunctor.TwistEquivalent

/-- An object `P` of an abelian category `C` is a projective generator if it is
projective and detects zero objects (any `X` admitting only the zero map from `P`
must itself be zero). -/
structure IsProjectiveGenerator
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) : Prop where
  proj : Projective P
  generates : ∀ (X : C), (∀ f : P ⟶ X, f = 0) → Limits.IsZero X








end TensorCategories


open TensorCategories in
/-- Reference abbreviation for Definition 1.14.1: a quasi-tensor functor. -/
abbrev Definition_1_14_1_QuasiTensorFunctor := @QuasiTensorFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.14.1: a tensor functor. -/
abbrev Definition_1_14_1_TensorFunctor := @TensorFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.14.1. -/
abbrev Definition_1_14_1 := @QuasiTensorFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.19.1: a quasi-fiber functor. -/
abbrev Definition_1_19_1_QuasiFiberFunctor := @QuasiFiberFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.19.1: a fiber functor. -/
abbrev Definition_1_19_1_FiberFunctor := @FiberFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.19.1. -/
abbrev Definition_1_19_1 := @FiberFunctor
