/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂

namespace TensorCategories


section Section_1_1

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

/-- Definition 1.1.2: a monoidal subcategory of a monoidal category `C` is a monoidal
category `D` together with a faithful monoidal functor `ι : D ⥤ C`. -/
structure Definition_1_1_2_MonoidalSubcategory where
  D : Type u₂
  [instCat : Category.{v₂} D]
  [instMonoidal : MonoidalCategory D]
  ι : D ⥤ C
  [instFaithful : ι.Faithful]
  instMonoidalFunctor : ι.Monoidal

attribute [instance] Definition_1_1_2_MonoidalSubcategory.instCat
  Definition_1_1_2_MonoidalSubcategory.instMonoidal
  Definition_1_1_2_MonoidalSubcategory.instFaithful

/-- A full subcategory cut out by a monoidal object-property of `C` gives a monoidal
subcategory in the sense of `Definition_1_1_2_MonoidalSubcategory`. -/
def Definition_1_1_2_MonoidalSubcategory.ofFullSubcategory
    (P : ObjectProperty C) [P.IsMonoidal] :
    Definition_1_1_2_MonoidalSubcategory.{v₁, v₁, u₁, u₁} C where
  D := P.FullSubcategory
  ι := P.ι
  instMonoidalFunctor := inferInstance

/-- Definition 1.1.2 (alias): the type of monoidal subcategories of `C`. -/
abbrev Definition_1_1_2 := Definition_1_1_2_MonoidalSubcategory (C := C)

/-- Lower-case alias for `Definition_1_1_2`, used by other files. -/
abbrev def_1_1_2 := Definition_1_1_2_MonoidalSubcategory (C := C)

/-- Definition 1.1.3 (helper): the monoidal-category instance on the monoidal opposite of
`C`, where tensor product is reversed. -/
@[reducible]
def def_1_1_3_monoidalOpposite : MonoidalCategory (MonoidalOpposite C) := inferInstance

/-- Definition 1.1.3: the monoidal opposite category `C^{op,⊗}` of a monoidal category. -/
abbrev Definition_1_1_3 := MonoidalOpposite C

end Section_1_1


section Section_1_2

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Proposition 1.2.2 (left triangle): the pentagon-axiom consequence
`α(1,X,Y) ≫ λ_{X⊗Y} = λ_X ▷ Y`. -/
theorem prop_1_2_2_left (X Y : C) :
    (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ▷ Y := by
  rw [leftUnitor_tensor_hom, Iso.hom_inv_id_assoc]

/-- The property of an object `U : C` being a (two-sided) unit object: tensoring with `U`
on either side is naturally isomorphic to the identity. -/
structure IsUnitObject (U : C) where
  leftEquiv : ∀ X : C, U ⊗ X ≅ X
  rightEquiv : ∀ X : C, X ⊗ U ≅ X

/-- The monoidal unit object `𝟙_ C` is a unit object, with the natural left and right
unitor isomorphisms. -/
def isUnitObject_unit : IsUnitObject (𝟙_ C : C) where
  leftEquiv X := λ_ X
  rightEquiv X := ρ_ X

/-- The inverses of the left and right unitor at the unit object coincide:
`λ_{𝟙}⁻¹ = ρ_{𝟙}⁻¹`. -/
lemma unitors_inv_equal :
    (λ_ (𝟙_ C : C)).inv = (ρ_ (𝟙_ C : C)).inv := by
  rw [← cancel_mono (λ_ (𝟙_ C : C)).hom, Iso.inv_hom_id, unitors_equal, Iso.inv_hom_id]

/-- Right-whiskering by `𝟙_ C` of an endomorphism of the unit equals conjugation by the
right unitor: `h ▷ 𝟙 = ρ_{𝟙} ≫ h ≫ ρ_{𝟙}⁻¹`. -/
lemma rightUnitor_conjugate_whiskerRight_unit (h : (𝟙_ C : C) ⟶ 𝟙_ C) :
    h ▷ 𝟙_ C = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by
  have nat := rightUnitor_naturality h
  calc h ▷ 𝟙_ C
      = h ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv := by simp
    _ = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by rw [← assoc, nat, assoc]

/-- Left-whiskering by `𝟙_ C` of an endomorphism of the unit equals the same conjugation
by the right unitor as in `rightUnitor_conjugate_whiskerRight_unit`. -/
lemma rightUnitor_conjugate_whiskerLeft_unit (h : (𝟙_ C : C) ⟶ 𝟙_ C) :
    𝟙_ C ◁ h = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by
  have nat := leftUnitor_naturality h
  calc 𝟙_ C ◁ h
      = 𝟙_ C ◁ h ≫ (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv := by simp
    _ = (λ_ (𝟙_ C)).hom ≫ h ≫ (λ_ (𝟙_ C)).inv := by rw [← assoc, nat, assoc]
    _ = (ρ_ (𝟙_ C)).hom ≫ h ≫ (ρ_ (𝟙_ C)).inv := by rw [unitors_equal, unitors_inv_equal]

/-- Proposition 1.2.7 (Eckmann–Hilton): the endomorphism monoid of the unit object in a
monoidal category is commutative. -/
theorem prop_1_2_7 (f g : (𝟙_ C : C) ⟶ 𝟙_ C) :
    f ≫ g = g ≫ f := by

  have expand1 : f ⊗ₘ g = (ρ_ (𝟙_ C)).hom ≫ (f ≫ g) ≫ (ρ_ (𝟙_ C)).inv := by
    rw [MonoidalCategory.tensorHom_def,
        rightUnitor_conjugate_whiskerRight_unit f,
        rightUnitor_conjugate_whiskerLeft_unit g]; simp [assoc]

  have expand2 : f ⊗ₘ g = (ρ_ (𝟙_ C)).hom ≫ (g ≫ f) ≫ (ρ_ (𝟙_ C)).inv := by
    rw [tensorHom_def',
        rightUnitor_conjugate_whiskerLeft_unit g,
        rightUnitor_conjugate_whiskerRight_unit f]; simp [assoc]

  have := expand1.symm.trans expand2
  simp [cancel_epi] at this
  exact this

/-- Proposition 1.2.7 (textbook-named alias of `prop_1_2_7`): endomorphisms of the unit
object commute. -/
theorem Proposition_1_2_7 (f g : (𝟙_ C : C) ⟶ 𝟙_ C) :
    f ≫ g = g ≫ f :=
  prop_1_2_7 f g

end Section_1_2


/-- Definition 1.2.6: a monoidal category is the data of a category together with a
monoidal structure (tensor product, unit, associator, unitors satisfying pentagon and
triangle). -/
abbrev Definition_1_2_6 (C : Type u₁) [Category.{v₁} C] := MonoidalCategory C


section Section_1_3

end Section_1_3


section Section_1_4

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A monoidal functor `F : C ⥤ D` is a monoidal equivalence if its underlying functor is
an equivalence of categories. -/
def IsMonoidalEquivalence_def_1_1_3
    (F : C ⥤ D) [F.Monoidal] : Prop :=
  F.IsEquivalence

end Section_1_4


section Section_1_5

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Definition 1.4.5: a monoidal natural isomorphism between two lax-monoidal functors is
a natural isomorphism whose forward component is a monoidal natural transformation. -/
structure def_1_4_5_MonoidalNatIso
    (F₁ F₂ : C ⥤ D) [F₁.LaxMonoidal] [F₂.LaxMonoidal] where
  toNatIso : F₁ ≅ F₂
  [isMonoidal : NatTrans.IsMonoidal toNatIso.hom]

attribute [instance] def_1_4_5_MonoidalNatIso.isMonoidal

/-- The inverse component of a monoidal natural isomorphism is again a monoidal natural
transformation. -/
instance def_1_4_5_MonoidalNatIso.inv_isMonoidal
    {F₁ F₂ : C ⥤ D} [F₁.LaxMonoidal] [F₂.LaxMonoidal]
    (η : def_1_4_5_MonoidalNatIso F₁ F₂) : NatTrans.IsMonoidal η.toNatIso.inv :=
  inferInstance

end Section_1_5


section Section_1_6

/-- The category of right-exact endofunctors of an additive category inherits a monoidal
structure from composition: the unit (the identity functor) is right-exact and composition
of right-exact functors is right-exact. -/
noncomputable instance rightExactEndofunctor_isMonoidal
    (C : Type*) [Category C] :
    (rightExactFunctor C C).IsMonoidal where
  prop_unit := by
    simp only [rightExactFunctor_iff]
    exact Limits.PreservesColimitsOfSize0.preservesFiniteColimits (𝟭 C)
  prop_tensor := by
    intro F G hF hG
    simp only [rightExactFunctor_iff] at hF hG ⊢
    exact Limits.comp_preservesFiniteColimits F G

/-- The enveloping algebra `A^e := A ⊗_k A^{op}` of a `k`-algebra `A`. -/
abbrev EnvelopingAlgebra (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] :=
  TensorProduct k A (MulOpposite A)



end Section_1_6


section Section_1_7

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]
variable {A : Type*} [CommGroup A]

/-- Definition 1.4.5 (alias): packages a `Functor.Monoidal` instance for a functor
between monoidal categories. -/
abbrev Definition_1_4_5_MonoidalFunctor
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [hF : F.Monoidal] : Functor.Monoidal F :=
  hF

/-- The cocycle condition describing the data of a monoidal functor between two
3-cocycle-twisted vector-space categories `Vec_{G₁}^{ω₁} → Vec_{G₂}^{ω₂}` associated to a
group homomorphism `f` and a 2-cochain `μ`. -/
def IsMonoidalFunctorDatum
    (ω₁ : G₁ → G₁ → G₁ → A) (ω₂ : G₂ → G₂ → G₂ → A)
    (f : G₁ →* G₂) (μ : G₁ → G₁ → A) : Prop :=
  ∀ g h l : G₁,
    ω₁ g h l * μ (g * h) l * μ g h =
    μ g (h * l) * μ h l * ω₂ (f g) (f h) (f l)

/-- The cohomological condition characterising when a 1-cochain `η : G₁ → A` provides a
monoidal natural transformation between two monoidal functors with cochain data `μ` and
`μ'`. -/
def IsMonoidalTransformationDatum
    (μ μ' : G₁ → G₁ → A) (η : G₁ → A) : Prop :=
  ∀ g h : G₁, μ' g h * η g * η h = η (g * h) * μ g h

end Section_1_7


section Section_1_8

/-- A monoidal category is strict if the associator and unitors are identities on the
nose: `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)`, `𝟙_ C ⊗ X = X`, and `X ⊗ 𝟙_ C = X`. -/
class IsStrictMonoidal (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] : Prop where
  assoc_strict : ∀ X Y Z : C, (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  left_unit_strict : ∀ X : C, 𝟙_ C ⊗ X = X
  right_unit_strict : ∀ X : C, X ⊗ 𝟙_ C = X

/-- Example 1.8.2: the category of endofunctors `C ⥤ C` of any category is monoidal
under composition, and that monoidal structure is strict. -/
@[reducible]
def ex_1_8_2_endofunctor_monoidal (C : Type u₁) [Category.{v₁} C] :
    MonoidalCategory (C ⥤ C) :=
  endofunctorMonoidalCategory C

end Section_1_8


section Section_1_9

/-- Theorem 1.9 (Mac Lane normalization): the identity on the free monoidal category on
`C` is naturally isomorphic to the composition `fullNormalize ⋙ inclusion`. -/
def thm_1_9_normalization (C : Type*) :
    𝟭 (FreeMonoidalCategory C) ≅
    FreeMonoidalCategory.fullNormalize C ⋙ FreeMonoidalCategory.inclusion :=
  FreeMonoidalCategory.fullNormalizeIso C

end Section_1_9

end TensorCategories

/-- Top-level alias for `Definition_1_1_2_MonoidalSubcategory`, namespaced for external
use. -/
abbrev def_1_1_2 := @TensorCategories.Definition_1_1_2_MonoidalSubcategory

/-- Top-level alias for `def_1_1_3_monoidalOpposite`, namespaced for external use. -/
abbrev def_1_1_3 := @TensorCategories.def_1_1_3_monoidalOpposite
