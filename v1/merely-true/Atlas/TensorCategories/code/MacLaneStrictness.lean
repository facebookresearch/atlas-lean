/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Basic

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

namespace EGNO.MacLaneStrictness

/-- Definition 1.8.1: A monoidal category is strict if the associator and unitors are
identity morphisms, i.e. `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)`, `𝟙_C ⊗ X = X`, and `X ⊗ 𝟙_C = X`
on the nose, with the structure isomorphisms equal to the corresponding `eqToHom`. -/
class MonoidalCategory.IsStrict (C : Type*) [Category C] [MonoidalCategory C] : Prop where
  tensorObj_assoc : ∀ (X Y Z : C), (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  tensorUnit_left : ∀ (X : C), 𝟙_ C ⊗ X = X
  tensorUnit_right : ∀ (X : C), X ⊗ 𝟙_ C = X
  associator_eqToHom : ∀ (X Y Z : C),
    (α_ X Y Z).hom = eqToHom (tensorObj_assoc X Y Z)
  leftUnitor_eqToHom : ∀ (X : C),
    (λ_ X).hom = eqToHom (tensorUnit_left X)
  rightUnitor_eqToHom : ∀ (X : C),
    (ρ_ X).hom = eqToHom (tensorUnit_right X)

section EndofunctorStrict

universe v u
variable (C : Type u) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

/-- The monoidal category of endofunctors of `C` is strict: tensor product is composition,
the unit is the identity functor, and all structure isomorphisms are identities. -/
instance endofunctorMonoidalCategory_isStrict :
    @MonoidalCategory.IsStrict (C ⥤ C) _ (endofunctorMonoidalCategory C) where
  tensorObj_assoc _ _ _ := rfl
  tensorUnit_left _ := rfl
  tensorUnit_right _ := rfl
  associator_eqToHom _ _ _ := by ext X; simp
  leftUnitor_eqToHom _ := by ext X; simp
  rightUnitor_eqToHom _ := by ext X; simp

end EndofunctorStrict

section SkeletalStrictness

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- In a skeletal monoidal category, the associator becomes a literal equality of objects. -/
theorem skeletal_monoidal_tensorObj_assoc (hC : Skeletal C) (X Y Z : C) :
    (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) :=
  hC ⟨α_ X Y Z⟩

/-- In a skeletal monoidal category, the left unitor becomes a literal equality of objects. -/
theorem skeletal_monoidal_tensorUnit_left (hC : Skeletal C) (X : C) :
    𝟙_ C ⊗ X = X :=
  hC ⟨λ_ X⟩

/-- In a skeletal monoidal category, the right unitor becomes a literal equality of objects. -/
theorem skeletal_monoidal_tensorUnit_right (hC : Skeletal C) (X : C) :
    X ⊗ 𝟙_ C = X :=
  hC ⟨ρ_ X⟩

/-- A skeletal monoidal category yields a monoid structure on the type of its objects. -/
noncomputable abbrev skeletal_monoidFromMonoidal (hC : Skeletal C) : Monoid C :=
  monoidOfSkeletalMonoidal hC

end SkeletalStrictness

section StrictnessTheorem

universe v u
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The skeleton of a monoidal category satisfies strict associativity at the object level. -/
theorem skeleton_tensorObj_assoc (X Y Z : Skeleton C) :
    (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) :=
  skeletal_monoidal_tensorObj_assoc (skeleton_skeletal C) X Y Z

/-- The skeleton of a monoidal category satisfies strict left unit equality at the object level. -/
theorem skeleton_tensorUnit_left (X : Skeleton C) :
    𝟙_ _ ⊗ X = X :=
  skeletal_monoidal_tensorUnit_left (skeleton_skeletal C) X

/-- The skeleton of a monoidal category satisfies strict right unit equality at the object level. -/
theorem skeleton_tensorUnit_right (X : Skeleton C) :
    X ⊗ 𝟙_ _ = X :=
  skeletal_monoidal_tensorUnit_right (skeleton_skeletal C) X

/-- An intermediate version of MacLane's strictness theorem: every monoidal category is
monoidally equivalent to a category with strict associativity and unit equalities at the
object level, given by its skeleton. -/
theorem macLane_strictness' :
    ∃ (D : Type u) (_ : Category.{v} D) (_ : MonoidalCategory D),
      (∀ (X Y Z : D), (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)) ∧
      (∀ (X : D), 𝟙_ D ⊗ X = X) ∧
      (∀ (X : D), X ⊗ 𝟙_ D = X) ∧
      ∃ (e : C ≌ D), Nonempty (e.functor.Monoidal) ∧ Nonempty (e.inverse.Monoidal) :=
  ⟨Skeleton C, inferInstance, inferInstance,
    skeleton_tensorObj_assoc C,
    skeleton_tensorUnit_left C,
    skeleton_tensorUnit_right C,
    ⟨(skeletonEquivalence C).symm, ⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩


end StrictnessTheorem

section MonoidalEmbedding

universe v u
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

attribute [local instance] endofunctorMonoidalCategory

/-- The right-tensoring functor `C → C ⥤ C`, `X ↦ • ⊗ X`, is naturally a monoidal functor,
giving the monoidal embedding of `C` into its category of endofunctors. -/
instance tensoringRight_monoidal : (tensoringRight C).Monoidal := inferInstance

end MonoidalEmbedding

section CoherenceTheorem

universe u

open FreeMonoidalCategory

end CoherenceTheorem

end EGNO.MacLaneStrictness
