/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Subobject.Lattice

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u

/-- An object `X` has finite length if its subobject lattice is well-founded both as an
order and as its opposite (equivalently, both ascending and descending chains stabilize). -/
def HasFiniteLength {C : Type u} [Category.{v} C] (X : C) : Prop :=
  WellFoundedLT (Subobject X) ∧ WellFoundedGT (Subobject X)

/-- A locally finite `k`-linear abelian category: all Hom-spaces are finite-dimensional and
every object has finite length. -/
class LocallyFiniteCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] : Prop where
  homFinite : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  hasFiniteLength : ∀ (X : C), HasFiniteLength X

/-- A multiring category over `k`: a locally finite `k`-linear abelian monoidal category in
which tensoring with any object preserves monomorphisms and epimorphisms on both sides. -/
class MultiringCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    : Prop extends LocallyFiniteCategory k C where
  whiskerRight_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] (Z : C), Mono (f ▷ Z)
  whiskerLeft_mono : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Mono f], Mono (Z ◁ f)
  whiskerRight_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f] (Z : C), Epi (f ▷ Z)
  whiskerLeft_epi : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Epi f], Epi (Z ◁ f)

/-- A semisimple category: every object is a finite direct sum of simple objects. -/
class IsSemisimpleCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroMorphisms C] : Prop where
  semisimple : ∀ (X : C), ∃ (n : ℕ) (Y : Fin n → C) (_ : ∀ i, Simple (Y i))
    (_ : HasBiproduct Y), Nonempty (X ≅ ⨁ Y)

/-- Proposition 1.13.6 (special case): the tensor product `P ⊗ X` of a projective object
`P` with an object `X` having a right dual is again projective, provided right-whiskering
preserves epimorphisms. -/
theorem proposition_1_13_6_projective_tensor_right_dual
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P X : C} [Projective P] [HasRightDual X]
    (whiskerRight_epi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
    Projective (P ⊗ X) where
  factors := by
    intro E Y f e he
    let f' : P ⟶ Y ⊗ Xᘁ := (tensorRightHomEquiv P X (Xᘁ) Y) f
    have _he' : Epi (e ▷ Xᘁ) := whiskerRight_epi e (Xᘁ)
    obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ Xᘁ)
    use (tensorRightHomEquiv P X (Xᘁ) E).symm g'
    apply (tensorRightHomEquiv P X (Xᘁ) Y).injective
    rw [tensorRightHomEquiv_naturality]
    change (tensorRightHomEquiv P X (Xᘁ) E) ((tensorRightHomEquiv P X (Xᘁ) E).symm g') ≫
      e ▷ Xᘁ = f'
    rw [Equiv.apply_symm_apply]
    exact hg'

variable (k : Type*) [Field k]
variable (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]



