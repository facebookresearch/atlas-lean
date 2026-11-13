/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Atlas.TensorCategories.code.TensorExact
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Subobject.Lattice

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u

namespace TensorCategories

/-- An object `X` has finite length if the lattice of its subobjects is both
Noetherian (well-founded `<`) and Artinian (well-founded `>`). -/
def HasFiniteLength {C : Type u} [Category.{v} C] (X : C) : Prop :=
  WellFoundedLT (Subobject X) ∧ WellFoundedGT (Subobject X)

/-- Definition 1.12.1: a `k`-linear abelian category is locally finite if all hom-spaces are
finite-dimensional over `k` and every object has finite length. -/
class LocallyFiniteCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] : Prop where
  homFinite : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  hasFiniteLength : ∀ (X : C), HasFiniteLength X

attribute [instance] LocallyFiniteCategory.homFinite

/-- Definition 1.12.1 alias: a locally finite `k`-linear abelian category. -/
abbrev Definition_1_12_1_LocallyFiniteCategory (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C] :=
  LocallyFiniteCategory k C

/-- Definition 1.12.3: a multitensor category is a locally finite `k`-linear abelian rigid
monoidal category whose tensor bifunctor is bilinear on morphisms. -/
class MultitensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop extends LocallyFiniteCategory k C

/-- Definition 1.12.3: a tensor category is a multitensor category satisfying additionally
that `End(𝟙) ≃ₐ[k] k`. -/
class TensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop extends MultitensorCategory k C where
  endUnit_iso_k : Nonempty ((End (𝟙_ C)) ≃ₐ[k] k)

/-- Definition 1.13.3: a multiring category is a locally finite `k`-linear abelian monoidal
category whose tensor product is biexact (preserves mono- and epimorphisms in both factors). -/
class MultiringCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    : Prop extends LocallyFiniteCategory k C where
  whiskerRight_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] (Z : C), Mono (f ▷ Z)
  whiskerLeft_mono : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Mono f], Mono (Z ◁ f)
  whiskerRight_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f] (Z : C), Epi (f ▷ Z)
  whiskerLeft_epi : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Epi f], Epi (Z ◁ f)

/-- Definition 1.13.3: a ring category is a multiring category with `End(𝟙) ≃ₐ[k] k`. -/
class RingCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    : Prop extends MultiringCategory k C where
  endUnit_iso_k : Nonempty ((End (𝟙_ C)) ≃ₐ[k] k)

/-- Definition 1.13.3 alias: a multiring category. -/
abbrev Definition_1_13_3_MultiringCategory (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  MultiringCategory k C

/-- Definition 1.13.3 alias: a ring category. -/
abbrev Definition_1_13_3_RingCategory (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  RingCategory k C

/-- Definition 1.13.3 alias (snake-case): a multiring category. -/
abbrev def_1_13_3_multiring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  MultiringCategory k C

/-- Definition 1.13.3 alias (snake-case): a ring category. -/
abbrev def_1_13_3_ring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  RingCategory k C

/-- A preadditive category is semisimple if every object is isomorphic to a finite biproduct
of simple objects. -/
class IsSemisimpleCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroMorphisms C] : Prop where
  semisimple : ∀ (X : C), ∃ (n : ℕ) (Y : Fin n → C) (_ : ∀ i, Simple (Y i))
    (_ : HasBiproduct Y), Nonempty (X ≅ ⨁ Y)

/-- A category has finitely many simple objects if there exists a finite list of simples
representing every isomorphism class of simple objects. -/
class HasFinitelyManySimples (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  finiteSimples : ∃ (n : ℕ) (S : Fin n → C), (∀ i, Simple (S i)) ∧
    (∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ S i))

/-- Definition 1.12.3: a multifusion category is a semisimple multitensor category with
finitely many isomorphism classes of simple objects. -/
class MultifusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop extends MultitensorCategory k C where
  semisimple : IsSemisimpleCategory C
  hasFinitelyManySimples : HasFinitelyManySimples C

/-- Definition 1.12.3: a fusion category is a semisimple tensor category with finitely many
isomorphism classes of simple objects. -/
class FusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop extends TensorCategory k C where
  semisimple : IsSemisimpleCategory C
  hasFinitelyManySimples : HasFinitelyManySimples C

/-- Every fusion category is in particular a multifusion category. -/
instance FusionCategory.toMultifusionCategory (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [h : FusionCategory k C] : MultifusionCategory k C where
  toLocallyFiniteCategory := h.toLocallyFiniteCategory
  semisimple := h.semisimple
  hasFinitelyManySimples := h.hasFinitelyManySimples

/-- Definition 1.12.3 alias: a multitensor category. -/
abbrev Definition_1_12_3_MultitensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultitensorCategory k C

/-- Definition 1.12.3 alias: a tensor category. -/
abbrev Definition_1_12_3_TensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  TensorCategory k C

/-- Definition 1.12.3 alias: a multifusion category. -/
abbrev Definition_1_12_3_MultifusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultifusionCategory k C

/-- Definition 1.12.3 alias: a fusion category. -/
abbrev Definition_1_12_3_FusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  FusionCategory k C

/-- Definition 1.12.3 alias (snake-case): a multitensor category. -/
abbrev def_1_12_3_multitensor (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultitensorCategory k C

/-- Definition 1.12.3 alias (snake-case): a tensor category. -/
abbrev def_1_12_3_tensor (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  TensorCategory k C

/-- Definition 1.12.3 alias: default multitensor category Prop. -/
abbrev def_1_12_3 (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultitensorCategory k C

end TensorCategories

/-- Definition 1.12.1 alias (snake-case, top-level): a locally finite `k`-linear abelian category. -/
abbrev def_1_12_1_locally_finite_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C] :=
  TensorCategories.LocallyFiniteCategory k C

/-- Definition 1.13.3 alias (snake-case, top-level): a multiring category. -/
abbrev def_1_13_3_multiring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  TensorCategories.MultiringCategory k C

/-- Definition 1.13.3 alias (snake-case, top-level): a ring category. -/
abbrev def_1_13_3_ring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  TensorCategories.RingCategory k C

section SchurLemma

open TensorCategories

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
variable [LocallyFiniteCategory k C]

/-- Schur's lemma in a locally finite `k`-linear abelian category over an algebraically closed
field: every morphism between non-isomorphic simple objects is zero. -/
theorem schur_hom_eq_zero_of_not_iso {X Y : C} [Simple X] [Simple Y]
    (h : (X ≅ Y) → False) : ∀ (f : X ⟶ Y), f = 0 := by
  intro f
  have := subsingleton_of_forall_eq (0 : X ⟶ Y) fun g => by
    have p := not_congr (isIso_iff_nonzero g)
    simp only [Classical.not_not, Ne] at p
    exact p.mp fun _ => h (asIso g)
  exact Subsingleton.elim f 0

end SchurLemma
