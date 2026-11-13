/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Category.FGModuleCat.Basic

set_option maxHeartbeats 800000

open CategoryTheory

universe v u

namespace CategoryTheory

/-- Definition 1.18.1 (EGNO), explicit form: a `k`-linear abelian category `C` is a
finite category if it is equivalent to the category of finite-dimensional modules over
some finite-dimensional `k`-algebra `A`. -/
def Definition_1_18_1_FiniteCategory
    (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Abelian C] [Linear k C] : Prop :=
  ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A),
    Nonempty (C ≌ FGModuleCat.{v} A)

/-- Intrinsic axiomatic version of "finite abelian category" over a field `k`: hom-spaces
are finite-dimensional, every object is artinian and noetherian, there are enough
projectives, and there are finitely many isomorphism classes of simple objects. -/
class IsFiniteAbelianCategory
    (k : Type*) [Field k] (A : Type*) [Category A] [Abelian A] [Linear k A] : Prop where
  finiteDimHom : ∀ (X Y : A), Module.Finite k (X ⟶ Y)
  artinian : ∀ (X : A), IsArtinianObject X
  noetherian : ∀ (X : A), IsNoetherianObject X
  enoughProj : EnoughProjectives A
  finitelyManySimples : ∃ (n : ℕ) (S : Fin n → A),
    (∀ i, Simple (S i)) ∧ (∀ (X : A), Simple X → ∃ i, Nonempty (X ≅ S i))

/-- Short alias for `Definition_1_18_1_FiniteCategory`. -/
abbrev Definition_1_18_1 := @Definition_1_18_1_FiniteCategory

/-- Short alias for `IsFiniteAbelianCategory` (the intrinsic axioms of Definition 1.18.2
in EGNO). -/
abbrev Definition_1_18_2 := @IsFiniteAbelianCategory

end CategoryTheory
