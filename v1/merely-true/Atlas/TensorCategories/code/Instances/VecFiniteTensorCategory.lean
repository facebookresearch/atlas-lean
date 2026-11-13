/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective

set_option maxHeartbeats 400000

open CategoryTheory

universe u

namespace CategoryTheory

/-- A finite tensor category over a field `k`: a monoidal, abelian, `k`-linear rigid category
with enough projective objects and finite-dimensional hom spaces. -/
class FiniteTensorCategory' (k : Type*) [Field k] (C : Type*) [Category C]
    extends MonoidalCategory C, Abelian C, Linear k C, RigidCategory C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

namespace FGModuleCat

variable (K : Type u) [Field K]

/-- Every finite-dimensional vector space (viewed as an object of `FGModuleCat K`) is projective. -/
noncomputable instance instProjective (V : FGModuleCat.{u} K) :
    Projective V := by
  constructor
  intro E X f e he
  set F := forget₂ (FGModuleCat K) (ModuleCat K)
  haveI : Projective (F.obj V) := inferInstance
  haveI : Epi (F.map e) := Functor.map_epi F e
  obtain ⟨g, hg⟩ := Projective.factors (F.map f) (F.map e)
  haveI : F.Full := inferInstance
  obtain ⟨g', rfl⟩ := F.map_surjective g
  refine ⟨g', ?_⟩
  haveI : F.Faithful := inferInstance
  exact F.map_injective (by rw [F.map_comp, hg])

/-- `FGModuleCat K` has enough projectives, witnessed trivially by `V ↠ V` (since every object
is projective). -/
noncomputable instance instEnoughProjectives :
    EnoughProjectives (FGModuleCat.{u} K) where
  presentation V := ⟨{
    p := V
    f := 𝟙 V
  }⟩

/-- `FGModuleCat K`, the category of finite-dimensional `K`-vector spaces, is a finite tensor
category over `K`. -/
noncomputable instance instFiniteTensorCategory :
    FiniteTensorCategory' K (FGModuleCat.{u} K) where
  enoughProj := inferInstance
  homFiniteDim _ _ := inferInstance

end FGModuleCat

end CategoryTheory
