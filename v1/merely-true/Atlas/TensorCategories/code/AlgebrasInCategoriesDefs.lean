/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.AlgebrasInCategories
import Atlas.TensorCategories.code.ExactModuleCategory
import Atlas.TensorCategories.code.InternalHom
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

set_option maxHeartbeats 400000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Convenient abbreviation: an algebra structure on an object `A : C` is a `MonObj A`. -/
abbrev AlgebraObj (A : C) := MonObj A

/-- Convenient abbreviation: a left module structure on `M : C` over the algebra `A` is a
`ModObj A M`. -/
abbrev LeftModObj (A : C) [MonObj A] (M : C) := ModObj A M

/-- Two algebras `A` and `B` in `C` are Morita equivalent if the module categories `Mod_C(A)`
and `Mod_C(B)` are module equivalent. -/
abbrev Definition_2_9_18_MoritaEquivalent (A B : C) [MonObj A] [MonObj B] : Prop :=
  MoritaEquivalent A B

/-- An algebra `A` in `C` is exact when the category `RightMod_ A` of right `A`-modules,
viewed as a left `C`-module category, is an exact module category. -/
def IsExactAlgebra (A : C) [MonObj A]
    [LeftModuleCategory C (RightMod_ (A := A))] : Prop :=
  Nonempty (ExactModuleCategory C (RightMod_ (C := C) (A := A)))

/-- An algebra `A` in the category `C` is called exact if the module category `Mod_C(A)`
is exact. -/
abbrev Definition_2_9_21_ExactAlgebra (A : C) [MonObj A]
    [LeftModuleCategory C (RightMod_ (A := A))] : Prop :=
  IsExactAlgebra A

section Proposition_2_9_10

variable {A : C} [MonObj A]

/-- The category `Mod_C(A)` of right `A`-modules, equipped with the natural tensor action
of `C`, the standard associativity, and unit constraints, is a left `C`-module category. -/
def proposition_2_9_10 : LeftModuleCategory C (RightMod_ (A := A)) :=
  RightMod_.actLeftModuleCategory

end Proposition_2_9_10

variable [Limits.HasCoequalizers C]

/-- Tensor product over an algebra `A`: for a right `A`-module `(M, actR)` and a left
`A`-module `(N, actL)`, the object `M ⊗_A N` is the quotient of `M ⊗ N` by the image of
`actR ⊗ id - id ⊗ actL : M ⊗ A ⊗ N → M ⊗ N`. -/
noncomputable def Definition_2_9_22_TensorOverAlgebra
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  TensorOverAlgebra actR actL

/-- Abbreviation for an `A`-`B`-bimodule object in `C`, identified with Mathlib's `Bimod A B`. -/
abbrev BimoduleObj (A B : Mon C) := Bimod A B

/-- An `A`-`B`-bimodule in a monoidal category `C` is a triple `(M, p, q)` where `M ∈ C`,
`p : A ⊗ M → M` makes `M` a left `A`-module, `q : M ⊗ B → M` makes `M` a right `B`-module,
and the two actions commute. -/
abbrev Definition_2_9_24_Bimodule (A B : Mon C) := Bimod A B

variable {A : C} [MonObj A]

section FreeModule

variable {A : C} [MonObj A]

/-- Right `A`-module structure on `X ⊗ A` obtained by tensoring on the left by `X` with the
right regular `A`-module. -/
def freeRightModuleObj (X : C) : RightModObj A (X ⊗ A) :=
  RightMod_.tensorModObj X (RightMod_.regular A)

/-- The free right `A`-module on an object `X : C`, namely `X ⊗ A` with the action coming
from multiplication on the right factor. -/
def FreeRightModule (X : C) : RightMod_ (A := A) where
  X := X ⊗ A
  mod := freeRightModuleObj X

end FreeModule

section InternalEnd

open ModuleInternalHom

variable {C₀ : Type*} [Category C₀] [MonoidalCategory C₀]
    {M₀ : Type*} [Category M₀] [LeftModuleCategory C₀ M₀]
    [HasModuleInternalHom C₀ M₀]

/-- The identity morphism `𝟙_ C₀ → Hom̲(m, m)`, obtained from the left unitor `actℓ_ m`
via the defining adjunction of the internal Hom. -/
def moduleIHomId (m : M₀) : 𝟙_ C₀ ⟶ moduleIHom (C := C₀) m m :=
  moduleIHomEquiv (𝟙_ C₀) m m (actℓ_ m).hom


end InternalEnd

end CategoryTheory
