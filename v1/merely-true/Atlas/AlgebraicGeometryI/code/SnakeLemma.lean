/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.RightDerived

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace SnakeLemma


section AbelianCategory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Snake lemma: a snake input in an abelian category yields an exact sequence
through the connecting homomorphism (Prop 42, Lec 23). -/
theorem snake_lemma_exact (S : ShortComplex.SnakeInput C) :
    S.composableArrows.Exact :=
  S.snake_lemma

/-- The connecting homomorphism produced by the snake lemma, mapping the third
object of the top row to the first object of the bottom row. -/
def connectingHomomorphism (S : ShortComplex.SnakeInput C) :
    S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.δ

end AbelianCategory


section ModuleCat

variable {R : Type u} [CommRing R]

end ModuleCat


section CohomologyConnection

variable {C : Type u} [Category.{v} C] [Abelian C]

end CohomologyConnection

end SnakeLemma
