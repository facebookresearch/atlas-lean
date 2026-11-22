/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory


attribute [local instance] endofunctorMonoidalCategory

universe u v

namespace Prop164

/-- The full subcategory of right-exact endofunctors of `C` is monoidal: the identity
functor is right-exact, and a composition of right-exact functors is right-exact. -/
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

/-- The enveloping algebra `A ⊗_k Aᵒᵖ`, whose modules are precisely `A`-bimodules. -/
abbrev EnvelopingAlgebra (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] :=
  TensorProduct k A (MulOpposite A)



end Prop164

