/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

open CategoryTheory MonoidalCategory Limits

universe u

variable (R : Type u) [CommRing R]

noncomputable def lemma_23_78 (M A : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 0).obj M).obj A ≅ M ⊗ A :=
  (Functor.leftDerivedZeroIsoSelf ((tensoringLeft (ModuleCat.{u} R)).obj M)).app A
