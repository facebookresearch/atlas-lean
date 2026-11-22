/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

universe u

open CategoryTheory

instance corollary_23_61 {R : Type u} [Ring R] (A : ModuleCat.{u} R) :
    Functor.Additive (preadditiveYoneda.obj A) :=
  CategoryTheory.additive_yonedaObj' A
