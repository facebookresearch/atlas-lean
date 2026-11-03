/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

open AlgebraicGeometry

universe u

/-- Definition 25 (Lec 10): a sheaf of `O_X`-modules on a scheme `X`; abbreviation for
the mathlib `Scheme.Modules`. -/
abbrev SheafOfOXModules (X : Scheme.{u}) := X.Modules

/-- Definitional unfolding: a sheaf of `O_X`-modules is a sheaf of modules over the
ring-valued structure sheaf `X.ringCatSheaf`. -/
theorem sheafOfOXModules_eq_sheafOfModules (X : Scheme.{u}) :
    SheafOfOXModules X = SheafOfModules.{u} X.ringCatSheaf := rfl
