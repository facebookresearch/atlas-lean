/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

open CategoryTheory

universe u

namespace AlgebraicGeometry

section General

universe v v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- An O_X-module (Definition 25, Lecture 10): a sheaf of modules over a sheaf of rings
R on a site, i.e. a sheafified version of a ring-action structure. -/
abbrev SheafOfOXModules := SheafOfModules.{v} R

end General

section Scheme

variable (X : Scheme.{u})

end Scheme

end AlgebraicGeometry
