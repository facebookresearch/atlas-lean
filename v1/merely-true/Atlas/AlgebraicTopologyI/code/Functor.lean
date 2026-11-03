/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Functor.Basic

namespace AlgebraicTopologyI

open CategoryTheory

/-- **Definition 3.4 (Functor).**  A functor `F : C ⥤ D` between two
categories, in the sense of Miller's *Lectures on Algebraic Topology I*.
This is a thin wrapper around Mathlib's `CategoryTheory.Functor`, repackaging
it under the `AlgebraicTopologyI` namespace so that downstream files in this
book can refer to it directly. -/
abbrev Functor := @CategoryTheory.Functor

end AlgebraicTopologyI
