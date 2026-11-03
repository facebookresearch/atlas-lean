/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace DimensionFormula

open Module LinearMap

theorem dimension_formula
    {F : Type*} [DivisionRing F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W]
    (T : V →ₗ[F] W) :
    finrank F (ker T) + finrank F (range T) = finrank F V := by
  have h := T.finrank_range_add_finrank_ker
  omega

end DimensionFormula
