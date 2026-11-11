/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SheafCohomology
import Mathlib.Analysis.Complex.Basic

namespace GAGA


/-- Algebraic side of GAGA for `P¹`: the Euler characteristic of `O(n)` is
`h⁰ − h¹ = n + 1`, matching its analytic counterpart. -/
theorem P1_gaga_algebraic_side (k : Type) [Field k] (n : ℤ) :
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
  SheafCohomology.euler_characteristic k n

end GAGA
