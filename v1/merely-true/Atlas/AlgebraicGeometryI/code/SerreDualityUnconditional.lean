/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.TateCechInfra

noncomputable section

namespace SerreDualityUnconditional

open TateCechInfra SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves

variable {k : Type*} [Field k]

/-- Numerical Serre duality, unconditional form: for any Čech sheaf data `D`,
`h¹(E) = h⁰(E∨ ⊗ K)`. -/
theorem serre_duality_numerical_unconditional (D : CechSheafData k) :
    D.h1_E = D.h0_EK :=
  (serre_duality_unconditional D).symm

/-- Arithmetic genus equals geometric genus from the unconditional Serre duality. -/
theorem genus_arithmetic_eq_geometric_unconditional (D : CechSheafData k)
    (ga gm : ℤ)
    (_hh0_O : D.h0_E = 1)
    (hga : ga = D.h1_E)
    (hgm : gm = D.h0_EK) :
    ga = gm := by
  rw [hga, hgm]
  exact (serre_duality_unconditional D).symm

/-- Unconditional Serre duality in both directions (here `h¹(E) = h⁰(E∨ ⊗ K)`). -/
theorem serre_duality_both_directions_unconditional (D : CechSheafData k) :
    D.h1_E = D.h0_EK :=
  (serre_duality_unconditional D).symm

end SerreDualityUnconditional

end
