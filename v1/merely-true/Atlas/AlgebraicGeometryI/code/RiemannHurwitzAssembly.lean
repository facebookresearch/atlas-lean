/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

noncomputable section

open CanonicalSheafCurves

namespace RiemannHurwitzAssembly

/-- A finite morphism of smooth complete curves: source `X`, target `Y`,
degree `n > 0`, and a ramification divisor of nonnegative degree `deg_R`,
together with the canonical-divisor identity `K_X = n · K_Y + R`. -/
structure CurveCovering where
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  hn : 0 < n
  deg_R : ℤ
  deg_R_nonneg : 0 ≤ deg_R
  degK_eq : X.degK = n * Y.degK + deg_R

namespace CurveCovering



/-- The defining canonical-divisor identity `K_X = n K_Y + R`, repackaged. -/
theorem degree_form (f : CurveCovering) :
    f.X.degK = f.n * f.Y.degK + f.deg_R :=
  f.degK_eq





end CurveCovering




end RiemannHurwitzAssembly

end
