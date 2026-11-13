/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
import Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree

noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

/-- Convert a `CurveCovering` into the abstract `CurveMorphismData` used by the
Riemann–Hurwitz formula, by packaging degree, canonical degrees, and ramification. -/
def CurveCovering.toCurveMorphismData (C : CurveCovering) : CurveMorphismData where
  degree := C.n
  deg_KX := C.X.degK
  deg_KY := C.Y.degK
  deg_R := C.deg_R
  h_deg_R_nonneg := C.deg_R_nonneg
  h_deg_pos := C.h_n_pos

/-- The packaged `CurveMorphismData` of a `CurveCovering` satisfies the Riemann–Hurwitz identity
`deg K_X = n · deg K_Y + deg R`. -/
theorem CurveCovering.toCurveMorphismData_satisfies_RH (C : CurveCovering) :
    C.toCurveMorphismData.deg_KX =
      C.toCurveMorphismData.degree * C.toCurveMorphismData.deg_KY +
      C.toCurveMorphismData.deg_R := by
  show C.X.degK = C.n * C.Y.degK + C.deg_R
  exact C.degK_eq



/-- Package a `CurveCovering` as `CurveCoverData`, combining the morphism data with the
source and target curves. -/
def CurveCovering.toCurveCoverData (C : CurveCovering) : CurveCoverData where
  morphism := C.toCurveMorphismData
  source := C.X
  target := C.Y
  h_degK_X := rfl
  h_degK_Y := rfl

/-- The cover data of a `CurveCovering` satisfies the canonical-divisor decomposition
underlying the Riemann–Hurwitz formula. -/
theorem CurveCovering.toCurveCoverData_satisfies_decomp (C : CurveCovering) :
    C.toCurveCoverData.morphism.deg_KX =
      C.toCurveCoverData.morphism.degree * C.toCurveCoverData.morphism.deg_KY +
      C.toCurveCoverData.morphism.deg_R :=
  C.toCurveMorphismData_satisfies_RH




end
