/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochApplications

set_option maxHeartbeats 800000

open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm
open RiemannRochApplications SheafCohCurvesFiniteness

noncomputable section

namespace RRApplicationsAudit


/-- Audit: Riemann inequality `h^0(L) ≥ d + 1 − g` for line bundles. -/
theorem audit_riemann_inequality (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    SD.h0 ≥ d + 1 - C.g :=
  riemann_inequality_line_bundle C d SD


/-- Audit: vanishing of `h^1` makes Riemann–Roch exact. -/
theorem audit_high_degree_exact (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + 1 - C.g :=
  high_degree_exact_rr C d SD h1_zero

/-- Audit: degree-1 line bundles on `ℙ¹` have two global sections. -/
theorem audit_genus_zero_sections (C : SmoothCompleteCurve) (hg : C.g = 0)
    (SD : SerreDualityCurve C 1 1) (h1_zero : SD.h1 = 0) :
    SD.h0 = 2 :=
  genus_zero_point_sections C hg SD h1_zero








end RRApplicationsAudit

end
