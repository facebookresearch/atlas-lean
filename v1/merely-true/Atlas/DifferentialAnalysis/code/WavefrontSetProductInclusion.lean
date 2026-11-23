/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontProducts
import Atlas.DifferentialAnalysis.code.WavefrontSetCorollaries

noncomputable section

open scoped SchwartzMap FourierTransform Pointwise
open MeasureTheory Set WavefrontSet

namespace WavefrontSet

/-- Minkowski-style upper bound for the scattering wavefront set of a product/sum of
distributions: a pair `(p, q)` lies in this set if `(p, q) ∈ WFsc u`, or
`(p, q) ∈ WFsc v`, or there exist boundary points `p₁, p₂` with `(p₁, pq.2) ∈ WFsc u`
and `(p₂, pq.2) ∈ WFsc v` while `(p, q)` lies on the boundary product. -/
def WFscMinkowskiSum {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    Set (ClosedBall n × ClosedBall n) :=
  WFsc u ∪ WFsc v ∪
  { pq | ∃ (p₁ p₂ : ClosedBall n),
    (p₁, pq.2) ∈ WFsc u ∧ (p₂, pq.2) ∈ WFsc v ∧
    pq ∈ BoundaryProd n }


end WavefrontSet

end
