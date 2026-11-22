/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory Set

namespace WavefrontSet

variable {n : ℕ}

/-- A point `p` of the closed unit ball is "on the sphere" if its underlying
norm equals `1`. -/
def IsOnSphere (p : ClosedBall n) : Prop := ‖p.val‖ = 1

/-- The disjoint scattering wavefront set condition that ensures the product
`u · v` of two tempered distributions is well-defined: for every point `p` of
the closed unit ball and every direction `ω` on the sphere, if `(p, ω)` lies
in the scattering wavefront set of `u`, then the antipodal direction
`(p, -ω)` must not lie in the scattering wavefront set of `v`. -/
def DisjointWFscProductCondition
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (p ω : ClosedBall n),
    IsOnSphere ω →
    (p, ω) ∈ WFsc u →
    (p, -ω) ∉ WFsc v

/-- The disjoint scattering wavefront set condition that ensures the
convolution `u ∗ v` of two tempered distributions is well-defined: for every
direction `θ` on the sphere and every point `q` of the closed unit ball, if
`(θ, q)` lies in the scattering wavefront set of `u`, then `(-θ, q)` must not
lie in the scattering wavefront set of `v`. This is the Fourier-dual of
`DisjointWFscProductCondition`. -/
def DisjointWFscConvolutionCondition
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (θ q : ClosedBall n),
    IsOnSphere θ →
    (θ, q) ∈ WFsc u →
    (-θ, q) ∉ WFsc v









end WavefrontSet

end
