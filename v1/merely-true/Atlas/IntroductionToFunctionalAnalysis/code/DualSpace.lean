/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.Algebra.Module.LinearMap

namespace DualSpace

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The dual space `V' = 𝓑(V, 𝕜)` of a normed vector space `V` over a field `𝕜`,
defined as the space of bounded (continuous) linear functionals `V →L[𝕜] 𝕜`.
An element of `Dual 𝕜 V` is called a functional. When `𝕜 = ℝ` or `ℂ`, the
completeness of `𝕜` makes `Dual 𝕜 V` a Banach space. -/
abbrev Dual := V →L[𝕜] 𝕜

end DualSpace
