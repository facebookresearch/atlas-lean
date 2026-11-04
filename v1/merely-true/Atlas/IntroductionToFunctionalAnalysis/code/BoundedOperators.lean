/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Operator.CompleteCodomain

namespace BoundedOperators

/-- If $V$ is a normed vector space over a nontrivially normed field $𝕜$ and $W$ is a Banach space
(a complete normed $𝕜$-vector space), then the space of bounded linear operators $\mathcal{B}(V, W)
= V \to_L[𝕜] W$ is itself a Banach space, i.e., it is complete with respect to the operator norm. -/
theorem bounded_operators_completeSpace (𝕜 : Type*) (V W : Type*)
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [CompleteSpace W] : CompleteSpace (V →L[𝕜] W) :=
  inferInstance

end BoundedOperators
