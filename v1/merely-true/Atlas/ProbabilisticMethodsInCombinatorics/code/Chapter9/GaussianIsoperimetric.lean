/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussianIsoperimetric

/-- A set $H \subseteq E$ is a half-space if it has the form $\{x : \langle v, x \rangle \leq c\}$
for some nonzero $v$ and real $c$. -/
def IsHalfSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Set E) : Prop :=
  ∃ (v : E) (_ : v ≠ 0) (c : ℝ), H = {x | @inner ℝ _ _ v x ≤ c}





end GaussianIsoperimetric
