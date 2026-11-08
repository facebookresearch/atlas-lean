/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.Basic
set_option maxHeartbeats 400000

open MeasureTheory Measure Filter Real Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace MaxDegreeNormalLabels

/-- Standard normal cumulative distribution function:
$\Phi(x) = \mathbb{P}(Z \leq x)$ for $Z \sim \mathcal{N}(0, 1)$. -/
noncomputable def std_normal_cdf (x : ℝ) : ℝ :=
  (gaussianReal 0 1 (Iic x)).toReal

/-- Auxiliary functional appearing in Proposition 7.2.6:
$g(y) = -y^2 / 2 + \log \Phi(y)$. -/
noncomputable def g (y : ℝ) : ℝ :=
  -y ^ 2 / 2 + Real.log (std_normal_cdf y)

/-- Probability (integral representation) that in a graph with i.i.d. normal edge
labels, the labelled-degree-sums at all $n$ vertices are simultaneously nonpositive. -/
noncomputable def prob_all_nonpos (n : ℕ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) *
    ∫ z : ℝ, Real.exp (-z ^ 2 / 2) * (std_normal_cdf (-z / Real.sqrt (↑n - 2))) ^ n


end MaxDegreeNormalLabels
