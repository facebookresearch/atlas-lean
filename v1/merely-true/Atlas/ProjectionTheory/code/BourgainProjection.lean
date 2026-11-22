/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.DeltaRegular

open scoped ENNReal NNReal
open Metric Set Finset Classical

namespace BourgainProjection

/-- Projection of $v \in \mathbb{R}^2$ onto the line with affine parameter $\theta$:
$\pi_\theta(v) = v_0 + \theta v_1$. -/
noncomputable def projLine (θ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  v 0 + θ * v 1

/-- The $1$-scale covering number of a subset $S \subseteq \mathbb{R}$. -/
noncomputable def coveringNumber1 (S : Set ℝ) : ℕ∞ :=
  Metric.externalCoveringNumber 1 S



end BourgainProjection
