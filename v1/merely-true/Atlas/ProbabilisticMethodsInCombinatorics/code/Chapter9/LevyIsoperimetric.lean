/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open MeasureTheory Metric Set

namespace LevyIsoperimetric

/-- The unit sphere $S^{n-1} \subseteq \mathbb{R}^n$, viewed as a subtype of
$\mathbb{R}^n$ consisting of vectors of norm $1$. -/
abbrev UnitSphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- A subset $B \subseteq S^{n-1}$ is a **spherical cap** if it has the form
$\{x \in S^{n-1} \mid \langle x, v \rangle \ge c\}$ for some unit vector $v$ and some
threshold $c \in \mathbb{R}$. -/
def IsSphericalCap {n : ℕ} (B : Set (UnitSphere n)) : Prop :=
  ∃ (v : EuclideanSpace ℝ (Fin n)) (_ : ‖v‖ = 1) (c : ℝ),
    B = {x : UnitSphere n | @inner ℝ _ _ (x : EuclideanSpace ℝ (Fin n)) v ≥ c}

/-- The $(n-1)$-dimensional Hausdorff measure on the unit sphere $S^{n-1}$, used as the natural
surface-area measure on the sphere. -/
def sphereHausdorffMeasure (n : ℕ) : Measure (UnitSphere n) :=
  Measure.hausdorffMeasure (↑(n - 1) : ℝ)

end LevyIsoperimetric

open LevyIsoperimetric

