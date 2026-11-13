/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory Real Set Finset

namespace Talagrand

/-- The **discrete hypercube** $\{0, 1\}^n$, viewed as a subset of
$\mathbb{R}^n$: vectors whose every coordinate is $0$ or $1$. -/
def hypercube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- The standard Euclidean distance $\|x - y\|_2 = \sqrt{\sum_i (x_i - y_i)^{2}}$ on
$\mathbb{R}^n$. -/
noncomputable def euclideanDist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i - y i) ^ 2)

/-- The Euclidean distance from a point $x \in \mathbb{R}^n$ to a set $A$: the infimum of
$\|x - a\|_2$ over $a \in A$. -/
noncomputable def euclideanInfDist {n : ℕ} (x : Fin n → ℝ) (A : Set (Fin n → ℝ)) : ℝ :=
  ⨅ a ∈ A, euclideanDist x a


end Talagrand
