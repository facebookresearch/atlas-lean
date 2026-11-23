/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace ProjectionTheory

/-- **Definition (Hausdorff spacing).** A finite set `X` in a (pseudo)metric space has
*Hausdorff spacing* at scale `R` if there is a uniform constant `C > 0` such that for
every exponent `β ∈ [0, 1]` and every centre `c`, the number of points of `X` within
distance `R^β` of `c` satisfies $N_{R^\beta}(X) \le C\,|X|^\beta$. -/
def HasHausdorffSpacing {α : Type*} [PseudoMetricSpace α]
    (X : Finset α) (R : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    ∀ c : α, ((X.filter (fun x => dist x c < R ^ β)).card : ℝ) ≤ C * (X.card : ℝ) ^ β

end ProjectionTheory
