/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open Filter Topology

namespace DifferentialOperators

variable {n : ℕ}

/-- A complex-valued function on Euclidean space is harmonic if it is smooth and its
Laplacian (sum of pure second partial derivatives along the standard basis directions)
vanishes everywhere. -/
def IsHarmonic (u : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u ∧
    ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ j : Fin n, (fderiv ℝ (fderiv ℝ u) x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 0

/-- Any smooth function that vanishes at infinity on Euclidean space is globally bounded:
combine continuity with the eventually-small tail to get a uniform bound. -/
theorem SmoothZeroAtInfty.exists_norm_le (u : SmoothZeroAtInfty n) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), ‖u x‖ ≤ C := by
  have hcont : Continuous u := u.smooth.continuous
  have htend : Tendsto (fun x => ‖u x‖) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
    have h0 := u.iteratedFDeriv_zero_at_infty 0
    simp only [norm_iteratedFDeriv_zero] at h0
    exact h0
  have hev : ∀ᶠ x in cocompact (EuclideanSpace ℝ (Fin n)), ‖u x‖ < 1 := by
    have := htend.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with x hx
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hx
  rw [Filter.hasBasis_cocompact.eventually_iff] at hev
  obtain ⟨K, hKc, hKp⟩ := hev
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max M 1, fun x => by
    by_cases hx : x ∈ K
    · exact le_trans (hM x hx) (le_max_left _ _)
    · exact le_trans (le_of_lt (hKp hx)) (le_max_right _ _)⟩



/-- A constant function on a noncompact Euclidean space that tends to zero at infinity
must be zero, since constants converge to themselves and limits are unique. -/
theorem eq_zero_of_const_tendsto_zero (hn : 0 < n) (c : ℂ)
    (h : Tendsto (fun _ : EuclideanSpace ℝ (Fin n) => c)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)) : c = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : NoncompactSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  exact tendsto_nhds_unique tendsto_const_nhds h

end DifferentialOperators

end
