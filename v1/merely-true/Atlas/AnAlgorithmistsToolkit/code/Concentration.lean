/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Atlas.AnAlgorithmistsToolkit.code.HighDimensional

open MeasureTheory ProbabilityTheory Real InnerProductSpace

namespace Concentration



theorem inner_product_eq_dist_hyperplane {n : ℕ}
    (a x : EuclideanSpace ℝ (Fin n)) (ha : ‖a‖ = 1) :
    Metric.infDist x {y | @inner ℝ _ _ a y = (0 : ℝ)} = |@inner ℝ _ _ a x| := by
  set H := {y : EuclideanSpace ℝ (Fin n) | @inner ℝ _ _ a y = (0 : ℝ)}
  set c : ℝ := @inner ℝ _ _ a x
  set p := x - c • a
  have hp : p ∈ H := by
    simp only [H, Set.mem_setOf_eq, p, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, ha]
    simp [c]
  have hdist : dist x p = |c| := by
    simp only [p, dist_eq_norm, sub_sub_cancel]
    rw [norm_smul, ha, mul_one, Real.norm_eq_abs]
  have hne : H.Nonempty := ⟨p, hp⟩
  apply le_antisymm
  · rw [← hdist]
    exact Metric.infDist_le_dist_of_mem hp
  · rw [Metric.le_infDist hne]
    intro y hy
    rw [dist_eq_norm]
    have hinner : @inner ℝ _ _ a y = (0 : ℝ) := hy
    calc |c| = |@inner ℝ _ _ a (x - y)| := by
          simp only [c, inner_sub_right, hinner, sub_zero]
      _ ≤ ‖a‖ * ‖x - y‖ := abs_real_inner_le_norm a (x - y)
      _ = ‖x - y‖ := by rw [ha, one_mul]


end Concentration

namespace VolumeHardness

open MeasureTheory Real Set Finset BigOperators




end VolumeHardness
