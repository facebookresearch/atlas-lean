/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- A family of probability measures `μ : ι → Measure α` is **tight** if for every `ε > 0` there
exists a compact set `K` such that `μ i K ≥ 1 - ε` for every index `i`. -/
def IsTightFamily {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {ι : Type*} (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ K : Set α, IsCompact K ∧ ∀ i, μ i K ≥ 1 - ε

/-- A family of probability measures on `ℝ` is **tight** if for every `ε > 0` there exists `M > 0`
such that `μ i [-M, M] ≥ 1 - ε` for every index `i`. This is the textbook definition specialised
to the real line. -/
def IsTightFamilyReal {ι : Type*} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ M : ℝ, ∀ i, μ i (Set.Icc (-M) M) ≥ 1 - ε

/-- Tightness in the real-line sense (`[-M, M]` exhausts mass uniformly) implies tightness in the
general topological sense (a compact set exhausts mass uniformly), since `[-M, M]` is compact. -/
theorem IsTightFamilyReal.isTightFamily {ι : Type*} {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)]
    (h : IsTightFamilyReal μ) : IsTightFamily μ := by
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨Set.Icc (-M) M, isCompact_Icc, hM⟩

/-- Converse direction: tightness in the general topological sense for measures on `ℝ` implies
the real-line `[-M, M]` formulation, by enclosing the compact set in a closed ball. -/
theorem IsTightFamily.isTightFamilyReal {ι : Type*} {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)]
    (h : IsTightFamily μ) : IsTightFamilyReal μ := by
  intro ε hε
  obtain ⟨K, hK_compact, hK_meas⟩ := h ε hε
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK_compact.isBounded
  refine ⟨r, fun i => ?_⟩
  calc (1 : ENNReal) - ε ≤ μ i K := hK_meas i
    _ ≤ μ i (Set.Icc (-r) r) := by
        rw [← Real.closedBall_zero_eq_Icc]
        exact measure_mono hr

end MeasureTheory.Measure
