/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Stieltjes

noncomputable section

open Set Filter MeasureTheory ENNReal Topology

open ENNReal (ofReal)

/--
Construction of measures on ℝ (Lecture 2, "How do we produce measures on R?"):
for every right-continuous, non-decreasing function `f : ℝ → ℝ` (encoded here
as a `StieltjesFunction`) tending to `0` at `-∞` and to `1` at `+∞`, there is
a unique Borel probability measure on ℝ assigning each half-open interval
`(a, b]` the mass `f b - f a`. This packages existence (a probability
measure), the interval-mass formula, and uniqueness as a single statement.
-/
theorem stieltjes_measure_construction (f : StieltjesFunction ℝ)
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure ∧
    (∀ a b : ℝ, a ≤ b → f.measure (Ioc a b) = ofReal (f b - f a)) ∧
    (∀ ν : Measure ℝ, [IsFiniteMeasure ν] →
      (∀ a b : ℝ, a ≤ b → ν (Ioc a b) = ofReal (f b - f a)) →
      ν = f.measure) := by
  refine ⟨f.isProbabilityMeasure hf_bot hf_top, fun a b _ => f.measure_Ioc a b, ?_⟩
  intro ν hν_inst hν
  haveI := hν_inst
  exact Measure.ext_of_Ioc ν f.measure (fun {a b} hab => by rw [hν a b hab.le, f.measure_Ioc])
