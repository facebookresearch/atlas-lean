/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral

set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal

noncomputable section

namespace StrongMarkovBMGoal98

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- Abbreviation for `d`-dimensional Euclidean space `ℝ^d`, represented as functions
`Fin d → ℝ`. -/
abbrev Rd (d : ℕ) := Fin d → ℝ

/-- Predicate bundling the defining properties of a `d`-dimensional Brownian motion
`B` with respect to a filtration `ℱ` and a family `P : Rd d → Measure Ω` of
starting-point laws. The fields encode: starting at `x` under `P x`, Gaussian
increments with the correct variance, independence of increments from the past,
adaptedness to `ℱ`, that each `P x` is a probability measure, measurability in
the starting point, and almost-sure continuity of sample paths. -/
structure IsBrownianMotion (B : ℝ≥0 → Ω → Rd d) (ℱ : Filtration ℝ≥0 m)
    (P : Rd d → Measure Ω) : Prop where
  start : ∀ x : Rd d, ∀ᵐ ω ∂(P x), B 0 ω = x
  increment_dist : ∀ (x : Rd d) (i : Fin d) (s t : ℝ≥0), s ≤ t →
    Measure.map (fun ω => B t ω i - B s ω i) (P x) = gaussianReal 0 (t - s)
  indep_increment : ∀ (x : Rd d) (i : Fin d) (s t : ℝ≥0), s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω i - B s ω i) inferInstance) (P x)
  adapted : ∀ (t : ℝ≥0), Measurable[ℱ t] (B t)
  isProbMeasure : ∀ x : Rd d, IsProbabilityMeasure (P x)
  measurable_P : Measurable P
  continuous_path : ∀ (x : Rd d), ∀ᵐ ω ∂(P x), ∀ i : Fin d,
    Continuous (fun t => B t ω i)

/-- The path of `B` shifted by the (possibly infinite) stopping time `S`: at sample `ω`
returns the path `t ↦ B (S ω + t) ω`. -/
def pathShiftAtStopping (B : ℝ≥0 → Ω → Rd d) (S : Ω → ℝ≥0∞) (ω : Ω) :
    ℝ≥0 → Rd d :=
  fun t => B ((S ω).toNNReal + t) ω

/-- The function `(t, x) ↦ E_x[Y t (B_·)]`: integrating the time-indexed path
functional `Y` against the Brownian motion law started from `x`. -/
def bmExpectation (B : ℝ≥0 → Ω → Rd d) (P : Rd d → Measure Ω)
    (Y : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ) (t : ℝ≥0) (x : Rd d) : ℝ :=
  ∫ ω, Y t (fun s => B s ω) ∂(P x)


/-- Helper measurability lemma: the map `(t, x) ↦ E_x[Y t (B_·)]` is jointly measurable
in time and starting point, given that `Y` is bounded measurable and `P` is measurable
in `x`. -/
theorem bmExpectation_measurable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {B : ℝ≥0 → Ω → Rd d} {ℱ : Filtration ℝ≥0 m} {P : Rd d → Measure Ω}
    (hBM : IsBrownianMotion B ℱ P)
    (Y : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ)
    (hY_meas : Measurable (fun p : ℝ≥0 × (ℝ≥0 → Rd d) => Y p.1 p.2))
    (_hY_bdd : ∃ C : ℝ, ∀ t f, |Y t f| ≤ C) :
    Measurable (fun p : ℝ≥0 × Rd d => bmExpectation B P Y p.1 p.2) := by


  let κ : ProbabilityTheory.Kernel (ℝ≥0 × Rd d) Ω :=
    ⟨fun p => P p.2, hBM.measurable_P.comp measurable_snd⟩

  haveI : ProbabilityTheory.IsMarkovKernel κ :=
    ⟨fun p => hBM.isProbMeasure p.2⟩


  have hf_meas : Measurable (fun p : (ℝ≥0 × Rd d) × Ω =>
      Y p.1.1 (fun s => B s p.2)) := by

    let g : (ℝ≥0 × Rd d) × Ω → ℝ≥0 × (ℝ≥0 → Rd d) :=
      fun p => (p.1.1, fun s => B s p.2)
    have hg : Measurable g :=
      Measurable.prodMk measurable_fst.fst
        (measurable_pi_lambda _ fun s =>
          ((hBM.adapted s).mono (ℱ.le s) le_rfl).comp measurable_snd)

    show Measurable ((fun q : ℝ≥0 × (ℝ≥0 → Rd d) => Y q.1 q.2) ∘ g)
    exact hY_meas.comp hg

  have h_sm : StronglyMeasurable (fun p : ℝ≥0 × Rd d =>
      ∫ ω, Y p.1 (fun s => B s ω) ∂κ p) :=
    hf_meas.stronglyMeasurable.integral_kernel_prod_right'

  suffices h_eq : (fun p : ℝ≥0 × Rd d => ∫ ω, Y p.1 (fun s => B s ω) ∂κ p) =
      (fun p : ℝ≥0 × Rd d => bmExpectation B P Y p.1 p.2) by
    rw [← h_eq]; exact h_sm.measurable
  ext p
  rfl



end StrongMarkovBMGoal98
