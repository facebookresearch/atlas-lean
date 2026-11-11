/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Metric Set Real Filter

namespace TSPHelper

/-- The unit square $[0,1]^2 \subseteq \mathbb{R}^2$ as a subset of Euclidean space. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  { p | ∀ i : Fin 2, 0 ≤ p i ∧ p i ≤ 1 }

/-- The uniform probability measure on the unit square, obtained by restricting
Lebesgue measure on $\mathbb{R}^2$ to $[0,1]^2$. -/
def uniformOnSquare : Measure (EuclideanSpace ℝ (Fin 2)) :=
  volume.restrict unitSquare

/-- The product measure on $(\mathbb{R}^2)^k$ corresponding to $k$ i.i.d.\ uniform
points in the unit square. -/
def iidUniformOnSquare (k : ℕ) : Measure (Fin k → EuclideanSpace ℝ (Fin 2)) :=
  Measure.pi (fun _ => uniformOnSquare)

/-- The Lebesgue volume of the unit square $[0,1]^2$ is $1$. -/
lemma volume_unitSquare : (volume : Measure (EuclideanSpace ℝ (Fin 2))) unitSquare = 1 := by
  have heq : unitSquare = WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun _ : Fin 2 => Icc (0:ℝ) 1)) := by
    ext p; simp only [unitSquare, mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet),
    volume_pi_pi]
  simp [Real.volume_Icc]

/-- The uniform measure on the unit square is a probability measure. -/
instance uniformOnSquare_isProbabilityMeasure : IsProbabilityMeasure uniformOnSquare :=
  ⟨by rw [show uniformOnSquare = volume.restrict unitSquare from rfl,
          Measure.restrict_apply_univ]; exact volume_unitSquare⟩

/-- The product measure of $k$ i.i.d.\ uniform points in the unit square is a
probability measure. -/
instance iidUniformOnSquare_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (iidUniformOnSquare k) :=
  Measure.pi.instIsProbabilityMeasure (μ := fun _ => uniformOnSquare)





end TSPHelper
