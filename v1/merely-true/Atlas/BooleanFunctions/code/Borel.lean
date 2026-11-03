/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Atlas.BooleanFunctions.code.GaussianStability
import Atlas.BooleanFunctions.code.Sheppard
import Atlas.BooleanFunctions.code.BorelCoordSymmetrization
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

variable {n : ℕ}


lemma integral_stdGaussian_comp_coord {n : ℕ} (i : Fin n) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    ∫ x : EuclideanSpace ℝ (Fin n), f (x i) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
    ∫ t, f t ∂(gaussianReal 0 1) := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← hmp.integral_comp hemb]
  show ∫ v : Fin n → ℝ, f (v i) ∂(Measure.pi (fun _ => gaussianReal 0 1)) = _
  exact integral_comp_eval hf



def iterateSymmetrize {n : ℕ} (hn : 0 < n) :
    ℕ → (EuclideanSpace ℝ (Fin n) → ℝ) → (EuclideanSpace ℝ (Fin n) → ℝ)
  | 0, f => f
  | k + 1, f => if h : k < n then
      symmetrize_coord ⟨k, h⟩ (iterateSymmetrize hn k f)
    else iterateSymmetrize hn k f

lemma symmetrize_coord_range {n : ℕ} (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    symmetrize_coord i f x ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold symmetrize_coord
  exact thresholdFn_range _ _

lemma iterateSymmetrize_range {n : ℕ} (hn : 0 < n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ x, iterateSymmetrize hn k f x ∈ Set.Icc (-1 : ℝ) 1 := by
  induction k with
  | zero => exact hf_range
  | succ k ih =>
    intro x
    simp only [iterateSymmetrize]
    split_ifs with h
    · exact symmetrize_coord_range _ _ _
    · exact ih x







end GaussianStability

end
