/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AnAlgorithmistsToolkit.code.BrunnMinkowskiInequality

open Pointwise MeasureTheory Set Filter

namespace SurfaceArea

variable {n : ℕ}

def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

def minkowskiThickening (K : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  K + ε • unitBall n

noncomputable def surfaceArea (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
    (fun ε => ((volume (minkowskiThickening K ε)).toReal - (volume K).toReal) / ε)

lemma minkowskiThickening_unitBall_eq {n : ℕ} (hε : 0 ≤ ε) :
    minkowskiThickening (unitBall n) ε = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 + ε) := by
  unfold minkowskiThickening unitBall
  rw [smul_unitClosedBall_of_nonneg hε]
  rw [closedBall_add_closedBall (by norm_num : (0 : ℝ) ≤ 1) hε 0 0]
  simp

lemma minkowskiThickening_unitBall_eq_smul {n : ℕ} (hε : 0 ≤ ε) :
    minkowskiThickening (unitBall n) ε = (1 + ε) • unitBall n := by
  rw [minkowskiThickening_unitBall_eq hε]
  unfold unitBall
  rw [← smul_unitClosedBall_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε)]

lemma volume_minkowskiThickening_unitBall {n : ℕ} (hε : 0 ≤ ε) :
    (volume (minkowskiThickening (unitBall n) ε)).toReal =
    (1 + ε) ^ n * (volume (unitBall n)).toReal := by
  rw [minkowskiThickening_unitBall_eq_smul hε]
  unfold unitBall
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume (by linarith : (0 : ℝ) ≤ 1 + ε)]
  rw [finrank_euclideanSpace_fin (𝕜 := ℝ)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) n)]

lemma surfaceArea_unitBall_eq {n : ℕ} (_hn : 2 ≤ n)
    (_hVB_pos : 0 < (volume (unitBall n)).toReal) :
    surfaceArea (unitBall n) = ↑n * (volume (unitBall n)).toReal := by
  unfold surfaceArea
  have htendsto : Filter.Tendsto
      (fun ε => ((volume (minkowskiThickening (unitBall n) ε)).toReal -
        (volume (unitBall n)).toReal) / ε)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (↑n * (volume (unitBall n)).toReal)) := by
    have heq : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
        ((volume (minkowskiThickening (unitBall n) ε)).toReal -
          (volume (unitBall n)).toReal) / ε =
        ((1 + ε) ^ n - 1) / ε * (volume (unitBall n)).toReal := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nn : (0 : ℝ) ≤ ε := le_of_lt hε
      rw [volume_minkowskiThickening_unitBall hε_nn]
      ring
    have hder : HasDerivAt (fun ε : ℝ => (1 + ε) ^ n) (↑n : ℝ) 0 := by
      have h1 : HasDerivAt (fun ε : ℝ => 1 + ε) 1 0 :=
        (hasDerivAt_id 0).const_add 1
      have h2 := h1.pow n
      have h3 : (↑n : ℝ) * (1 + (0 : ℝ)) ^ (n - 1) * 1 = (↑n : ℝ) := by
        simp [one_pow]
      rw [h3] at h2
      exact h2
    have hslope' := hder.tendsto_slope_zero_right
    have hslope : Filter.Tendsto (fun ε : ℝ => ((1 + ε) ^ n - 1) / ε)
        (nhdsWithin 0 (Ioi 0)) (nhds (↑n : ℝ)) := by
      refine Filter.Tendsto.congr ?_ hslope'
      intro t
      simp [div_eq_inv_mul, smul_eq_mul, zero_add]
    have hmul : Filter.Tendsto (fun ε : ℝ => ((1 + ε) ^ n - 1) / ε * (volume (unitBall n)).toReal)
        (nhdsWithin 0 (Ioi 0)) (nhds (↑n * (volume (unitBall n)).toReal)) :=
      hslope.mul tendsto_const_nhds
    have heq_symm : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
        ((1 + ε) ^ n - 1) / ε * (volume (unitBall n)).toReal =
        ((volume (minkowskiThickening (unitBall n) ε)).toReal -
          (volume (unitBall n)).toReal) / ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nn : (0 : ℝ) ≤ ε := le_of_lt hε
      rw [volume_minkowskiThickening_unitBall hε_nn]
      ring
    exact Filter.Tendsto.congr' heq_symm hmul
  exact htendsto.limUnder_eq




end SurfaceArea
