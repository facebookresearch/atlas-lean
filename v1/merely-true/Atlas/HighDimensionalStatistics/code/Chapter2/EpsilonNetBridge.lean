/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Mul
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17

open scoped Matrix
open Metric Finset

noncomputable section

/-- Bridge identity: `⟨v, v⟩ = ‖v‖²` under the Euclidean identification of `Fin d → ℝ`. -/
lemma dotProduct_eq_euclideanNorm_sq {d : ℕ} (v : Fin d → ℝ) :
    dotProduct v v = ‖(WithLp.equiv 2 (Fin d → ℝ)).symm v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [dotProduct, WithLp.equiv_symm_apply]
  congr 1
  ext i
  simp [sq_abs]
  ring

/-- `1/2`-net for the Euclidean unit ball expressed in terms of `dotProduct`: there
exists a set `N` of cardinality at most `6^d` such that every unit vector is within
`1/2` (in squared norm: `1/4`) of some point in `N`. -/
lemma epsilon_net_dotProduct_of_euclidean {d : ℕ} (hd : 0 < d) :
    ∃ (N : Finset (Fin d → ℝ)),
      N.card ≤ 6 ^ d ∧
      (∀ z ∈ N, dotProduct z z ≤ 1) ∧
      (∀ v, dotProduct v v ≤ 1 →
        ∃ z ∈ N, dotProduct (v - z) (v - z) ≤ 1/4) := by

  obtain ⟨N₀, ⟨hN₀_sub, hN₀_cov⟩, hN₀_card⟩ :=
    lemma_1_18_covering_number_euclidean_ball hd (1/2) (by norm_num) (by norm_num)

  let e := WithLp.equiv 2 (Fin d → ℝ)
  let N : Finset (Fin d → ℝ) := N₀.image e
  refine ⟨N, ?_, ?_, ?_⟩

  · have hcard_eq : N.card = N₀.card := by
      exact Finset.card_image_of_injective N₀ e.injective
    rw [hcard_eq]
    calc N₀.card ≤ Nat.ceil ((3 / (1/2 : ℝ)) ^ d) := hN₀_card
      _ = Nat.ceil ((6 : ℝ) ^ d) := by norm_num
      _ = 6 ^ d := by
          rw [show (6 : ℝ) = ↑(6 : ℕ) from by norm_num, ← Nat.cast_pow]
          exact Nat.ceil_natCast (6 ^ d)

  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz

    have hx_ball := hN₀_sub hx
    rw [mem_closedBall, dist_zero_right] at hx_ball

    rw [dotProduct_eq_euclideanNorm_sq]
    have : (WithLp.equiv 2 (Fin d → ℝ)).symm (e x) = x := e.symm_apply_apply x
    rw [this]
    nlinarith [norm_nonneg x]

  · intro v hv

    rw [dotProduct_eq_euclideanNorm_sq] at hv
    have hv_norm : ‖e.symm v‖ ≤ 1 := by
      nlinarith [norm_nonneg (e.symm v)]

    have hv_ball : e.symm v ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_closedBall, dist_zero_right]; exact hv_norm

    obtain ⟨x, hxN, hdist⟩ := hN₀_cov (e.symm v) hv_ball

    refine ⟨e x, Finset.mem_image_of_mem e hxN, ?_⟩

    rw [dotProduct_eq_euclideanNorm_sq]

    have hsub : (WithLp.equiv 2 (Fin d → ℝ)).symm (v - e x) = e.symm v - x := by
      ext i; rfl
    rw [hsub]

    rw [dist_comm] at hdist
    rw [dist_eq_norm] at hdist
    nlinarith [norm_nonneg (e.symm v - x)]
