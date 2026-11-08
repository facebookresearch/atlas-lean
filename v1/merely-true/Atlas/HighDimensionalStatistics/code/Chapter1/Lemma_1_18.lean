/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Order.Zorn
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17

open MeasureTheory Metric Set Finset
open scoped ENNReal NNReal

noncomputable section

/-- An `ε`-separated subset `S` of a compact set `K` is necessarily finite.
Proof by covering `K` with finitely many balls of radius `ε/2` and noting each
ball contains at most one point of `S`. -/
lemma separated_finite_of_compact {X : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    {S : Set X} (hSK : S ⊆ K)
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) : S.Finite := by
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨t, _, htfin, htcov⟩ := hK.finite_cover_balls hε2
  have hcov_S : S ⊆ ⋃ c ∈ t, ball c (ε / 2) := fun s hs => htcov (hSK hs)
  suffices h : ∀ c ∈ t, (S ∩ ball c (ε / 2)).Subsingleton by
    apply (htfin.biUnion (fun c _ => (h c ‹_›).finite)).subset
    intro s hs
    have := hcov_S hs
    rw [mem_iUnion₂] at this
    obtain ⟨c, hc, hball⟩ := this
    exact mem_biUnion hc ⟨hs, hball⟩
  intro c _ x ⟨hxS, hxball⟩ y ⟨hyS, hyball⟩
  by_contra hne
  have hxy : dist x y < ε := by
    calc dist x y ≤ dist x c + dist c y := dist_triangle x c y
      _ < ε / 2 + ε / 2 :=
        add_lt_add (mem_ball.mp hxball) (by rw [dist_comm]; exact mem_ball.mp hyball)
      _ = ε := by ring
  exact absurd (hSep x hxS y hyS hne) (not_lt.mpr hxy.le)

/-- Zorn-based existence of a maximal `ε`-separated subset of `K`, which is
automatically an `ε`-net of `K`: every point of `K` lies within `ε` of some
element of the net. -/
lemma exists_maximal_separated_net {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, N ⊆ K ∧ (∀ x ∈ N, ∀ y ∈ N, x ≠ y → ε < dist x y) ∧
      ∀ z ∈ K, ∃ x ∈ N, dist x z ≤ ε := by
  have hchain : ∀ c : Set (Set X),
      c ⊆ {N | N ⊆ K ∧ ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ε < dist x y} →
      IsChain (· ⊆ ·) c →
      ∃ ub ∈ {N | N ⊆ K ∧ ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ε < dist x y}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_sUnion.mp hx
      exact (hc hs).1 hxs
    · intro x hx y hy hxy
      obtain ⟨sx, hsx, hxsx⟩ := mem_sUnion.mp hx
      obtain ⟨sy, hsy, hysy⟩ := mem_sUnion.mp hy
      rcases hchain.total hsx hsy with h | h
      · exact (hc hsy).2 x (h hxsx) y hysy hxy
      · exact (hc hsx).2 x hxsx y (h hysy) hxy
  obtain ⟨N, hN, hmax⟩ := zorn_subset _ hchain
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro z hz
  by_contra h
  push_neg at h

  have hNz : N ∪ {z} ⊆ K ∧
      ∀ x ∈ N ∪ {z}, ∀ y ∈ N ∪ {z}, x ≠ y → ε < dist x y := by
    refine ⟨Set.union_subset hN.1 (Set.singleton_subset_iff.mpr hz), ?_⟩
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hN.2 x hx y hy hxy
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact h x hx
    · rw [Set.mem_singleton_iff] at hx; subst hx; rw [dist_comm]; exact h y hy
    · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact absurd rfl hxy
  have hle : N ∪ {z} ⊆ N := hmax hNz Set.subset_union_left
  linarith [h z (hle (Set.mem_union_right N (Set.mem_singleton z))), dist_self z]

/-- Volume-packing argument: an `ε`-separated subset of the unit Euclidean
ball in `ℝ^d` has cardinality at most `(3/ε)^d`. -/
lemma packing_card_le_real {d : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hS_sub : ↑S ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) :
    (S.card : ℝ) ≤ (3 / ε) ^ d := by
  have hε2 : (0 : ℝ) < ε / 2 := by linarith

  have hdisj : (S : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint
      (fun x => closedBall x (ε / 2)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    rw [mem_closedBall] at hzx hzy
    have h2 : dist x z ≤ ε / 2 := by rw [dist_comm]; exact hzx
    have h4 : dist x y ≤ ε := by linarith [dist_triangle x z y]
    exact absurd (hS_sep x hx y hy hxy) (not_lt.mpr h4)

  have hcontain : ∀ x ∈ S, closedBall x (ε / 2) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 + ε / 2) := by
    intro x hx y hy
    rw [mem_closedBall] at *
    have hx0 : dist x 0 ≤ 1 := by
      have h := hS_sub hx; rw [mem_closedBall] at h; exact h
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
      _ ≤ ε / 2 + 1 := add_le_add hy hx0
      _ = 1 + ε / 2 := by ring

  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have hfin_dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin
  have hμ_pos : (0 : ℝ≥0∞) < μ (closedBall 0 1) := measure_closedBall_pos _ _ zero_lt_one
  have hμ_ne_top : μ (closedBall 0 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hμ_ne_zero : μ (closedBall 0 1) ≠ 0 := ne_of_gt hμ_pos
  have hle_meas : μ (⋃ x ∈ S, closedBall x (ε / 2)) ≤ μ (closedBall 0 (1 + ε / 2)) :=
    measure_mono (iUnion₂_subset hcontain)
  have hsum : μ (⋃ x ∈ S, closedBall x (ε / 2)) = ∑ x ∈ S, μ (closedBall x (ε / 2)) :=
    measure_biUnion_finset hdisj (fun _ _ => measurableSet_closedBall)
  have hvol_each : ∀ x ∈ S, μ (closedBall x (ε / 2)) =
      ENNReal.ofReal ((ε / 2) ^ d) * μ (closedBall 0 1) := by
    intro x _; rw [Measure.addHaar_closedBall' _ x hε2.le, hfin_dim]
  have hvol_sum : ∑ x ∈ S, μ (closedBall x (ε / 2)) =
      S.card • (ENNReal.ofReal ((ε / 2) ^ d) * μ (closedBall 0 1)) := by
    rw [Finset.sum_congr rfl hvol_each, Finset.sum_const]
  have hvol_big : μ (closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 + ε / 2)) =
      ENNReal.ofReal ((1 + ε / 2) ^ d) * μ (closedBall 0 1) := by
    rw [Measure.addHaar_closedBall' _ _ (by linarith : (0 : ℝ) ≤ 1 + ε / 2), hfin_dim]

  have hcombine : S.card • (ENNReal.ofReal ((ε / 2) ^ d) * μ (closedBall 0 1)) ≤
      ENNReal.ofReal ((1 + ε / 2) ^ d) * μ (closedBall 0 1) := by
    calc S.card • (ENNReal.ofReal ((ε / 2) ^ d) * μ (closedBall 0 1))
        = ∑ x ∈ S, μ (closedBall x (ε / 2)) := hvol_sum.symm
      _ = μ (⋃ x ∈ S, closedBall x (ε / 2)) := hsum.symm
      _ ≤ μ (closedBall 0 (1 + ε / 2)) := hle_meas
      _ = ENNReal.ofReal ((1 + ε / 2) ^ d) * μ (closedBall 0 1) := hvol_big
  rw [nsmul_eq_mul, ← mul_assoc] at hcombine
  have hcancel : (↑S.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d) ≤
      ENNReal.ofReal ((1 + ε / 2) ^ d) := by
    by_cases hS : S.card = 0
    · simp [hS]
    · exact (ENNReal.mul_le_mul_iff_left hμ_ne_zero hμ_ne_top).mp hcombine

  have hreal : (S.card : ℝ) * (ε / 2) ^ d ≤ (1 + ε / 2) ^ d := by
    have h1 : ENNReal.ofReal ((S.card : ℝ) * (ε / 2) ^ d) ≤
        ENNReal.ofReal ((1 + ε / 2) ^ d) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg S.card), ENNReal.ofReal_natCast]
      exact hcancel
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1

  have hεd_pos : (0 : ℝ) < (ε / 2) ^ d := pow_pos hε2 d
  have hcard_le : (S.card : ℝ) ≤ ((1 + ε / 2) / (ε / 2)) ^ d := by
    rw [div_pow]; rwa [le_div_iff₀ hεd_pos]
  have hbase_le : (1 + ε / 2) / (ε / 2) ≤ 3 / ε := by
    rw [div_le_div_iff₀ hε2 hε0]; nlinarith
  calc (S.card : ℝ) ≤ ((1 + ε / 2) / (ε / 2)) ^ d := hcard_le
    _ ≤ (3 / ε) ^ d := pow_le_pow_left₀ (div_nonneg (by linarith) hε2.le) hbase_le d

/-- **Lemma 1.18 (Covering number of the unit Euclidean ball).** For `0 < ε < 1`,
the closed unit ball `B₂` in `ℝ^d` admits an `ε`-net of cardinality
at most `⌈(3/ε)^d⌉`. -/
theorem lemma_1_18_covering_number_euclidean_ball
    {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ (N : Finset (EuclideanSpace ℝ (Fin d))),
      IsEpsilonNet (Metric.closedBall 0 1) (N : Set (EuclideanSpace ℝ (Fin d))) ε ∧
      N.card ≤ Nat.ceil ((3 / ε) ^ d) := by

  obtain ⟨N₀, hN₀_sub, hN₀_sep, hN₀_cov⟩ :=
    exists_maximal_separated_net (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ε hε_pos

  have hN₀_fin : N₀.Finite :=
    separated_finite_of_compact (isCompact_closedBall _ _) hε_pos hN₀_sub hN₀_sep

  refine ⟨hN₀_fin.toFinset, ⟨?_, ?_⟩, ?_⟩

  · intro x hx; exact hN₀_sub (hN₀_fin.mem_toFinset.mp hx)

  · intro z hz
    obtain ⟨x, hxN, hdist⟩ := hN₀_cov z hz
    exact ⟨x, hN₀_fin.mem_toFinset.mpr hxN, hdist⟩

  · have hcard_real : (hN₀_fin.toFinset.card : ℝ) ≤ (3 / ε) ^ d := by
      apply packing_card_le_real ε hε_pos hε_lt.le
      · intro x hx; exact hN₀_sub (hN₀_fin.mem_toFinset.mp hx)
      · intro x hx y hy hxy
        exact hN₀_sep x (hN₀_fin.mem_toFinset.mp hx) y (hN₀_fin.mem_toFinset.mp hy) hxy
    exact Nat.cast_le.mp (le_trans hcard_real (Nat.le_ceil _))
