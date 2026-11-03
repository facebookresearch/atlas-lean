/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian
set_option maxHeartbeats 800000

open MeasureTheory Real Set Metric

namespace Talagrand

variable {n : ℕ}

/-- The Boolean cube $\{0, 1\}^n$ embedded in $\mathbb{R}^n$. -/
def cube01 (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- The signed cube $\{-1, +1\}^n$ embedded in $\mathbb{R}^n$. -/
def cubePM (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = -1 ∨ x i = 1}

/-- The continuous cube $[0,1]^n$ in $\mathbb{R}^n$. -/
def continuousCube01 (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)




/-- $m$ is a median of $f$ under $\mu$ if both $\mu(\{f \leq m\}) \geq 1/2$
and $\mu(\{f \geq m\}) \geq 1/2$. -/
def IsMedian (μ : Measure (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (m : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ (μ {x | f x ≤ m}).toReal ∧ (1 : ℝ) / 2 ≤ (μ {x | m ≤ f x}).toReal








/-- Elementary inequality: $t^2/2 - K^2 \leq (t - K)^2$ for all real $t, K$. -/
lemma sq_sub_le_half_sq (t K : ℝ) : t ^ 2 / 2 - K ^ 2 ≤ (t - K) ^ 2 := by
  nlinarith [sq_nonneg (t - 2 * K)]

/-- Shifting the centering point of a sub-Gaussian tail bound: if $X$ concentrates
about $m$ with constants $(C_1, c_1)$ and $|m - a| \leq K$, then $X$ concentrates
about $a$ with adjusted constants, gaining a factor $e^{c_1 K^2}$. -/
lemma subgaussian_shift_center
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m a K : ℝ) (hK : |m - a| ≤ K)
    (C₁ c₁ : ℝ) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hbound : ∀ s : ℝ, 0 ≤ s →
      (μ {ω | s ≤ |X ω - m|}).toReal ≤ C₁ * Real.exp (-(c₁ * s ^ 2)))
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |X ω - a|}).toReal ≤
      C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) := by
  have hK_pos : 0 ≤ K := le_trans (abs_nonneg _) hK
  have hsub : {ω | t ≤ |X ω - a|} ⊆ {ω | t - K ≤ |X ω - m|} := by
    intro ω hω
    simp only [mem_setOf_eq] at *
    linarith [abs_sub_le (X ω) m a]
  by_cases htK : K ≤ t
  ·
    have hs : 0 ≤ t - K := by linarith
    have hb := hbound (t - K) hs
    have hmeas_mono : μ {ω | t ≤ |X ω - a|} ≤ μ {ω | t - K ≤ |X ω - m|} :=
      measure_mono hsub
    have h_tr : (μ {ω | t ≤ |X ω - a|}).toReal ≤ (μ {ω | t - K ≤ |X ω - m|}).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hmeas_mono
    calc (μ {ω | t ≤ |X ω - a|}).toReal
        ≤ C₁ * Real.exp (-(c₁ * (t - K) ^ 2)) := le_trans h_tr hb
      _ ≤ C₁ * Real.exp (-(c₁ * (t ^ 2 / 2 - K ^ 2))) := by
          gcongr; linarith [sq_sub_le_half_sq t K]
      _ = C₁ * Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) := by
          congr 1; ring_nf
      _ = C₁ * (Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2))) := by
          rw [Real.exp_add]
      _ = C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) := by ring
  ·
    simp only [not_le] at htK
    have hprob_le_one : (μ {ω | t ≤ |X ω - a|}).toReal ≤ 1 := by
      have hle : μ {ω | t ≤ |X ω - a|} ≤ 1 := by
        calc μ {ω | t ≤ |X ω - a|} ≤ μ Set.univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      exact ENNReal.toReal_le_of_le_ofReal one_pos.le (by rwa [ENNReal.ofReal_one])
    suffices h : (1 : ℝ) ≤ C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) from
      le_trans hprob_le_one h
    have htK2 : t ^ 2 < K ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2)) := by nlinarith
    have h4 : (1 : ℝ) ≤ Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) :=
      Real.one_le_exp h3
    have h5 : Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) =
        Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) :=
      Real.exp_add _ _
    nlinarith [Real.exp_pos (c₁ * K ^ 2), Real.exp_pos (-(c₁ / 2 * t ^ 2))]








end Talagrand
