/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

set_option maxHeartbeats 400000

open MeasureTheory Real BigOperators Finset ENNReal Set

namespace TSPConcentration

/-- A point in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The length $L_n$ of the optimal Travelling Salesman tour through the
$n$ points $\mathit{points}_0, \dots, \mathit{points}_{n-1}$: the infimum over
permutations $σ$ of the total cyclic distance
$\sum_i \mathrm{dist}(\mathit{points}_{σ(i)}, \mathit{points}_{σ(i+1 \bmod n)})$.
Returns $0$ when $n = 0$. -/
noncomputable def tspTourLength (n : ℕ) (points : Fin n → Point) : ℝ :=
  if h : n = 0 then 0
  else ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    dist (points (σ i)) (points (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩))

/-- The random variable $X$ is $K$-sub-Gaussian about its mean under $μ$:
for every $t \geq 0$,
$μ(\{ω : |X(ω) - \mathbb{E}_μ X| \geq t\}) \leq 2 e^{-t^2 / K^2}$. -/
def IsSubGaussianAboutMean {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (K : ℝ) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤
      ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2)))

/-- Harmonic-sum bound: $\sum_{i=0}^{n-1} \frac{1}{n - i} = H_n \leq 1 + \log n$. -/
lemma sum_inv_sub_le_log (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (↑(n - i) : ℝ) ≤ 1 + Real.log ↑n := by
  by_cases hn : n = 0
  · simp [hn]
  suffices h : ∑ i ∈ Finset.range n, (1 : ℝ) / (↑(n - i) : ℝ) = (harmonic n : ℝ) by
    rw [h]; exact_mod_cast harmonic_le_one_add_log n
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp_rw [one_div]
  apply Finset.sum_nbij' (fun i => n - 1 - i) (fun k => n - 1 - k)
  · intro i hi; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
  · intro k hk; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
  · intro i hi; have := Finset.mem_range.mp hi; omega
  · intro k hk; have := Finset.mem_range.mp hk; omega
  · intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    congr 1; exact_mod_cast show n - i = (n - 1 - i) + 1 from by omega

/-- The Azuma variance sum for the TSP martingale differences is bounded by
$C^2 (1 + \log n)$:
$\sum_{i=0}^{n-1} \bigl(C / \sqrt{n - i}\bigr)^2 \leq C^2 (1 + \log n)$. -/
lemma azuma_variance_bound (n : ℕ) (C : ℝ) :
    ∑ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2 ≤
      C ^ 2 * (1 + Real.log ↑n) := by
  by_cases hn : n = 0
  · simp [hn]; positivity
  have h_terms : ∀ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2 =
      C ^ 2 * (1 / (↑(n - i) : ℝ)) := by
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have h_pos : (0 : ℝ) < ↑(n - i) := by exact_mod_cast Nat.sub_pos_of_lt hi_lt
    rw [div_pow, sq_sqrt (le_of_lt h_pos)]; ring
  rw [Finset.sum_congr rfl h_terms, ← Finset.mul_sum]
  gcongr
  exact sum_inv_sub_le_log n

/-- Theorem 9.6.1 (Rhee–Talagrand 1987): given an Azuma-type bound on
the deviations of $L$ with martingale-difference variance summing to
$2 \sum_i (C / \sqrt{n-i})^2$, the TSP tour length $L$ is
$\sqrt{2 C^2 (1 + \log n)}$-sub-Gaussian about its mean, hence
$O(\sqrt{\log n})$-sub-Gaussian. -/
theorem rhee_talagrand_tsp_concentration
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 2 ≤ n)
    (L : Ω → ℝ)


    (C : ℝ) (hC : 0 < C)
    (hAzuma : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |L ω - ∫ ω', L ω' ∂μ|} ≤
        ENNReal.ofReal (2 * exp (-(t ^ 2 /
          (2 * (∑ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2)))))) :
    IsSubGaussianAboutMean L (Real.sqrt (2 * C ^ 2 * (1 + Real.log ↑n))) μ := by
  intro t ht
  have hlog_pos : (0 : ℝ) < Real.log (↑n : ℝ) :=
    Real.log_pos (by exact_mod_cast show (1 : ℕ) < n from by omega)
  have h_denom_pos : (0 : ℝ) < 2 * C ^ 2 * (1 + Real.log ↑n) := by positivity

  have hbd := hAzuma t ht

  have h_var := azuma_variance_bound n C


  calc μ {ω | t ≤ |L ω - ∫ ω', L ω' ∂μ|}
      ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 /
          (2 * (∑ i ∈ Finset.range n, (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2))))) := hbd
    _ ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 /
          (2 * C ^ 2 * (1 + Real.log ↑n))))) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        apply Real.exp_le_exp.mpr
        apply neg_le_neg
        apply div_le_div_of_nonneg_left (sq_nonneg t)
        · have h_sum_pos : (0 : ℝ) < ∑ i ∈ Finset.range n,
              (C / Real.sqrt (↑(n - i) : ℝ)) ^ 2 := by
            apply Finset.sum_pos
            · intro i hi
              have hi_lt : i < n := Finset.mem_range.mp hi
              have h_pos : (0 : ℝ) < ↑(n - i) := by exact_mod_cast Nat.sub_pos_of_lt hi_lt
              positivity
            · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
          positivity
        · linarith [h_var]
    _ = ENNReal.ofReal (2 * exp (-(t ^ 2 /
          (Real.sqrt (2 * C ^ 2 * (1 + Real.log ↑n))) ^ 2))) := by
        congr 1; congr 1; congr 1; congr 1
        rw [sq_sqrt (le_of_lt h_denom_pos)]

end TSPConcentration
