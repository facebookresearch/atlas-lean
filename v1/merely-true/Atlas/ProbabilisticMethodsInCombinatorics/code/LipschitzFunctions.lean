/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open NNReal

namespace LipschitzFunctions

variable {X : Type*} {Y : Type*}

/-- Definition 9.4.7 (Lipschitz functions). A function $f : X \to Y$ is $C$-Lipschitz iff
$d(f(x), f(y)) \le C \cdot d(x, y)$ for all $x, y \in X$. -/
abbrev IsLipschitz [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (C : ℝ≥0) (f : X → Y) : Prop :=
  LipschitzWith C f

end LipschitzFunctions

open MeasureTheory Measure NNReal Set Metric ENNReal

namespace LipschitzFunctions

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Theorem 9.4.8 (concentration equivalence). For a probability measure on a metric space
and any $t \ge 0$, the set-expansion concentration statement
$\mu(A) \ge 1/2 \Rightarrow \mu(A_t) \ge 1 - \varepsilon$
is equivalent to the median concentration statement
$\mu(f \le m) \ge 1/2 \Rightarrow \mu(f > m + t) \le \varepsilon$
for all $1$-Lipschitz $f$, where $A_t$ is the closed $t$-thickening of $A$. -/
theorem concentration_equivalence {t : ℝ} (ht : 0 ≤ t) {ε : ℝ≥0∞} :
    (∀ (A : Set Ω), MeasurableSet A → μ A ≥ 1 / 2 →
      μ (Metric.cthickening t A) ≥ 1 - ε) ↔
    (∀ (f : Ω → ℝ) (m : ℝ), LipschitzWith 1 f → Measurable f →
      μ {x | f x ≤ m} ≥ 1 / 2 →
      μ {x | f x > m + t} ≤ ε) := by
  constructor
  ·


    intro ha f m hf hfm hm
    set A := {x : Ω | f x ≤ m}
    have hA_meas : MeasurableSet A := hfm measurableSet_Iic
    have h_sub : Metric.cthickening t A ⊆ {x | f x ≤ m + t} := by
      intro x hx
      simp only [mem_setOf_eq]
      rw [Metric.mem_cthickening_iff] at hx
      by_contra h_neg
      push Not at h_neg
      have hε_pos : (0 : ℝ) < (f x - m - t) / 2 := by linarith
      have h_lt : infEDist x A < ENNReal.ofReal (t + (f x - m - t) / 2) :=
        calc infEDist x A
            ≤ ENNReal.ofReal t := hx
          _ < ENNReal.ofReal (t + (f x - m - t) / 2) :=
              (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      obtain ⟨y, hy, hxy⟩ := infEDist_lt_iff.mp h_lt
      simp only [A, mem_setOf_eq] at hy
      have hdist : dist x y < t + (f x - m - t) / 2 := by
        rw [edist_dist] at hxy
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hxy
      have hfxy : f x - f y ≤ dist x y := by
        have h := hf.dist_le_mul x y
        simp only [NNReal.coe_one, one_mul] at h
        calc f x - f y ≤ |f x - f y| := le_abs_self _
          _ = dist (f x) (f y) := (Real.dist_eq _ _).symm
          _ ≤ dist x y := h
      linarith
    have h_sub2 : {x : Ω | f x > m + t} ⊆ (Metric.cthickening t A)ᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_setOf_eq] at hx ⊢
      exact fun hx' => not_le.mpr hx (h_sub hx')
    have h_meas_cthick : MeasurableSet (Metric.cthickening t A) :=
      Metric.isClosed_cthickening.measurableSet
    have h_expansion := ha A hA_meas hm
    calc μ {x | f x > m + t}
        ≤ μ (Metric.cthickening t A)ᶜ := measure_mono h_sub2
      _ = 1 - μ (Metric.cthickening t A) := prob_compl_eq_one_sub h_meas_cthick
      _ ≤ ε := by
          rw [tsub_le_iff_right]
          calc (1 : ℝ≥0∞) ≤ (1 - ε) + ε := le_tsub_add
            _ ≤ μ (Metric.cthickening t A) + ε := by gcongr
            _ = ε + μ (Metric.cthickening t A) := add_comm _ _
  ·


    intro hb A hA_meas hA_half
    set f := fun x => Metric.infDist x A
    have hf_lip : LipschitzWith 1 f := Metric.lipschitz_infDist_pt A
    have hf_meas : Measurable f := (continuous_infDist_pt A).measurable
    have h_sublevel : A ⊆ {x | f x ≤ 0} :=
      fun x hx => le_of_eq (Metric.infDist_zero_of_mem hx)
    have h_half : μ {x | f x ≤ 0} ≥ 1 / 2 :=
      le_trans hA_half (measure_mono h_sublevel)
    have h_conc := hb f 0 hf_lip hf_meas h_half
    simp only [zero_add] at h_conc
    have hA_ne : A.Nonempty := by
      by_contra h_empty
      rw [Set.not_nonempty_iff_eq_empty] at h_empty
      rw [h_empty] at hA_half
      simp at hA_half
    have h_compl_sub : (Metric.cthickening t A)ᶜ ⊆ {x | f x > t} := by
      intro x hx
      simp only [f, mem_compl_iff, mem_setOf_eq] at hx ⊢
      rw [Metric.mem_cthickening_iff] at hx
      push Not at hx
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht (infEDist_ne_top hA_ne)).mp hx
    have h_meas_cthick : MeasurableSet (Metric.cthickening t A) :=
      Metric.isClosed_cthickening.measurableSet
    have h_compl_le : μ (Metric.cthickening t A)ᶜ ≤ ε :=
      le_trans (measure_mono h_compl_sub) h_conc
    rw [prob_compl_eq_one_sub h_meas_cthick] at h_compl_le
    rw [tsub_le_iff_right] at h_compl_le
    rw [add_comm] at h_compl_le
    exact tsub_le_iff_right.mpr h_compl_le

end LipschitzFunctions
