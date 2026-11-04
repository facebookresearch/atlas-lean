/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory Real ENNReal MeasureTheory.Measure Set

namespace SubGaussian

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Definition 9.4.17 ($K$-sub-Gaussian random variable). A real-valued random variable
$X$ is $K$-sub-Gaussian if for every $t \ge 0$,
$\mathbb{P}(|X - \mathbb{E} X| \ge t) \le 2 \exp(-t^2 / K^2)$. -/
def IsSubGaussian (X : Ω → ℝ) (K : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤
      ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2)))

/-- Sub-Gaussian tail bound around an arbitrary center $m$: for every $t \ge 0$,
$\mathbb{P}(|X - m| \ge t) \le 2 \exp(-t^2 / K^2)$. -/
def HasSubGaussianTail (X : Ω → ℝ) (m K : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω - m|} ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2)))

/-- $\mathrm{med}$ is a median of $X$ if $\mathbb{P}(X \ge \mathrm{med}) \ge 1/2$ and
$\mathbb{P}(X \le \mathrm{med}) \ge 1/2$. -/
def IsMedian (X : Ω → ℝ) (med : ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  μ {ω | med ≤ X ω} ≥ ENNReal.ofReal (1/2) ∧
  μ {ω | X ω ≤ med} ≥ ENNReal.ofReal (1/2)

/-- Numerical fact $\log 2 < 1$. -/
lemma log2_lt_one : Real.log 2 < 1 := by
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (by norm_num) (by linarith [exp_one_gt_d9])

/-- For $r > 2 \log 2$, we have $2 \exp(-r) < 1/2$. -/
lemma two_mul_exp_neg_lt_half {r : ℝ} (hr : 2 * Real.log 2 < r) :
    2 * Real.exp (-r) < 1/2 := by
  rw [show (1:ℝ)/2 = 2 * (1/4) from by ring]
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 2)
  rw [show (1:ℝ)/4 = Real.exp (-(2 * Real.log 2)) from by
    rw [show (2:ℝ) * Real.log 2 = Real.log (2^2) from by rw [Real.log_pow]; ring]
    rw [Real.exp_neg, Real.exp_log (by positivity : (2:ℝ)^2 > 0)]
    norm_num]
  exact Real.exp_strictMono (by linarith)

/-- For $r \le \log 2$, we have $1 \le 2 \exp(-r)$. -/
lemma one_le_two_mul_exp_neg {r : ℝ} (hr : r ≤ Real.log 2) :
    1 ≤ 2 * Real.exp (-r) := by
  have h1 : Real.exp (-r) ≥ Real.exp (-(Real.log 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(Real.log 2)) = 1/2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (2:ℝ) > 0)]; norm_num
  linarith

/-- Lemma 9.4.20 (first part). For a $K$-sub-Gaussian tail bound about a point $m$, any
median $\mathrm{med}$ of $X$ satisfies $|\mathrm{med} - m| \le \sqrt{2 \log 2} \cdot K$. -/
theorem median_close_to_center
    {X : Ω → ℝ} {m K : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hK : 0 < K) (htail : HasSubGaussianTail X m K μ) {med : ℝ}
    (hmed : IsMedian X med μ) :
    |med - m| ≤ Real.sqrt (2 * Real.log 2) * K := by
  by_contra h
  push_neg at h
  have hlog2_pos : (0:ℝ) < 2 * Real.log 2 :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hCK_pos : (0:ℝ) < Real.sqrt (2 * Real.log 2) * K :=
    mul_pos (Real.sqrt_pos.mpr hlog2_pos) hK
  have hmedm_pos : 0 < |med - m| := lt_trans hCK_pos h
  have htail_at := htail (|med - m|) (le_of_lt hmedm_pos)
  have hK2_pos : (0:ℝ) < K ^ 2 := by positivity
  have hsq_ineq : 2 * Real.log 2 < |med - m| ^ 2 / K ^ 2 := by
    rw [lt_div_iff₀ hK2_pos]
    calc 2 * Real.log 2 * K ^ 2
        = (Real.sqrt (2 * Real.log 2) * K) ^ 2 := by
          rw [mul_pow, sq_sqrt (le_of_lt hlog2_pos)]
      _ < |med - m| ^ 2 := sq_lt_sq' (by linarith) h
  have hexp_lt : 2 * Real.exp (-(|med - m| ^ 2 / K ^ 2)) < 1/2 :=
    two_mul_exp_neg_lt_half hsq_ineq
  rcases le_or_gt m med with hcase | hcase
  · have hsub : {ω : Ω | med ≤ X ω} ⊆ {ω : Ω | |med - m| ≤ |X ω - m|} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      calc |med - m| = med - m := abs_of_nonneg (by linarith)
        _ ≤ X ω - m := by linarith
        _ ≤ |X ω - m| := le_abs_self _
    have h_half_le : ENNReal.ofReal (1/2) ≤ μ {ω | |med - m| ≤ |X ω - m|} :=
      le_trans hmed.1 (measure_mono hsub)
    have h_lt : ENNReal.ofReal (2 * Real.exp (-(|med - m| ^ 2 / K ^ 2))) <
        ENNReal.ofReal (1/2) := by
      rwa [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1/2)]
    exact not_lt.mpr (le_trans h_half_le htail_at) h_lt
  · have hsub : {ω : Ω | X ω ≤ med} ⊆ {ω : Ω | |med - m| ≤ |X ω - m|} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      calc |med - m| = -(med - m) := by rw [abs_of_neg (by linarith)]
        _ = m - med := by ring
        _ ≤ m - X ω := by linarith
        _ = -(X ω - m) := by ring
        _ ≤ |X ω - m| := neg_le_abs _
    have h_half_le : ENNReal.ofReal (1/2) ≤ μ {ω | |med - m| ≤ |X ω - m|} :=
      le_trans hmed.2 (measure_mono hsub)
    have h_lt : ENNReal.ofReal (2 * Real.exp (-(|med - m| ^ 2 / K ^ 2))) <
        ENNReal.ofReal (1/2) := by
      rwa [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1/2)]
    exact not_lt.mpr (le_trans h_half_le htail_at) h_lt

/-- Lemma 9.4.20 (second part). For a $K$-sub-Gaussian tail bound about $m$,
$|\mathbb{E}[X] - m| \le \sqrt{\pi} \cdot K$. The proof integrates the Gaussian tail bound. -/
theorem mean_close_to_center
    {X : Ω → ℝ} {m K : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hK : 0 < K) (htail : HasSubGaussianTail X m K μ)
    (hX_int : Integrable X μ)
    (hX_mble : AEMeasurable (fun ω => |X ω - m|) μ) :
    |∫ ω, X ω ∂μ - m| ≤ Real.sqrt Real.pi * K := by

  have h1 : |∫ ω, X ω ∂μ - m| = |∫ ω, (X ω - m) ∂μ| := by
    congr 1; rw [integral_sub hX_int (integrable_const m)]; simp
  rw [h1]
  have h2 : |∫ ω, (X ω - m) ∂μ| ≤ ∫ ω, |X ω - m| ∂μ := by
    calc |∫ ω, (X ω - m) ∂μ|
        = ‖∫ ω, (X ω - m) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖X ω - m‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω, |X ω - m| ∂μ := by simp_rw [Real.norm_eq_abs]

  suffices h3 : ∫ ω, |X ω - m| ∂μ ≤ Real.sqrt Real.pi * K from le_trans h2 h3
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => abs_nonneg (X ω - m)))
    (hX_mble.aestronglyMeasurable)]
  rw [lintegral_eq_lintegral_meas_le μ
    (Filter.Eventually.of_forall (fun ω => abs_nonneg (X ω - m)))
    hX_mble]

  have h_bound : ∫⁻ (t : ℝ) in Ioi 0, μ {a | t ≤ |X a - m|} ≤
      ∫⁻ (t : ℝ) in Ioi 0, ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2))) := by
    apply setLIntegral_mono_ae' measurableSet_Ioi
    exact Filter.Eventually.of_forall (fun t ht => by
      simp only [mem_Ioi] at ht; exact htail t (le_of_lt ht))

  have h_gauss : ∫⁻ (t : ℝ) in Ioi (0:ℝ), ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2))) =
      ENNReal.ofReal (Real.sqrt Real.pi * K) := by
    have hb : (0:ℝ) < 1 / K ^ 2 := by positivity
    have hf_nn : ∀ t : ℝ, 0 ≤ 2 * exp (-(t ^ 2 / K ^ 2)) := by
      intro t; exact mul_nonneg (by norm_num) (le_of_lt (exp_pos _))
    have hf_int : IntegrableOn (fun t => 2 * exp (-(t ^ 2 / K ^ 2))) (Ioi 0) := by
      simp_rw [show ∀ t : ℝ, 2 * exp (-(t ^ 2 / K ^ 2)) =
        2 * exp (-(1 / K ^ 2) * t ^ 2) from fun t => by congr 1; ring]
      exact (integrable_exp_neg_mul_sq hb).integrableOn.const_mul 2
    rw [← ofReal_integral_eq_lintegral_ofReal hf_int
      (Filter.Eventually.of_forall (fun t => hf_nn t))]
    congr 1
    simp_rw [show ∀ t : ℝ, 2 * exp (-(t ^ 2 / K ^ 2)) =
      2 * exp (-(1 / K ^ 2) * t ^ 2) from fun t => by congr 1; ring]
    rw [show (fun t => 2 * exp (-(1 / K ^ 2) * t ^ 2)) =
      (fun t => (2 : ℝ) * (fun s => exp (-(1 / K ^ 2) * s ^ 2)) t) from rfl]
    rw [MeasureTheory.integral_const_mul, integral_gaussian_Ioi (1/K^2)]
    rw [show Real.pi / (1 / K ^ 2) = Real.pi * K ^ 2 from by field_simp]
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos), Real.sqrt_sq (le_of_lt hK)]
    ring
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans h_bound (le_of_eq h_gauss))

end SubGaussian



namespace SubGaussian

open MeasureTheory ProbabilityTheory Real ENNReal MeasureTheory.Measure Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Recentering a sub-Gaussian tail bound: if $X$ has a $K$-sub-Gaussian tail about $m$
and $|m' - m| \le AK$, then $X$ also has a sub-Gaussian tail about $m'$ with a constant
$c > 0$ depending on $A$. -/
theorem tail_recentering
    {X : Ω → ℝ} {m K : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hK : 0 < K) (htail : HasSubGaussianTail X m K μ)
    (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ m' : ℝ, |m' - m| ≤ A * K →
      ∀ t : ℝ, 0 ≤ t →
        μ {ω | t ≤ |X ω - m'|} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * t ^ 2 / K ^ 2))) := by


  set c := Real.log 2 / (4 * (A ^ 2 + 1)) with hc_def
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : (0:ℝ) < c := by positivity
  have hc_le_quarter : c ≤ 1/4 := by
    rw [hc_def]
    calc Real.log 2 / (4 * (A ^ 2 + 1))
        ≤ Real.log 2 / 4 := by
          exact div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith [sq_nonneg A])
      _ ≤ 1 / 4 := by
          exact div_le_div_of_nonneg_right (le_of_lt log2_lt_one) (by norm_num : (0:ℝ) ≤ 4)

  have hsmall_bound : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * A * K →
      c * t ^ 2 / K ^ 2 ≤ Real.log 2 := by
    intro t _ ht_le
    have hK2 : (0:ℝ) < K ^ 2 := by positivity
    rw [div_le_iff₀ hK2]
    calc c * t ^ 2 ≤ c * (2 * A * K) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hc_pos)
          exact sq_le_sq' (by linarith) ht_le
      _ = Real.log 2 / (4 * (A ^ 2 + 1)) * (4 * A ^ 2 * K ^ 2) := by rw [hc_def]; ring
      _ = Real.log 2 * (A ^ 2 / (A ^ 2 + 1)) * K ^ 2 := by
          field_simp
      _ ≤ Real.log 2 * 1 * K ^ 2 := by
          gcongr
          rw [div_le_one (by positivity : (0:ℝ) < A ^ 2 + 1)]
          linarith
      _ = Real.log 2 * K ^ 2 := by ring
  refine ⟨c, hc_pos, fun m' hm' t ht => ?_⟩
  rcases le_or_gt t (2 * A * K) with hsmall | hlarge
  ·
    calc μ {ω | t ≤ |X ω - m'|} ≤ μ Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(c * t ^ 2 / K ^ 2))) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_two_mul_exp_neg (hsmall_bound t ht hsmall))
  ·


    have hsub : {ω : Ω | t ≤ |X ω - m'|} ⊆ {ω : Ω | t / 2 ≤ |X ω - m|} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      have h_tri : |X ω - m| ≥ |X ω - m'| - |m' - m| := by
        have h := abs_sub_abs_le_abs_sub (X ω - m') (X ω - m)
        have : (X ω - m') - (X ω - m) = m - m' := by ring
        rw [this] at h
        rw [abs_sub_comm m m'] at h
        linarith
      have hAK : A * K < t / 2 := by linarith
      linarith

    have htail_half := htail (t / 2) (by linarith)
    calc μ {ω | t ≤ |X ω - m'|}
        ≤ μ {ω | t / 2 ≤ |X ω - m|} := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * Real.exp (-((t / 2) ^ 2 / K ^ 2))) := htail_half
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(c * t ^ 2 / K ^ 2))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          apply Real.exp_le_exp.mpr
          apply neg_le_neg
          apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ K ^ 2)
          calc c * t ^ 2 ≤ (1/4) * t ^ 2 := by
                exact mul_le_mul_of_nonneg_right hc_le_quarter (sq_nonneg t)
            _ = (t / 2) ^ 2 := by ring


end SubGaussian
