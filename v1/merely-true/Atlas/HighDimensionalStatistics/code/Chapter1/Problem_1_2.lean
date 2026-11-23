/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open ProbabilityTheory hiding stdGaussian
open MeasureTheory Real Set

noncomputable section

/-- The standard Gaussian measure on `ℝ` with mean `0` and variance `1`. -/
def stdGaussianMeasure : Measure ℝ := gaussianReal 0 1

variable {n : ℕ}

/-- Problem 1.2(a): for `s < 1/2`, the moment-generating function of `X² - 1`
under the standard Gaussian equals `e^{-s} / √(1 - 2s)`. -/
theorem problem_1_2a_mgf_chi_squared (s : ℝ) (hs : s < 1 / 2) :
    mgf (fun x => x ^ 2 - 1) stdGaussianMeasure s =
      Real.exp (-s) / Real.sqrt (1 - 2 * s) := by

  simp only [mgf, stdGaussianMeasure]

  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp only [smul_eq_mul]


  have integrand_eq : ∀ x : ℝ,
      gaussianPDFReal 0 1 x * rexp (s * (x ^ 2 - 1)) =
      rexp (-s) * ((√(2 * π))⁻¹ * rexp (-((1 - 2 * s) / 2) * x ^ 2)) := by
    intro x
    simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
    have h1 : rexp (-x ^ 2 / 2) * rexp (s * (x ^ 2 - 1)) =
        rexp (-s) * rexp (-((1 - 2 * s) / 2) * x ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (s * (x ^ 2 - 1))
        = (√(2 * π))⁻¹ * (rexp (-x ^ 2 / 2) * rexp (s * (x ^ 2 - 1))) := by ring
      _ = (√(2 * π))⁻¹ * (rexp (-s) * rexp (-((1 - 2 * s) / 2) * x ^ 2)) := by rw [h1]
      _ = rexp (-s) * ((√(2 * π))⁻¹ * rexp (-((1 - 2 * s) / 2) * x ^ 2)) := by ring
  simp_rw [integrand_eq]

  rw [integral_const_mul, integral_const_mul, integral_gaussian]

  have h_pos : 0 < 1 - 2 * s := by linarith
  have h1 : π / ((1 - 2 * s) / 2) = 2 * π / (1 - 2 * s) := by
    rw [div_div_eq_mul_div]; ring_nf
  rw [h1, Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * π)]

  have hsqrt_2pi_ne : √(2 * π) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsqrt_1m2s_ne : √(1 - 2 * s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h_pos)
  field_simp

/-- Derivative computation for the auxiliary function used in Problem 1.2(b):
the derivative of `s ↦ s²/(1-2s) + s + (1/2) log(1-2s)` is `2x²/(1-2x)²`. -/
lemma deriv_helper_p12b (x : ℝ) (hx : x < 1/2) :
    HasDerivAt (fun s => s ^ 2 / (1 - 2 * s) + s + 1/2 * Real.log (1 - 2 * s))
      (2 * x ^ 2 / (1 - 2 * x) ^ 2) x := by
  have h1 : (1 : ℝ) - 2 * x ≠ 0 := by linarith
  have hd_quot : HasDerivAt (fun s => s ^ 2 / (1 - 2 * s))
      (2 * x * (1 - x) / (1 - 2 * x) ^ 2) x := by
    have hd1 : HasDerivAt (fun s => s ^ 2) (2 * x) x := by
      have := (hasDerivAt_id x).pow 2; simp at this; exact this
    have hd2 : HasDerivAt (fun s => (1 : ℝ) - 2 * s) (-2) x := by
      have := (hasDerivAt_const x 1).sub ((hasDerivAt_const x 2).mul (hasDerivAt_id x))
      simp at this; exact this
    convert hd1.div hd2 h1 using 1; field_simp; ring
  have hd_log : HasDerivAt (fun s => 1/2 * Real.log (1 - 2 * s))
      (1/2 * (-2 / (1 - 2 * x))) x := by
    have := (HasDerivAt.log
      ((hasDerivAt_const x 1).sub ((hasDerivAt_const x 2).mul (hasDerivAt_id x))) h1)
    simp at this; exact this.const_mul (1/2)
  convert (hd_quot.add (hasDerivAt_id x)).add hd_log using 1; field_simp; ring

/-- Problem 1.2(b): for `0 < s < 1/2`, the chi-squared MGF is bounded by
`exp(s² / (1 - 2s))`. -/
theorem problem_1_2b_mgf_bound (s : ℝ) (hs_pos : 0 < s) (hs_lt : s < 1 / 2) :
    Real.exp (-s) / Real.sqrt (1 - 2 * s) ≤
      Real.exp (s ^ 2 / (1 - 2 * s)) := by
  have h_pos : (0 : ℝ) < 1 - 2 * s := by linarith

  have hkey : -s - 1/2 * Real.log (1 - 2 * s) ≤ s ^ 2 / (1 - 2 * s) := by
    suffices h : 0 ≤ s ^ 2 / (1 - 2 * s) + s + 1/2 * Real.log (1 - 2 * s) by linarith
    let f := fun s => s ^ 2 / (1 - 2 * s) + s + 1/2 * Real.log (1 - 2 * s)
    show 0 ≤ f s
    have g0 : f 0 = 0 := by simp [f, Real.log_one]
    rw [← g0]; show f 0 ≤ f s
    exact (monotoneOn_of_deriv_nonneg (convex_Icc 0 s)
      (by apply ContinuousOn.add; apply ContinuousOn.add
          · exact (continuousOn_pow 2).div
              (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
              (fun x hx => by simp; linarith [hx.2, hs_lt])
          · exact continuousOn_id
          · exact continuousOn_const.mul
              ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
                (fun x hx => by simp; linarith [hx.2, hs_lt])))
      (by intro x hx; rw [interior_Icc] at hx
          exact (deriv_helper_p12b x (by linarith [hx.2])).differentiableAt.differentiableWithinAt)
      (by intro x hx; rw [interior_Icc] at hx
          rw [(deriv_helper_p12b x (by linarith [hx.2])).deriv]
          exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg x)) (sq_nonneg _)))
      (left_mem_Icc.mpr hs_pos.le) (right_mem_Icc.mpr hs_pos.le) hs_pos.le

  have hsqrt : Real.sqrt (1 - 2 * s) = Real.exp (1/2 * Real.log (1 - 2 * s)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h_pos]; ring_nf
  rw [hsqrt, Real.exp_neg]

  have h1 : (Real.exp s)⁻¹ / Real.exp (1/2 * Real.log (1 - 2 * s)) =
      Real.exp (-s - 1/2 * Real.log (1 - 2 * s)) := by
    have : Real.exp (-s - 1/2 * Real.log (1 - 2 * s)) =
        Real.exp (-s) * Real.exp (-(1/2 * Real.log (1 - 2 * s))) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, Real.exp_neg, Real.exp_neg]; exact div_eq_mul_inv _ _
  rw [h1]
  exact Real.exp_le_exp.mpr hkey

/-- Problem 1.2(c): the standard Gaussian tail bound for `X² - 1`,
`P(X² - 1 > 2t + 2√t) ≤ e^{-t}` for `t > 0`. -/
theorem problem_1_2c_tail_bound (t : ℝ) (ht : 0 < t) :
    (stdGaussianMeasure {x : ℝ | x ^ 2 - 1 > 2 * t + 2 * Real.sqrt t}).toReal ≤
      Real.exp (-t) := by


  set u := 2 * t + 2 * Real.sqrt t with hu_def
  set s₀ := (t + Real.sqrt t) / (u + 1) with hs₀_def
  have hsqrt := Real.sqrt_nonneg t
  have hsqrt_pos := Real.sqrt_pos.mpr ht
  have hval : 0 < u + 1 := by simp [hu_def]; linarith
  have hs₀_pos : 0 < s₀ := div_pos (add_pos ht hsqrt_pos) hval
  have hs₀_lt : s₀ < 1 / 2 := by
    rw [hs₀_def, hu_def, div_lt_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
    nlinarith

  have hfm : IsFiniteMeasure stdGaussianMeasure := by
    show IsFiniteMeasure (gaussianReal 0 1); infer_instance
  have hmon : (stdGaussianMeasure {x : ℝ | x ^ 2 - 1 > u}).toReal ≤
      stdGaussianMeasure.real {x : ℝ | u ≤ x ^ 2 - 1} := by
    simp only [Measure.real]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (fun x hx => by simp only [mem_setOf_eq] at *; linarith)


  have hchernoff : stdGaussianMeasure.real {x : ℝ | u ≤ x ^ 2 - 1} ≤
      rexp (-s₀ * u) * mgf (fun x => x ^ 2 - 1) stdGaussianMeasure s₀ := by
    have hint : Integrable (fun ω => rexp (s₀ * ((fun x => x ^ 2 - 1) ω))) stdGaussianMeasure := by


      show Integrable (fun ω => rexp (s₀ * (ω ^ 2 - 1))) (gaussianReal 0 1)
      have hgr : gaussianReal (0 : ℝ) (1 : NNReal) =
          (ℙ : Measure ℝ).withDensity (gaussianPDF 0 1) := by simp [gaussianReal]
      rw [hgr, integrable_withDensity_iff (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
      have hsimp : ∀ x : ℝ, (gaussianPDF 0 1 x).toReal = gaussianPDFReal 0 1 x := by
        intro x; simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x)]
      simp_rw [hsimp]
      have hprod : (fun x : ℝ =>
          rexp (s₀ * (x ^ 2 - 1)) * gaussianPDFReal 0 1 x) =
          fun x => rexp (-s₀) * ((√(2 * π))⁻¹ * rexp (-((1/2 - s₀) * x ^ 2))) := by
        ext x
        simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
        rw [show (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) =
            (√(2 * π))⁻¹ * rexp (-(1/2 * x ^ 2)) by congr 1; ring]
        rw [show rexp (s₀ * (x ^ 2 - 1)) * ((√(2 * π))⁻¹ * rexp (-(1/2 * x ^ 2))) =
            (√(2 * π))⁻¹ * (rexp (s₀ * (x ^ 2 - 1)) * rexp (-(1/2 * x ^ 2))) by ring]
        rw [show rexp (-s₀) * ((√(2 * π))⁻¹ * rexp (-((1 / 2 - s₀) * x ^ 2))) =
            (√(2 * π))⁻¹ * (rexp (-s₀) * rexp (-((1 / 2 - s₀) * x ^ 2))) by ring]
        congr 1; rw [← exp_add, ← exp_add]; congr 1; ring
      rw [hprod]
      apply Integrable.const_mul; apply Integrable.const_mul
      have : (fun x : ℝ => rexp (-((1 / 2 - s₀) * x ^ 2))) =
          fun x => rexp (-(1/2 - s₀) * x ^ 2) := by ext x; congr 1; ring
      rw [this]
      exact integrable_exp_neg_mul_sq (by linarith)
    exact measure_ge_le_exp_mul_mgf u hs₀_pos.le hint

  have hmgf : mgf (fun x => x ^ 2 - 1) stdGaussianMeasure s₀ =
      rexp (-s₀) / Real.sqrt (1 - 2 * s₀) := problem_1_2a_mgf_chi_squared s₀ hs₀_lt


  have h_s0_times_up1 : s₀ * (u + 1) = t + Real.sqrt t := by
    rw [hs₀_def]; field_simp
  have h_1m2s : 1 - 2 * s₀ = 1 / (u + 1) := by
    rw [hs₀_def]; field_simp; ring

  calc (stdGaussianMeasure {x : ℝ | x ^ 2 - 1 > u}).toReal
      ≤ stdGaussianMeasure.real {x : ℝ | u ≤ x ^ 2 - 1} := hmon
    _ ≤ rexp (-s₀ * u) * mgf (fun x => x ^ 2 - 1) stdGaussianMeasure s₀ := hchernoff
    _ = rexp (-s₀ * u) * (rexp (-s₀) / Real.sqrt (1 - 2 * s₀)) := by rw [hmgf]
    _ = rexp (-(s₀ * u + s₀)) / Real.sqrt (1 - 2 * s₀) := by
        rw [show rexp (-s₀ * u) * (rexp (-s₀) / √(1 - 2 * s₀)) =
            rexp (-s₀ * u) * rexp (-s₀) / √(1 - 2 * s₀) from mul_div_assoc' _ _ _]
        congr 1; rw [← Real.exp_add]; congr 1; ring
    _ = rexp (-(t + Real.sqrt t)) / Real.sqrt (1 / (u + 1)) := by
        rw [show s₀ * u + s₀ = s₀ * (u + 1) by ring, h_s0_times_up1, h_1m2s]
    _ = rexp (-(t + Real.sqrt t)) * Real.sqrt (u + 1) := by
        rw [Real.sqrt_div' 1 (by positivity), Real.sqrt_one, one_div]
        simp [div_eq_mul_inv, inv_inv]
    _ ≤ rexp (-t) := by


        have hsqrt_le : Real.sqrt (u + 1) ≤ rexp (Real.sqrt t) := by
          rw [hu_def, show 2 * t + 2 * Real.sqrt t + 1 = u + 1 from by rw [hu_def]]
          rw [← Real.sqrt_sq (exp_pos _).le]
          apply Real.sqrt_le_sqrt
          rw [sq, ← Real.exp_add, ← two_mul]
          have h := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * Real.sqrt t)
          have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
          rw [hu_def]; nlinarith
        calc rexp (-(t + Real.sqrt t)) * Real.sqrt (u + 1)
            ≤ rexp (-(t + Real.sqrt t)) * rexp (Real.sqrt t) :=
              mul_le_mul_of_nonneg_left hsqrt_le (exp_pos _).le
          _ = rexp (-(t + Real.sqrt t) + Real.sqrt t) := (Real.exp_add _ _).symm
          _ = rexp (-t) := by ring_nf

/-- Problem 1.2(d) (chi-squared concentration): for `Z₁,…,Zₙ` i.i.d. standard
Gaussians,
`P(∑ Zᵢ² > n + 2√(n log(1/δ)) + 2 log(1/δ)) ≤ δ`. -/
theorem problem_1_2d_chi_squared_concentration
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (hP : IsProbabilityMeasure μ)
    {Z : Fin n → Ω → ℝ}
    (hZ_meas : ∀ i, Measurable (Z i))
    (hZ_dist : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    (hZ_indep : iIndepFun (β := fun (_ : Fin n) => ℝ) Z μ)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    (μ {ω | ∑ i, (Z i ω) ^ 2 >
        (n : ℝ) + 2 * Real.sqrt ((n : ℝ) * Real.log (1 / δ)) +
          2 * Real.log (1 / δ)}).toReal ≤ δ := by


  set logdelta := Real.log (1 / δ) with hlogdelta_def
  have hlog : 0 < logdelta := by
    apply Real.log_pos; rw [lt_div_iff₀ hδ_pos]; linarith

  by_cases hn : n = 0
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_add,
      zero_mul, Real.sqrt_zero, mul_zero]
    have hempty : {ω : Ω | (0 : ℝ) > 2 * logdelta} = ∅ := by
      ext ω; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]; linarith
    rw [hempty]; simp; exact hδ_pos.le

  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn

  set Y : Fin n → Ω → ℝ := fun i => (fun x : ℝ => x ^ 2 - 1) ∘ (Z i) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i =>
    (by measurability : Measurable (fun x : ℝ => x ^ 2 - 1)).comp (hZ_meas i)
  have hY_indep : iIndepFun Y μ :=
    hZ_indep.comp (fun _ => fun x => x ^ 2 - 1) (fun _ => by measurability)

  set u := 2 * Real.sqrt ((n : ℝ) * logdelta) + 2 * logdelta with hu_def

  have hsum_eq : ∀ ω, ∑ i, (Z i ω) ^ 2 = (n : ℝ) + ∑ i, Y i ω := by
    intro ω; simp only [Y, Function.comp]
    simp [Finset.sum_sub_distrib, Finset.card_univ]

  have hmon : (μ {ω | ∑ i, (Z i ω) ^ 2 >
        (n : ℝ) + 2 * Real.sqrt ((n : ℝ) * logdelta) + 2 * logdelta}).toReal ≤
      μ.real {ω | u ≤ (fun ω => ∑ i, Y i ω) ω} := by
    simp only [Measure.real]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq] at *
    have := hsum_eq ω
    linarith

  set a := Real.sqrt logdelta with ha_def
  set b := Real.sqrt (n : ℝ) with hb_def
  set s := a / (b + 2 * a) with hs_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hlog
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn_pos)
  have hba_pos : 0 < b + 2 * a := by linarith
  have hs_pos : 0 < s := div_pos ha_pos hba_pos
  have hs_lt : s < 1 / 2 := by
    rw [hs_def, div_lt_div_iff₀ hba_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have h1m2s_pos : 0 < 1 - 2 * s := by linarith


  have hint_each : ∀ i, Integrable (fun ω => rexp (s * Y i ω)) μ := by
    intro i

    have hident : IdentDistrib (Y i) (fun x : ℝ => x ^ 2 - 1) μ stdGaussianMeasure := by
      have h1 : IdentDistrib (Z i) id μ stdGaussianMeasure := {
        aemeasurable_fst := (hZ_meas i).aemeasurable
        aemeasurable_snd := aemeasurable_id
        map_eq := by simp [stdGaussianMeasure, hZ_dist i]
      }
      have h2 := h1.comp (u := fun x : ℝ => x ^ 2 - 1) (by measurability)
      simp only [Function.comp_id] at h2
      exact h2

    have hident_exp : IdentDistrib (fun ω => rexp (s * Y i ω))
        (fun x => rexp (s * (x ^ 2 - 1))) μ stdGaussianMeasure := by
      exact hident.comp (u := fun y => rexp (s * y)) (by measurability)
    rw [hident_exp.integrable_iff]
    show Integrable (fun x => rexp (s * (x ^ 2 - 1))) stdGaussianMeasure

    show Integrable (fun ω => rexp (s * (ω ^ 2 - 1))) (gaussianReal 0 1)
    have hgr : gaussianReal (0 : ℝ) (1 : NNReal) =
        (ℙ : Measure ℝ).withDensity (gaussianPDF 0 1) := by simp [gaussianReal]
    rw [hgr, integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have hsimp : ∀ x : ℝ, (gaussianPDF 0 1 x).toReal = gaussianPDFReal 0 1 x := by
      intro x; simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x)]
    simp_rw [hsimp]
    have hprod : (fun x : ℝ =>
        rexp (s * (x ^ 2 - 1)) * gaussianPDFReal 0 1 x) =
        fun x => rexp (-s) * ((√(2 * π))⁻¹ * rexp (-((1/2 - s) * x ^ 2))) := by
      ext x
      simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
      rw [show (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) =
          (√(2 * π))⁻¹ * rexp (-(1/2 * x ^ 2)) by congr 1; ring]
      rw [show rexp (s * (x ^ 2 - 1)) * ((√(2 * π))⁻¹ * rexp (-(1/2 * x ^ 2))) =
          (√(2 * π))⁻¹ * (rexp (s * (x ^ 2 - 1)) * rexp (-(1/2 * x ^ 2))) by ring]
      rw [show rexp (-s) * ((√(2 * π))⁻¹ * rexp (-((1 / 2 - s) * x ^ 2))) =
          (√(2 * π))⁻¹ * (rexp (-s) * rexp (-((1 / 2 - s) * x ^ 2))) by ring]
      congr 1; rw [← exp_add, ← exp_add]; congr 1; ring
    rw [hprod]
    apply Integrable.const_mul; apply Integrable.const_mul
    have : (fun x : ℝ => rexp (-((1 / 2 - s) * x ^ 2))) =
        fun x => rexp (-(1/2 - s) * x ^ 2) := by ext x; congr 1; ring
    rw [this]
    exact integrable_exp_neg_mul_sq (by linarith)

  have hint_sum : Integrable (fun ω => rexp (s * (∑ i, Y i ω))) μ := by
    have : (fun ω => rexp (s * (∑ i, Y i ω))) = (fun ω => rexp (s * (∑ i ∈ Finset.univ, Y i) ω)) := by
      ext ω; congr 1; congr 1; simp [Finset.sum_apply]
    rw [this]
    exact hY_indep.integrable_exp_mul_sum hY_meas (fun i _ => hint_each i)

  have hchernoff : μ.real {ω | u ≤ (fun ω => ∑ i, Y i ω) ω} ≤
      rexp (-s * u) * mgf (fun ω => ∑ i, Y i ω) μ s := by
    have hrewrite : (fun ω => ∑ i, Y i ω) = (∑ i ∈ Finset.univ, Y i) := by
      ext ω; simp [Finset.sum_apply]
    rw [hrewrite]
    have hint' : Integrable (fun ω => rexp (s * (∑ i ∈ Finset.univ, Y i) ω)) μ := by
      exact hY_indep.integrable_exp_mul_sum hY_meas (fun i _ => hint_each i)
    exact measure_ge_le_exp_mul_mgf u hs_pos.le hint'

  have hmgf_factor : mgf (fun ω => ∑ i, Y i ω) μ s = ∏ i : Fin n, mgf (Y i) μ s := by
    have hrewrite : (fun ω => ∑ i, Y i ω) = (∑ i ∈ Finset.univ, Y i) := by
      ext ω; simp [Finset.sum_apply]
    rw [hrewrite]
    exact hY_indep.mgf_sum hY_meas Finset.univ

  have hmgf_each : ∀ i, mgf (Y i) μ s = mgf (fun x : ℝ => x ^ 2 - 1) stdGaussianMeasure s := by
    intro i
    have hident : IdentDistrib (Y i) (fun x : ℝ => x ^ 2 - 1) μ stdGaussianMeasure := by
      have h1 : IdentDistrib (Z i) id μ stdGaussianMeasure := {
        aemeasurable_fst := (hZ_meas i).aemeasurable
        aemeasurable_snd := aemeasurable_id
        map_eq := by simp [stdGaussianMeasure, hZ_dist i]
      }
      have h2 := h1.comp (u := fun x : ℝ => x ^ 2 - 1) (by measurability)
      simp only [Function.comp_id] at h2
      exact h2
    exact congr_fun (mgf_congr_identDistrib hident) s

  have hmgf_val : mgf (fun x : ℝ => x ^ 2 - 1) stdGaussianMeasure s =
      rexp (-s) / Real.sqrt (1 - 2 * s) := problem_1_2a_mgf_chi_squared s hs_lt

  have hmgf_bound : rexp (-s) / Real.sqrt (1 - 2 * s) ≤ rexp (s ^ 2 / (1 - 2 * s)) :=
    problem_1_2b_mgf_bound s hs_pos hs_lt

  have hmgf_sum_bound : mgf (fun ω => ∑ i, Y i ω) μ s ≤
      rexp ((n : ℝ) * s ^ 2 / (1 - 2 * s)) := by
    rw [hmgf_factor]
    have h1 : ∏ i : Fin n, mgf (Y i) μ s = (mgf (fun x : ℝ => x ^ 2 - 1) stdGaussianMeasure s) ^ n := by
      simp [hmgf_each, Finset.prod_const, Finset.card_univ]
    rw [h1, hmgf_val]
    calc (rexp (-s) / Real.sqrt (1 - 2 * s)) ^ n
        ≤ (rexp (s ^ 2 / (1 - 2 * s))) ^ n := by
          apply pow_le_pow_left₀ (by positivity) hmgf_bound
      _ = rexp ((n : ℝ) * (s ^ 2 / (1 - 2 * s))) := by
          rw [← Real.exp_nat_mul]
      _ = rexp ((n : ℝ) * s ^ 2 / (1 - 2 * s)) := by ring_nf


  have ha_sq : a ^ 2 = logdelta := Real.sq_sqrt hlog.le
  have hb_sq : b ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hu_eq : u = 2 * a * b + 2 * a ^ 2 := by
    rw [hu_def, ha_sq, ha_def, hb_def]
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    ring
  have h_exponent : -s * u + (n : ℝ) * s ^ 2 / (1 - 2 * s) = -logdelta := by
    rw [hs_def]
    have hba_ne : b + 2 * a ≠ 0 := ne_of_gt hba_pos
    have h1m2s_eq : 1 - 2 * (a / (b + 2 * a)) = b / (b + 2 * a) := by
      field_simp; ring
    rw [hu_eq, h1m2s_eq]
    field_simp
    rw [← hb_sq, ← ha_sq]; ring

  calc (μ {ω | ∑ i, (Z i ω) ^ 2 >
        (n : ℝ) + 2 * Real.sqrt ((n : ℝ) * logdelta) + 2 * logdelta}).toReal
      ≤ μ.real {ω | u ≤ (fun ω => ∑ i, Y i ω) ω} := hmon
    _ ≤ rexp (-s * u) * mgf (fun ω => ∑ i, Y i ω) μ s := hchernoff
    _ ≤ rexp (-s * u) * rexp ((n : ℝ) * s ^ 2 / (1 - 2 * s)) := by
        apply mul_le_mul_of_nonneg_left hmgf_sum_bound (exp_pos _).le
    _ = rexp (-s * u + (n : ℝ) * s ^ 2 / (1 - 2 * s)) := by
        rw [← Real.exp_add]
    _ = rexp (-logdelta) := by rw [h_exponent]
    _ ≤ δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ)]
        simp

end
