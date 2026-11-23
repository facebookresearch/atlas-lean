/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_4

set_option maxHeartbeats 4800000

open MeasureTheory Real Set Measure Filter


/-- Elementary inequality: `e^u · (1 + u) ≤ e^{2u}` for all real `u`. -/
lemma exp_mul_one_add_le_exp_double (u : ℝ) :
    exp u * (1 + u) ≤ exp (2 * u) := by
  rw [show (2 : ℝ) * u = u + u from by ring, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp u]) (exp_pos u).le


/-- If every exponential moment `E[exp(sX)]` is finite, then every polynomial moment
`E[X^k]` is finite as well. -/
lemma integrable_pow_of_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX_meas : AEStronglyMeasurable X μ)
    (hX_exp_int : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (k : ℕ) : Integrable (fun ω => (X ω) ^ k) μ := by
  have h1 := hX_exp_int 1
  have h2 := hX_exp_int (-1)
  simp only [one_mul, neg_one_mul] at h1 h2

  have h_abs_exp : Integrable (fun ω => Real.exp (|X ω|)) μ := by
    apply (h1.add h2).mono
      ((continuous_exp.comp continuous_abs).comp_aestronglyMeasurable hX_meas)
    filter_upwards with ω
    have hexp_bound : rexp |X ω| ≤ rexp (X ω) + rexp (-X ω) := by
      by_cases h : (0 : ℝ) ≤ X ω
      · rw [abs_of_nonneg h]; linarith [exp_pos (-X ω)]
      · push Not at h; rw [abs_of_neg h]; linarith [exp_pos (X ω)]
    show ‖rexp |X ω|‖ ≤ ‖((fun ω => rexp (X ω)) + fun ω => rexp (-X ω)) ω‖
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (exp_pos _).le,
        Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ rexp (X ω) + rexp (-X ω))]
    exact hexp_bound

  apply (h_abs_exp.const_mul ↑k.factorial).mono
    ((continuous_pow k).comp_aestronglyMeasurable hX_meas)
  filter_upwards with ω
  show ‖(X ω) ^ k‖ ≤ ‖(fun ω => ↑k.factorial * rexp |X ω|) ω‖
  have hle := pow_div_factorial_le_exp (|X ω|) (abs_nonneg _) k
  have hfact_pos : (0 : ℝ) < ↑k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  rw [norm_pow, Real.norm_eq_abs]
  simp only [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ↑k.factorial * rexp |X ω|)]
  calc |X ω| ^ k = ↑k.factorial * (|X ω| ^ k / ↑k.factorial) := by
          rw [mul_div_cancel₀ _ hfact_pos.ne']
    _ ≤ ↑k.factorial * rexp (|X ω|) := by gcongr

/-- Interchange of integral and Taylor series for the MGF: under integrability of all
exponential moments, `E[exp(sX)] = ∑_{k} (s^k / k!) · E[X^k]`. -/
lemma mgf_taylor_interchange
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_exp_int : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (s : ℝ) :
    ∫ ω, Real.exp (s * X ω) ∂μ =
      ∑' k : ℕ, (s ^ k / ↑k.factorial) * ∫ ω, (X ω) ^ k ∂μ := by

  set F : ℕ → Ω → ℝ := fun k ω => (s * X ω) ^ k / ↑k.factorial with hF_def

  have hexp_eq : ∀ ω, Real.exp (s * X ω) = ∑' k, F k ω := by
    intro ω
    rw [Real.exp_eq_exp_ℝ]
    exact congr_fun NormedSpace.exp_eq_tsum_div (s * X ω)

  have hF_meas : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    exact ((((continuous_const.mul continuous_id).pow k).div_const
      ↑k.factorial).comp_aestronglyMeasurable hX_meas)


  have hF_enorm : ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≠ ⊤ := by


    have h_abs_exp : Integrable (fun ω => rexp (|s * X ω|)) μ := by
      have h1 := hX_exp_int |s|; have h2 := hX_exp_int (-|s|)
      exact Integrable.mono' (h1.add h2)
        ((continuous_exp.comp continuous_abs).comp_aestronglyMeasurable (hX_meas.const_mul s))
        (Filter.Eventually.of_forall fun ω => by
          simp only [Pi.add_apply, Real.norm_of_nonneg (exp_pos _).le]
          rw [abs_mul]
          by_cases h : 0 ≤ X ω
          · rw [abs_of_nonneg h]
            linarith [exp_pos (-|s| * X ω)]
          · push Not at h; rw [abs_of_neg h]
            have : |s| * -X ω = -|s| * X ω := by ring
            rw [this]
            linarith [exp_pos (|s| * X ω)])


    have hpw : ∀ ω, ∑' k, ‖F k ω‖ₑ ≤ ‖rexp (|s * X ω|)‖ₑ := by
      intro ω
      simp only [enorm_eq_nnnorm]

      have hsumm_abs : Summable (fun k => |s * X ω| ^ k / (↑k.factorial : ℝ)) := by
        have h := NormedSpace.expSeries_summable (𝕂 := ℝ) (|s * X ω|)
        simp only [NormedSpace.expSeries_apply_eq_div] at h; exact h

      have hhs : HasSum (fun k => |s * X ω| ^ k / (↑k.factorial : ℝ)) (rexp |s * X ω|) := by
        rw [exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]; exact hsumm_abs.hasSum

      have hnorm_eq : ∀ k, ‖(s * X ω) ^ k / (↑k.factorial : ℝ)‖₊ =
          ⟨|s * X ω| ^ k / ↑k.factorial, by positivity⟩ := by
        intro k; ext
        simp [coe_nnnorm, Real.norm_eq_abs]

      have hnn_hs : HasSum (fun k => ‖(s * X ω) ^ k / (↑k.factorial : ℝ)‖₊)
          ⟨rexp |s * X ω|, (exp_pos _).le⟩ := by
        rw [← NNReal.hasSum_coe]
        simp_rw [hnorm_eq, NNReal.coe_mk]; exact hhs

      rw [← ENNReal.coe_tsum hnn_hs.summable, hnn_hs.tsum_eq, ENNReal.coe_le_coe]
      exact le_of_eq (by ext; simp [coe_nnnorm, Real.norm_of_nonneg (exp_pos _).le])
    rw [← lintegral_tsum (fun k => (hF_meas k).enorm)]
    exact ne_top_of_le_ne_top (h_abs_exp.hasFiniteIntegral.ne) (lintegral_mono hpw)

  conv_lhs => rw [show (fun ω => Real.exp (s * X ω)) = fun ω => ∑' k, F k ω from
    funext hexp_eq]
  rw [integral_tsum hF_meas hF_enorm]

  congr 1; ext k
  show ∫ ω, (s * X ω) ^ k / ↑k.factorial ∂μ = (s ^ k / ↑k.factorial) * ∫ ω, (X ω) ^ k ∂μ
  have : ∀ ω, (s * X ω) ^ k / ↑k.factorial = (s ^ k / ↑k.factorial) * (X ω) ^ k := by
    intro ω; rw [mul_pow]; ring
  simp_rw [this]
  exact integral_const_mul _ _


/-- Combinatorial identity: `(2m)! = (2m)!! · (2m-1)!!`. -/
lemma factorial_eq_double_factorial_mul (m : ℕ) (hm : 1 ≤ m) :
    (2 * m).factorial = (2 * m).doubleFactorial * (2 * m - 1).doubleFactorial := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; norm_num [Nat.doubleFactorial]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hfact : (2 * (n + 1)).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
        have : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
        rw [this, Nat.factorial_succ, show 2 * n + 1 = (2*n) + 1 from by omega, Nat.factorial_succ]
      have hdf_even : (2 * (n + 1)).doubleFactorial = (2 * n + 2) * (2 * n).doubleFactorial := by
        rw [show 2 * (n + 1) = 2 * n + 2 from by omega]
        exact Nat.doubleFactorial_add_two (2*n)
      have hdf_odd : (2 * (n + 1) - 1).doubleFactorial = (2 * n + 1) * (2 * n - 1).doubleFactorial := by
        rw [show 2 * (n + 1) - 1 = 2 * n + 1 from by omega,
            show 2 * n + 1 = (2 * n - 1) + 2 from by omega]
        exact Nat.doubleFactorial_add_two (2 * n - 1)
      rw [hfact, hdf_even, hdf_odd, ih hn1]
      ring

/-- Combinatorial identity: `(2m+1)! = (2m+1) · (2m-1)!! · 2^m · m!`. -/
lemma factorial_two_mul_add_one_eq (m : ℕ) (hm : 1 ≤ m) :
    (2 * m + 1).factorial = (2 * m + 1) * (2 * m - 1).doubleFactorial * (2 ^ m * m.factorial) := by
  have h1 : (2 * m + 1).factorial = (2 * m + 1) * (2 * m).factorial := by
    rw [show 2 * m + 1 = (2 * m) + 1 from by omega, Nat.factorial_succ]
  have h2 := factorial_eq_double_factorial_mul m hm
  have h3 := Nat.doubleFactorial_two_mul m
  rw [h1, h2, h3]
  ring

/-- Gamma-factorial ratio inequality: for `n ≥ 2`, `n · Γ(n/2) · ⌊n/2⌋! ≤ n!`. -/
theorem gamma_factorial_ratio_le :
    ∀ n : ℕ, 2 ≤ n →
      ↑n * Real.Gamma (↑n / 2) * ↑((n / 2).factorial) ≤ ↑(n.factorial) := by
  intro n hn

  have two_mul_fsq : ∀ m : ℕ, 1 ≤ m → 2 * m.factorial * m.factorial ≤ (2 * m).factorial := by
    intro m hm
    have hchoose_eq := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m from by omega)
    rw [show 2 * m - m = m from by omega] at hchoose_eq
    have hge2 : 2 ≤ (2 * m).choose m := by
      have h1 : (2 * m).choose 1 ≤ (2 * m).choose ((2 * m) / 2) :=
        Nat.choose_le_middle 1 (2 * m)
      simp only [show (2 * m) / 2 = m from by omega, Nat.choose_one_right] at h1
      linarith
    nlinarith [Nat.factorial_pos m]

  have hsqrt_pi : Real.sqrt π < 2 := by
    calc Real.sqrt π < Real.sqrt 4 := Real.sqrt_lt_sqrt pi_pos.le pi_lt_four
      _ = 2 := by
        rw [show (4:ℝ) = 2^2 from by norm_num]
        exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)

  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    subst hm
    have hm1 : 1 ≤ m := by omega

    rw [show (m + m) / 2 = m from by omega]

    have hreal_div : (↑(m + m) : ℝ) / 2 = ↑m := by push_cast; ring
    rw [hreal_div]

    have hGamma_m : Real.Gamma (↑m : ℝ) = ↑((m - 1).factorial) := by
      have : (↑m : ℝ) = ↑(m - 1 : ℕ) + 1 := by
        rw [Nat.cast_sub hm1]; ring
      rw [this, Real.Gamma_nat_eq_factorial]
    rw [hGamma_m]

    have key : m * (m - 1).factorial = m.factorial := by
      cases m with
      | zero => omega
      | succ n => simp [Nat.factorial_succ]

    have lhs_eq : (↑(m + m) : ℝ) * ↑((m - 1).factorial) * ↑(m.factorial)
        = ↑(2 * m.factorial * m.factorial) := by
      push_cast
      have : (↑m : ℝ) * ↑((m - 1).factorial) = ↑(m.factorial) := by exact_mod_cast key
      nlinarith
    rw [lhs_eq]
    have : m + m = 2 * m := by omega
    rw [this]
    exact_mod_cast two_mul_fsq m hm1
  ·


    subst hm
    have hm1 : 1 ≤ m := by omega

    rw [show (2 * m + 1) / 2 = m from by omega]

    have hreal_div : (↑(2 * m + 1) : ℝ) / 2 = ↑m + 1/2 := by push_cast; ring
    rw [hreal_div]

    rw [Real.Gamma_nat_add_half]


    have hfact := factorial_two_mul_add_one_eq m hm1
    have hfact_real : (↑((2 * m + 1).factorial) : ℝ) =
        ↑(2 * m + 1) * ↑((2 * m - 1).doubleFactorial) * ((2 : ℝ) ^ m * ↑(m.factorial)) := by
      rw [hfact]; push_cast; ring
    rw [hfact_real]
    have h2m_pos : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num : (0:ℝ) < 2) m
    have lhs_rw : ↑(2 * m + 1) * (↑((2 * m - 1).doubleFactorial) * √π / (2 : ℝ) ^ m) * ↑(m.factorial) =
        ↑(2 * m + 1) * ↑((2 * m - 1).doubleFactorial) * ↑(m.factorial) * (√π / (2 : ℝ) ^ m) := by ring
    have rhs_rw : ↑(2 * m + 1) * ↑((2 * m - 1).doubleFactorial) * ((2 : ℝ) ^ m * ↑(m.factorial)) =
        ↑(2 * m + 1) * ↑((2 * m - 1).doubleFactorial) * ↑(m.factorial) * (2 : ℝ) ^ m := by ring
    rw [lhs_rw, rhs_rw]
    apply mul_le_mul_of_nonneg_left _ (by positivity)

    rw [div_le_iff₀ h2m_pos]
    have hsqpi := hsqrt_pi.le
    calc Real.sqrt π ≤ 2 := hsqpi
      _ ≤ (2 : ℝ) ^ m := le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : m ≠ 0)
      _ ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ m :=
          le_mul_of_one_le_right (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) m)
            (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- For `x > 0` and natural `n`, `x^(n/2) = (√x)^n`. -/
lemma rpow_half_eq_sqrt_pow (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ ((n : ℝ) / 2) = (Real.sqrt x) ^ n := by
  rw [Real.sqrt_eq_rpow, show (n : ℝ) / 2 = (1/2 : ℝ) * (n : ℝ) from by ring,
      Real.rpow_mul (le_of_lt hx), Real.rpow_natCast]

/-- Algebraic identity: `s^n · (√(2σ²))^n = (√(2σ²s²))^n` for `s > 0`. -/
lemma mul_sqrt_pow_eq (σsq s : ℝ) (_hσ : 0 < σsq) (hs : 0 < s) (n : ℕ) :
    s ^ n * (Real.sqrt (2 * σsq)) ^ n = (Real.sqrt (2 * σsq * s ^ 2)) ^ n := by
  rw [← mul_pow]; congr 1
  rw [show 2 * σsq * s ^ 2 = s ^ 2 * (2 * σsq) from by ring,
      Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]

/-- Per-term bound for the MGF series in the proof of Lemma 1.5: each term is bounded
using the gamma-factorial ratio inequality. -/
lemma series_term_bound_via_gamma (σsq s : ℝ) (hσ : 0 < σsq) (hs : 0 < s)
    (moments : ℕ → ℝ)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      |moments k| ≤ (2 * σsq) ^ ((k : ℝ)/2) * k * Real.Gamma (k/2))
    (n : ℕ) (hn : 2 ≤ n) :
    s ^ n / ↑(n.factorial) * |moments n| ≤
      (Real.sqrt (2 * σsq * s ^ 2)) ^ n / ↑((n / 2).factorial) := by
  have hn1 : 1 ≤ n := by omega
  have hmom_n := hmom n hn1
  have hfact_pos : (0 : ℝ) < ↑(n.factorial) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hfact2_pos : (0 : ℝ) < ↑((n/2).factorial) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hcoeff_nn : 0 ≤ s ^ n / ↑(n.factorial) :=
    div_nonneg (pow_nonneg hs.le _) (Nat.cast_nonneg _)
  have hsqrt_pow_nn : 0 ≤ (Real.sqrt (2 * σsq * s ^ 2)) ^ n :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc s ^ n / ↑(n.factorial) * |moments n|
      ≤ s ^ n / ↑(n.factorial) * ((2 * σsq) ^ ((n : ℝ)/2) * ↑n * Real.Gamma (↑n/2)) :=
        mul_le_mul_of_nonneg_left hmom_n hcoeff_nn
    _ = s ^ n * (2 * σsq) ^ ((n : ℝ)/2) * (↑n * Real.Gamma (↑n/2)) / ↑(n.factorial) := by
        ring
    _ = (Real.sqrt (2 * σsq * s ^ 2)) ^ n * (↑n * Real.Gamma (↑n/2)) / ↑(n.factorial) := by
        congr 1; congr 1
        rw [rpow_half_eq_sqrt_pow (2 * σsq) (by positivity) n]
        exact mul_sqrt_pow_eq σsq s hσ hs n
    _ ≤ (Real.sqrt (2 * σsq * s ^ 2)) ^ n / ↑((n / 2).factorial) := by
        exact (div_le_div_iff₀ hfact_pos hfact2_pos).mpr
          (by nlinarith [gamma_factorial_ratio_le n hn])

/-- Sum-level bound for the MGF tail in the proof of Lemma 1.5: the tail series is
bounded by `e^{2σ²s²}(1 + 2σ²s²) - 1`. -/
theorem gamma_factorial_series_bound (σsq : ℝ) (hσ : 0 < σsq) (s : ℝ) (hs : 0 < s)
    (moments : ℕ → ℝ)
    (hmom_bound : ∀ k : ℕ, 1 ≤ k →
      |moments k| ≤ (2 * σsq) ^ ((k : ℝ)/2) * k * Real.Gamma (k/2)) :
    ∑' k : ℕ, (s ^ (k + 2) / ↑((k + 2).factorial)) * |moments (k + 2)| ≤
      exp (2 * σsq * s ^ 2) * (1 + 2 * σsq * s ^ 2) - 1 := by
  set u := 2 * σsq * s ^ 2 with hu_def
  have hu_pos : 0 < u := by positivity
  have hu_nn : 0 ≤ u := hu_pos.le

  have hRHS_nn : 0 ≤ exp u * (1 + u) - 1 := by
    have h1 : 1 ≤ exp u := one_le_exp hu_nn
    nlinarith

  set f : ℕ → ℝ := fun k => (s ^ (k + 2) / ↑((k + 2).factorial)) * |moments (k + 2)|
  have hf_nn : ∀ k, 0 ≤ f k := fun k =>
    mul_nonneg (div_nonneg (pow_nonneg hs.le _) (Nat.cast_nonneg _)) (abs_nonneg _)

  by_cases hsumm : Summable f
  ·

    set g : ℕ → ℝ := fun k =>
      (Real.sqrt u) ^ (k + 2) / ↑(((k + 2) / 2).factorial)

    have hf_le_g : ∀ k, f k ≤ g k :=
      fun k => series_term_bound_via_gamma σsq s hσ hs moments hmom_bound (k + 2) (by omega)

    have hse : HasSum (fun n : ℕ => u ^ (n + 1) / ↑((n + 1).factorial)) (rexp u - 1) := by
      have hfull := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u
      rw [← Real.exp_eq_exp_ℝ] at hfull
      have : rexp u - ∑ i ∈ Finset.range 1, (fun n => u ^ n / ↑(n.factorial)) i = rexp u - 1 := by simp
      rw [← this]; exact (hasSum_nat_add_iff' 1).mpr hfull
    have hsumm_shifted := hse.summable

    have heven_eq : ∀ j, g (2 * j) = u ^ (j + 1) / ↑((j + 1).factorial) := by
      intro j; simp only [g]
      rw [show (2 * j + 2) / 2 = j + 1 from by omega]; congr 1
      rw [show 2 * j + 2 = 2 * (j + 1) from by omega, pow_mul, Real.sq_sqrt hu_nn]

    have hodd_eq : ∀ j, g (2 * j + 1) =
        Real.sqrt u * (u ^ (j + 1) / ↑((j + 1).factorial)) := by
      intro j; simp only [g]
      rw [show (2 * j + 1 + 2) / 2 = j + 1 from by omega]
      rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 from by omega]
      rw [pow_succ, pow_mul, Real.sq_sqrt hu_nn]
      ring
    have hsumm_even : Summable (fun j => g (2 * j)) :=
      Summable.congr hsumm_shifted (fun j => (heven_eq j).symm)
    have hsumm_odd : Summable (fun j => g (2 * j + 1)) :=
      Summable.congr (hsumm_shifted.mul_left (Real.sqrt u))
        (fun j => (hodd_eq j).symm)
    have hg_summ : Summable g := hsumm_even.even_add_odd hsumm_odd
    have h_fg : ∑' k, f k ≤ ∑' k, g k := hsumm.tsum_le_tsum hf_le_g hg_summ

    have h_g_val : ∑' k, g k = (1 + Real.sqrt u) * (rexp u - 1) := by
      rw [← tsum_even_add_odd hsumm_even hsumm_odd]
      simp_rw [heven_eq, hodd_eq, tsum_mul_left, hse.tsum_eq]; ring


    rw [h_g_val] at h_fg
    suffices h_aux : (1 + Real.sqrt u) * (rexp u - 1) ≤ rexp u * (1 + u) - 1 by
      linarith
    suffices hsuff : rexp u * (1 - Real.sqrt u) ≤ 1 by
      nlinarith [exp_pos u, Real.sqrt_nonneg u,
                 mul_le_mul_of_nonneg_left hsuff (Real.sqrt_nonneg u),
                 Real.mul_self_sqrt hu_nn]
    by_cases h1 : 1 ≤ Real.sqrt u
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (exp_pos u).le (by linarith)) zero_le_one
    · push Not at h1
      have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_nn
      have hge : u ≤ Real.sqrt u := by nlinarith [Real.sqrt_nonneg u]
      have hexp_neg : 1 - u ≤ rexp (-u) := by linarith [add_one_le_exp (-u)]
      have hprod : rexp u * rexp (-u) = 1 := by rw [← exp_add]; simp
      calc rexp u * (1 - Real.sqrt u) ≤ rexp u * (1 - u) := by
              nlinarith [exp_pos u]
        _ ≤ 1 := by nlinarith [exp_pos u]
  ·
    rw [tsum_eq_zero_of_not_summable hsumm]
    exact hRHS_nn

noncomputable section

/-- Combining the gamma series bound with the trivial zeroth moment gives the bound
`1 + tail ≤ e^{2σ²s²}(1 + 2σ²s²)`. -/
lemma moment_bound_series_le (σsq : ℝ) (hσ : 0 < σsq) (s : ℝ) (hs : 0 < s)
    (moments : ℕ → ℝ)
    (hmom_bound : ∀ k : ℕ, 1 ≤ k → |moments k| ≤ (2 * σsq) ^ ((k : ℝ)/2) * k * Real.Gamma (k/2))
    (_hm0 : moments 0 = 1)
    (_hm1 : moments 1 = 0) :
    1 + ∑' k : ℕ, (s ^ (k + 2) / ↑((k + 2).factorial)) * |moments (k + 2)| ≤
      exp (2 * σsq * s ^ 2) * (1 + 2 * σsq * s ^ 2) := by

  set u := 2 * σsq * s ^ 2 with hu_def
  have hu_nn : 0 ≤ u := by positivity


  suffices hsuff : ∑' k : ℕ, (s ^ (k + 2) / ↑((k + 2).factorial)) * |moments (k + 2)| ≤
      exp u * (1 + u) - 1 by linarith
  exact gamma_factorial_series_bound σsq hσ s hs moments hmom_bound


/-- One-sided MGF bound version of Lemma 1.5: under the sub-Gaussian tail bound
`P[|X| > t] ≤ 2 exp(-t²/(2σ²))`, the MGF satisfies `E[exp(sX)] ≤ exp(4σ²s²)`
for `s > 0`. -/
theorem lemma_1_5_mgf_bound_from_tails
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (hP : IsProbabilityMeasure μ)
    {X : Ω → ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hX_int : Integrable X μ)
    (hX_mean : ∫ ω, X ω ∂μ = 0)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t^2 / (2 * σsq))))
    (hX_exp_int : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (4 * σsq * s ^ 2) := by

  set u := 2 * σsq * s ^ 2 with hu_def
  have hu_pos : 0 < u := by positivity


  suffices h : ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp u * (1 + u) by
    calc ∫ ω, Real.exp (s * X ω) ∂μ
        ≤ Real.exp u * (1 + u) := h
      _ ≤ Real.exp (2 * u) := exp_mul_one_add_le_exp_double u
      _ = Real.exp (4 * σsq * s ^ 2) := by
          congr 1; rw [hu_def]; ring


  have hB := mgf_taylor_interchange hX_meas hX_exp_int s

  set moments : ℕ → ℝ := fun k => ∫ ω, (X ω) ^ k ∂μ with hmoments_def

  have hm0 : moments 0 = 1 := by
    simp only [hmoments_def, pow_zero]
    simp [integral_const]

  have hm1 : moments 1 = 0 := by
    simp only [hmoments_def, pow_one]
    exact hX_mean


  have hmom_bound : ∀ k : ℕ, 1 ≤ k →
      |moments k| ≤ (2 * σsq) ^ ((k : ℝ) / 2) * ↑k * Real.Gamma (↑k / 2) := by
    intro k hk

    have h_int_k : Integrable (fun ω => (X ω) ^ k) μ :=
      integrable_pow_of_exp_integrable hX_meas hX_exp_int k
    have h_triangle : |moments k| ≤ ∫ ω, |X ω| ^ k ∂μ := by
      have h1 : ‖∫ ω, (X ω) ^ k ∂μ‖ ≤ ∫ ω, ‖(X ω) ^ k‖ ∂μ :=
        norm_integral_le_integral_norm _
      rw [Real.norm_eq_abs] at h1
      calc |moments k| = |∫ ω, (X ω) ^ k ∂μ| := rfl
        _ ≤ ∫ ω, ‖(X ω) ^ k‖ ∂μ := h1
        _ = ∫ ω, |X ω| ^ k ∂μ := by
            congr 1; ext ω; rw [norm_pow, Real.norm_eq_abs]

    have h_nn : 0 ≤ᶠ[ae μ] fun ω => |X ω| ^ k :=
      Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) _)
    have h_meas_abs_k : AEStronglyMeasurable (fun ω => |X ω| ^ k) μ :=
      ((continuous_abs.pow k).comp_aestronglyMeasurable hX_meas)
    have h_bochner_eq : ∫ ω, |X ω| ^ k ∂μ =
        (∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae h_nn h_meas_abs_k

    have h_pow_eq : ∀ ω, |X ω| ^ k = |X ω| ^ (↑k : ℝ) := by
      intro ω; rw [rpow_natCast]
    have h_lintegral_eq : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (↑k : ℝ)) ∂μ := by
      congr 1; ext ω; rw [h_pow_eq]

    have hL14 : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (↑k : ℝ)) ∂μ ≤
        ENNReal.ofReal ((2 * σsq) ^ ((↑k : ℝ)/2) * ↑k * Real.Gamma (↑k/2)) :=
      lemma_1_4_moment_bound hσ hX_meas hX_tail k hk

    have hRHS_nn : (0 : ℝ) ≤ (2 * σsq) ^ ((↑k : ℝ) / 2) * ↑k * Real.Gamma (↑k / 2) := by
      apply mul_nonneg
      · apply mul_nonneg
        · exact rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * σsq) _
        · exact Nat.cast_nonneg k
      · exact le_of_lt (Gamma_pos_of_pos (by positivity : (0 : ℝ) < ↑k / 2))
    calc |moments k| ≤ ∫ ω, |X ω| ^ k ∂μ := h_triangle
      _ = (∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ).toReal := h_bochner_eq
      _ = (∫⁻ ω, ENNReal.ofReal (|X ω| ^ (↑k : ℝ)) ∂μ).toReal := by rw [h_lintegral_eq]
      _ ≤ (ENNReal.ofReal ((2 * σsq) ^ ((↑k : ℝ)/2) * ↑k * Real.Gamma (↑k/2))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hL14
      _ = (2 * σsq) ^ ((↑k : ℝ) / 2) * ↑k * Real.Gamma (↑k / 2) :=
          ENNReal.toReal_ofReal hRHS_nn

  have hC := moment_bound_series_le σsq hσ s hs moments hmom_bound hm0 hm1


  rw [hB]


  set f : ℕ → ℝ := fun k => (s ^ k / ↑k.factorial) * moments k with hf_def

  have hsumm : Summable f := by
    by_contra h_not
    have h_zero := tsum_eq_zero_of_not_summable h_not
    have hB' : ∫ ω, Real.exp (s * X ω) ∂μ = ∑' k, f k := hB
    rw [h_zero] at hB'
    have h_ge_one : (1 : ℝ) ≤ ∫ ω, Real.exp (s * X ω) ∂μ := by
      have h_pointwise : ∀ ω, (1 : ℝ) + s * X ω ≤ Real.exp (s * X ω) :=
        fun ω => by linarith [add_one_le_exp (s * X ω)]
      have h_int_lb : ∫ ω, (1 + s * X ω) ∂μ ≤ ∫ ω, Real.exp (s * X ω) ∂μ :=
            integral_mono ((integrable_const 1).add (hX_int.const_mul s))
              (hX_exp_int s) h_pointwise
      have h_int_eq : ∫ ω, (1 + s * X ω) ∂μ = 1 := by
        rw [integral_add (integrable_const 1) (hX_int.const_mul s)]
        simp [integral_const, integral_const_mul, hX_mean]
      linarith
    linarith

  have h_sum_eq : ∑' k, f k = f 0 + ∑' k, f (k + 1) :=
    hsumm.tsum_eq_zero_add
  have hf0 : f 0 = 1 := by simp [hf_def, hm0]

  have hsumm1 : Summable (fun k => f (k + 1)) :=
    hsumm.comp_injective (fun _ _ h => by omega)
  have h_sum1_eq : ∑' k, f (k + 1) = f 1 + ∑' k, f (k + 2) :=
    hsumm1.tsum_eq_zero_add
  have hf1 : f 1 = 0 := by simp [hf_def, hm1]

  rw [h_sum_eq, hf0, h_sum1_eq, hf1, zero_add]

  have hsumm2 : Summable (fun k => f (k + 2)) :=
    hsumm1.comp_injective (fun _ _ h => by omega)

  set g : ℕ → ℝ := fun k =>
    (s ^ (k + 2) / ↑((k + 2).factorial)) * |moments (k + 2)| with hg_def

  have hg_nonneg : ∀ k, 0 ≤ g k := by
    intro k; apply mul_nonneg
    · exact div_nonneg (pow_nonneg hs.le _) (Nat.cast_nonneg _)
    · exact abs_nonneg _

  have hg_summ : Summable g := by

    have hg_eq : g = fun k => ‖f (k + 2)‖ := by
      ext k; simp only [hf_def, hg_def, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (div_nonneg (pow_nonneg hs.le _) (Nat.cast_nonneg _))]
    rw [hg_eq]; exact hsumm2.norm

  have h_le_abs : ∀ k, f (k + 2) ≤ g k := by
    intro k
    simp only [hf_def, hg_def]
    exact mul_le_mul_of_nonneg_left (le_abs_self _)
      (div_nonneg (pow_nonneg hs.le _) (Nat.cast_nonneg _))

  calc 1 + ∑' k, f (k + 2)
      ≤ 1 + ∑' k, g k := by linarith [hsumm2.tsum_mono hg_summ h_le_abs]
    _ ≤ exp u * (1 + u) := hC

/-- **Lemma 1.5**: If `P[X > t] ≤ exp(-t²/(2σ²))` (and likewise for `-X`), then
`E[exp(sX)] ≤ exp(4σ²s²)` for all `s`, i.e. `X` is sub-Gaussian with variance proxy
`8σ²`. -/
theorem lemma_1_5_implies_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hX_int : Integrable X μ)
    (hX_mean : ∫ ω, X ω ∂μ = 0)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t^2 / (2 * σsq))))
    (hX_exp_int : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ) :
    IsSubGaussian X (8 * σsq) μ := by
  refine ⟨hX_int, hX_mean, hX_exp_int, fun s => ?_⟩


  by_cases hs_pos : 0 < s
  · have h := lemma_1_5_mgf_bound_from_tails inferInstance hσ hX_int hX_mean hX_meas hX_tail hX_exp_int s hs_pos
    calc ∫ ω, exp (s * X ω) ∂μ
        ≤ exp (4 * σsq * s ^ 2) := h
      _ = exp (8 * σsq * s ^ 2 / 2) := by ring_nf
  · by_cases hs_zero : s = 0
    · simp [hs_zero, integral_const]
    ·
      have hs_neg : s < 0 := lt_of_le_of_ne (not_lt.mp hs_pos) hs_zero
      have hss : ∫ ω, exp (s * X ω) ∂μ = ∫ ω, exp ((-s) * (-X ω)) ∂μ := by
        congr 1; ext ω; ring_nf
      rw [hss]
      have hX_neg_tail : ∀ t : ℝ, 0 < t →
          μ {ω | |(fun ω => -X ω) ω| > t} ≤
            ENNReal.ofReal (2 * exp (-t ^ 2 / (2 * σsq))) := by
        intro t ht
        simp only [abs_neg]
        exact hX_tail t ht
      have hX_neg_exp_int : ∀ r : ℝ, Integrable (fun ω => exp (r * (fun ω => -X ω) ω)) μ := by
        intro r
        show Integrable (fun ω => exp (r * (-X ω))) μ
        have : (fun ω => exp (r * (-X ω))) = (fun ω => exp ((-r) * X ω)) := by
          ext ω; ring_nf
        rw [this]; exact hX_exp_int (-r)
      have h := lemma_1_5_mgf_bound_from_tails inferInstance hσ hX_int.neg
        (by simp [integral_neg, hX_mean]) hX_meas.neg hX_neg_tail hX_neg_exp_int
        (-s) (neg_pos.mpr hs_neg)
      calc ∫ ω, exp ((-s) * (-X ω)) ∂μ
          ≤ exp (4 * σsq * (-s) ^ 2) := h
        _ = exp (8 * σsq * s ^ 2 / 2) := by ring_nf

end



/-- Integrability of `X` follows from integrability of all of its exponential moments. -/
lemma integrable_of_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX_meas : AEStronglyMeasurable X μ)
    (hX_exp_int : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ) :
    Integrable X μ := by
  have := integrable_pow_of_exp_integrable hX_meas hX_exp_int 1
  simpa [pow_one] using this

namespace SubGaussianTailBound

end SubGaussianTailBound
