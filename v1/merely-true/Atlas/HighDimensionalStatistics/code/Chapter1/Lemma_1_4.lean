/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxHeartbeats 4800000

open MeasureTheory Real Set Measure Filter

namespace SubGaussianMoments

/-- **Lemma 1.4 (Moment bound from a sub-Gaussian-style tail).** If `X` has
the two-sided tail bound `P(|X| > t) ≤ 2 exp(-t²/(2σ²))`, then for every
integer `k ≥ 1`, `E[|X|^k] ≤ (2σ²)^{k/2} · k · Γ(k/2)`. -/
theorem moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t → μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t^2 / (2 * σsq))))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (k : ℝ)) ∂μ ≤
      ENNReal.ofReal ((2 * σsq) ^ ((k : ℝ)/2) * k * Real.Gamma (k/2)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hq : (-1 : ℝ) < (↑k : ℝ) - 1 := by linarith
  have hb : (0 : ℝ) < 1 / (2 * σsq) := by positivity

  set g : ℝ → ℝ := fun t => 2 * rexp (-t^2 / (2 * σsq)) * t ^ ((↑k : ℝ) - 1) with hg_def

  have hg_int : IntegrableOn g (Ioi 0) := by
    have hint := integrableOn_rpow_mul_exp_neg_mul_rpow hq (by norm_num : (1 : ℝ) ≤ 2) hb
    refine (hint.const_mul 2).congr ?_
    filter_upwards with t
    simp only [hg_def]
    have hexp : (-(1 / (2 * σsq)) * (t : ℝ) ^ (2 : ℝ)) = (-t ^ 2 / (2 * σsq)) := by
      simp only [Real.rpow_two]; ring
    rw [hexp]; ring

  have hg_nn : 0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi, hg_def] at *
    exact mul_nonneg (mul_nonneg (by norm_num) (exp_pos _).le) (rpow_nonneg ht.le _)


  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ (fun ω => abs_nonneg _))
    hX_meas.aemeasurable.norm
    hk_pos]


  have step2 : ∫⁻ t in Ioi (0:ℝ), μ {a | t < |X a|} * ENNReal.ofReal (t ^ ((↑k : ℝ) - 1)) ≤
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (g t) := by
    apply setLIntegral_mono (by fun_prop)
    intro t ht
    simp only [hg_def]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * rexp (-t^2 / (2 * σsq)))]
    gcongr
    exact hX_tail t (mem_Ioi.mp ht)

  have step3 : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (g t) =
      ENNReal.ofReal (∫ t in Ioi (0:ℝ), g t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nn]


  have step4 : ∫ t in Ioi (0:ℝ), g t =
      2 * ((1/(2*σsq)) ^ (-((↑k:ℝ)-1+1)/2) * (1/2) * Gamma (((↑k:ℝ)-1+1)/2)) := by
    simp only [hg_def]
    have hrewrite : (fun t : ℝ => 2 * rexp (-t^2 / (2 * σsq)) * t ^ ((↑k : ℝ) - 1)) =
      fun t => 2 * (t ^ ((↑k : ℝ) - 1) * rexp (-(1/(2*σsq)) * t ^ (2 : ℝ))) := by
      ext t
      have hexp : (-(1 / (2 * σsq)) * (t : ℝ) ^ (2 : ℝ)) = (-t ^ 2 / (2 * σsq)) := by
        simp only [Real.rpow_two]; ring
      rw [hexp]; ring
    rw [hrewrite, integral_const_mul]
    congr 1
    exact integral_rpow_mul_exp_neg_mul_rpow (by positivity : (0 : ℝ) < 2) hq hb


  have step5 : ↑k * (2 * ((1 / (2 * σsq)) ^ (-((↑k:ℝ) - 1 + 1) / 2) * (1 / 2) *
      Gamma (((↑k:ℝ) - 1 + 1) / 2))) =
      (2 * σsq) ^ ((↑k:ℝ) / 2) * ↑k * Gamma ((↑k:ℝ) / 2) := by
    have hsub : (↑k:ℝ) - 1 + 1 = (↑k:ℝ) := by ring
    rw [hsub, one_div, Real.inv_rpow (by positivity : (0:ℝ) ≤ 2 * σsq)]
    have : -(↑k : ℝ) / 2 = -(↑k / 2 : ℝ) := by ring
    rw [this, Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * σsq), inv_inv]; ring

  calc ENNReal.ofReal ↑k *
        ∫⁻ t in Ioi (0:ℝ), μ {a | t < |X a|} * ENNReal.ofReal (t ^ ((↑k : ℝ) - 1))
      ≤ ENNReal.ofReal ↑k * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (g t) := by gcongr
    _ = ENNReal.ofReal ↑k * ENNReal.ofReal (∫ t in Ioi (0:ℝ), g t) := by rw [step3]
    _ = ENNReal.ofReal (↑k * ∫ t in Ioi (0:ℝ), g t) := by
        rw [← ENNReal.ofReal_mul hk_pos.le]
    _ = ENNReal.ofReal (↑k * (2 * ((1/(2*σsq)) ^ (-((↑k:ℝ)-1+1)/2) * (1/2) *
        Gamma (((↑k:ℝ)-1+1)/2)))) := by rw [step4]
    _ = ENNReal.ofReal ((2 * σsq) ^ ((↑k:ℝ) / 2) * ↑k * Gamma ((↑k:ℝ) / 2)) := by rw [step5]

/-- Auxiliary estimate used in the proof of Lemma 1.4: for integers `k ≥ 2`,
`Γ(k/2) ≤ (k/2)^{k/2}`. -/
theorem gamma_half_le_rpow (k : ℕ) (hk : 2 ≤ k) :
    Real.Gamma ((k : ℝ) / 2) ≤ ((k : ℝ) / 2) ^ ((k : ℝ) / 2) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
  match k, hk with
  | 2, _ =>
    have h2 : ((2:ℕ) : ℝ) / 2 = 1 := by norm_num
    rw [h2, Real.Gamma_one]; simp [rpow_one]
  | 3, _ =>
    have h3 : ((3:ℕ) : ℝ) / 2 = 3 / 2 := by norm_num
    rw [h3]
    have h1 : Real.Gamma (3/2 : ℝ) = (1/2) * Real.Gamma (1/2 : ℝ) := by
      rw [show (3:ℝ)/2 = 1/2 + 1 from by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [h1, Real.Gamma_one_half_eq]
    calc (1:ℝ)/2 * Real.sqrt Real.pi ≤ 1 := by
          have : Real.sqrt Real.pi ≤ 2 := by
            calc Real.sqrt Real.pi
                ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
              _ = 2 := by rw [show (4:ℝ) = 2^2 from by norm_num]
                          exact Real.sqrt_sq (by norm_num)
          linarith
      _ ≤ (3/2 : ℝ) ^ (3/2 : ℝ) := by
          rw [← one_rpow (3/2 : ℝ)]
          exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  | k + 4, _ =>
    have ih_prev := ih (k + 2) (by omega) (by omega)
    have hconv : (↑(k + 4) : ℝ) / 2 = (↑(k + 2) : ℝ) / 2 + 1 := by push_cast; ring
    rw [hconv]
    set x := (↑(k + 2) : ℝ) / 2 with hx_def
    have hx : 1 ≤ x := by
      rw [hx_def]
      have : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 2 k
      linarith
    have hx_pos : (0 : ℝ) < x := by linarith
    rw [Real.Gamma_add_one (by linarith : x ≠ 0)]
    calc x * Real.Gamma x
        ≤ x * x ^ x := by gcongr
      _ = x ^ (x + 1) := by rw [rpow_add hx_pos, rpow_one]; ring
      _ ≤ (x + 1) ^ (x + 1) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)

/-- Calculus lemma: `log x / x ≤ 1/e` for `x > 0`. Used in bounding
`k^{1/k}` for the kth-root moment estimate. -/
lemma log_div_le_inv_exp (x : ℝ) (hx : 0 < x) : Real.log x / x ≤ 1 / Real.exp 1 := by
  have he_pos : (0 : ℝ) < Real.exp 1 := exp_pos 1
  have h_key : Real.log x ≤ x / Real.exp 1 := by
    have h : Real.log (x / Real.exp 1) ≤ x / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hx he_pos)
    rw [Real.log_div hx.ne' he_pos.ne', Real.log_exp] at h
    linarith
  rw [div_le_div_iff₀ hx he_pos]
  calc Real.log x * Real.exp 1
      ≤ (x / Real.exp 1) * Real.exp 1 := by gcongr
    _ = x := by field_simp
    _ = 1 * x := by ring

/-- The bound `k^{1/k} ≤ exp(1/e)` for integers `k ≥ 2`, obtained from
`log x / x ≤ 1/e`. -/
theorem rpow_inv_le_exp_inv_exp (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) ^ ((k : ℝ)⁻¹) ≤ Real.exp (1 / Real.exp 1) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  rw [Real.rpow_def_of_pos hk_pos]
  apply Real.exp_le_exp_of_le
  rw [mul_comm, inv_mul_eq_div]
  exact log_div_le_inv_exp k hk_pos

/-- **Lemma 1.4 (kth root moment bound).** With the same sub-Gaussian-style
tail hypothesis, for `k ≥ 2`,
`(E[|X|^k])^{1/k} ≤ σ · exp(1/e) · √k`. -/
theorem kth_root_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (k : ℕ) (hk : 2 ≤ k)
    (hX : Measurable X)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | |X ω| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))) :
    (∫ ω, |X ω| ^ (k : ℕ) ∂μ) ^ ((k : ℝ)⁻¹) ≤ σ * Real.exp (1 / Real.exp 1) * Real.sqrt k := by
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hσsq : 0 < σ ^ 2 := sq_pos_of_pos hσ

  have htail' : ∀ t : ℝ, 0 < t → μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2))) := by
    intro t ht
    calc μ {ω | |X ω| > t}
        ≤ μ {ω | |X ω| ≥ t} := by
          apply measure_mono; intro ω hω; simp only [mem_setOf_eq] at *; exact le_of_lt hω
      _ ≤ _ := htail t ht.le

  have hlint := moment_bound hσsq hX.aestronglyMeasurable htail' k hk1

  have hf_nn : 0 ≤ᵐ[μ] fun ω => |X ω| ^ k := ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) _)
  have hf_meas : AEStronglyMeasurable (fun ω => |X ω| ^ k) μ := hX.aestronglyMeasurable.norm.pow k
  rw [integral_eq_lintegral_of_nonneg_ae hf_nn hf_meas]
  have hrw : (fun a : Ω => ENNReal.ofReal (|X a| ^ k)) = (fun a => ENNReal.ofReal (|X a| ^ (k:ℝ))) := by
    ext a; congr 1; exact (Real.rpow_natCast _ _).symm
  rw [hrw]
  set C := (2 * σ ^ 2) ^ ((k : ℝ) / 2) * ↑k * Real.Gamma (↑k / 2) with hC_def
  have hC_nn : 0 ≤ C := by positivity
  have hint_le : (∫⁻ (a : Ω), ENNReal.ofReal (|X a| ^ (↑k : ℝ)) ∂μ).toReal ≤ C :=
    ENNReal.toReal_le_of_le_ofReal hC_nn hlint

  have hkinv_nn : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
  calc (∫⁻ (a : Ω), ENNReal.ofReal (|X a| ^ (↑k : ℝ)) ∂μ).toReal ^ ((↑k : ℝ)⁻¹)
      ≤ C ^ ((↑k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hint_le hkinv_nn
    _ ≤ σ * Real.exp (1 / Real.exp 1) * Real.sqrt ↑k := by
        have hk_half_pos : (0 : ℝ) < (k : ℝ) / 2 := by positivity
        have hGamma := gamma_half_le_rpow k hk
        have hC_bound : C ≤ (2 * σ ^ 2) ^ ((k : ℝ) / 2) * (↑k * ((↑k / 2) ^ ((↑k : ℝ) / 2))) := by
          rw [hC_def, mul_assoc]; gcongr
        calc C ^ ((↑k : ℝ)⁻¹)
            ≤ ((2 * σ ^ 2) ^ ((k : ℝ) / 2) * (↑k * ((↑k / 2) ^ ((↑k : ℝ) / 2)))) ^ ((↑k : ℝ)⁻¹) :=
              Real.rpow_le_rpow (by positivity) hC_bound hkinv_nn
          _ = ((2 * σ ^ 2) ^ ((k : ℝ) / 2)) ^ ((↑k : ℝ)⁻¹) *
              (↑k * ((↑k / 2) ^ ((↑k : ℝ) / 2))) ^ ((↑k : ℝ)⁻¹) :=
              Real.mul_rpow (by positivity) (by positivity)
          _ = (2 * σ ^ 2) ^ ((1:ℝ) / 2) *
              (↑k * ((↑k / 2) ^ ((↑k : ℝ) / 2))) ^ ((↑k : ℝ)⁻¹) := by
              rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * σ ^ 2)]
              congr 1; field_simp
          _ = (2 * σ ^ 2) ^ ((1:ℝ) / 2) *
              ((↑k) ^ ((↑k : ℝ)⁻¹) * ((↑k / 2) ^ ((1:ℝ) / 2))) := by
              congr 1
              rw [Real.mul_rpow hk_pos.le (Real.rpow_nonneg (by positivity) _)]
              congr 1
              rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ↑k / 2)]
              congr 1; field_simp
          _ = σ * Real.sqrt 2 * ((↑k) ^ ((↑k : ℝ)⁻¹) * Real.sqrt (↑k / 2)) := by
              rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2),
                  Real.sqrt_sq hσ.le, ← Real.sqrt_eq_rpow]; ring
          _ = σ * (↑k) ^ ((↑k : ℝ)⁻¹) * Real.sqrt ↑k := by
              have h1 : Real.sqrt 2 * Real.sqrt (↑k / 2) = Real.sqrt ↑k := by
                rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2)]; congr 1; field_simp
              calc σ * Real.sqrt 2 * ((↑k : ℝ) ^ ((↑k : ℝ)⁻¹) * Real.sqrt (↑k / 2))
                  = σ * (↑k : ℝ) ^ ((↑k : ℝ)⁻¹) * (Real.sqrt 2 * Real.sqrt (↑k / 2)) := by ring
                _ = σ * (↑k : ℝ) ^ ((↑k : ℝ)⁻¹) * Real.sqrt ↑k := by rw [h1]
          _ ≤ σ * Real.exp (1 / Real.exp 1) * Real.sqrt ↑k := by
              gcongr; exact rpow_inv_le_exp_inv_exp k hk

/-- **Lemma 1.4 (first absolute moment).** For a variable with sub-Gaussian
tail bound at parameter `σ`, `E|X| ≤ σ · √(2π)`. -/
theorem first_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : Measurable X)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | |X ω| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))) :
    ∫ ω, |X ω| ∂μ ≤ σ * Real.sqrt (2 * Real.pi) := by

  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun ω => abs_nonneg _))
      hX.aestronglyMeasurable.norm]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)

  have hrw : (fun a => ENNReal.ofReal |X a|) = (fun a => ENNReal.ofReal (|X a| ^ (1:ℝ))) := by
    ext a; simp [rpow_one]
  rw [hrw]

  have htail' : ∀ t : ℝ, 0 < t → μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2))) := by
    intro t ht
    calc μ {ω | |X ω| > t}
        ≤ μ {ω | |X ω| ≥ t} := by
          apply measure_mono; intro ω hω; simp only [mem_setOf_eq] at *; exact le_of_lt hω
      _ ≤ _ := htail t ht.le

  have hbound := moment_bound (sq_pos_of_pos hσ) hX.aestronglyMeasurable htail' 1 le_rfl

  calc ∫⁻ (a : Ω), ENNReal.ofReal (|X a| ^ (1:ℝ)) ∂μ
      ≤ ENNReal.ofReal ((2 * σ ^ 2) ^ ((1:ℝ) / 2) * (1:ℝ) * Real.Gamma ((1:ℝ) / 2)) := by
        push_cast at hbound ⊢; exact hbound
    _ = ENNReal.ofReal (σ * Real.sqrt (2 * Real.pi)) := by
        congr 1
        rw [Real.Gamma_one_half_eq, mul_one, ← Real.sqrt_eq_rpow,
            Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2), Real.sqrt_sq hσ.le,
            show (2 : ℝ) * Real.pi = Real.pi * 2 by ring,
            Real.sqrt_mul (by positivity : (0:ℝ) ≤ Real.pi)]
        ring

/-- Combined statement of Lemma 1.4: the kth-root moment bound for `k ≥ 2`
together with the first absolute moment bound. -/
theorem subgaussian_moment_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : Measurable X)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | |X ω| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))) :
    (∀ k : ℕ, 2 ≤ k →
      (∫ ω, |X ω| ^ (k : ℕ) ∂μ) ^ ((k : ℝ)⁻¹) ≤ σ * Real.exp (1 / Real.exp 1) * Real.sqrt k) ∧
    (∫ ω, |X ω| ∂μ ≤ σ * Real.sqrt (2 * Real.pi)) :=
  ⟨fun k hk => kth_root_bound X σ hσ k hk hX htail,
   first_moment_bound X σ hσ hX htail⟩

end SubGaussianMoments

/-- **Lemma 1.4 (top-level statement).** Public re-export of the moment bound
`E[|X|^k] ≤ (2σ²)^{k/2} · k · Γ(k/2)` for variables with a sub-Gaussian-style
tail bound. -/
theorem lemma_1_4_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ} (hσ : 0 < σsq)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t → μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t^2 / (2 * σsq))))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (k : ℝ)) ∂μ ≤
      ENNReal.ofReal ((2 * σsq) ^ ((k : ℝ)/2) * k * Real.Gamma (k/2)) :=
  SubGaussianMoments.moment_bound hσ hX_meas hX_tail k hk
