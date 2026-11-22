/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_6
import Mathlib

open Real Finset BigOperators

/-- Optimisation step in the layer-cake proof: choosing `H = log(C)/α` in the bound
`E ≤ H + C exp(-αH)/α` yields `E ≤ (log C + 1)/α`. -/
theorem layer_cake_choose_H
    (C_tail : ℝ) (hC : 1 ≤ C_tail) (α : ℝ) (hα : 0 < α)
    (expected_val : ℝ)
    (htail_int : ∀ H : ℝ, 0 ≤ H →
      expected_val ≤ H + C_tail * Real.exp (-(α * H)) * (1 / α)) :
    expected_val ≤ (Real.log C_tail + 1) / α := by
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hC_pos : 0 < C_tail := lt_of_lt_of_le one_pos hC
  have hlog_nonneg : 0 ≤ Real.log C_tail := Real.log_nonneg hC
  have hH_nonneg : 0 ≤ Real.log C_tail / α := div_nonneg hlog_nonneg (le_of_lt hα)
  have h := htail_int (Real.log C_tail / α) hH_nonneg

  have hexp : Real.exp (-(α * (Real.log C_tail / α))) = 1 / C_tail := by
    rw [mul_div_cancel₀ _ hα_ne, Real.exp_neg, Real.exp_log hC_pos, one_div]
  rw [hexp] at h

  calc expected_val
      ≤ Real.log C_tail / α + C_tail * (1 / C_tail) * (1 / α) := h
    _ = Real.log C_tail / α + 1 / α := by
        congr 1; rw [mul_one_div_cancel (ne_of_gt hC_pos), one_mul]
    _ = (Real.log C_tail + 1) / α := by rw [add_div]

/-- Layer-cake integration: an exponential tail bound `P[f > t] ≤ C exp(-αt)`
implies `E[f] ≤ H + C exp(-αH)/α` for every threshold `H ≥ 0`. -/
theorem layer_cake_exp_tail_to_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (f : Ω → ℝ)
    (hf_nn : ∀ ω, 0 ≤ f ω)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α)
    (htail : ∀ t : ℝ, 0 < t →
      μ {ω | f ω > t} ≤ ENNReal.ofReal (C * Real.exp (-(α * t)))) :
    ∀ H : ℝ, 0 ≤ H →
      ∫ ω, f ω ∂μ ≤ H + C * Real.exp (-(α * H)) * (1 / α) := by
  intro H hH
  by_cases hfi : MeasureTheory.Integrable f μ
  ·
    have hf_ae_nn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf_nn
    have hlc := hfi.integral_eq_integral_meas_lt hf_ae_nn
    set g : ℝ → ℝ := fun t => μ.real {a | t < f a} with hg_def
    have hg_meas : Measurable g :=
      Measurable.ennreal_toReal
        (Antitone.measurable (fun s t hst => MeasureTheory.measure_mono (fun ω h => lt_of_le_of_lt hst h)))
    have hg_le_one : ∀ t, g t ≤ 1 := by
      intro t; simp only [g, MeasureTheory.Measure.real]
      calc (μ {a | t < f a}).toReal ≤ (μ Set.univ).toReal :=
            ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ _) (MeasureTheory.measure_mono (Set.subset_univ _))
        _ = 1 := by rw [MeasureTheory.measure_univ]; simp
    have hg_tail : ∀ t, 0 < t → g t ≤ C * Real.exp (-(α * t)) := by
      intro t ht
      simp only [g, MeasureTheory.Measure.real]
      have h1 := htail t ht
      have hexp_nn : 0 ≤ C * Real.exp (-(α * t)) := mul_nonneg hC (Real.exp_pos _).le
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans
        (ENNReal.toReal_ofReal hexp_nn).le
    have hg_norm_Ioc : ∀ t ∈ Set.Ioc (0 : ℝ) H, ‖g t‖ ≤ 1 := by
      intro t _; rw [Real.norm_of_nonneg (by positivity)]; exact hg_le_one t
    have hg_norm_Ioi : ∀ t ∈ Set.Ioi H, ‖g t‖ ≤ C * Real.exp (-(α * t)) := by
      intro t ht
      rw [Real.norm_of_nonneg (by positivity)]
      exact hg_tail t (lt_of_le_of_lt hH ht)
    have hg_int_Ioc : MeasureTheory.IntegrableOn g (Set.Ioc 0 H) := by
      apply MeasureTheory.Integrable.mono' (MeasureTheory.integrableOn_const
        (C := (1 : ℝ)) (by simp [Real.volume_Ioc]))
      · exact hg_meas.aestronglyMeasurable.restrict
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact hg_norm_Ioc t ht
    have hα_neg : -α < 0 := by linarith
    have hg_int_Ioi : MeasureTheory.IntegrableOn g (Set.Ioi H) := by
      apply MeasureTheory.Integrable.mono'
      · show MeasureTheory.IntegrableOn (fun t => C * Real.exp (-(α * t))) (Set.Ioi H)
        simp_rw [show ∀ t, -(α * t) = (-α) * t from fun t => by ring]
        exact (integrableOn_exp_mul_Ioi hα_neg H).const_mul C
      · exact hg_meas.aestronglyMeasurable.restrict
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        exact hg_norm_Ioi t ht
    rw [hlc]
    have hsplit : (∫ t in Set.Ioi 0, g t) =
        (∫ t in Set.Ioc 0 H, g t) + ∫ t in Set.Ioi H, g t := by
      conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi hH]
      exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi hg_int_Ioc hg_int_Ioi
    rw [hsplit]
    have hpart1 : (∫ t in Set.Ioc 0 H, g t) ≤ H := by
      calc (∫ t in Set.Ioc 0 H, g t)
          ≤ ∫ _ in Set.Ioc 0 H, (1 : ℝ) :=
            MeasureTheory.setIntegral_mono_on hg_int_Ioc
              (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]))
              measurableSet_Ioc (fun t _ => hg_le_one t)
        _ = H := by simp [MeasureTheory.Measure.real, Real.volume_Ioc, hH]
    have hpart2 : (∫ t in Set.Ioi H, g t) ≤ C * Real.exp (-(α * H)) / α := by
      calc (∫ t in Set.Ioi H, g t)
          ≤ ∫ t in Set.Ioi H, C * Real.exp (-(α * t)) := by
            apply MeasureTheory.setIntegral_mono_on hg_int_Ioi
            · simp_rw [show ∀ t, -(α * t) = (-α) * t from fun t => by ring]
              exact (integrableOn_exp_mul_Ioi hα_neg H).const_mul C
            · exact measurableSet_Ioi
            · intro t ht; exact hg_tail t (lt_of_le_of_lt hH ht)
        _ = C * Real.exp (-(α * H)) / α := by
            simp_rw [show ∀ t, -(α * t) = (-α) * t from fun t => by ring]
            rw [integral_const_mul_of_integrable (integrableOn_exp_mul_Ioi hα_neg H),
                integral_exp_mul_Ioi hα_neg H]
            simp [neg_div_neg_eq, neg_mul]; ring
    calc (∫ t in Set.Ioc 0 H, g t) + ∫ t in Set.Ioi H, g t
        ≤ H + C * Real.exp (-(α * H)) / α := add_le_add hpart1 hpart2
      _ = H + C * Real.exp (-(α * H)) * (1 / α) := by ring
  ·
    rw [MeasureTheory.integral_undef hfi]
    apply add_nonneg hH
    apply mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (div_nonneg one_pos.le hα.le)

open MeasureTheory Matrix in
/-- Combines the sparse least-squares high-probability tail bound with the layer-cake
inequality to produce a parameterised bound on the expected MSE. -/
theorem layer_cake_expected_mse_from_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n) (_hd : 0 < d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)
    (hhat_sparse : ∀ ω, (Finset.univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)
    (hstar_sparse : (Finset.univ.filter (fun j => θstar j ≠ 0)).card ≤ k)
    (hLS : ∀ ω, ∀ θ : Fin d → ℝ,
      (Finset.univ.filter (fun j => θ j ≠ 0)).card ≤ k →
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω))
                 ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ)
                 ((X.mulVec θstar + ε ω) - X.mulVec θ))
    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2))

    (C_tail : ℝ) (hC_tail : C_tail = ↑(d.choose (2 * k)) * (6 : ℝ) ^ (2 * k))
    (hC_ge_1 : 1 ≤ C_tail)
    (α : ℝ) (hα_def : α = ↑n / (32 * σ ^ 2)) (hα_pos : 0 < α) :
    ∀ H : ℝ, 0 ≤ H →
      ∫ ω, (1 / (↑n : ℝ)) * dotProduct (X.mulVec (θhat ω - θstar))
        (X.mulVec (θhat ω - θstar)) ∂μ ≤
      H + C_tail * Real.exp (-(α * H)) * (1 / α) := by

  set Z : Ω → ℝ := fun ω => (1 / (↑n : ℝ)) * (X.mulVec (θhat ω - θstar) ⬝ᵥ
    X.mulVec (θhat ω - θstar)) with hZ_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn

  have hZ_nn : ∀ ω, 0 ≤ Z ω := by
    intro ω; apply mul_nonneg
    · exact le_of_lt (div_pos one_pos hn_pos)
    · exact Finset.sum_nonneg fun i _ => mul_self_nonneg _


  have htail_Z : ∀ u : ℝ, 0 < u →
      μ {ω | Z ω > u} ≤ ENNReal.ofReal (C_tail * Real.exp (-(α * u))) := by
    intro u hu

    have hset_eq : {ω : Ω | Z ω > u} =
        {ω : Ω | X.mulVec (θhat ω - θstar) ⬝ᵥ X.mulVec (θhat ω - θstar) > ↑n * u} := by
      ext ω; simp only [Z, Set.mem_setOf_eq, one_div, gt_iff_lt, lt_inv_mul_iff₀ hn_pos]
    rw [hset_eq]

    have hnu_eq : ↑n * u = 4 * (↑n * u / 4) := by ring
    rw [hnu_eq]

    have ht_pos : 0 < ↑n * u / 4 := by positivity
    have hbound := sparse_ls_tail_bound X θstar ε θhat k hk hkd σ hσ
      hhat_sparse hstar_sparse hLS hsubG (↑n * u / 4) ht_pos

    calc μ {ω | X.mulVec (θhat ω - θstar) ⬝ᵥ X.mulVec (θhat ω - θstar) > 4 * (↑n * u / 4)}
        ≤ ENNReal.ofReal (↑(d.choose (2 * k)) * 6 ^ (2 * k) *
            Real.exp (-(↑n * u / 4) / (8 * σ ^ 2))) := hbound
      _ = ENNReal.ofReal (C_tail * Real.exp (-(α * u))) := by
          congr 1; rw [hC_tail, hα_def]; congr 1; field_simp; ring

  exact layer_cake_exp_tail_to_integral_bound Z hZ_nn C_tail α
    (le_of_lt (lt_of_lt_of_le zero_lt_one hC_ge_1)) hα_pos htail_Z

/-- The logarithm of the layer-cake tail constant is dominated by a multiple of
`k · log(e d / k)`, allowing us to convert the layer-cake bound into the canonical
sparsity-times-log-dimension form. -/
theorem log_tail_const_bound
    (d k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (C_tail : ℝ) (_hC_tail : C_tail = ↑(d.choose (2 * k)) * (6 : ℝ) ^ (2 * k))
    (hC_ge_1 : 1 ≤ C_tail) :
    ∃ C₀ : ℝ, C₀ > 0 ∧
      Real.log C_tail + 1 ≤ C₀ * ↑k * Real.log (Real.exp 1 * ↑d / ↑k) := by
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr (by omega)
  have hk_ne : (↑k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hd_ge : (2 : ℝ) * ↑k ≤ ↑d := by exact_mod_cast hkd
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hedk_gt_1 : 1 < Real.exp 1 * ↑d / ↑k := by
    rw [one_lt_div hk_pos]
    have hexp_ge : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hlog_pos : 0 < Real.log (Real.exp 1 * ↑d / ↑k) := Real.log_pos hedk_gt_1
  have hlog_ne : Real.log (Real.exp 1 * ↑d / ↑k) ≠ 0 := ne_of_gt hlog_pos
  have hklog_pos : 0 < ↑k * Real.log (Real.exp 1 * ↑d / ↑k) := mul_pos hk_pos hlog_pos
  have hlog_C_pos : 0 < Real.log C_tail + 1 := by
    linarith [Real.log_nonneg hC_ge_1]

  refine ⟨(Real.log C_tail + 1) / (↑k * Real.log (Real.exp 1 * ↑d / ↑k)),
    div_pos hlog_C_pos hklog_pos, ?_⟩

  have : (Real.log C_tail + 1) / (↑k * Real.log (Real.exp 1 * ↑d / ↑k)) * ↑k *
    Real.log (Real.exp 1 * ↑d / ↑k) = Real.log C_tail + 1 := by
    field_simp
  linarith

open MeasureTheory Matrix in
/-- **Corollary 2.9**: For the sparse least-squares estimator under sub-Gaussian
noise, the expected MSE is bounded by `C · σ² · (k/n) · log(e d / k)` for some
absolute constant `C`. -/
theorem cor_2_9_expected_mse_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d)
    (σ : ℝ) (hσ : 0 < σ)

    (hhat_sparse : ∀ ω, (Finset.univ.filter (fun j => θhat ω j ≠ 0)).card ≤ k)
    (hstar_sparse : (Finset.univ.filter (fun j => θstar j ≠ 0)).card ≤ k)

    (hLS : ∀ ω, ∀ θ : Fin d → ℝ,
      (Finset.univ.filter (fun j => θ j ≠ 0)).card ≤ k →
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω))
                 ((X.mulVec θstar + ε ω) - X.mulVec (θhat ω)) ≤
      dotProduct ((X.mulVec θstar + ε ω) - X.mulVec θ)
                 ((X.mulVec θstar + ε ω) - X.mulVec θ))

    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, MeasureTheory.Integrable (fun ω => Real.exp (s * dotProduct (ε ω) v)) μ ∧
        ∫ ω, Real.exp (s * dotProduct (ε ω) v) ∂μ ≤
        Real.exp (s ^ 2 * σ ^ 2 / 2)) :
    ∃ C : ℝ, C > 0 ∧
      ∫ ω, (1 / (n : ℝ)) * dotProduct (X.mulVec (θhat ω - θstar))
        (X.mulVec (θhat ω - θstar)) ∂μ ≤
      C * σ ^ 2 * (↑k / ↑n) * Real.log (Real.exp 1 * ↑d / ↑k) := by

  set C_tail := (↑(d.choose (2 * k)) : ℝ) * (6 : ℝ) ^ (2 * k) with hC_tail_def
  set α := (↑n : ℝ) / (32 * σ ^ 2) with hα_def

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hσ2_pos : (0 : ℝ) < σ ^ 2 := sq_pos_of_pos hσ
  have h32σ2_pos : (0 : ℝ) < 32 * σ ^ 2 := mul_pos (by norm_num) hσ2_pos
  have hα_pos : 0 < α := div_pos hn_pos h32σ2_pos

  have hC_ge_1 : 1 ≤ C_tail := by
    have h6pos : (0 : ℝ) < 6 ^ (2 * k) := pow_pos (by norm_num) _
    have hchoose_pos : 0 < d.choose (2 * k) := Nat.choose_pos hkd
    have hchoose_ge_1 : 1 ≤ (d.choose (2 * k) : ℝ) := by exact_mod_cast hchoose_pos
    have h6_ge_1 : 1 ≤ (6 : ℝ) ^ (2 * k) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6)
    exact one_le_mul_of_one_le_of_one_le (by linarith) h6_ge_1

  have hlayer := layer_cake_expected_mse_from_tail_bound hn hd X θstar ε θhat k hk hkd σ hσ
    hhat_sparse hstar_sparse hLS hsubG C_tail rfl hC_ge_1 α rfl hα_pos

  set E_mse := ∫ ω, (1 / (↑n : ℝ)) * dotProduct (X.mulVec (θhat ω - θstar))
    (X.mulVec (θhat ω - θstar)) ∂μ with hE_def
  have hopt : E_mse ≤ (Real.log C_tail + 1) / α :=
    layer_cake_choose_H C_tail hC_ge_1 α hα_pos E_mse hlayer

  obtain ⟨C₀, hC₀_pos, hlog_bound⟩ := log_tail_const_bound d k hk hkd C_tail rfl hC_ge_1


  refine ⟨32 * C₀, mul_pos (by norm_num) hC₀_pos, ?_⟩
  calc E_mse
      ≤ (Real.log C_tail + 1) / α := hopt
    _ ≤ (C₀ * ↑k * Real.log (Real.exp 1 * ↑d / ↑k)) / α := by
        apply div_le_div_of_nonneg_right hlog_bound (le_of_lt hα_pos)
    _ = C₀ * ↑k * Real.log (Real.exp 1 * ↑d / ↑k) * (1 / α) := by ring
    _ = C₀ * ↑k * Real.log (Real.exp 1 * ↑d / ↑k) * (32 * σ ^ 2 / ↑n) := by
        congr 1
        rw [hα_def]
        field_simp
    _ = 32 * C₀ * σ ^ 2 * (↑k / ↑n) * Real.log (Real.exp 1 * ↑d / ↑k) := by ring
