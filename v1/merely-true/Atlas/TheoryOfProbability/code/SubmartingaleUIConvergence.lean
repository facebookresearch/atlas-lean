/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.TFAE

open scoped MeasureTheory NNReal ENNReal Topology
open MeasureTheory Filter

noncomputable section

/-- Translates `L¹` convergence in the `eLpNorm` formulation to convergence of the real-valued
`L¹` integrals `∫ ‖f n - g‖ dμ → 0`. -/
lemma tendsto_integral_norm_zero_of_tendsto_eLpNorm
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hint : ∀ n, Integrable (f n - g) μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, ‖f n ω - g ω‖ ∂μ) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (h (ENNReal.ofReal (ε / 2)) (by positivity)).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have hstep := hN n hn
  rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hint n)] at hstep
  have hle := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hstep
  have : (fun ω : Ω => ‖f n ω - g ω‖) = fun x => ‖(f n - g) x‖ := by
    ext; simp [Pi.sub_apply]
  simp_rw [this]; linarith

/-- Converse of `tendsto_integral_norm_zero_of_tendsto_eLpNorm`: convergence of
`∫ ‖f n - g‖ dμ → 0` upgrades to `eLpNorm (f n - g) 1 μ → 0`. -/
lemma tendsto_eLpNorm_of_tendsto_integral_norm_zero
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hint : ∀ n, Integrable (f n - g) μ)
    (h : Tendsto (fun n => ∫ ω, ‖f n ω - g ω‖ ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0) := by
  have heq : (fun n => eLpNorm (f n - g) 1 μ) =
      (fun n => ENNReal.ofReal (∫ ω, ‖f n ω - g ω‖ ∂μ)) := by
    ext n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    congr 1
  rw [heq, show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from by simp]
  exact ENNReal.tendsto_ofReal h

/-- If `f n → g` in `L¹` (in `eLpNorm` form) and `g` is integrable, then the family
`f n` is uniformly `L¹`-bounded by some constant `C : ℝ≥0`. -/
lemma eLpNorm_bound_of_L1_tendsto
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0)) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) 1 μ ≤ C := by
  rw [ENNReal.tendsto_nhds_zero] at hL1
  obtain ⟨N, hN⟩ := (hL1 1 one_pos).exists_forall_of_atTop
  set Ctail : ℝ≥0 := 1 + (eLpNorm g 1 μ).toNNReal
  set Cinit : ℝ≥0 := (Finset.range N).sup fun n => (eLpNorm (f n) 1 μ).toNNReal
  refine ⟨Cinit ⊔ Ctail, fun i => ?_⟩
  by_cases hi : i < N
  · calc eLpNorm (f i) 1 μ
        = ↑((eLpNorm (f i) 1 μ).toNNReal) := (ENNReal.coe_toNNReal (hf i).2.ne).symm
      _ ≤ ↑Cinit := ENNReal.coe_le_coe.mpr
          (Finset.le_sup (f := fun n => (eLpNorm (f n) 1 μ).toNNReal)
            (Finset.mem_range.mpr hi))
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_left
  · simp only [not_lt] at hi
    calc eLpNorm (f i) 1 μ
        = eLpNorm ((f i - g) + g) 1 μ := by ring_nf
      _ ≤ eLpNorm (f i - g) 1 μ + eLpNorm g 1 μ :=
          eLpNorm_add_le ((hf i).1.sub hg.1) hg.1 le_rfl
      _ ≤ 1 + eLpNorm g 1 μ := by gcongr; exact hN i hi
      _ = ↑(1 : ℝ≥0) + ↑((eLpNorm g 1 μ).toNNReal) := by
          rw [ENNReal.coe_toNNReal hg.2.ne, ENNReal.coe_one]
      _ = ↑Ctail := by push_cast; rfl
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_right

/-- **Submartingale convergence theorem.** For a submartingale `X` on a probability space, the
following are equivalent:
1. `X` is uniformly integrable.
2. There exists an integrable `X_∞` such that `X_n → X_∞` almost surely and in `L¹` (in the
   `∫ ‖X n - X_∞‖` sense).
3. There exists an integrable `X_∞` such that `X_n → X_∞` in `L¹`. -/
theorem submartingale_ui_convergence_equiv
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0}
    {X : ℕ → Ω → ℝ}
    (hsub : MeasureTheory.Submartingale X ℱ μ) :
    List.TFAE [
      MeasureTheory.UniformIntegrable X 1 μ,
      ∃ X_inf, MeasureTheory.Integrable X_inf μ ∧
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop (nhds (X_inf ω))) ∧
        Filter.Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) Filter.atTop (nhds 0),
      ∃ X_inf, MeasureTheory.Integrable X_inf μ ∧
        Filter.Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) Filter.atTop (nhds 0)
    ] := by

  tfae_have 1 → 2 := by
    intro hUI
    obtain ⟨R, hR⟩ := hUI.2.2
    have hmeas : ∀ n, AEStronglyMeasurable (X n) μ := hUI.1
    set X_inf := ℱ.limitProcess X μ
    have hint_lim : Integrable X_inf μ :=
      (Filtration.memLp_limitProcess_of_eLpNorm_bdd hmeas hR).integrable le_rfl
    have hae := hsub.ae_tendsto_limitProcess_of_uniformIntegrable hUI
    have hL1 := hsub.tendsto_eLpNorm_one_limitProcess hUI
    exact ⟨X_inf, hint_lim, hae,
      tendsto_integral_norm_zero_of_tendsto_eLpNorm
        (fun n => (hsub.integrable n).sub hint_lim) hL1⟩

  tfae_have 2 → 3 := by
    rintro ⟨X_inf, hint, _, hL1⟩
    exact ⟨X_inf, hint, hL1⟩

  tfae_have 3 → 1 := by
    rintro ⟨X_inf, hint, hL1⟩
    have hMemLp_n : ∀ n, MemLp (X n) 1 μ := fun n =>
      memLp_one_iff_integrable.mpr (hsub.integrable n)
    have hMemLp_inf : MemLp X_inf 1 μ := memLp_one_iff_integrable.mpr hint
    have hint_sub : ∀ n, Integrable (X n - X_inf) μ := fun n =>
      (hsub.integrable n).sub hint
    have heLpNorm := tendsto_eLpNorm_of_tendsto_integral_norm_zero hint_sub hL1
    exact ⟨fun n => (hMemLp_n n).1,
      unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hMemLp_n hMemLp_inf heLpNorm,
      eLpNorm_bound_of_L1_tendsto hMemLp_n hMemLp_inf heLpNorm⟩
  tfae_finish

end
