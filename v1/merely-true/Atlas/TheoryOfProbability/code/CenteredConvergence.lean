/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Integration

set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory Filter Finset ENNReal

noncomputable section

namespace KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- On a probability space, the `L¹` norm is dominated by the `L²` norm:
`‖f‖₁ ≤ ‖f‖₂`. -/
lemma eLpNorm_one_le_two {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf
  simp only [measure_univ, one_rpow, mul_one] at h
  exact h

set_option maxHeartbeats 800000 in
/-- If `∫ ‖f‖² dμ ≤ C` for an `L²` function on a probability space, then
`‖f‖₁ ≤ √C`. -/
lemma eLpNorm_one_le_sqrt_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) {C : ℝ}
    (h_int_sq : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ ≤ C) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  have h1 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := eLpNorm_one_le_two hf.aestronglyMeasurable
  have h2 : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply ENNReal.ofReal_le_ofReal
    simp only [ENNReal.toReal_ofNat]
    rw [Real.sqrt_eq_rpow]
    show (∫ (a : Ω), ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ ≤ C ^ ((1 : ℝ) / 2)
    rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 from by norm_num]
    exact Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) h_int_sq (by norm_num)
  exact h1.trans h2

set_option linter.unusedSectionVars false in

set_option maxHeartbeats 6400000 in
/-- Key step toward the Kolmogorov three-series theorem: if the `Zₙ` are independent
centered (mean zero) integrable random variables whose partial sums `Sₙ = ∑_{k≤n} Zₖ`
are uniformly bounded in `L¹`, then `Sₙ` converges almost surely. This is proved by
realizing `Sₙ` as a martingale and applying the `L¹`-bounded martingale convergence
theorem. -/
theorem ae_tendsto_sum_of_indep_centered_L1bdd {Z : ℕ → Ω → ℝ}
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hZ_indep : iIndepFun (m := fun _ => inferInstance) Z μ)
    (hZ_mean : ∀ n, ∫ ω, Z n ω ∂μ = 0)
    (hZ_int : ∀ n, Integrable (Z n) μ)
    {R : NNReal}
    (hZ_L1_bdd : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤ ↑R) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ k ∈ range (n + 1), Z k ω) atTop (nhds c) := by
  set ℱ := Filtration.natural (β := fun _ : ℕ => ℝ) Z hZ_sm
  have sum_eq : ∀ n, (fun ω => ∑ k ∈ range (n + 1), Z k ω) = ∑ k ∈ range (n + 1), Z k := by
    intro n; ext ω; simp [Finset.sum_apply]
  have hS_int : ∀ n, Integrable (fun ω => ∑ k ∈ range (n + 1), Z k ω) μ := fun n =>
    integrable_finset_sum _ (fun k _ => hZ_int k)
  have hS_sm_m : ∀ n, StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ range (n + 1), Z k ω) := by
    intro n; rw [sum_eq]
    exact stronglyMeasurable_sum _ (fun k hk => by
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      exact (Filtration.stronglyAdapted_natural hZ_sm k).mono (ℱ.mono hkn))
  have hS_mart : Martingale (fun n ω => ∑ k ∈ range (n + 1), Z k ω) ℱ μ := by
    apply martingale_nat (fun n => hS_sm_m n) hS_int
    intro i
    have heq_add : (fun ω => ∑ k ∈ range (i + 2), Z k ω) =
        (fun ω => ∑ k ∈ range (i + 1), Z k ω) + Z (i + 1) := by
      ext ω; simp [sum_range_succ, Pi.add_apply]
    rw [heq_add]
    have hce := condExp_add (hS_int i) (hZ_int (i + 1)) (ℱ i : MeasurableSpace Ω)
    have hSi_ce : μ[fun ω => ∑ k ∈ range (i + 1), Z k ω | (ℱ i : MeasurableSpace Ω)] =
        fun ω => ∑ k ∈ range (i + 1), Z k ω :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hS_sm_m i) (hS_int i)
    have hZi1_ce : μ[Z (i + 1) | (ℱ i : MeasurableSpace Ω)] =ᵐ[μ] fun _ => (0 : ℝ) := by
      have h := hZ_indep.condExp_natural_ae_eq_of_lt hZ_sm (show i < i + 1 by omega)
      simpa [hZ_mean (i + 1)] using h
    filter_upwards [hce, hZi1_ce] with ω hω1 hω3
    simp only [Pi.add_apply] at hω1
    rw [hSi_ce] at hω1
    linarith
  exact hS_mart.submartingale.exists_ae_tendsto_of_bdd (R := R) hZ_L1_bdd

end KolmogorovThreeSeries
