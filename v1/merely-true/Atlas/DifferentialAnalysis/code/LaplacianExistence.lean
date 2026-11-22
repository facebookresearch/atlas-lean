/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.HormanderFundamental
import Atlas.DifferentialAnalysis.code.ConvolutionTheorem

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DifferentialOperators

variable {n : ℕ}












set_option maxHeartbeats 800000 in
/-- A smooth function `g` of polynomial growth defines a tempered distribution via integration:
there is a continuous linear functional on Schwartz space whose value at `φ` is `∫ φ • g`. -/
theorem tempered_distribution_of_polynomial_growth
    {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgrowth : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)) :
    ∃ u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        u_td φ = ∫ x, φ x • g x := by
  obtain ⟨Cg, k, hCg, hgrowth⟩ := hgrowth

  obtain ⟨P, hP⟩ := (Measure.HasTemperateGrowth.exists_integrable :
    ∃ P : ℕ, Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) ^ (-(P : ℝ))) volume)
  set m : ℕ × ℕ := (k + P, 0)

  let S (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :=
    (Finset.Iic m).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ

  have hg_rpow : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖g x‖ ≤ Cg * (1 + ‖x‖) ^ (k : ℝ) := by
    intro x
    have key : (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖x‖) ^ (k : ℝ) := by
      have h1 : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
      have h2 : 1 + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
      have h3 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      calc (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)
          ≤ ((1 + ‖x‖) ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_le_rpow h1 h2 h3
        _ = (1 + ‖x‖) ^ (k : ℝ) := by
            rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul (by positivity)]
            congr 1; push_cast; ring
    exact (hgrowth x).trans (mul_le_mul_of_nonneg_left key (le_of_lt hCg))

  have hphi_bound : ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (x : EuclideanSpace ℝ (Fin n)),
      ‖φ x‖ ≤ (1 + ‖x‖) ^ (-(↑(k + P) : ℝ)) * (2 ^ (k + P) * S φ) := by
    intro φ x
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖x‖), Real.rpow_natCast,
        ← div_eq_inv_mul, le_div_iff₀' (by positivity : (0:ℝ) < (1 + ‖x‖) ^ (k+P))]
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := m) (k := k + P) (n := 0)
      le_rfl le_rfl φ x
    simpa [norm_iteratedFDeriv_zero] using h

  have hcombined : ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (x : EuclideanSpace ℝ (Fin n)),
      ‖φ x • g x‖ ≤ (Cg * 2 ^ (k + P) * S φ) * (1 + ‖x‖) ^ (-(P : ℝ)) := by
    intro φ x
    rw [norm_smul]
    have hbase : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have hrpow_eq : (1 + ‖x‖) ^ (-(↑(k + P) : ℝ)) * (1 + ‖x‖) ^ (k : ℝ) =
        (1 + ‖x‖) ^ (-(P : ℝ)) := by
      rw [← Real.rpow_add hbase]; congr 1; push_cast; ring
    calc ‖φ x‖ * ‖g x‖
        ≤ ((1 + ‖x‖) ^ (-(↑(k + P) : ℝ)) * (2 ^ (k + P) * S φ)) *
          (Cg * (1 + ‖x‖) ^ (k : ℝ)) := by
          gcongr; exact hphi_bound φ x; exact hg_rpow x
      _ = (Cg * 2 ^ (k + P) * S φ) * (1 + ‖x‖) ^ (-(P : ℝ)) := by
          linear_combination (Cg * 2 ^ (k + P) * S φ) * hrpow_eq

  have hint : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      Integrable (fun x => φ x • g x) volume := by
    intro φ
    apply (hP.const_mul _).mono
      (φ.continuous.smul hsmooth.continuous).aestronglyMeasurable
    apply ae_of_all; intro x
    exact (hcombined φ x).trans (le_abs_self _)

  refine ⟨SchwartzMap.mkCLMtoNormedSpace (fun φ => ∫ x, φ x • g x) ?_ ?_ ?_, fun φ => rfl⟩

  · intro f f'
    simp only [SchwartzMap.add_apply, add_smul]
    exact integral_add (hint f) (hint f')

  · intro a f
    simp only [SchwartzMap.smul_apply, smul_assoc, RingHom.id_apply]
    exact integral_smul a _

  · refine ⟨Finset.Iic m, Cg * 2 ^ (k + P) *
      ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) ^ (-(P : ℝ)),
      by positivity, fun f => ?_⟩
    have hSf : S f = (Finset.Iic m).sup (schwartzSeminormFamily ℂ _ ℂ) f := rfl
    calc ‖∫ x, f x • g x‖
        ≤ ∫ x, ‖f x • g x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n),
            (Cg * 2 ^ (k + P) * S f) * (1 + ‖x‖) ^ (-(P : ℝ)) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ (fun x => norm_nonneg _))
            (hP.const_mul _)
            (ae_of_all _ (fun x => hcombined f x))
      _ = (Cg * 2 ^ (k + P) *
            ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) ^ (-(P : ℝ))) * S f := by
          rw [integral_const_mul]; ring
      _ = (Cg * 2 ^ (k + P) *
            ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) ^ (-(P : ℝ))) *
            (Finset.Iic m).sup (schwartzSeminormFamily ℂ _ ℂ) f := by
          rw [hSf]



end DifferentialOperators
