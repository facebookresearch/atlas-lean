/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevEmbedding
open scoped ZeroAtInfty SchwartzMap

noncomputable section

namespace SobolevEmbedding

/-- Any natural power of the Japanese bracket is a nonzero complex number,
since `⟨x⟩ ≥ 1 > 0`. -/
theorem japaneseBracket_pow_ne_zero_complex {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_pos (TestFunctions.japaneseBracket_pos n x) k).ne'

/-- Multiplying a Schwartz function by any natural power of the Japanese
bracket again gives a Schwartz function, with the prescribed pointwise
formula.  Uses the fact that `⟨x⟩^k` has temperate growth. -/
def schwartz_mul_japaneseBracket_pow {n k : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    { g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) //
      ∀ x, g x = (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * f x } := by

  set φ : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun x => (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) with hφ_def

  have hφ : Function.HasTemperateGrowth φ := by
    simp only [hφ_def, TestFunctions.japaneseBracket]

    have h1 : (fun x : EuclideanSpace ℝ (Fin n) =>
        (↑((Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) : ℂ)) =
      Complex.ofReal ∘ (fun x => (Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) := by
      ext x; simp
    rw [h1]
    apply Function.Complex.hasTemperateGrowth_ofReal.comp

    have h2 : (fun x : EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) =
      (fun x => (1 + ‖x‖ ^ 2) ^ (k / 2 : ℝ)) := by
      ext x
      have hpos : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hpos]
      ring_nf
    rw [h2]
    exact Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _

  exact ⟨SchwartzMap.smulLeftCLM ℂ φ f, fun x => by
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ]
    exact smul_eq_mul (φ x) (f x)⟩

open MeasureTheory in
/-- Every iterated Fréchet derivative of a Schwartz function lies in `L²` with
respect to Lebesgue measure on `ℝⁿ`. -/
theorem schwartz_iteratedFDeriv_memLp {n : ℕ}
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (j : ℕ) :
    MemLp (fun x => iteratedFDeriv ℝ j (⇑g) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  set_option synthInstance.maxHeartbeats 80000 in
  rw [memLp_two_iff_integrable_sq_norm
    ((g.smooth (j : ℕ∞)).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable]

  obtain ⟨C, hCpos, hC⟩ := g.decay 0 j
  simp only [pow_zero, one_mul] at hC

  have hint := g.integrable_pow_mul_iteratedFDeriv volume 0 j
  simp only [pow_zero, one_mul] at hint

  apply Integrable.mono (hint.const_mul C)
  · set_option synthInstance.maxHeartbeats 80000 in
    exact (((g.smooth (j : ℕ∞)).continuous_iteratedFDeriv le_rfl).norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [norm_mul, Real.norm_of_nonneg hCpos.le, Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖iteratedFDeriv ℝ j (⇑g) x‖ ^ 2
        = ‖iteratedFDeriv ℝ j (⇑g) x‖ * ‖iteratedFDeriv ℝ j (⇑g) x‖ := sq _
      _ ≤ C * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by gcongr; exact hC x

end SobolevEmbedding

end
