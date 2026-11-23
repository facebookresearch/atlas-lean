/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Notation

open MeasureTheory
open scoped ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ} {τ : Ω → ℕ∞}

/-- Optional stopping inequality for submartingales: if `τ ≤ π` are stopping times with `π`
bounded by some constant `N`, then `E[f_τ] ≤ E[f_π]`. This is the monotonicity of expected
stopped values along bounded stopping times. -/
theorem Submartingale.expected_stoppedValue_mono_real
    {π : Ω → ℕ∞}
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := by
  rw [← sub_nonneg, ← integral_sub', stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have hmeas : ∀ i, MeasurableSet[𝒢 i] {ω : Ω | τ ω ≤ i ∧ ↑i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert (hπ i).compl using 1
      ext x
      simp; rfl
    rw [integral_finset_sum]
    · refine Finset.sum_nonneg fun i _ => ?_
      rw [integral_indicator (𝒢.le _ _ (hmeas _)), integral_sub', sub_nonneg]
      · exact hf.setIntegral_le (Nat.le_succ i) (hmeas _)
      · exact (hf.integrable _).integrableOn
      · exact (hf.integrable _).integrableOn
    · intro i _
      exact ((hf.integrable _).sub (hf.integrable _)).indicator
        (𝒢.le _ _ (hmeas _))
  · exact hf.integrable_stoppedValue hπ hbdd
  · exact hf.integrable_stoppedValue hτ (fun ω => (hle ω).trans (hbdd ω))

/-- Optional stopping inequality for supermartingales: if `τ` is a bounded stopping time and
`f` is a supermartingale, then `E[f_τ] ≤ E[f_0]`. Dual of the submartingale version, obtained
by negating. -/
theorem Supermartingale.expected_stoppedValue_le
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Supermartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue f τ] ≤ μ[f 0] := by
  have hsub : Submartingale (-f) 𝒢 μ := hf.neg
  have h0 : ∀ ω, (fun _ : Ω => (0 : ℕ∞)) ω ≤ τ ω := fun ω => zero_le _
  have key := hsub.expected_stoppedValue_mono_real (isStoppingTime_const 𝒢 0) hτ h0 hbdd
  simp only [stoppedValue_const] at key
  have eq1 : μ[stoppedValue (-f) τ] = -μ[stoppedValue f τ] := by
    simp only [integral_neg, stoppedValue, Pi.neg_apply]
  have eq2 : μ[(-f) 0] = -μ[f 0] := integral_neg _
  rw [eq1, eq2] at key
  linarith

end MeasureTheory
