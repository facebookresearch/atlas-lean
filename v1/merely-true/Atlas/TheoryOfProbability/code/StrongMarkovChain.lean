/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Atlas.TheoryOfProbability.code.StoppingTime
import Atlas.TheoryOfProbability.code.MarkovPropertyChain

open MeasureTheory ProbabilityTheory

/-- Shift a path `ω : ℕ → S` by the stopping time `T ω`: the resulting path at index `k`
is `ω (T ω + k)`. -/
def stoppedPathShift {S : Type*} (T : (ℕ → S) → ℕ) : (ℕ → S) → (ℕ → S) :=
  fun ω k => ω (T ω + k)

/-- On the event `{T ω = n}`, the stopping-time shift coincides with the fixed shift by
`n`: `stoppedPathShift T ω = shiftPath n ω`. -/
theorem stoppedPathShift_eq_shiftPath_on_eq {S : Type*}
    (T : (ℕ → S) → ℕ) (n : ℕ) (ω : ℕ → S) (h : T ω = n) :
    stoppedPathShift T ω = shiftPath n ω := by
  ext k
  simp [stoppedPathShift, shiftPath, h]

/-- If `f =ᵐ g` on each fiber `{T = n}` of an `ℕ`-valued measurable function `T`, then
`f =ᵐ g` on the whole space. -/
lemma ae_eq_of_ae_eq_restrict_fibers {Ω : Type*} {m0 : MeasurableSpace Ω}
    (T : Ω → ℕ) (μ : @Measure Ω m0)
    (f g : Ω → ℝ)
    (hT_meas : ∀ n, MeasurableSet {ω : Ω | T ω = n})
    (h : ∀ n, f =ᵐ[μ.restrict {ω | T ω = n}] g) :
    f =ᵐ[μ] g := by
  have hfiber : ∀ n, ∀ᵐ ω ∂μ, T ω = n → f ω = g ω := by
    intro n
    have hn := h n
    rw [Filter.EventuallyEq, ae_restrict_iff' (hT_meas n)] at hn
    exact hn
  suffices ∀ᵐ ω ∂μ, ∀ n, T ω = n → f ω = g ω by
    filter_upwards [this] with ω hω
    exact hω (T ω) rfl
  rw [ae_all_iff]
  exact hfiber

