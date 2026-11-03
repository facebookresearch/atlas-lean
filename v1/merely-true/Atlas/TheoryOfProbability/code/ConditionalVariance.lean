/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CondVar
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Filter

noncomputable section

section AlternativeFormula

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- **Alternative formula for conditional variance.**

For an `L²` random variable `X`, the conditional variance equals
`Var(X | m) = E[X² | m] − (E[X | m])²` almost everywhere. This is the conditional
analogue of the identity `Var(X) = E[X²] − (EX)²`. -/
theorem condVar_eq_condExp_sq_sub_sq_condExp' (hm : m ≤ m₀) [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) :
    condVar m X μ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
  condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX

end AlternativeFormula

section LawOfTotalVariance

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

end LawOfTotalVariance

section MartingaleCondVar

/-- **Conditional variance theorem for martingales** (Lecture 28).

If `Xₙ` is a square-integrable martingale with respect to the filtration `𝓕`, then for
`m ≤ n`,
`E[(Xₙ − Xₘ)² | 𝓕ₘ] = E[Xₙ² | 𝓕ₘ] − Xₘ²` almost surely.

This expresses the conditional variance of the increment `Xₙ − Xₘ` in terms of the
conditional second moment of `Xₙ`. -/
theorem martingale_condVar_identity
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X 𝓕 μ)
    (hL2 : ∀ n, MemLp (X n) 2 μ)
    {m n : ℕ} (hmn : m ≤ n) :
    μ[fun ω => (X n ω - X m ω) ^ 2 | 𝓕 m] =ᵐ[μ]
      fun ω => (μ[fun ω' => (X n ω') ^ 2 | 𝓕 m]) ω - (X m ω) ^ 2 := by

  have hcond : μ[X n | ↑(𝓕 m)] =ᵐ[μ] X m := hmart.condExp_ae_eq hmn

  have hfun_ae : (fun ω => (X n ω - X m ω) ^ 2) =ᵐ[μ]
      (fun ω => (X n ω - (μ[X n | 𝓕 m]) ω) ^ 2) := by
    filter_upwards [hcond] with ω hω
    rw [hω]

  have step3 : μ[fun ω => (X n ω - X m ω) ^ 2 | 𝓕 m] =ᵐ[μ]
      condVar (𝓕 m) (X n) μ :=
    condExp_congr_ae (m := ↑(𝓕 m)) hfun_ae

  have step4 : condVar (𝓕 m) (X n) μ =ᵐ[μ]
      μ[X n ^ 2 | 𝓕 m] - μ[X n | 𝓕 m] ^ 2 :=
    condVar_ae_eq_condExp_sq_sub_sq_condExp (𝓕.le m) (hL2 n)

  have step5 : (fun ω => (μ[X n | 𝓕 m]) ω ^ 2) =ᵐ[μ]
      (fun ω => (X m ω) ^ 2) := by
    filter_upwards [hcond] with ω hω
    rw [hω]

  have hpow : X n ^ 2 = fun ω' => X n ω' ^ 2 := by ext; simp [Pi.pow_apply]

  filter_upwards [step3, step4, step5] with ω h3 h4 h5
  rw [h3, h4]
  simp only [Pi.sub_apply, Pi.pow_apply]
  rw [h5, hpow]

end MartingaleCondVar

end
