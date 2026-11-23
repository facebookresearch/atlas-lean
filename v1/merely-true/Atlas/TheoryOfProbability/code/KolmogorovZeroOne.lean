/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.TailSigmaAlgebra
import Mathlib.Probability.Independence.ZeroOne

open MeasureTheory MeasurableSpace ProbabilityTheory Filter
open scoped ENNReal MeasureTheory

variable {Ω : Type*}

/-- The tail σ-algebra `⋂ₙ σ(𝓐 n, 𝓐 (n+1), …)` coincides with `limsup` of the sequence of
σ-algebras along `atTop`. -/
theorem tailMeasurableSpace_eq_limsup_atTop (𝓐 : ℕ → MeasurableSpace Ω) :
    tailMeasurableSpace 𝓐 = limsup 𝓐 atTop := by
  simp only [tailMeasurableSpace, tailMeasurableSpaceFrom]
  rw [limsup_eq_iInf_iSup_of_nat]

variable {β : Type*} [mβ : MeasurableSpace β]

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Kolmogorov 0-1 law (for independent σ-algebras).** If `𝓐 : ℕ → MeasurableSpace Ω`
is a sequence of independent sub-σ-algebras of `m0`, then every event `A` in the tail
σ-algebra `⋂ₙ σ(𝓐 n, 𝓐 (n+1), …)` satisfies `μ A = 0` or `μ A = 1`. -/
theorem kolmogorov_zero_one
    (𝓐 : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, 𝓐 n ≤ m0)
    (h_indep : iIndep 𝓐 μ)
    {A : Set Ω}
    (hA : MeasurableSet[tailMeasurableSpace 𝓐] A) :
    μ A = 0 ∨ μ A = 1 := by
  rw [tailMeasurableSpace_eq_limsup_atTop] at hA
  exact measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep hA

/-- **Kolmogorov 0-1 law (for sequences of random variables).** If `X : ℕ → Ω → β` is a
sequence of random variables whose generated σ-algebras are independent, then every event `A`
in the tail σ-algebra `⋂ₙ σ(X n, X (n+1), …)` satisfies `μ A = 0` or `μ A = 1`. -/
theorem kolmogorov_zero_one_fun
    (X : ℕ → Ω → β)
    (h_le : ∀ n, MeasurableSpace.comap (X n) mβ ≤ m0)
    (h_indep : iIndep (fun n => MeasurableSpace.comap (X n) mβ) μ)
    {A : Set Ω}
    (hA : MeasurableSet[tailMeasurableSpaceOfFun X] A) :
    μ A = 0 ∨ μ A = 1 :=
  kolmogorov_zero_one _ h_le h_indep hA

/-- **Kolmogorov 0-1 law from `iIndepFun`.** If `X : ℕ → Ω → β` is an independent sequence of
random variables (in the `iIndepFun` sense), then every event `A` in the tail σ-algebra of `X`
satisfies `μ A = 0` or `μ A = 1`. -/
theorem kolmogorov_zero_one_of_iIndepFun
    (X : ℕ → Ω → β)
    (h_le : ∀ n, MeasurableSpace.comap (X n) mβ ≤ m0)
    (h_indep : iIndepFun (m := fun _ => mβ) X μ)
    {A : Set Ω}
    (hA : MeasurableSet[tailMeasurableSpaceOfFun X] A) :
    μ A = 0 ∨ μ A = 1 :=
  kolmogorov_zero_one_fun X h_le h_indep hA
