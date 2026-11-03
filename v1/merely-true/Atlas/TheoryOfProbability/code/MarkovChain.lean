/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.TransitionProbability
import Atlas.TheoryOfProbability.code.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory ProbabilityTheory

variable {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]

/-- `IsMarkovChain X ℱ κ μ` asserts that the sequence of random variables `X : ℕ → Ω → S`
is a Markov chain with respect to the filtration `ℱ` with transition probability kernel
`κ` under the measure `μ`. Concretely it requires that `X` is `ℱ`-adapted and that for
each `n` and measurable `B ⊆ S`,

  `μ[1_{B} ∘ X (n+1) | ℱ n] = κ (X n ·) B  μ`-a.e.,

which is the standard form `P(X_{n+1} ∈ B | ℱ_n) = κ(X n, B)` of the Markov property. -/
structure IsMarkovChain (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (κ : Kernel S S)
    [IsMarkovKernel κ] (μ : Measure Ω) : Prop where
  adapted : Adapted ℱ X
  markov_prop : ∀ n : ℕ, ∀ B : Set S, MeasurableSet B →
    μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n] =ᵐ[μ]
      fun ω => (κ (X n ω) B).toReal
