/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Basic
import Atlas.TheoryOfProbability.code.Filtration

open MeasureTheory ProbabilityTheory Finset BigOperators

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A `StochasticMatrix M` is an `(M+1) × (M+1)` row-stochastic matrix: entries
`prob i j` are non-negative real numbers, and the rows sum to `1`. This is the
transition matrix of a Markov chain on the finite state space `Fin (M + 1)`. -/
structure StochasticMatrix (M : ℕ) where
  prob : Fin (M + 1) → Fin (M + 1) → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  row_sum : ∀ i, ∑ j, prob i j = 1

namespace StochasticMatrix

variable {M : ℕ} (P : StochasticMatrix M)

end StochasticMatrix

/-- `IsFiniteMarkovChain X P ℱ μ` asserts that the sequence `X : ℕ → Ω → Fin (M+1)`
is a Markov chain with transition matrix `P`, adapted to the discrete filtration `ℱ`,
under the measure `μ`. Concretely: each `X n` is `ℱ n`-measurable, and the conditional
probability that `X (n+1) = j` given `ℱ n` equals `P.prob (X n) j`, matching the
Markov property `P(X_{n+1} = j | X_n = i, ...) = P_{ij}`. -/
structure IsFiniteMarkovChain {M : ℕ} (X : ℕ → Ω → Fin (M + 1))
    (P : StochasticMatrix M) (ℱ : DiscreteFiltration Ω m) (μ : Measure Ω) : Prop where
  adapted : ∀ n, @Measurable _ _ (ℱ n) _ (X n)
  markov_prop : ∀ n : ℕ, ∀ j : Fin (M + 1),
    μ[(fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] =ᵐ[μ]
      fun ω => P.prob (X n ω) j
