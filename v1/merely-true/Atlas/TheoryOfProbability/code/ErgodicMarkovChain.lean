/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.FiniteMarkovChain
import Mathlib.Data.Matrix.Basic

open Matrix Finset BigOperators

namespace StochasticMatrix

variable {M : ℕ}

/-- Underlying matrix of probabilities of a `StochasticMatrix`. -/
def toMatrix (P : StochasticMatrix M) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  P.prob

/-- A finite-state Markov chain (given by its stochastic transition matrix `P`) is
*ergodic* if some positive power `P^n` has all strictly positive entries. -/
def IsErgodic (P : StochasticMatrix M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i j : Fin (M + 1), (P.toMatrix ^ n) i j > 0

end StochasticMatrix
