/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 400000

open Finset

namespace AlgorithmicLLL

/-- Hypotheses for the general (asymmetric) Lovász Local Lemma: weights $x_i \in [0,1)$ such
that each event probability satisfies $P_i \le x_i \prod_{j \in N(i)} (1 - x_j)$, where $N(i)$
is the dependency neighborhood of event $i$ (Theorem 6.1.9). -/
structure LLLCondition (n : ℕ) (P : Fin n → ℝ) (x : Fin n → ℝ)
    (N : Fin n → Finset (Fin n)) : Prop where
  x_nonneg : ∀ i, 0 ≤ x i
  x_lt_one : ∀ i, x i < 1
  prob_bound : ∀ i, P i ≤ x i * ∏ j ∈ N i, (1 - x j)
  P_nonneg : ∀ i, 0 ≤ P i




end AlgorithmicLLL
