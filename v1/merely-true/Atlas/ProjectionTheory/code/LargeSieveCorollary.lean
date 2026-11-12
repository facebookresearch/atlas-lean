/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.LargeSieveAvg

open Finset Real

namespace LargeSieve

/-- The set of primes in the dyadic interval `[M/2, M]`. -/
noncomputable def primesDyadic (M : ℕ) : Finset ℕ :=
  (Finset.Icc (M / 2) M).filter Nat.Prime

/-- The cardinality of the fiber of `A` over `a ∈ ZMod p`, i.e. the number of `n ∈ A` with
`n ≡ a (mod p)`. -/
def fiberCard (A : Finset ℕ) (p : ℕ) (a : ZMod p) : ℕ :=
  (A.filter (fun (n : ℕ) => (n : ZMod p) = a)).card

/-- Average deviation from equidistribution modulo `p`:
$\frac{1}{p} \sum_{a \in \mathbb{Z}_p} \big|\, |A \cap (a + p\mathbb{Z})| - |A|/p \,\big|$. -/
noncomputable def avgDeviationMod (A : Finset ℕ) (p : ℕ) : ℝ :=
  if hp : p = 0 then 0
  else
    haveI : NeZero p := ⟨hp⟩
    (1 / (p : ℝ)) * ∑ a : ZMod p, |((fiberCard A p a : ℝ) - (A.card : ℝ) / (p : ℝ))|

/-- The average deviation `avgDeviationMod A p` is non-negative. -/
lemma avgDeviationMod_nonneg (A : Finset ℕ) (p : ℕ) : 0 ≤ avgDeviationMod A p := by
  unfold avgDeviationMod
  split_ifs with hp
  · linarith
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun a _ => abs_nonneg _)

/-- The indicator function `1_A : Fin N → ℂ`, where index `n` corresponds to the integer
`n.val + 1 ∈ [1, N]`. -/
noncomputable def indicatorFin (N : ℕ) (A : Finset ℕ) : Fin N → ℂ :=
  fun n => if (n.val + 1) ∈ A then 1 else 0



end LargeSieve
