/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.BregmanMincHelpers
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Equiv Classical BigOperators Real

noncomputable section

namespace BregmanMinc

/-- $\text{rankInSubset}(S, j, \tau)$: the rank (1-indexed) of $j$ within the subset
$S$ when elements are ordered by the inverse permutation $\tau^{-1}$. -/
noncomputable def rankInSubset {n : ℕ} (S : Finset (Fin n)) (j : Fin n)
    (τ : Equiv.Perm (Fin n)) : ℕ :=
  (S.filter (fun k => τ.symm k < τ.symm j)).card + 1

/-- Set of indices $k$ such that the entry $A_{i, \sigma(k)} = 1$; these are the
positions in the permutation $\sigma$ whose row $i$ contributes a $1$ in $A$. -/
def relevantRows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => A i (σ k) = 1)

end BregmanMinc
