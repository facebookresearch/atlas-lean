/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Martingale.Basic
set_option maxHeartbeats 800000

namespace BoundedDifferences

open MeasureTheory ProbabilityTheory Real Finset Function
open scoped NNReal ENNReal

/-- The function $f$ has bounded differences with coefficients $c_i$: changing the $i$-th
coordinate of the input changes $f$ by at most $c_i$ in absolute value. -/
def HasBoundedDifferences {n : ℕ} {α : Fin n → Type*} [∀ i, DecidableEq (α i)]
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∀ x : (∀ i, α i), ∀ y : α i,
    |f x - f (Function.update x i y)| ≤ c i

/-- Lift a function `Fin n → ℝ` to a function `ℕ → ℝ` by extending with zeros for indices ≥ $n$. -/
noncomputable def liftToNat {n : ℕ} (c : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then c ⟨i, h⟩ else 0

/-- The nat-lifted version of a nonnegative `Fin n`-indexed function is nonnegative. -/
lemma liftToNat_nonneg {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ liftToNat c i := by
  intro i; simp only [liftToNat]; split_ifs with h
  · exact hc ⟨i, h⟩
  · linarith

/-- The Hoeffding sub-Gaussian parameter $c^2/4$ associated with a bounded random variable
of range $c$, packaged as a nonnegative real. -/
noncomputable def hoeffdingParam (c : ℝ) (_hc : 0 ≤ c) : ℝ≥0 :=
  ⟨c ^ 2 / 4, by positivity⟩

/-- The sum of Hoeffding parameters $\sum_{i<n} c_i^2/4$ equals $(\sum_i c_i^2)/4$. -/
lemma sum_hoeffdingParam_eq {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (↑(∑ i ∈ range n,
      hoeffdingParam (liftToNat c i) (liftToNat_nonneg c hc i)) : ℝ) =
    (∑ i : Fin n, c i ^ 2) / 4 := by
  rw [NNReal.coe_sum]
  simp only [hoeffdingParam, NNReal.coe_mk]
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
  congr 1; ext ⟨i, hi⟩; simp [liftToNat, hi]






end BoundedDifferences
