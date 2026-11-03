/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Atlas.DifferentialAnalysis.code.DistributionalKernels2

noncomputable section

open BigOperators
open scoped SchwartzMap

namespace WeightedDerivExpansion

/-- Size (sum of components) of a multi-index `γ : Fin n → ℕ`. -/
def multiIndexSize {n : ℕ} (γ : Fin n → ℕ) : ℕ := ∑ i : Fin n, γ i

/-- Componentwise order on multi-indices: `α ≤ γ` iff `α i ≤ γ i` for every `i`. -/
def multiIndexLE {n : ℕ} (α γ : Fin n → ℕ) : Prop := ∀ i, α i ≤ γ i

/-- The componentwise order on multi-indices is decidable. -/
instance {n : ℕ} (α γ : Fin n → ℕ) : Decidable (multiIndexLE α γ) :=
  Fintype.decidableForallFintype

/-- The total size of the componentwise difference `γ - α` of multi-indices. -/
def multiIndexDiffSize {n : ℕ} (γ α : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, (γ i - α i)

/-- Decreasing the `j₀`-th coordinate of `γ` by one strictly decreases the difference size
`multiIndexDiffSize γ α` by at least one (and `α` still bounds the updated `γ`). -/
lemma diff_size_update_lt {n : ℕ} {γ α : Fin n → ℕ} {j₀ : Fin n}
    (hj₀ : 0 < γ j₀) (hα : multiIndexLE α (Function.update γ j₀ (γ j₀ - 1))) :
    1 + multiIndexDiffSize (Function.update γ j₀ (γ j₀ - 1)) α ≤
      multiIndexDiffSize γ α := by
  simp only [multiIndexDiffSize]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have htail : ∀ i ∈ Finset.univ.erase j₀,
      Function.update γ j₀ (γ j₀ - 1) i - α i = γ i - α i := fun i hi =>
    congrArg (· - α i) (Function.update_of_ne (Finset.ne_of_mem_erase hi) (γ j₀ - 1) γ)
  rw [Finset.sum_congr rfl htail, Function.update_self]
  have : α j₀ ≤ γ j₀ - 1 := by
    have := hα j₀; rwa [Function.update_self] at this
  omega

end WeightedDerivExpansion

end
