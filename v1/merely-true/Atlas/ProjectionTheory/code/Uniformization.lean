/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.UniformSet

open Finset Real

namespace UniformSet

/-- A real-valued set function `μ` is sub-additive if
`μ(A ∪ B) ≤ μ(A) + μ(B)` for all finite sets `A, B`. This is the
hypothesis used in the Uniformization Lemma (e.g. `μ(B) = |B|_δ`). -/
def IsSubAdditive {d : ℕ} (μ : Finset (Fin d → ℕ) → ℝ) : Prop :=
  ∀ A B : Finset (Fin d → ℕ), μ (A ∪ B) ≤ μ A + μ B

/-- A real-valued set function `μ` is monotone if `A ⊆ B` implies `μ A ≤ μ B`. -/
def IsMonotoneSetFn {d : ℕ} (μ : Finset (Fin d → ℕ) → ℝ) : Prop :=
  ∀ A B : Finset (Fin d → ℕ), A ⊆ B → μ A ≤ μ B

/-- `IsUniformFrom N m d k X` is the "partial" uniformity property used in the
inductive proof of the Uniformization Lemma: the set `X` is required to be
`(Δ, m)`-uniform only at scales `j ∈ {k, k+1, …, m-1}`. Taking `k = 0` recovers
the full `IsUniform` predicate; `k = m` is automatic. -/
def IsUniformFrom (N m d : ℕ) (k : ℕ) (X : Finset (Fin d → ℕ)) : Prop :=
  ∀ j : ℕ, k ≤ j → j < m →
    ∃ R : ℕ, ∀ Q : Fin d → ℕ,
      (X.filter (fun p => cubeOf N m j p = Q)).Nonempty →
      subcubeCovering N m j d X Q = R

/-- Full `(Δ, m)`-uniformity is the same as `IsUniformFrom` starting at scale `0`. -/
theorem isUniform_iff_uniformFrom_zero (N m d : ℕ) (X : Finset (Fin d → ℕ)) :
    IsUniform N m d X ↔ IsUniformFrom N m d 0 X :=
  ⟨fun h j _ hj => h j hj, fun h j hj => h j (Nat.zero_le _) hj⟩

/-- Every set is vacuously `IsUniformFrom` at the top scale `k = m`,
since there are no indices `j` satisfying `m ≤ j < m`. This is the base
case for the inductive proof of the Uniformization Lemma. -/
theorem isUniformFrom_m (N m d : ℕ) (X : Finset (Fin d → ℕ)) :
    IsUniformFrom N m d m X :=
  fun _ hj hj' => absurd (Nat.lt_of_lt_of_le hj' hj) (lt_irrefl _)





end UniformSet
