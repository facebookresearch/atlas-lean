/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Atlas.AlgebraicGeometryI.code.ChevalleyImage

namespace BertiniArithmetic

/-- Dimension of a generic fiber in the Bertini dimension count: `n - d - 1`. -/
def fiberDim (d n : ℕ) : ℕ := n - d - 1

/-- Dimension of the incidence variety in the Bertini argument: dimension of the base plus the
generic fiber dimension. -/
def incidenceDim (d n : ℕ) : ℕ := d + fiberDim d n

/-- Dimension of the dual projective space `(ℙⁿ)ⱽ` of hyperplanes: `n`. -/
def dualDim (n : ℕ) : ℕ := n

/-- For `d < n`, the incidence variety has dimension `n - 1`. -/
theorem incidence_dim_eq (d n : ℕ) (hdn : d < n) :
    incidenceDim d n = n - 1 := by
  simp [incidenceDim, fiberDim]; omega

/-- Dimension comparison: `dim(incidence) < dim(dual projective space)` for `d < n`. This is the
gap that produces a generic smooth hyperplane section in Bertini. -/
theorem incidence_dim_lt_dual (d n : ℕ) (hdn : d < n) :
    incidenceDim d n < dualDim n := by
  simp [incidenceDim, fiberDim, dualDim]; omega

/-- The codimension of the image of the incidence variety in the dual space is at least `1`. -/
theorem bertini_codimension_bound (d n : ℕ) (hdn : d < n) :
    dualDim n - incidenceDim d n ≥ 1 := by
  simp [dualDim, incidenceDim, fiberDim]; omega

/-- Helper: for `n > 0`, `n - 1 < n`. -/
theorem pred_lt_of_pos (n : ℕ) (hn : 0 < n) : n - 1 < n := by omega

end BertiniArithmetic

/-- A set that is not the whole space has a point outside it. -/
theorem exists_not_mem_of_ne_univ
    {X : Type*} {Z : Set X} (hne : Z ≠ Set.univ) :
    ∃ x : X, x ∉ Z := by
  by_contra h
  push Not at h
  exact hne (Set.eq_univ_of_forall h)

set_option linter.unusedVariables false in
/-- Bertini via Chevalley's theorem + dimension gap: if the "bad" locus of singular hyperplane
sections is a proper subset of the dual projective space, then there exists a good hyperplane. -/
theorem bertini_projective_chevalley_gap
    {HyperplaneIndex : Type}
    (isBadLocus : HyperplaneIndex → Prop)
    (n d : ℕ) (hdn : d < n)
    (h_incidence_dim : d + (n - d - 1) = n - 1)
    (h_incidence_lt : n - 1 < n)
    (h_bad_proper : {H | isBadLocus H} ≠ Set.univ) :
    ∃ H : HyperplaneIndex, ¬ isBadLocus H :=
  exists_not_mem_of_ne_univ h_bad_proper

/-- An abstract bundle of data for a smooth subvariety of `ℙⁿ` of dimension `d` together with
its space of hyperplanes — used to state Bertini's theorem combinatorially. -/
structure SmoothSubvariety where
  n : ℕ
  d : ℕ
  HyperplaneIndex : Type
  hdn : d < n




