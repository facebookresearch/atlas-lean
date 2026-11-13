/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order
import Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
import Atlas.DifferentialAnalysis.code.ContinuousFunctions

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology ZeroAtInfty

namespace MeasuresAndSigmaAlgebras

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]

/-- A continuous linear functional `u : C₀(X, ℝ) →L[ℝ] ℝ` is *positive* if `u f ≥ 0`
whenever `f ≥ 0` pointwise. -/
def IsPositiveLinearFunctional (u : C₀(X, ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ u f

/-- The premeasure of an open set `U` associated to a positive linear functional `u`:
the supremum of `u f` over all `f : C₀(X, ℝ)` with `0 ≤ f ≤ 1` and `tsupport f ⊆ U` compact.
This is the open-set value used to induce an outer measure (Section 1.11 of Melrose). -/
def functionalMeasureOpen (u : C₀(X, ℝ) →L[ℝ] ℝ) (U : Set X) (_ : IsOpen U) : ℝ≥0∞ :=
  ⨆ (f : C₀(X, ℝ)) (_ : (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
    IsCompact (tsupport f) ∧ tsupport f ⊆ U),
    ENNReal.ofReal (u f)

/-- A continuous function vanishing at infinity whose topological support is contained in `∅`
must be identically zero. -/
theorem zeroAtInfty_eq_zero_of_tsupport_subset_empty
    {X : Type*} [MetricSpace X] {f : C₀(X, ℝ)}
    (h : tsupport f ⊆ (∅ : Set X)) : f = 0 := by
  ext x
  simp only [ZeroAtInftyContinuousMap.zero_apply]
  by_contra hne
  have hmem : x ∈ tsupport (⇑f : X → ℝ) := subset_closure hne
  exact (h hmem).elim

/-- The functional premeasure of the empty open set is zero: the only test function with
support in `∅` is the zero function. -/
theorem functionalMeasureOpen_empty
    {X : Type*} [MetricSpace X] (u : C₀(X, ℝ) →L[ℝ] ℝ) :
    functionalMeasureOpen u ∅ isOpen_empty = 0 := by
  simp only [functionalMeasureOpen]
  apply le_antisymm _ (zero_le _)
  apply iSup₂_le
  intro f ⟨_, _, hsupp⟩
  rw [zeroAtInfty_eq_zero_of_tsupport_subset_empty hsupp, map_zero, ENNReal.ofReal_zero]

/-- Monotonicity of the functional premeasure on open sets: if `U ⊆ V` then
`functionalMeasureOpen u U ≤ functionalMeasureOpen u V`. -/
theorem functionalMeasureOpen_mono
    {X : Type*} [MetricSpace X] (u : C₀(X, ℝ) →L[ℝ] ℝ)
    ⦃U V : Set X⦄ (hU : IsOpen U) (hV : IsOpen V) (h : U ⊆ V) :
    functionalMeasureOpen u U hU ≤ functionalMeasureOpen u V hV := by
  apply iSup₂_le
  intro f ⟨hf01, hcomp, hsupp⟩
  exact le_iSup₂_of_le f ⟨hf01, hcomp, hsupp.trans h⟩ le_rfl




/-- The outer measure on `X` induced by a positive linear functional `u` via its values on
open sets (Section 1.11/1.12 of Melrose). Used as the starting point for constructing the
associated Radon measure via Caratheodory's theorem. -/
noncomputable def functionalOuterMeasure (u : C₀(X, ℝ) →L[ℝ] ℝ)
    (_ : IsPositiveLinearFunctional u) : OuterMeasure X :=
  inducedOuterMeasure
    (fun U (hU : IsOpen U) => functionalMeasureOpen u U hU)
    isOpen_empty
    (functionalMeasureOpen_empty u)

/-- `functionalOuterMeasure u hu` satisfies the abstract axioms of an outer measure
(monotonicity, σ-subadditivity, and vanishing on the empty set). -/
theorem functionalOuterMeasure_isOuterMeasure (u : C₀(X, ℝ) →L[ℝ] ℝ)
    (hu : IsPositiveLinearFunctional u) :
    IsOuterMeasure (⇑(functionalOuterMeasure u hu)) :=
  outerMeasure_isOuterMeasure (functionalOuterMeasure u hu)

end MeasuresAndSigmaAlgebras

end
