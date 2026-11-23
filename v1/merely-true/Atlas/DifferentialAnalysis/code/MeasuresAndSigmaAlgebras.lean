/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory Set

open scoped ENNReal

namespace MeasuresAndSigmaAlgebras

/-- Predicate axiomatising an outer measure `μ*` on `X`: empty set has measure zero,
monotone with respect to inclusion, and countably subadditive. -/
structure IsOuterMeasure {X : Type*} (μstar : Set X → ℝ≥0∞) : Prop where
  empty : μstar ∅ = 0
  mono : ∀ {A B : Set X}, A ⊆ B → μstar A ≤ μstar B
  iUnion_le : ∀ (A : ℕ → Set X), μstar (⋃ j, A j) ≤ ∑' j, μstar (A j)

/-- Every Mathlib `OuterMeasure` satisfies the predicate `IsOuterMeasure`. -/
theorem outerMeasure_isOuterMeasure {X : Type*} (μ : OuterMeasure X) :
    IsOuterMeasure (⇑μ) where
  empty := measure_empty
  mono h := measure_mono h
  iUnion_le A := measure_iUnion_le A

/-- Conversion from an `IsOuterMeasure` proof to a Mathlib `OuterMeasure` bundle. -/
noncomputable def IsOuterMeasure.toOuterMeasure {X : Type*} {μstar : Set X → ℝ≥0∞}
    (h : IsOuterMeasure μstar) : OuterMeasure X where
  measureOf := μstar
  empty := h.empty
  mono hsub := h.mono hsub
  iUnion_nat s _ := (h.iUnion_le s)

/-- Volume of the axis-aligned rectangle `[a, b]` in `ℝⁿ`, defined as the product of
side lengths `b i - a i`. -/
@[simp]
noncomputable def rectangleVolume {n : ℕ} (a b : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (b i - a i)




/-- A σ-algebra on `X` (Melrose Def 2.1) is identified with `MeasurableSpace X`. -/
abbrev SigmaAlgebra (X : Type*) := MeasurableSpace X

section SigmaAlgebraAxioms

variable {X : Type*} [MeasurableSpace X]

end SigmaAlgebraAxioms

section RadonMeasure

open Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A Radon measure on a topological measurable space is a Borel measure that is
regular (inner regular on opens, outer regular, locally finite). -/
class IsRadonMeasure (μ : Measure X) extends Regular μ : Prop

/-- Any regular measure is automatically a Radon measure in our sense. -/
instance Regular.toIsRadonMeasure (μ : Measure X) [Regular μ] : IsRadonMeasure μ := ⟨⟩

end RadonMeasure

/-- Every Borel set in `ℝⁿ` is Carathéodory-measurable with respect to Lebesgue
outer measure. -/
theorem lebesgue_borel_le_caratheodory (n : ℕ) :
    borel (Fin n → ℝ) ≤ (volume : Measure (Fin n → ℝ)).toOuterMeasure.caratheodory :=
  le_trans OpensMeasurableSpace.borel_le (le_toOuterMeasure_caratheodory volume)

/-- Carathéodory measurability condition: `E` splits every test set `A` additively
with respect to the outer measure `μ*`. -/
def IsOuterMeasureMeasurable {X : Type*} (μstar : Set X → ℝ≥0∞) (E : Set X) : Prop :=
  ∀ A : Set X, μstar A = μstar (A ∩ E) + μstar (A ∩ Eᶜ)

/-- Our `IsOuterMeasureMeasurable` predicate agrees with Mathlib's `IsCaratheodory`. -/
theorem isOuterMeasureMeasurable_iff_isCaratheodory {X : Type*} (μ : OuterMeasure X)
    (E : Set X) :
    IsOuterMeasureMeasurable (⇑μ) E ↔ μ.IsCaratheodory E := by
  simp only [IsOuterMeasureMeasurable, OuterMeasure.IsCaratheodory, sdiff_eq, Set.inf_eq_inter]

section CaratheodoryMeasurable

variable {X : Type*} (μ : OuterMeasure X)

/-- The σ-algebra of Carathéodory-measurable sets for an outer measure `μ`. -/
@[reducible] def caratheodorySigmaAlgebra : SigmaAlgebra X := μ.caratheodory

end CaratheodoryMeasurable

section Caratheodory

variable {X : Type*} (μ : OuterMeasure X)

/-- The measure on the Carathéodory σ-algebra induced by an outer measure `μ` by
restriction. -/
noncomputable def caratheodoryMeasure : @Measure X μ.caratheodory :=
  letI : MeasurableSpace X := μ.caratheodory
  μ.toMeasure le_rfl

/-- Any null set is Carathéodory-measurable. -/
theorem isOuterMeasureMeasurable_of_measure_zero {E : Set X}
    (hE : μ E = 0) : μ.IsCaratheodory E := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro A

  have hAE : μ (A ∩ E) = 0 :=
    le_antisymm ((measure_mono Set.inter_subset_right).trans hE.le) (zero_le _)

  have hAEc : μ (A \ E) ≤ μ A := measure_mono diff_subset
  rw [hAE, zero_add]
  exact hAEc

/-- The Carathéodory measure on `μ.caratheodory` is complete: every null set is
measurable. -/
theorem caratheodoryMeasure_isComplete :
    @Measure.IsComplete X μ.caratheodory (caratheodoryMeasure μ) := by
  letI : MeasurableSpace X := μ.caratheodory
  constructor
  intro s hs


  have hμs : μ s = 0 := by
    have h1 : μ s ≤ (caratheodoryMeasure μ) s := le_toMeasure_apply μ le_rfl s
    rw [hs] at h1
    exact le_antisymm h1 (zero_le _)
  exact isOuterMeasureMeasurable_of_measure_zero μ hμs

/-- Carathéodory's extension theorem (Melrose Thm 2.4): every outer measure restricts
to a complete measure on its σ-algebra of measurable sets, with the values matching
the outer measure. -/
theorem caratheodory_theorem :
    ∃ (m : @Measure X μ.caratheodory),
      @Measure.IsComplete X μ.caratheodory m ∧
      (∀ (s : Set X), MeasurableSet[μ.caratheodory] s → m s = μ s) := by
  letI : MeasurableSpace X := μ.caratheodory
  exact ⟨caratheodoryMeasure μ,
    caratheodoryMeasure_isComplete μ,
    fun s hs => toMeasure_apply μ le_rfl hs⟩

end Caratheodory

section RieszOuterMeasureMeasurability

open scoped NNReal
open CompactlySupportedContinuousMap

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
variable (Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)

/-- For the Riesz content associated to a positive linear functional, open sets are
Carathéodory-measurable and their measure equals the inner content. -/
theorem isOpen_outerMeasureMeasurable_and_measure_eq_innerContent [MeasurableSpace X] [BorelSpace X]
    (U : Set X) (hU : IsOpen U) :
    IsOuterMeasureMeasurable (⇑(rieszContent (toNNRealLinear Λ)).outerMeasure) U ∧
    (rieszContent (toNNRealLinear Λ)).measure U =
      (rieszContent (toNNRealLinear Λ)).innerContent ⟨U, hU⟩ := by
  constructor
  · intro A
    exact (rieszContent (toNNRealLinear Λ)).borel_le_caratheodory U hU.measurableSet A
  · rw [(rieszContent (toNNRealLinear Λ)).measure_apply hU.measurableSet]
    exact (rieszContent (toNNRealLinear Λ)).outerMeasure_of_isOpen U hU

end RieszOuterMeasureMeasurability

section RieszMeasureRadon

open Measure RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]
  (Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)

/-- The Riesz-Markov-Kakutani measure associated with a positive linear functional
on `C_c(X, ℝ)` is a Radon measure. -/
instance rieszMeasure_isRadonMeasure : IsRadonMeasure (rieszMeasure Λ) :=
  ⟨⟩

end RieszMeasureRadon

section RieszMeasureFromC0

open Measure RealRMK
open scoped CompactlySupported ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]

/-- Linear inclusion of compactly supported continuous functions into the space of
continuous functions vanishing at infinity. -/
noncomputable def inclusionCcC0 : C_c(X, ℝ) →ₗ[ℝ] C₀(X, ℝ) where
  toFun f := ⟨f.toContinuousMap, zero_at_infty f⟩
  map_add' f g := by
    apply ZeroAtInftyContinuousMap.ext; intro x
    simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
    rfl
  map_smul' r f := by
    apply ZeroAtInftyContinuousMap.ext; intro x
    simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rfl

/-- Restriction of a positive linear functional on `C₀(X, ℝ)` to `C_c(X, ℝ)`, viewed
as a positive linear map. -/
noncomputable def restrictC0ToCc
    (Φ : C₀(X, ℝ) →ₗ[ℝ] ℝ)
    (hΦ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φ f) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (Φ.comp inclusionCcC0) fun f hf => by
    apply hΦ; intro x; exact hf x

/-- The Riesz measure on `X` produced from a positive linear functional defined on
`C₀(X, ℝ)`, by restricting it to `C_c(X, ℝ)` and applying the RMK theorem. -/
noncomputable def rieszMeasureOfC0Functional
    (Φ : C₀(X, ℝ) →ₗ[ℝ] ℝ)
    (hΦ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φ f) :
    Measure X :=
  rieszMeasure (restrictC0ToCc Φ hΦ)

/-- Melrose Proposition 2.8: a positive linear functional on `C₀(X, ℝ)` produces a
Radon measure on `X`. -/
theorem prop_2_8_radon_measure_from_C0_functional
    (Φ : C₀(X, ℝ) →ₗ[ℝ] ℝ)
    (hΦ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φ f) :
    IsRadonMeasure (rieszMeasureOfC0Functional Φ hΦ) := by
  show IsRadonMeasure (rieszMeasure _)
  exact ⟨⟩

end RieszMeasureFromC0

section BorelMeasure

variable {X : Type*} [TopologicalSpace X]

/-- Sufficient condition for the Borel σ-algebra to be contained in the Carathéodory
σ-algebra of `μ`: every open set must be `μ*`-measurable. -/
theorem borel_le_caratheodory_of_openSets_measurable (μ : OuterMeasure X)
    (h : ∀ (U : Set X), IsOpen U → IsOuterMeasureMeasurable (⇑μ) U) :
    borel X ≤ μ.caratheodory :=
  MeasurableSpace.generateFrom_le fun U hU =>
    (isOuterMeasureMeasurable_iff_isCaratheodory μ U).mp (h U hU)

end BorelMeasure

end MeasuresAndSigmaAlgebras
