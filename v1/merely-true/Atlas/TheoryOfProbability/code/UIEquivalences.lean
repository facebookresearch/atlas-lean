/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable

open scoped MeasureTheory NNReal ENNReal
open MeasureTheory

namespace TheoryOfProbability3

variable {α : Type*} {ι : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- Textbook definition of uniform integrability of a family `f : ι → α → ℝ`:
each `f i` is `AEStronglyMeasurable` and for every `ε > 0` there is a uniform
truncation level `C : ℝ≥0` such that the `L¹` norm of the tail
`{x | C ≤ ‖f i x‖₊}.indicator (f i)` is at most `ε` for all `i`. This matches
Durrett's definition: `lim_{M→∞} sup_i E(|X_i|; |X_i| > M) = 0`. -/
def TextbookUniformlyIntegrable' (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  (∀ i, AEStronglyMeasurable (f i) μ) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0, ∀ i, eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε

/-- On a finite measure space, the textbook definition `TextbookUniformlyIntegrable'`
is equivalent to Mathlib's `UniformIntegrable f 1 μ`. -/
theorem textbookUI'_iff_uniformIntegrable
    [IsFiniteMeasure μ] (f : ι → α → ℝ) :
    TextbookUniformlyIntegrable' f μ ↔ UniformIntegrable f 1 μ :=
  (uniformIntegrable_iff le_rfl ENNReal.one_ne_top).symm

/-- Uniform absolute continuity of the `L¹` integrals of a family `f : ι → α → ℝ`,
expressed via Mathlib's `UnifIntegrable f 1 μ`. -/
abbrev UnifAbsContIntegrals (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  UnifIntegrable f 1 μ

/-- A uniform `L¹`-bound on the family `f : ι → α → ℝ`:
there exists `C : ℝ≥0` with `‖f i‖₁ ≤ C` for all `i`. -/
abbrev UnifL1Bound (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) 1 μ ≤ ↑C

/-- On a finite measure space, the textbook notion of uniform integrability is
equivalent to the conjunction of: (i) each `f i` is `AEStronglyMeasurable`,
(ii) uniform absolute continuity of integrals, and (iii) a uniform `L¹`-bound. -/
theorem textbookUI_iff_bound_and_unifAbsCont [IsFiniteMeasure μ] (f : ι → α → ℝ) :
    TextbookUniformlyIntegrable' f μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧
        UnifAbsContIntegrals f μ ∧
          UnifL1Bound f μ := by
  rw [textbookUI'_iff_uniformIntegrable]
  unfold UniformIntegrable
  exact Iff.rfl

/-- A uniformly integrable family (in the textbook sense) is uniformly bounded in `L¹`. -/
theorem TextbookUniformlyIntegrable'.unifL1Bound [IsFiniteMeasure μ] {f : ι → α → ℝ}
    (hf : TextbookUniformlyIntegrable' f μ) : UnifL1Bound f μ :=
  ((textbookUI_iff_bound_and_unifAbsCont f).mp hf).2.2

/-- A uniformly integrable family (in the textbook sense) has uniformly
absolutely continuous integrals. -/
theorem TextbookUniformlyIntegrable'.unifAbsContIntegrals [IsFiniteMeasure μ] {f : ι → α → ℝ}
    (hf : TextbookUniformlyIntegrable' f μ) : UnifAbsContIntegrals f μ :=
  ((textbookUI_iff_bound_and_unifAbsCont f).mp hf).2.1

/-- Each function in a uniformly integrable family is `AEStronglyMeasurable`. -/
theorem TextbookUniformlyIntegrable'.aEStronglyMeasurable' [IsFiniteMeasure μ] {f : ι → α → ℝ}
    (hf : TextbookUniformlyIntegrable' f μ) : ∀ i, AEStronglyMeasurable (f i) μ :=
  ((textbookUI_iff_bound_and_unifAbsCont f).mp hf).1

end TheoryOfProbability3
