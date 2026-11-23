/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Adapted

open MeasureTheory

namespace MartingaleDef

variable {Ω E ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end MartingaleDef

/--
Textbook definition of a real-valued martingale with respect to a filtration `ℱ`
and measure `μ` (Lecture 29, "Martingales"): a process `f : ι → Ω → ℝ` is a
martingale if it is adapted to `ℱ`, each `f i` is integrable, and the
conditional expectation satisfies `E[f j | ℱ i] = f i` almost surely whenever
`i ≤ j`.
-/
structure TextbookMartingale {Ω : Type*} {ι : Type*} [Preorder ι]
    {m0 : MeasurableSpace Ω} (f : ι → Ω → ℝ) (ℱ : MeasureTheory.Filtration ι m0)
    (μ : MeasureTheory.Measure Ω) : Prop where
  adapted : MeasureTheory.StronglyAdapted ℱ f
  integrable : ∀ i, MeasureTheory.Integrable (f i) μ
  condExp_eq : ∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i
