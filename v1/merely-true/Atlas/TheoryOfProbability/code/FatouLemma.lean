/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Filter

/-- **Fatou's lemma.** For a sequence of nonnegative (`ENNReal`-valued) measurable
functions `f n`, the integral of the pointwise `liminf` is bounded above by the `liminf`
of the integrals: `∫ liminf f_n dμ ≤ liminf ∫ f_n dμ`. -/
theorem fatou_lemma {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ENNReal} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤
      liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  MeasureTheory.lintegral_liminf_le hf

/-- **Fatou's lemma (almost-everywhere measurable version).** Same statement as
`fatou_lemma`, but only requires each `f n` to be `AEMeasurable` rather than
`Measurable`. -/
theorem fatou_lemma' {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ENNReal} (hf : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤
      liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  MeasureTheory.lintegral_liminf_le' hf
