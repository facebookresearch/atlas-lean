/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Filter ENNReal Topology

/--
Monotone convergence theorem (Lecture 5, "More integral properties"):
if `f_n : α → [0, ∞]` is a pointwise non-decreasing sequence of measurable
functions converging pointwise to `g`, then `∫ f_n dμ ↑ ∫ g dμ`, i.e. the
sequence of Lebesgue integrals tends to the integral of the limit.
-/
theorem monotone_convergence_theorem
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf_meas : ∀ n, Measurable (f n))
    (hf_mono : Monotone f)
    (hf_lim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) := by

  have hg : g = fun x => ⨆ n, f n x := by
    ext x
    exact tendsto_nhds_unique (hf_lim x)
      (tendsto_atTop_iSup (fun n m hnm => hf_mono hnm x))

  rw [hg, lintegral_iSup hf_meas hf_mono]

  exact tendsto_atTop_iSup fun n m hnm => lintegral_mono (hf_mono hnm)
