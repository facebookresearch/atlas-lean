/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace DominatedConvergence

open MeasureTheory Filter Topology

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

/-- Dominated Convergence Theorem (Melrose Theorem 4.6): if `(Fₙ)` is integrable, dominated by an
integrable `g`, and converges pointwise a.e. to `f`, then `f` is integrable and the integrals of
`Fₙ` converge to the integral of `f`. -/
theorem dominated_convergence_integrable_and_tendsto
    {F : ℕ → α → ℝ} {f : α → ℝ} {g : α → ℝ}
    (hF_integrable : ∀ n, Integrable (F n) μ)
    (hg_integrable : Integrable g μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ g a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Integrable f μ ∧ Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n => (hF_integrable n).aestronglyMeasurable
  constructor
  ·
    have hf_meas : AEStronglyMeasurable f μ :=
      aestronglyMeasurable_of_tendsto_ae _ hF_meas h_lim
    have h_bound_f : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a := by
      filter_upwards [h_lim, ae_all_iff.mpr h_bound] with a ha_lim ha_bound
      exact le_of_tendsto' ha_lim.norm ha_bound
    exact hg_integrable.mono' hf_meas h_bound_f
  ·
    exact MeasureTheory.tendsto_integral_of_dominated_convergence g hF_meas hg_integrable
      h_bound h_lim

end DominatedConvergence
