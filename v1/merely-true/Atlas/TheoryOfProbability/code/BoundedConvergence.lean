/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter Topology

/-- **Bounded convergence theorem.** Let `μ` be a probability measure and let `Fₙ`
be a sequence of (a.e. strongly) measurable functions into a normed space with
`‖Fₙ‖ ≤ C` almost surely. If `Fₙ → f` in measure (i.e. in probability), then
`∫ Fₙ dμ → ∫ f dμ`. -/
theorem MeasureTheory.tendsto_integral_of_bounded_convergence
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℕ → α → G} {f : α → G} {C : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : TendstoInMeasure μ F atTop f) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns

  have h_lim_ns : TendstoInMeasure μ (fun n ↦ F (ns n)) atTop f :=
    fun ε hε ↦ (h_lim ε hε).comp hns

  obtain ⟨ms, -, hms_ae⟩ := h_lim_ns.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩

  exact tendsto_integral_of_dominated_convergence (fun _ ↦ C)
    (fun n ↦ hF_meas (ns (ms n)))
    (integrable_const C)
    (fun n ↦ h_bound (ns (ms n)))
    hms_ae
