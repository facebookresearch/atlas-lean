/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory Filter

/-- **Dominated convergence theorem.** If `F n → f` pointwise almost everywhere, each
`F n` is almost-everywhere strongly measurable, and `‖F n a‖ ≤ bound a` a.e. for an
integrable function `bound`, then `∫ F n dμ → ∫ f dμ`. -/
theorem dominated_convergence_theorem
    {α : Type*} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : MeasurableSpace α} {μ : Measure α}
    {F : ℕ → α → G} {f : α → G} {bound : α → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound_int : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (nhds (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (nhds (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hF_meas h_bound_int h_bound h_lim

end
