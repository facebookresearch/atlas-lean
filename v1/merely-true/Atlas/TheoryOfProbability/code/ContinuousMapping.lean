/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory Filter ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

noncomputable section

namespace ProbabilityTheory

/-- **Weak convergence** of a sequence of probability measures on `ℝ`.

`μs n ⇒ μ` iff `∫ f d(μs n) → ∫ f dμ` for every bounded continuous `f : ℝ →ᵇ ℝ`,
which is the Portmanteau characterization of weak convergence (Lecture 12). -/
def WeakConvergenceMeasures (μs : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μs n)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ∀ f : ℝ →ᵇ ℝ,
    Tendsto (fun n ↦ ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂μ))

/-- **Continuous Mapping Theorem** (Lecture 12).

If `g : ℝ → ℝ` is measurable and its set of discontinuity points has `μ`-measure zero,
and `μs n` converges weakly to `μ`, then the pushforwards `(μs n).map g` converge weakly
to `μ.map g`. -/
theorem continuous_mapping
    (μs : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μs n)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg_meas : Measurable g)
    (hg_ae : μ {x | ¬ContinuousAt g x} = 0)
    (hconv : WeakConvergenceMeasures μs μ) :
    haveI : ∀ n, IsProbabilityMeasure ((μs n).map g) :=
      fun _ ↦ Measure.isProbabilityMeasure_map hg_meas.aemeasurable
    haveI : IsProbabilityMeasure (μ.map g) :=
      Measure.isProbabilityMeasure_map hg_meas.aemeasurable
    WeakConvergenceMeasures (fun n ↦ (μs n).map g) (μ.map g) := by
  haveI : ∀ n, IsProbabilityMeasure ((μs n).map g) :=
    fun _ ↦ Measure.isProbabilityMeasure_map hg_meas.aemeasurable
  haveI : IsProbabilityMeasure (μ.map g) :=
    Measure.isProbabilityMeasure_map hg_meas.aemeasurable


  let pμs : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨μs n, inferInstance⟩
  let pμ : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
  have htendsto_orig : Tendsto pμs atTop (𝓝 pμ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    change Tendsto (fun i ↦ ∫ x, f x ∂(μs i)) atTop (𝓝 (∫ x, f x ∂μ))
    exact hconv f


  have h_open_orig : ∀ G : Set ℝ, IsOpen G →
      μ G ≤ atTop.liminf (fun i ↦ μs i G) :=
    fun G hG ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto htendsto_orig hG


  have h_open_push : ∀ O : Set ℝ, IsOpen O →
      (μ.map g) O ≤ atTop.liminf (fun i ↦ ((μs i).map g) O) := by
    intro O hO
    rw [Measure.map_apply hg_meas hO.measurableSet]

    have h_eq : μ (g ⁻¹' O) = μ (interior (g ⁻¹' O)) := by
      apply le_antisymm
      ·

        have hsub : g ⁻¹' O \ interior (g ⁻¹' O) ⊆ {x | ¬ContinuousAt g x} := by
          intro x ⟨hx1, hx2⟩ hcont
          exact hx2 (mem_interior_iff_mem_nhds.mpr (hcont.preimage_mem_nhds (hO.mem_nhds hx1)))
        have h0 : μ (g ⁻¹' O \ interior (g ⁻¹' O)) = 0 :=
          le_antisymm ((measure_mono hsub).trans (le_of_eq hg_ae)) (zero_le _)
        calc μ (g ⁻¹' O)
            = μ (interior (g ⁻¹' O) ∪ (g ⁻¹' O \ interior (g ⁻¹' O))) := by
                rw [union_diff_cancel interior_subset]
          _ ≤ μ (interior (g ⁻¹' O)) + μ (g ⁻¹' O \ interior (g ⁻¹' O)) :=
                measure_union_le _ _
          _ = μ (interior (g ⁻¹' O)) := by rw [h0, add_zero]
      · exact measure_mono interior_subset
    rw [h_eq]

    calc μ (interior (g ⁻¹' O))
        ≤ atTop.liminf (fun i ↦ μs i (interior (g ⁻¹' O))) :=
          h_open_orig _ isOpen_interior
      _ ≤ atTop.liminf (fun i ↦ μs i (g ⁻¹' O)) :=
          liminf_le_liminf (Eventually.of_forall (fun i ↦ measure_mono interior_subset))
      _ = atTop.liminf (fun i ↦ ((μs i).map g) O) := by
          congr 1; ext i; rw [Measure.map_apply hg_meas hO.measurableSet]


  let pμs_push : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨(μs n).map g, inferInstance⟩
  let pμ_push : ProbabilityMeasure ℝ := ⟨μ.map g, inferInstance⟩
  have htendsto_push : Tendsto pμs_push atTop (𝓝 pμ_push) := by
    apply tendsto_of_forall_isOpen_le_liminf_nat'
    exact h_open_push

  intro f
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htendsto_push) f
  change Tendsto (fun i ↦ ∫ x, f x ∂((μs i).map g)) atTop (𝓝 (∫ x, f x ∂(μ.map g)))
  exact this

end ProbabilityTheory
