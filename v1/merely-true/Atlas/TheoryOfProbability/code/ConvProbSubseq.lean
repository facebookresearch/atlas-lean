/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Normed.Group.Real

open MeasureTheory Filter Set MeasurableSpace
open scoped ENNReal NNReal Topology MeasureTheory

/-- **Convergence in probability via subsequential a.s. convergence** (Lecture 9),
real-valued version.

For real random variables `Xₙ`, `Y` on a finite measure space, `Xₙ → Y` in probability
(i.e. `μ{|Xₙ − Y| > ε} → 0` for every `ε > 0`) if and only if every subsequence of `Xₙ`
admits a further subsequence converging to `Y` almost everywhere. -/
theorem convergence_in_prob_iff_subseq_ae_real
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0)) ↔
    (∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => X (ns (ns' k)) ω) atTop (𝓝 (Y ω))) := by
  constructor
  ·
    intro hconv
    have hTIM : TendstoInMeasure μ X atTop Y := by
      rw [tendstoInMeasure_iff_enorm]
      intro ε hε hε_top
      set δ := ε.toReal
      have hδ_pos : 0 < δ := ENNReal.toReal_pos hε.ne' hε_top
      have hδ2_pos : 0 < δ / 2 := half_pos hδ_pos
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv (δ / 2) hδ2_pos)
      · intro n; exact zero_le _
      · intro n
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        rw [Real.enorm_eq_ofReal_abs] at hω
        have h1 : δ ≤ |X n ω - Y ω| :=
          ENNReal.toReal_le_of_le_ofReal (abs_nonneg _) hω
        linarith
    exact (exists_seq_tendstoInMeasure_atTop_iff hX).mp hTIM
  ·
    intro hsub
    have hTIM : TendstoInMeasure μ X atTop Y :=
      (exists_seq_tendstoInMeasure_atTop_iff hX).mpr hsub
    rw [tendstoInMeasure_iff_enorm] at hTIM
    intro ε hε
    have hε_ennreal : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    have hε_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
    specialize hTIM (ENNReal.ofReal ε) hε_ennreal hε_ne_top
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTIM
    · intro n; exact zero_le _
    · intro n
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)

/-- **Theorem (convergence in probability ↔ subsequential a.s. convergence)**
(Lecture 9).

`Xₙ → Y` in probability iff for every subsequence of `Xₙ` there is a further
subsequence converging a.s. to `Y`. Alias of `convergence_in_prob_iff_subseq_ae_real`. -/
theorem convergence_in_probability_iff_subsequential_ae_convergence
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0)) ↔
    (∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => X (ns (ns' k)) ω) atTop (𝓝 (Y ω))) :=
  convergence_in_prob_iff_subseq_ae_real hX
