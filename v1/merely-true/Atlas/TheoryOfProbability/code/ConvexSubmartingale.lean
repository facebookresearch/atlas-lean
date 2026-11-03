/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Continuous

open MeasureTheory Filter

/-- **Convex function of a martingale is a submartingale** (Lecture 26/27 claim).

If `Xₙ` is a martingale w.r.t. the filtration `ℱ`, and `φ : ℝ → ℝ` is convex with
`E|φ(Xₙ)| < ∞` for all `n`, then `φ ∘ Xₙ` is a submartingale. The proof uses conditional
Jensen's inequality together with the martingale property `E[Xⱼ | ℱᵢ] = Xᵢ`. -/
theorem convex_comp_martingale_is_submartingale
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ)
    {φ : ℝ → ℝ} (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Submartingale (fun n ω => φ (X n ω)) ℱ μ := by

  have hφ_cont : Continuous φ :=
    continuousOn_univ.1 (hφ_convex.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro n
    exact hφ_cont.comp_stronglyMeasurable (hmart.stronglyMeasurable n)
  ·
    intro i j hij

    have hJensen : (φ ∘ μ[X j | ℱ i]) ≤ᵐ[μ] μ[φ ∘ (X j) | ℱ i] :=
      hφ_convex.map_condExp_le_of_finiteDimensional (ℱ.le i)
        (hmart.integrable j) (hφ_int j)

    have hcondexp : μ[X j | ℱ i] =ᵐ[μ] X i := hmart.condExp_ae_eq hij

    have hcomp : (fun ω => φ (X i ω)) =ᵐ[μ] (φ ∘ μ[X j | ℱ i]) := by
      filter_upwards [hcondexp] with ω hω
      simp [Function.comp, hω]

    exact hcomp.le.trans hJensen
  ·
    exact hφ_int
