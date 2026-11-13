/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff
open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- The singular support of (the tempered distribution associated to) a Schwartz function is
empty: Schwartz functions are smooth at every point, so the distribution has no singularities. -/
theorem schwartz_singularSupport_empty
    (f : 𝓢(E n, ℂ)) :
    singularSupport (schwEmbed f) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  apply hx

  show IsSmoothNear (schwEmbed f) x

  have hx_nhds : (Set.univ : Set (E n)) ∈ nhds x := Filter.univ_mem
  obtain ⟨φ₀, -, hφ₀_compact, hφ₀_smooth, -, hφ₀_x⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hx_nhds

  let φ : E n → ℂ := Complex.ofRealCLM ∘ φ₀
  have hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
    Complex.ofRealCLM.contDiff.comp hφ₀_smooth
  have hφ_compact : HasCompactSupport φ := hφ₀_compact.comp_left (map_zero _)
  have hφ_x : φ x ≠ 0 := by
    simp only [φ, Function.comp, Complex.ofRealCLM_apply, Complex.ofReal_ne_zero, hφ₀_x]
    exact one_ne_zero
  have hφ_temp : φ.HasTemperateGrowth := hφ_compact.hasTemperateGrowth hφ_smooth

  let g : 𝓢(E n, ℂ) := SchwartzMap.smulLeftCLM ℂ φ f

  refine ⟨φ, hφ_smooth, hφ_compact, hφ_x, g, ?_⟩
  ext h
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, schwEmbed,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
  congr 1
  ext y
  simp only [g, SchwartzMap.smulLeftCLM_apply_apply hφ_temp, smul_eq_mul]
  ring

end ConeSupport
