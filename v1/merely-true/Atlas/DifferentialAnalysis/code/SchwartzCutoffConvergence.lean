/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- A sequence of smooth bump functions `χ_m` on `E`, supported in
`B(0, m + 2)` and equal to one on `B(0, m + 1)`. -/
noncomputable def bumpSeq (m : ℕ) : ContDiffBump (0 : E) :=
  ⟨↑m + 1, ↑m + 2, by positivity, by linarith⟩

omit [NormedSpace ℝ E] [HasContDiffBump E] [FiniteDimensional ℝ E] in
/-- The inner radius of `bumpSeq m` is `m + 1`. -/
@[simp]
lemma bumpSeq_rIn (m : ℕ) : (bumpSeq (E := E) m).rIn = ↑m + 1 := rfl

omit [NormedSpace ℝ E] [HasContDiffBump E] [FiniteDimensional ℝ E] in
/-- The outer radius of `bumpSeq m` is `m + 2`. -/
@[simp]
lemma bumpSeq_rOut (m : ℕ) : (bumpSeq (E := E) m).rOut = ↑m + 2 := rfl

/-- The bump `bumpSeq m` is identically `1` on the closed ball of radius `m + 1`. -/
lemma bumpSeq_one_of_norm_le (m : ℕ) {x : E} (hx : ‖x‖ ≤ ↑m + 1) :
    bumpSeq (E := E) m x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hx

/-- Each `bumpSeq m` has temperate growth: it is compactly supported and smooth. -/
lemma bumpSeq_hasTemperateGrowth (m : ℕ) :
    Function.HasTemperateGrowth (fun x => (bumpSeq (E := E) m x : ℝ)) :=
  HasCompactSupport.hasTemperateGrowth (bumpSeq m).hasCompactSupport (bumpSeq m).contDiff

/-- Cutoff of a Schwartz function by `bumpSeq m`: multiplies `f` pointwise by the bump. -/
noncomputable def bumpCutoffMul (m : ℕ) (f : SchwartzMap E F) : SchwartzMap E F :=
  SchwartzMap.smulLeftCLM (𝕜 := ℝ) F (fun x => bumpSeq (E := E) m x) f

/-- Pointwise formula for the cutoff: `bumpCutoffMul m f x = χ_m(x) • f x`. -/
@[simp]
lemma bumpCutoffMul_apply (m : ℕ) (f : SchwartzMap E F) (x : E) :
    bumpCutoffMul m f x = bumpSeq (E := E) m x • f x := by
  unfold bumpCutoffMul
  rw [SchwartzMap.smulLeftCLM_apply (bumpSeq_hasTemperateGrowth m)]

/-- The cutoff `bumpCutoffMul m f` has compact support inside `B̄(0, m + 2)`. -/
lemma bumpCutoffMul_hasCompactSupport (m : ℕ) (f : SchwartzMap E F) :
    HasCompactSupport (bumpCutoffMul m f) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (↑m + 2))
    (isCompact_closedBall 0 _)
  intro x hx
  rw [Function.mem_support] at hx
  simp only [bumpCutoffMul_apply] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  have hout : (bumpSeq (E := E) m).rOut ≤ dist x 0 := by
    rw [dist_zero_right]; simp only [bumpSeq]; linarith
  have := (bumpSeq m).zero_of_le_dist hout
  simp [this] at hx

/-- The difference `f - χ_m f` vanishes in a neighbourhood of any point inside
`B(0, m + 1)`, since `χ_m ≡ 1` there. -/
lemma sub_bumpCutoffMul_eventuallyEq_zero (m : ℕ) (f : SchwartzMap E F) {x : E}
    (hx : ‖x‖ < ↑m + 1) :
    (fun y => (f - bumpCutoffMul m f) y) =ᶠ[nhds x] (fun _ => (0 : F)) := by
  have hmem : x ∈ Metric.ball (0 : E) (bumpSeq (E := E) m).rIn := by
    simp only [Metric.mem_ball, dist_zero_right, bumpSeq]; exact hx
  have hev := (bumpSeq (E := E) m).eventuallyEq_one_of_mem_ball hmem
  filter_upwards [hev] with y hy
  simp only [SchwartzMap.sub_apply, bumpCutoffMul_apply, Pi.one_apply] at hy ⊢
  rw [hy, one_smul, sub_self]

/-- All iterated Fréchet derivatives of `f - χ_m f` vanish on `B(0, m + 1)`. -/
lemma iteratedFDeriv_sub_bumpCutoffMul_eq_zero (m : ℕ) (f : SchwartzMap E F)
    (n : ℕ) {x : E} (hx : ‖x‖ < ↑m + 1) :
    iteratedFDeriv ℝ n (fun y => (f - bumpCutoffMul m f) y) x = 0 := by
  have hev := sub_bumpCutoffMul_eventuallyEq_zero m f hx
  have h := (hev.iteratedFDeriv ℝ n).self_of_nhds
  rw [h]
  rcases eq_or_ne n 0 with rfl | hn
  · ext v; simp
  · simp [iteratedFDeriv_const_of_ne hn (0 : F)]

end SchwartzMap

/-- If the `j`-th iterated derivative of a Schwartz map `g` vanishes on `B(0, R)`, then
the `(k, j)`-Schwartz seminorm is bounded by the `(k + 1, j)`-seminorm divided by `R`. -/
lemma SchwartzMap.seminorm_le_div_of_vanish
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (g : SchwartzMap E F) (k j : ℕ) (R : ℝ) (hR : 0 < R)
    (hvanish : ∀ x : E, ‖x‖ < R → iteratedFDeriv ℝ j (⇑g) x = 0) :
    (SchwartzMap.seminorm 𝕜 k j) g ≤ (SchwartzMap.seminorm 𝕜 (k + 1) j) g / R := by
  rw [div_eq_inv_mul]
  apply SchwartzMap.seminorm_le_bound 𝕜 k j g (by positivity)
  intro x
  by_cases hx : ‖x‖ < R
  · rw [hvanish x hx, norm_zero, mul_zero]; positivity
  · push Not at hx
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (⇑g) x‖
        = R⁻¹ * (R * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by
          rw [inv_mul_cancel_left₀ (ne_of_gt hR)]
      _ ≤ R⁻¹ * (‖x‖ * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by
          gcongr
      _ = R⁻¹ * (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j (⇑g) x‖) := by
          rw [pow_succ]; ring
      _ ≤ R⁻¹ * (SchwartzMap.seminorm 𝕜 (k + 1) j) g := by
          gcongr; exact SchwartzMap.le_seminorm 𝕜 (k + 1) j g x







namespace SchwartzMap


end SchwartzMap
