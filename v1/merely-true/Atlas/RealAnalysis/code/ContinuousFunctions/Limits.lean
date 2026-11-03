/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Separation.Hausdorff

open Filter Topology Set

namespace ContinuousFunctions

/-- `x` is a cluster point of `S` if every punctured neighborhood `(x - δ, x + δ) \ {x}`
of `x` meets `S`, i.e. for all `δ > 0` there exists `y ∈ S` with `y ≠ x` and
`|y - x| < δ`. -/
def IsClusterPoint (S : Set ℝ) (x : ℝ) : Prop :=
  ∀ δ > 0, ∃ y ∈ S, y ≠ x ∧ |y - x| < δ

/-- The elementary `ε`-`δ` notion `IsClusterPoint S x` agrees with Mathlib's
topological accumulation point `AccPt x (𝓟 S)`. -/
theorem cluster_point_iff_acc_point (S : Set ℝ) (x : ℝ) :
    IsClusterPoint S x ↔ AccPt x (𝓟 S) := by
  rw [accPt_iff_nhds]
  constructor
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨y, hyS, hyx, habs⟩ := h ε hε
    refine ⟨y, ⟨?_, hyS⟩, hyx⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [abs_sub_comm y x]
  · intro h δ hδ
    obtain ⟨y, ⟨hyU, hyS⟩, hyx⟩ := h _ (Metric.ball_mem_nhds x hδ)
    refine ⟨y, hyS, hyx, ?_⟩
    have := Metric.mem_ball.mp hyU
    rw [Real.dist_eq] at this
    linarith [abs_sub_comm y x]

/-- `f` converges to `L` at `c` along `S`, written informally `f(x) → L` as `x → c`,
if for every `ε > 0` there exists `δ > 0` such that for all `x ∈ S` with
`0 < |x - c| < δ` one has `|f x - L| < ε`. -/
def FunctionConvergesAt (f : ℝ → ℝ) (S : Set ℝ) (c L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, 0 < |x - c| → |x - c| < δ → |f x - L| < ε

/-- The elementary `ε`-`δ` definition `FunctionConvergesAt f S c L` is equivalent
to the Mathlib filter statement that `f` tends to `L` along the neighborhood
filter of `c` restricted to `S \ {c}`. -/
theorem function_limit_iff_tendsto (f : ℝ → ℝ) (S : Set ℝ) (c L : ℝ) :
    FunctionConvergesAt f S c L ↔
    Filter.Tendsto f (nhdsWithin c (S \ {c})) (nhds L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hfx⟩ := h ε hε
    refine ⟨δ, hδ, fun {x} hxmem hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    exact hfx x hxmem.1 (abs_pos.mpr (sub_ne_zero.mpr hxmem.2)) hdist
  · intro h ε hε
    obtain ⟨δ, hδ, hfx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hxS hpos hdist => ?_⟩
    have hxc : x ≠ c := by
      intro heq
      simp [heq] at hpos
    have hxmem : x ∈ S \ {c} := ⟨hxS, hxc⟩
    have hdist' : dist x c < δ := by rwa [Real.dist_eq]
    have := hfx hxmem hdist'
    rwa [Real.dist_eq] at this

/-- The right-hand limit `f(x) → L` as `x → c⁺` along `S`: for every `ε > 0`
there exists `δ > 0` such that for all `x ∈ S` with `c < x < c + δ` one has
`|f x - L| < ε`. -/
def RightLimit (f : ℝ → ℝ) (S : Set ℝ) (c L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, c < x → x < c + δ → |f x - L| < ε

/-- Uniqueness of the function limit: if `c` is a cluster point of `S` and `f`
converges both to `L₁` and to `L₂` at `c` along `S`, then `L₁ = L₂`. -/
theorem function_limit_unique (f : ℝ → ℝ) (S : Set ℝ) (c L₁ L₂ : ℝ)
    (hc : IsClusterPoint S c)
    (hL₁ : FunctionConvergesAt f S c L₁)
    (hL₂ : FunctionConvergesAt f S c L₂) : L₁ = L₂ := by
  have hne : (nhdsWithin c (S \ {c})).NeBot := by
    rwa [← accPt_principal_iff_nhdsWithin, ← cluster_point_iff_acc_point]
  exact tendsto_nhds_unique
    ((function_limit_iff_tendsto f S c L₁).mp hL₁)
    ((function_limit_iff_tendsto f S c L₂).mp hL₂)

end ContinuousFunctions
