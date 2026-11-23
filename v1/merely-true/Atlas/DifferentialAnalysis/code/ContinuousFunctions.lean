/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz

open Set Filter Topology
open scoped ZeroAtInfty

namespace ContinuousFunctions

/-- For maps between metric spaces, the following are equivalent: continuity, openness of
preimages of open sets, closedness of preimages of closed sets, and sequential continuity
(Melrose Prop 1.1). -/
theorem continuous_iff_isOpen_preimage
    {X : Type*} {Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    List.TFAE [
      Continuous f,
      ∀ O : Set Y, IsOpen O → IsOpen (f ⁻¹' O),
      ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C),
      SeqContinuous f
    ] := by
  tfae_have 1 ↔ 2 := continuous_def
  tfae_have 1 ↔ 3 := continuous_iff_isClosed
  tfae_have 1 ↔ 4 := continuous_iff_seqContinuous
  tfae_finish


section PosNegDecomposition

variable {X : Type*} [TopologicalSpace X]

/-- Positive part `f⁺ = max(f, 0)` of a real-valued continuous function vanishing at infinity,
itself in `C₀(X, ℝ)`. -/
noncomputable def zeroAtInftyPosPart (f : C₀(X, ℝ)) : C₀(X, ℝ) where
  toFun := fun x => max (f x) 0
  continuous_toFun := (map_continuous f).max continuous_const
  zero_at_infty' := by
    have h := (zero_at_infty f).max (tendsto_const_nhds (x := (0 : ℝ)))
    simp only [max_self] at h
    exact h

/-- Negative part `f⁻ = max(-f, 0)` of a real-valued continuous function vanishing at infinity,
itself in `C₀(X, ℝ)`. -/
noncomputable def zeroAtInftyNegPart (f : C₀(X, ℝ)) : C₀(X, ℝ) where
  toFun := fun x => max (-f x) 0
  continuous_toFun := ((map_continuous f).neg).max continuous_const
  zero_at_infty' := by
    have hnf : Tendsto (fun x => -f x) (cocompact X) (𝓝 0) := by
      simpa only [neg_zero] using (zero_at_infty f).neg
    have h := hnf.max (tendsto_const_nhds (x := (0 : ℝ)))
    simp only [max_self] at h
    exact h

/-- Pointwise evaluation of the positive part: `f⁺(x) = max(f(x), 0)`. -/
@[simp]
theorem posPart_apply (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyPosPart f x = max (f x) 0 := rfl

/-- Pointwise evaluation of the negative part: `f⁻(x) = max(-f(x), 0)`. -/
@[simp]
theorem negPart_apply (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyNegPart f x = max (-f x) 0 := rfl

/-- Decomposition `f = f⁺ - f⁻` in `C₀(X, ℝ)`. -/
theorem decompose_pos_neg (f : C₀(X, ℝ)) :
    f = zeroAtInftyPosPart f - zeroAtInftyNegPart f := by
  ext x
  simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, posPart_apply, negPart_apply]
  exact (max_zero_sub_max_neg_zero_eq_self (f x)).symm

/-- Pointwise bound: `f⁺(x) ≤ |f(x)|`. -/
theorem posPart_le_abs (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyPosPart f x ≤ |f x| := by
  simp only [posPart_apply]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Pointwise bound: `f⁻(x) ≤ |f(x)|`. -/
theorem negPart_le_abs (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyNegPart f x ≤ |f x| := by
  simp only [negPart_apply]
  exact max_le (neg_le_abs _) (abs_nonneg _)

/-- Nonnegativity of the positive part: `0 ≤ f⁺(x)`. -/
theorem posPart_nonneg (f : C₀(X, ℝ)) (x : X) :
    0 ≤ zeroAtInftyPosPart f x := le_max_right _ _

/-- Nonnegativity of the negative part: `0 ≤ f⁻(x)`. -/
theorem negPart_nonneg (f : C₀(X, ℝ)) (x : X) :
    0 ≤ zeroAtInftyNegPart f x := le_max_right _ _

/-- Uniqueness of the `f⁺/f⁻` decomposition: any decomposition `f = g - h` with `g, h` both
nonnegative and pointwise bounded by `|f|` must coincide with `(f⁺, f⁻)`. -/
theorem decompose_unique (f g h : C₀(X, ℝ))
    (hdecomp : f = g - h)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hh_nonneg : ∀ x, 0 ≤ h x)
    (hg_le : ∀ x, g x ≤ |f x|)
    (hh_le : ∀ x, h x ≤ |f x|) :
    g = zeroAtInftyPosPart f ∧ h = zeroAtInftyNegPart f := by
  have hfx : ∀ x, f x = g x - h x := fun x => by
    have := DFunLike.congr_fun hdecomp x
    simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply] at this
    exact this
  constructor
  · ext x
    simp only [posPart_apply]
    rcases le_or_gt (f x) 0 with hle | hgt
    ·
      rw [max_eq_right hle]
      have hg_abs := hg_le x
      have hh_abs := hh_le x
      rw [abs_of_nonpos hle] at hg_abs hh_abs
      linarith [hg_nonneg x, hh_nonneg x, hfx x]
    ·
      rw [max_eq_left hgt.le]
      have hh_abs := hh_le x
      have hg_abs := hg_le x
      rw [abs_of_pos hgt] at hh_abs hg_abs
      linarith [hh_nonneg x, hfx x]
  · ext x
    simp only [negPart_apply]
    rcases le_or_gt (f x) 0 with hle | hgt
    ·
      rw [max_eq_left (by linarith)]
      have hg_abs := hg_le x
      have hh_abs := hh_le x
      rw [abs_of_nonpos hle] at hg_abs hh_abs
      linarith [hg_nonneg x, hh_nonneg x, hfx x]
    ·
      rw [max_eq_right (by linarith)]
      have hh_abs := hh_le x
      have hg_abs := hg_le x
      rw [abs_of_pos hgt] at hh_abs hg_abs
      linarith [hh_nonneg x, hfx x]

/-- Combined statement (Melrose Lemma 1.4): every `f ∈ C₀(X, ℝ)` admits the canonical
positive/negative decomposition `f = f⁺ - f⁻` with the appropriate dominance bounds, and the
decomposition is unique among such pairs. -/
theorem zeroAtInfty_unique_posNeg_decomposition (f : C₀(X, ℝ)) :
    f = zeroAtInftyPosPart f - zeroAtInftyNegPart f ∧
    (∀ x, (zeroAtInftyPosPart f) x ≤ |f x|) ∧
    (∀ x, (zeroAtInftyNegPart f) x ≤ |f x|) ∧
    (∀ g h : C₀(X, ℝ), f = g - h → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
      (∀ x, g x ≤ |f x|) → (∀ x, h x ≤ |f x|) →
      g = zeroAtInftyPosPart f ∧ h = zeroAtInftyNegPart f) :=
  ⟨decompose_pos_neg f, posPart_le_abs f, negPart_le_abs f, decompose_unique f⟩

end PosNegDecomposition

end ContinuousFunctions

namespace NormedSpaces

/-- Two norms on `V` are equivalent if they are mutually controlled by a single positive
constant, i.e. `(1/C) · norm₁ v ≤ norm₂ v ≤ C · norm₁ v` for all `v`. -/
def AreEquivalentNorms {V : Type*} (norm₁ norm₂ : V → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ v : V, (1 / C) * norm₁ v ≤ norm₂ v ∧ norm₂ v ≤ C * norm₁ v


end NormedSpaces

open Bornology Metric Set

namespace ContinuousLinearFunctional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous linear functional is continuous at the origin. -/
theorem continuousAt_zero_of_continuous (u : V →ₗ[ℝ] ℝ)
    (h : Continuous u) : ContinuousAt u 0 :=
  h.continuousAt

/-- A linear functional continuous at the origin sends the closed unit ball to a bounded set. -/
theorem bounded_image_closedBall_of_continuousAt_zero (u : V →ₗ[ℝ] ℝ)
    (h : ContinuousAt u 0) :
    IsBounded (u '' {f : V | ‖f‖ ≤ 1}) := by
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h 1 one_pos
  rw [isBounded_iff_forall_norm_le]


  have hδ2_pos : (0 : ℝ) < δ / 2 := half_pos hδ_pos
  refine ⟨(δ / 2)⁻¹, fun y hy => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hy
  simp only [mem_setOf_eq] at hf
  have norm_scaled : ‖(δ / 2) • f‖ < δ := by
    calc ‖(δ / 2) • f‖ = δ / 2 * ‖f‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ2_pos]
      _ ≤ δ / 2 * 1 := by gcongr
      _ < δ := by linarith
  have hd : dist (u ((δ / 2) • f)) (u 0) < 1 := hδ (by rwa [dist_zero_right])
  simp only [map_zero, dist_zero_right, map_smul, smul_eq_mul] at hd
  rw [norm_mul, show ‖(δ / 2 : ℝ)‖ = δ / 2 from by
    rw [Real.norm_eq_abs, abs_of_pos hδ2_pos]] at hd

  exact le_of_lt (by rwa [inv_eq_one_div, lt_div_iff₀ hδ2_pos, mul_comm])

/-- If a linear functional sends the unit ball to a bounded set, it satisfies a global linear
bound `‖u f‖ ≤ C · ‖f‖`. -/
theorem bound_of_bounded_image_closedBall (u : V →ₗ[ℝ] ℝ)
    (h : IsBounded (u '' {f : V | ‖f‖ ≤ 1})) :
    ∃ C, ∀ f : V, ‖u f‖ ≤ C * ‖f‖ := by
  rw [isBounded_iff_forall_norm_le] at h
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun f => ?_⟩
  by_cases hf : f = 0
  · simp [hf, map_zero]
  · have hfn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    have normalized_in_ball : ‖f‖⁻¹ • f ∈ {g : V | ‖g‖ ≤ 1} := by
      simp only [mem_setOf_eq, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hfn, le_refl]
    have hbound := hC (u (‖f‖⁻¹ • f)) ⟨‖f‖⁻¹ • f, normalized_in_ball, rfl⟩
    rw [map_smul, smul_eq_mul, norm_mul, norm_inv, norm_norm] at hbound

    calc ‖u f‖ = ‖f‖ * (‖f‖⁻¹ * ‖u f‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ hfn, one_mul]
      _ ≤ ‖f‖ * C := by gcongr
      _ = C * ‖f‖ := mul_comm _ _

/-- A linear functional satisfying a global linear bound `‖u f‖ ≤ C · ‖f‖` is continuous. -/
theorem continuous_of_bound (u : V →ₗ[ℝ] ℝ)
    (h : ∃ C, ∀ f : V, ‖u f‖ ≤ C * ‖f‖) :
    Continuous u := by
  obtain ⟨C, hC⟩ := h
  exact AddMonoidHomClass.continuous_of_bound u C hC

/-- The four standard characterisations of continuity for a real linear functional on a real
normed space are equivalent: global continuity, continuity at zero, bounded image of the unit
ball, and existence of an operator-norm bound. -/
theorem linearFunctional_continuous_tfae (u : V →ₗ[ℝ] ℝ) :
    List.TFAE [
      Continuous u,
      ContinuousAt u 0,
      IsBounded (u '' {f : V | ‖f‖ ≤ 1}),
      ∃ C, ∀ f : V, ‖u f‖ ≤ C * ‖f‖
    ] := by
  tfae_have 1 → 2 := continuousAt_zero_of_continuous u
  tfae_have 2 → 3 := bounded_image_closedBall_of_continuousAt_zero u
  tfae_have 3 → 4 := bound_of_bounded_image_closedBall u
  tfae_have 4 → 1 := continuous_of_bound u
  tfae_finish

end ContinuousLinearFunctional
