/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.SchwartzPartition
import Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Atlas.DifferentialAnalysis.code.DistributionSupport
import Atlas.DifferentialAnalysis.code.SmoothingOperators

noncomputable section

open scoped SchwartzMap
open TemperedDistribution LineDeriv Distribution

namespace HeatEquation

variable (n : ℕ)

/-- Space-time `ℝ^(n+1)` for the heat equation, with the time coordinate at index `0` and
spatial coordinates at indices `1, …, n`. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

/-- The unit vector in the time direction (index `0`) in space-time. -/
def timeDirection : SpaceTime n :=
  EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)

/-- The `i`-th spatial unit vector in space-time (at index `i.succ`, since `0` is time). -/
def spatialDirection (i : Fin n) : SpaceTime n :=
  EuclideanSpace.single i.succ (1 : ℝ)

/-- The (positive) spatial Laplacian `Δ_x = Σ ∂²/∂xᵢ²` acting on tempered distributions on
space-time. -/
def positiveSpatialLaplacian (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∑ i : Fin n, ∂_{spatialDirection n i} (∂_{spatialDirection n i} u)

/-- The heat operator `∂_t - Δ_x` acting on tempered distributions on space-time. -/
def heatOperator (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∂_{timeDirection n} u - positiveSpatialLaplacian n u

/-- A tempered distribution has compact distributional support if its `dsupport` is compact. -/
def HasCompactDSupport (u : 𝓢'(SpaceTime n, ℂ)) : Prop :=
  IsCompact (dsupport u)

/-- The time coordinate of a space-time point `x`, i.e. `x 0`. -/
def timeCoord (x : SpaceTime n) : ℝ := x 0

/-- A tempered distribution `u` is supported in `{t ≥ c}` if its distributional support is
contained in the half-space `{x | timeCoord x ≥ c}`. -/
def SupportedInTimeGeq (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) : Prop :=
  dsupport u ⊆ {x : SpaceTime n | timeCoord n x ≥ c}

/-- `IsVanishingOn` is preserved by subtraction: if `u` and `v` both vanish on `s`, so does
`u - v`. -/
lemma isVanishingOn_sub {u v : 𝓢'(SpaceTime n, ℂ)} {s : Set (SpaceTime n)}
    (hu : IsVanishingOn u s) (hv : IsVanishingOn v s) :
    IsVanishingOn (u - v) s := by
  intro φ hφ
  rw [show (u - v) φ = u φ - v φ from rfl, hu φ hφ, hv φ hφ, sub_self]

/-- The distributional support of `u - v` is contained in the union of the supports of `u`
and `v`. -/
lemma dsupport_sub_subset (u v : 𝓢'(SpaceTime n, ℂ)) :
    dsupport (u - v) ⊆ dsupport u ∪ dsupport v := by
  intro x hx
  by_contra h
  simp only [Set.mem_union, not_or] at h
  obtain ⟨hnu, hnv⟩ := h
  simp only [Distribution.notMem_dsupport_iff] at hnu hnv
  obtain ⟨s₁, hvan₁, hopen₁, hx₁⟩ := hnu
  obtain ⟨s₂, hvan₂, hopen₂, hx₂⟩ := hnv
  have hvan : IsVanishingOn (u - v) (s₁ ∩ s₂) :=
    isVanishingOn_sub n (hvan₁.mono Set.inter_subset_left)
      (hvan₂.mono Set.inter_subset_right)
  have : x ∉ dsupport (u - v) := by
    simp only [Distribution.notMem_dsupport_iff]
    exact ⟨s₁ ∩ s₂, hvan, hopen₁.inter hopen₂, ⟨hx₁, hx₂⟩⟩
  exact this hx

/-- If `u` is supported in `{t ≥ a}` and `v` is supported in `{t ≥ b}`, then `u - v` is supported
in `{t ≥ min a b}`. -/
lemma supportedInTimeGeq_sub (u v : 𝓢'(SpaceTime n, ℂ))
    (a b : ℝ) (ha : SupportedInTimeGeq n u a) (hb : SupportedInTimeGeq n v b) :
    SupportedInTimeGeq n (u - v) (min a b) := by
  intro x hx
  have hsub := dsupport_sub_subset n u v hx
  simp only [Set.mem_union] at hsub
  simp only [Set.mem_setOf_eq]
  rcases hsub with hu | hv
  · exact le_trans (min_le_left a b) (ha hu)
  · exact le_trans (min_le_right a b) (hb hv)

/-- `SupportedInTimeGeq` is invariant under negation of the distribution. -/
lemma supportedInTimeGeq_neg (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) :
    SupportedInTimeGeq n (-u) c ↔ SupportedInTimeGeq n u c := by
  unfold SupportedInTimeGeq
  constructor
  · intro h x hx
    apply h
    rw [Distribution.mem_dsupport_iff] at hx ⊢
    intro C hvan hclosed
    apply hx C _ hclosed
    intro φ hφ
    have := hvan φ hφ
    show u φ = 0
    rwa [show (-u) φ = -(u φ) from rfl, neg_eq_zero] at this
  · intro h x hx
    apply h
    rw [Distribution.mem_dsupport_iff] at hx ⊢
    intro C hvan hclosed
    apply hx C _ hclosed
    intro φ hφ
    have := hvan φ hφ
    show -(u φ) = 0
    rw [this, neg_zero]

/-- A distribution with compact distributional support is automatically supported in some
half-space `{t ≥ b}`: the time coordinate attains its minimum on a compact set. -/
lemma compact_dsupport_time_bounded_below
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f) :
    ∃ b : ℝ, SupportedInTimeGeq n f b := by
  by_cases hempty : dsupport f = ∅
  · exact ⟨0, fun x hx => (hempty ▸ hx : x ∈ (∅ : Set _)).elim⟩
  · have hne : Set.Nonempty (dsupport f) := Set.nonempty_iff_ne_empty.mpr hempty
    have hcont : Continuous (timeCoord n) :=
      PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0
    obtain ⟨x₀, _, hx₀_min⟩ := hf.exists_isMinOn hne hcont.continuousOn
    exact ⟨timeCoord n x₀, fun x hx => hx₀_min hx⟩

/-- The classical heat-kernel density `(4πt)^(-n/2) · exp(-|x|²/(4t))` for `t > 0`, extended by
`0` for `t ≤ 0`. -/
noncomputable def heatKernelFun (v : SpaceTime n) : ℝ :=
  let t := v (0 : Fin (n + 1))
  if t > 0 then
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
      Real.exp (- ‖fun i : Fin n => v i.succ‖ ^ 2 / (4 * t))
  else 0

/-- The heat-kernel density is everywhere nonnegative. -/
lemma heatKernelFun_nonneg (v : SpaceTime n) : 0 ≤ heatKernelFun n v := by
  simp only [heatKernelFun]
  split_ifs with ht
  · apply mul_nonneg
    · exact Real.rpow_nonneg (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) ht.le) _
    · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The heat-kernel density vanishes whenever the time coordinate is nonpositive. -/
lemma heatKernelFun_eq_zero_of_time_nonpos (v : SpaceTime n)
    (hv : v (0 : Fin (n + 1)) ≤ 0) : heatKernelFun n v = 0 := by
  simp only [heatKernelFun]
  split_ifs with ht
  · linarith
  · rfl

/-- The heat-kernel measure on space-time: the Lebesgue measure weighted by the heat-kernel
density. -/
def heatKernelMeasure : MeasureTheory.Measure (SpaceTime n) :=
  MeasureTheory.Measure.withDensity MeasureTheory.volume
    (fun v => ENNReal.ofReal (heatKernelFun n v))

open MeasureTheory in
/-- The heat-kernel measure assigns measure zero to the half-space `{t ≤ 0}`. -/
lemma heatKernelMeasure_nonpos_eq_zero :
    (heatKernelMeasure n) {v : SpaceTime n | v 0 ≤ 0} = 0 := by
  have hms : MeasurableSet {v : SpaceTime n | v 0 ≤ 0} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [heatKernelMeasure, withDensity_apply _ hms]
  exact setLIntegral_eq_zero hms (fun v (hv : v 0 ≤ 0) => by
    simp only [Pi.zero_apply]
    rw [heatKernelFun_eq_zero_of_time_nonpos n v hv, ENNReal.ofReal_zero])

/-- For `t ≥ 1`, the heat-kernel density is bounded above by `1`. -/
lemma heatKernelFun_le_one_of_time_ge_one (v : SpaceTime n)
    (ht : v (0 : Fin (n+1)) ≥ 1) : heatKernelFun n v ≤ 1 := by
  simp only [heatKernelFun]
  split_ifs with h
  · exact le_trans (mul_le_one₀
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
      (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))) le_rfl
  · linarith

open MeasureTheory in
set_option maxHeartbeats 800000 in
/-- On the half-space `{t ≥ 1}`, the heat-kernel measure is dominated by Lebesgue measure
(since the density there is at most `1`). -/
lemma heatKernelMeasure_le_volume_on_time_ge_one :
    (heatKernelMeasure n).restrict {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1} ≤
    MeasureTheory.volume.restrict {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1} := by
  rw [MeasureTheory.Measure.le_iff]
  intro A hA
  rw [MeasureTheory.Measure.restrict_apply hA, MeasureTheory.Measure.restrict_apply hA]
  have hms : MeasurableSet (A ∩ {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1}) :=
    hA.inter (measurableSet_le (by fun_prop) (by fun_prop))
  rw [heatKernelMeasure, MeasureTheory.withDensity_apply _ hms]
  calc ∫⁻ v in A ∩ {v | v (0 : Fin (n+1)) ≥ 1},
        ENNReal.ofReal (heatKernelFun n v) ∂MeasureTheory.volume
      ≤ ∫⁻ _ in A ∩ {v | v (0 : Fin (n+1)) ≥ 1}, 1 ∂MeasureTheory.volume := by
        apply MeasureTheory.setLIntegral_mono (by fun_prop)
        intro v hv
        have hvS : v (0 : Fin (n+1)) ≥ 1 := hv.2
        exact ENNReal.ofReal_le_one.mpr
          (heatKernelFun_le_one_of_time_ge_one n v hvS)
    _ = MeasureTheory.volume (A ∩ {v | v (0 : Fin (n+1)) ≥ 1}) := by simp

end HeatEquation


/-- The Gaussian `exp(-b·|v|²)` on Euclidean space `ℝ^m` is Lebesgue integrable for any `b > 0`. -/
lemma HeatEquation.integrable_rexp_neg_mul_sq_norm_euclidean (m : ℕ) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin m) => Real.exp (-b * ‖v‖ ^ 2))
      MeasureTheory.volume := by
  have hcint := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show (0 : ℝ) < (↑b : ℂ).re by simp [hb]) (0 : ℂ) (0 : EuclideanSpace ℝ (Fin m))
  simp only [zero_mul, add_zero] at hcint
  refine hcint.re.congr (MeasureTheory.ae_of_all _ fun v => ?_)
  simp only
  have h1 : (-↑b * ↑‖v‖ ^ 2 : ℂ) = ↑(-b * ‖v‖ ^ 2) := by push_cast; ring
  rw [h1]; exact Complex.ofReal_re _








open HeatEquation in
/-- The heat-kernel density is measurable. -/
lemma HeatEquation.heatKernelFun_measurable (n : ℕ) : Measurable (heatKernelFun n) := by
  unfold heatKernelFun
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
  · exact (by fun_prop : Measurable _).mul (by fun_prop)
  · exact measurable_const









































namespace HeatEquation

variable (n : ℕ)

/-- The heat operator is linear, in particular `heatOperator (u - v) = heatOperator u
- heatOperator v`. -/
lemma heatOperator_sub (u v : 𝓢'(SpaceTime n, ℂ)) :
    heatOperator n (u - v) = heatOperator n u - heatOperator n v := by
  simp only [heatOperator, positiveSpatialLaplacian, sub_eq_add_neg,
    lineDerivOp_add, lineDerivOp_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel


end HeatEquation

end
