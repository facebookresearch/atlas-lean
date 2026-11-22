/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped SchwartzMap
open TemperedDistribution LineDeriv

namespace DifferentialOperators

variable (n : ℕ)

/-- The `(n + 1)`-dimensional spacetime `ℝ^{1+n}`, with the first coordinate
playing the role of time and the remaining `n` coordinates the spatial ones. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

/-- The unit vector in the time direction of `SpaceTime n`. -/
def timeDirection : SpaceTime n :=
  EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)

/-- The unit vector in the `i`-th spatial direction of `SpaceTime n`. -/
def spatialDirection (i : Fin n) : SpaceTime n :=
  EuclideanSpace.single i.succ (1 : ℝ)

/-- The positive spatial Laplacian acting on tempered distributions on
`SpaceTime n`: `Σᵢ ∂ᵢ²` summed over the spatial directions. -/
def positiveSpatialLaplacian (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∑ i : Fin n, ∂_{spatialDirection n i} (∂_{spatialDirection n i} u)

/-- The heat operator `∂ₜ − Δ` on tempered distributions on `SpaceTime n`. -/
def heatOperator (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∂_{timeDirection n} u - positiveSpatialLaplacian n u

/-- A tempered distribution `u` vanishes on an open set `U` if it pairs to
zero with every Schwartz function whose support is contained in `U`. -/
def DistributionVanishesOn (u : 𝓢'(SpaceTime n, ℂ)) (U : Set (SpaceTime n)) : Prop :=
  ∀ φ : 𝓢(SpaceTime n, ℂ), tsupport (⇑φ) ⊆ U → u φ = 0

/-- The distributional support of `u`: the set of points without any open
neighbourhood on which `u` vanishes (i.e., the complement of the largest
open set on which `u` vanishes). -/
def distributionalSupport (u : 𝓢'(SpaceTime n, ℂ)) : Set (SpaceTime n) :=
  {x | ¬∃ U : Set (SpaceTime n), IsOpen U ∧ x ∈ U ∧ DistributionVanishesOn n u U}

/-- A tempered distribution has compact distributional support iff its
distributional support is a compact set. -/
def HasCompactDistributionalSupport (u : 𝓢'(SpaceTime n, ℂ)) : Prop :=
  IsCompact (distributionalSupport n u)

/-- The time coordinate (first component) of a point in `SpaceTime n`. -/
def timeCoord (x : SpaceTime n) : ℝ := x 0

/-- A tempered distribution `u` is supported in the half-space `{t ≥ c}` if
its distributional support lies in `{x | timeCoord x ≥ c}`. -/
def SupportedInTimeGeq (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) : Prop :=
  distributionalSupport n u ⊆ {x : SpaceTime n | timeCoord n x ≥ c}

/-- If two tempered distributions both vanish on an open set `U`, so does
their difference. -/
lemma distributionVanishesOn_sub {u v : 𝓢'(SpaceTime n, ℂ)} {U : Set (SpaceTime n)}
    (hu : DistributionVanishesOn n u U) (hv : DistributionVanishesOn n v U) :
    DistributionVanishesOn n (u - v) U := by
  intro φ hφ
  rw [show (u - v) φ = u φ - v φ from rfl, hu φ hφ, hv φ hφ, sub_self]

/-- The distributional support of `u - v` is contained in the union of the
distributional supports of `u` and `v`. -/
lemma distributionalSupport_sub_subset (u v : 𝓢'(SpaceTime n, ℂ)) :
    distributionalSupport n (u - v) ⊆
    distributionalSupport n u ∪ distributionalSupport n v := by
  intro x hx
  by_contra h
  simp only [Set.mem_union, not_or] at h
  obtain ⟨hnu, hnv⟩ := h
  simp only [distributionalSupport, Set.mem_setOf_eq, not_not] at hnu hnv
  obtain ⟨U₁, hU₁_open, hx_U₁, hU₁⟩ := hnu
  obtain ⟨U₂, hU₂_open, hx_U₂, hU₂⟩ := hnv
  exact hx ⟨U₁ ∩ U₂, hU₁_open.inter hU₂_open, ⟨hx_U₁, hx_U₂⟩,
    distributionVanishesOn_sub n
      (fun φ hφ => hU₁ φ (hφ.trans Set.inter_subset_left))
      (fun φ hφ => hU₂ φ (hφ.trans Set.inter_subset_right))⟩

/-- If `u` is supported in `{t ≥ a}` and `v` is supported in `{t ≥ b}`, then
`u - v` is supported in `{t ≥ min a b}`. -/
lemma supportedInTimeGeq_sub (u v : 𝓢'(SpaceTime n, ℂ))
    (a b : ℝ) (ha : SupportedInTimeGeq n u a) (hb : SupportedInTimeGeq n v b) :
    SupportedInTimeGeq n (u - v) (min a b) := by
  intro x hx
  have hsub := distributionalSupport_sub_subset n u v hx
  simp only [Set.mem_union] at hsub
  simp only [Set.mem_setOf_eq]
  rcases hsub with hu | hv
  · exact le_trans (min_le_left a b) (ha hu)
  · exact le_trans (min_le_right a b) (hb hv)

/-- A distribution with compact distributional support is supported in some
half-space `{t ≥ b}` (i.e. has a lower time bound). -/
lemma compact_support_time_bounded_below
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDistributionalSupport n f) :
    ∃ b : ℝ, SupportedInTimeGeq n f b := by
  by_cases hempty : (distributionalSupport n f) = ∅
  · exact ⟨0, fun x hx => (hempty ▸ hx : x ∈ (∅ : Set _)).elim⟩
  · have hne : Set.Nonempty (distributionalSupport n f) := Set.nonempty_iff_ne_empty.mpr hempty
    have hcont : Continuous (timeCoord n) :=
      PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0
    obtain ⟨x₀, _, hx₀_min⟩ := hf.exists_isMinOn hne hcont.continuousOn
    exact ⟨timeCoord n x₀, fun x hx => hx₀_min hx⟩

end DifferentialOperators

















namespace DifferentialOperators

variable (n : ℕ)

/-- The heat operator distributes over subtraction:
`(∂ₜ − Δ)(u − v) = (∂ₜ − Δ)u − (∂ₜ − Δ)v`. -/
lemma heatOperator_sub (u v : 𝓢'(SpaceTime n, ℂ)) :
    heatOperator n (u - v) = heatOperator n u - heatOperator n v := by
  simp only [heatOperator, positiveSpatialLaplacian, sub_eq_add_neg,
    lineDerivOp_add, lineDerivOp_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

end DifferentialOperators

end
