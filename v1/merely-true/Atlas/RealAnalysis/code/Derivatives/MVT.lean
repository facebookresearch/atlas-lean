/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- Characterization of relative extrema in terms of an explicit `δ`-neighborhood.
For `f : ℝ → ℝ`, `S ⊆ ℝ`, and `c ∈ S`:
`f` has a relative maximum at `c` on `S` (`IsLocalMaxOn f S c`) iff there exists `δ > 0`
such that for all `x ∈ S` with `|x - c| < δ`, `f x ≤ f c`; and analogously, `f` has a
relative minimum at `c` on `S` iff there exists `δ > 0` such that for all `x ∈ S` with
`|x - c| < δ`, `f c ≤ f x`. -/
theorem relative_extremum_def (f : ℝ → ℝ) (S : Set ℝ) (c : ℝ) (_hc : c ∈ S) :
    (IsLocalMaxOn f S c ↔ ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → f x ≤ f c) ∧
    (IsLocalMinOn f S c ↔ ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → f c ≤ f x) := by
  have key : ∀ (q : ℝ → Prop),
      (∀ᶠ x in nhdsWithin c S, q x) ↔ ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → q x := by
    intro q
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    simp only [Real.dist_eq]
    constructor
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun x hxS hd => h hd hxS⟩
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun x hd hxS => h x hxS hd⟩
  exact ⟨key _, key _⟩

/-- Fermat's interior extremum theorem: if `f : ℝ → ℝ` attains a (global) local maximum or
local minimum at an interior point `c`, and `f` is differentiable at `c`, then the derivative
of `f` at `c` vanishes, i.e. `deriv f c = 0`. -/
theorem fermats_theorem (f : ℝ → ℝ) (c : ℝ)
    (hext : IsLocalMax f c ∨ IsLocalMin f c) (_hd : DifferentiableAt ℝ f c) :
    deriv f c = 0 := by
  rcases hext with hmax | hmin
  · exact hmax.deriv_eq_zero
  · exact hmin.deriv_eq_zero

/-- Rolle's theorem: if `f : ℝ → ℝ` is continuous on the closed interval `[a, b]`,
differentiable at every point of the open interval `(a, b)`, and satisfies `f a = f b`,
then there exists some `c ∈ (a, b)` at which the derivative vanishes, i.e. `deriv f c = 0`. -/
theorem rolle (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (_hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (heq : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc heq

/-- The Mean Value Theorem: if `f : ℝ → ℝ` is continuous on `[a, b]` and differentiable at
every point of `(a, b)`, then there exists some `c ∈ (a, b)` such that
`f b - f a = deriv f c * (b - a)`. -/
theorem mean_value_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Set.Ioo a b, f b - f a = deriv f c * (b - a) := by
  have hfd' : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun x hx => (hfd x hx).differentiableWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope f hab hfc hfd'
  have hba : (b - a) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  exact ⟨c, hc, by rw [hc', div_mul_cancel₀ (f b - f a) hba]⟩

/-- Zero derivative implies constant: if `f : ℝ → ℝ` is differentiable on a convex set
`I ⊆ ℝ` (i.e. an interval) and `deriv f x = 0` for every `x ∈ I`, then `f` is constant on
`I`, i.e. `f x = f y` for all `x, y ∈ I`. -/
theorem zero_deriv_imp_constant (f : ℝ → ℝ) (I : Set ℝ)
    (hI : Convex ℝ I)
    (hfd : DifferentiableOn ℝ f I)
    (hf' : ∀ x ∈ I, deriv f x = 0) :
    ∀ x ∈ I, ∀ y ∈ I, f x = f y := by
  intro x hx y hy
  have hfc : ContinuousOn f I := hfd.continuousOn
  have hDiffInt : DifferentiableOn ℝ f (interior I) := hfd.mono interior_subset
  have hDerivNN : ∀ z ∈ interior I, (0 : ℝ) ≤ deriv f z := by
    intro z hz; rw [hf' z (interior_subset hz)]
  have hDerivNP : ∀ z ∈ interior I, deriv f z ≤ (0 : ℝ) := by
    intro z hz; rw [hf' z (interior_subset hz)]
  have hmono : MonotoneOn f I :=
    monotoneOn_of_deriv_nonneg hI hfc hDiffInt hDerivNN
  have hanti : AntitoneOn f I :=
    antitoneOn_of_deriv_nonpos hI hfc hDiffInt hDerivNP
  rcases le_total x y with hle | hle
  · exact le_antisymm (hmono hx hy hle) (hanti hx hy hle)
  · exact (le_antisymm (hmono hy hx hle) (hanti hy hx hle)).symm

/-- Monotonicity characterized by the sign of the derivative on an interval.
If `f : ℝ → ℝ` is continuous on `[a, b]` and differentiable at every point of `(a, b)`, then:
(1) `f` is monotonically increasing on `[a, b]` iff `0 ≤ deriv f x` for all `x ∈ (a, b)`;
(2) `f` is monotonically decreasing on `[a, b]` iff `deriv f x ≤ 0` for all `x ∈ (a, b)`. -/
theorem monotonicity_and_derivatives (f : ℝ → ℝ) (a b : ℝ) (_hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    (MonotoneOn f (Set.Icc a b) ↔ ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x) ∧
    (AntitoneOn f (Set.Icc a b) ↔ ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) := by
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hint : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  have hDiffOn : DifferentiableOn ℝ f (interior (Set.Icc a b)) := by
    rw [hint]
    intro x hx
    exact (hfd x hx).differentiableWithinAt
  constructor
  ·
    constructor
    ·
      intro hmono x hx
      have hxab : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
      have hdiff : DifferentiableAt ℝ f x := hfd x hx
      have htend := hdiff.hasDerivAt.tendsto_slope_zero_right
      apply ge_of_tendsto htend
      have hxb : x < b := hx.2
      have hev_lt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < b - x :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      have hev_pos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t :=
        eventually_nhdsWithin_of_forall (fun _ hx => hx)
      apply (hev_pos.and hev_lt).mono
      intro t ⟨ht_pos, ht_lt⟩
      have hxt : x + t ∈ Set.Icc a b := ⟨by linarith [hx.1], by linarith⟩
      have hle : f x ≤ f (x + t) := hmono hxab hxt (by linarith)
      simp only [smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht_pos)) (sub_nonneg.mpr hle)
    ·
      intro hnn
      exact monotoneOn_of_deriv_nonneg hconv hfc hDiffOn (fun x hx => hnn x (hint ▸ hx))
  ·
    constructor
    ·
      intro hanti x hx
      have hxab : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
      have hdiff : DifferentiableAt ℝ f x := hfd x hx
      have htend := hdiff.hasDerivAt.tendsto_slope_zero_right
      apply le_of_tendsto htend
      have hxb : x < b := hx.2
      have hev_lt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < b - x :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      have hev_pos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t :=
        eventually_nhdsWithin_of_forall (fun _ hx => hx)
      apply (hev_pos.and hev_lt).mono
      intro t ⟨ht_pos, ht_lt⟩
      have hxt : x + t ∈ Set.Icc a b := ⟨by linarith [hx.1], by linarith⟩
      have hle : f (x + t) ≤ f x := hanti hxab hxt (by linarith)
      simp only [smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht_pos)) (sub_nonpos.mpr hle)
    ·
      intro hnn
      exact antitoneOn_of_deriv_nonpos hconv hfc hDiffOn (fun x hx => hnn x (hint ▸ hx))
