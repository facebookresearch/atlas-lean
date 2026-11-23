/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood

set_option autoImplicit false

noncomputable section

open Filter Topology


/-- A symplectic form on $M$: a smoothly varying nondegenerate skew-symmetric bilinear form $\omega_x : E \times E \to \mathbb{R}$ at each point. -/
structure SymplecticForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  form : M → E → E → ℝ
  bilinear_left : ∀ (x : M) (a b : ℝ) (v₁ v₂ w : E),
    form x (a • v₁ + b • v₂) w = a * form x v₁ w + b * form x v₂ w
  skewSymm : ∀ (x : M) (v w : E), form x v w = -(form x w v)
  nondegenerate : ∀ (x : M) (v : E), (∀ w : E, form x v w = 0) → v = 0

/-- $\varphi : M \to M$ is a symplectomorphism if $\varphi^* \omega = \omega$, i.e. $\omega_{\varphi(x)}(d\varphi_x v, d\varphi_x w) = \omega_x(v, w)$. -/
def IsSymplectomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (ω : SymplecticForm I M)
    (φ : M → M) : Prop :=
  ∀ (x : M) (v w : E),
    ω.form (φ x) (mfderiv I I φ x v) (mfderiv I I φ x w) = ω.form x v w

/-- $x$ is a critical point of $f : M \to \mathbb{R}$ if $df_x = 0$. -/
def IsCriticalPt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → ℝ) (x : M) : Prop :=
  mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0

/-- A $1$-form $\mu : M \to E^*$ is closed if its derivative is symmetric: $D\mu_x(v)(w) = D\mu_x(w)(v)$. -/
def IsClosed1Form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (μ : M → (E →L[ℝ] ℝ)) : Prop :=
  ∀ (x : M) (v w : E),
    (show E →L[ℝ] ℝ from mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) μ x v) w =
    (show E →L[ℝ] ℝ from mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) μ x w) v

/-- $H^1(M, \mathbb{R}) = 0$: every smooth closed $1$-form on $M$ is exact, i.e. $\mu = dh$ for some smooth $h$. -/
def DeRhamH1Vanishes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ (μ : M → (E →L[ℝ] ℝ)),
    ContMDiff I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) ⊤ μ →
    IsClosed1Form I μ →
    ∃ (h : M → ℝ), ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h ∧
      ∀ x : M, mfderiv I (modelWithCornersSelf ℝ ℝ) h x = μ x

/-- $\varphi$ is $C^1$-close to the identity: smooth, with $\|d\varphi_x - \mathrm{id}\| < 1$ at every point. -/
def IsC1CloseToId
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (φ : M → M) : Prop :=
  ContMDiff I I ⊤ φ ∧
    ∀ (x : M), ‖(show E →L[ℝ] E from mfderiv I I φ x) -
      ContinuousLinearMap.id ℝ E‖ < 1





/-- When $H^1(M, \mathbb{R}) = 0$, a closed $1$-form $\mu$ is exact ($\mu = dh$), and its zeros are precisely the critical points of $h$. -/
theorem closed_form_exact_zeros_eq_crit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (μ : M → (E →L[ℝ] ℝ))
    (hμ_smooth : ContMDiff I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) ⊤ μ)
    (hμ_closed : IsClosed1Form I μ)
    (hH1 : DeRhamH1Vanishes I M) :
    ∃ (h : M → ℝ), ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h ∧
      (∀ x : M, μ x = 0 ↔ IsCriticalPt I h x) := by

  obtain ⟨h, h_smooth, h_deriv⟩ := hH1 μ hμ_smooth hμ_closed

  exact ⟨h, h_smooth, fun x => by
    unfold IsCriticalPt
    constructor
    · intro hzero; rw [h_deriv x]; exact hzero
    · intro hcrit; rw [h_deriv x] at hcrit; exact hcrit⟩




/-- Fermat's lemma on manifolds: the manifold derivative of $f$ vanishes at any local minimum. -/
lemma mfderiv_eq_zero_of_isLocalMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f x)
    (hlmin : IsLocalMin f x) :
    mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0 := by
  simp only [mfderiv, hf, if_pos]
  have hrange : Set.range I = Set.univ := I.range_eq_univ
  rw [hrange, fderivWithin_univ]
  apply IsLocalMin.fderiv_eq_zero
  have hmap := map_extChartAt_nhds_of_boundaryless (I := I) (x := x)
  simp only [IsLocalMin, ← hmap, IsMinFilter, eventually_map]
  filter_upwards [hlmin, (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source (I := I) x)]
    with y hy hy_src
  simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
             PartialEquiv.refl_coe, id]
  rw [(extChartAt I x).left_inv hy_src, (extChartAt I x).left_inv (mem_extChartAt_source x)]
  exact hy

/-- Fermat's lemma on manifolds: the manifold derivative of $f$ vanishes at any local maximum. -/
lemma mfderiv_eq_zero_of_isLocalMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f x)
    (hlmax : IsLocalMax f x) :
    mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0 := by
  simp only [mfderiv, hf, if_pos]
  have hrange : Set.range I = Set.univ := I.range_eq_univ
  rw [hrange, fderivWithin_univ]
  apply IsLocalMax.fderiv_eq_zero
  have hmap := map_extChartAt_nhds_of_boundaryless (I := I) (x := x)
  simp only [IsLocalMax, ← hmap, IsMaxFilter, eventually_map]
  filter_upwards [hlmax, (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source (I := I) x)]
    with y hy hy_src
  simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
             PartialEquiv.refl_coe, id]
  rw [(extChartAt I x).left_inv hy_src, (extChartAt I x).left_inv (mem_extChartAt_source x)]
  exact hy

/-- Any smooth function on a nontrivial compact manifold has at least two distinct critical points (its global minimum and maximum). -/
theorem compact_manifold_two_critical_points
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    [CompactSpace M] [Nontrivial M]
    (f : M → ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f) :
    ∃ x y : M, x ≠ y ∧ IsCriticalPt I f x ∧ IsCriticalPt I f y := by

  have hne : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  have hcont : ContinuousOn f Set.univ := hf.continuous.continuousOn
  obtain ⟨xmin, _, hxmin⟩ := isCompact_univ.exists_isMinOn hne hcont
  obtain ⟨xmax, _, hxmax⟩ := isCompact_univ.exists_isMaxOn hne hcont
  by_cases hne_pts : xmin ≠ xmax
  ·
    refine ⟨xmin, xmax, hne_pts, ?_, ?_⟩
    ·
      exact mfderiv_eq_zero_of_isLocalMin (hf.mdifferentiableAt (by simp))
        (hxmin.isLocalMin (isOpen_univ.mem_nhds (Set.mem_univ _)))
    ·
      exact mfderiv_eq_zero_of_isLocalMax (hf.mdifferentiableAt (by simp))
        (hxmax.isLocalMax (isOpen_univ.mem_nhds (Set.mem_univ _)))
  ·
    simp only [not_not] at hne_pts
    subst hne_pts

    have hconst : ∀ y : M, f y = f xmin := by
      intro y
      have hle : f xmin ≤ f y := hxmin (Set.mem_univ y)
      have hge : f y ≤ f xmin := hxmax (Set.mem_univ y)
      linarith

    obtain ⟨a, b, hab⟩ := exists_pair_ne M

    refine ⟨a, b, hab, ?_, ?_⟩ <;> {
      unfold IsCriticalPt
      have heq : f = fun _ => f xmin := funext hconst
      rw [heq, mfderiv_const]
    }


