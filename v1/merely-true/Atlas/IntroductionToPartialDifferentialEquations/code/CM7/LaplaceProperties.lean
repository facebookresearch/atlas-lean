/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.HaarToSphere

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic
open Set Metric MeasureTheory Topology Filter

noncomputable section

namespace CM7

/-- A `PDEDomain` in $\mathbb{R}^n$ is a connected open subset, the natural setting in
which to pose boundary-value problems for PDEs. -/
structure PDEDomain (n : ℕ) where
  carrier : Set (Fin n → ℝ)
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier

/-- The Laplacian $\Delta u(x) = \sum_{i=1}^n \partial_i^2 u(x)$ of a function
$u : \mathbb{R}^n \to \mathbb{R}$, defined using iterated Fréchet derivatives applied to the
standard basis vectors $e_i$. -/
noncomputable def Laplacian (n : ℕ) (u : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single i 1)

/-- Linearity of the Laplacian under subtraction: for $C^2$ functions $u, v$ on an open
set $\Omega$, we have $\Delta(u - v)(x) = \Delta u(x) - \Delta v(x)$ at every $x \in \Omega$. -/
theorem laplacian_sub {n : ℕ} {u v : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    Laplacian n (fun x => u x - v x) x = Laplacian n u x - Laplacian n v x := by

  have hu_diff : ∀ᶠ y in nhds x, DifferentiableAt ℝ u y := by
    have : DifferentiableOn ℝ u Ω := hu.differentiableOn (by norm_num)
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact this.differentiableAt (hΩ.mem_nhds hy)
  have hv_diff : ∀ᶠ y in nhds x, DifferentiableAt ℝ v y := by
    have : DifferentiableOn ℝ v Ω := hv.differentiableOn (by norm_num)
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact this.differentiableAt (hΩ.mem_nhds hy)

  have hu2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x := by
    intro i
    have : ContDiffOn ℝ (1 + 1) u Ω := by exact_mod_cast hu
    have h_fderiv_diff : DifferentiableOn ℝ (fderiv ℝ u) Ω :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp this).2.2.differentiableOn (by norm_num)
    exact (h_fderiv_diff.differentiableAt (hΩ.mem_nhds hx)).clm_apply (differentiableAt_const _)
  have hv2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ v y (Pi.single i 1)) x := by
    intro i
    have : ContDiffOn ℝ (1 + 1) v Ω := by exact_mod_cast hv
    have h_fderiv_diff : DifferentiableOn ℝ (fderiv ℝ v) Ω :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp this).2.2.differentiableOn (by norm_num)
    exact (h_fderiv_diff.differentiableAt (hΩ.mem_nhds hx)).clm_apply (differentiableAt_const _)

  simp only [Laplacian]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i

  have h_inner : ∀ᶠ y in nhds x, fderiv ℝ (fun z => u z - v z) y (Pi.single i 1) =
      fderiv ℝ u y (Pi.single i 1) - fderiv ℝ v y (Pi.single i 1) := by
    filter_upwards [hu_diff, hv_diff] with y hy_u hy_v
    rw [fderiv_fun_sub hy_u hy_v, ContinuousLinearMap.sub_apply]

  rw [Filter.EventuallyEq.fderiv_eq h_inner]

  rw [fderiv_fun_sub (hu2 i) (hv2 i)]
  simp [ContinuousLinearMap.sub_apply]

/-- The Laplacian commutes with negation: $\Delta(-u) = -\Delta u$. -/
theorem laplacian_neg {n : ℕ} (u : (Fin n → ℝ) → ℝ) :
    Laplacian n (fun x => -u x) = fun x => -Laplacian n u x := by
  ext x
  simp only [Laplacian, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  have h1 : ∀ y, fderiv ℝ (fun x => -u x) y = -fderiv ℝ u y := fun y => fderiv_fun_neg
  simp_rw [h1, ContinuousLinearMap.neg_apply]
  rw [fderiv_fun_neg]
  simp

/-- The Laplacian of a constant function is identically zero: $\Delta c = 0$. -/
theorem laplacian_const {n : ℕ} (c : ℝ) :
    Laplacian n (fun _ : Fin n → ℝ => c) = fun _ => 0 := by
  ext x
  simp only [Laplacian]
  apply Finset.sum_eq_zero
  intro i _
  have h1 : ∀ y : Fin n → ℝ, fderiv ℝ (fun _ : Fin n → ℝ => c) y = 0 :=
    fun y => fderiv_const_apply c
  simp_rw [h1]
  simp [fderiv_const_apply]

/-- A function $u : \mathbb{R}^n \to \mathbb{R}$ is harmonic on an open set $\Omega$ if it
is $C^2$ on $\Omega$ and satisfies Laplace's equation $\Delta u(x) = 0$ for all $x \in \Omega$. -/
structure IsHarmonic {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop where
  contDiffOn : ContDiffOn ℝ 2 u Ω
  laplacian_eq_zero : ∀ x ∈ Ω, Laplacian n u x = 0

/-- The predicate that $u$ solves Poisson's equation $\Delta u = f$ on $\Omega$, i.e. for
every $x \in \Omega$, $\Delta u(x) = f(x)$. -/
def IsPoisson {n : ℕ} (u : (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (Ω : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, Laplacian n u x = f x

/-- A harmonic function is $C^2$ on its domain. -/
theorem harmonic_is_contDiffOn {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : IsHarmonic u Ω) :
    ContDiffOn ℝ 2 u Ω :=
  hu.contDiffOn

/-- The difference of two harmonic functions on an open set is harmonic. -/
lemma IsHarmonic.sub {n : ℕ} {u v : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω) (hv : IsHarmonic v Ω) :
    IsHarmonic (fun x => u x - v x) Ω where
  contDiffOn := hu.contDiffOn.sub hv.contDiffOn
  laplacian_eq_zero := by
    intro x hx
    rw [laplacian_sub hΩ hu.contDiffOn hv.contDiffOn hx]
    rw [hu.laplacian_eq_zero x hx, hv.laplacian_eq_zero x hx, sub_self]

/-- The negation of a harmonic function is harmonic. -/
lemma IsHarmonic.neg {n : ℕ} {u : (Fin n → ℝ) → ℝ} {Ω : Set (Fin n → ℝ)}
    (hu : IsHarmonic u Ω) :
    IsHarmonic (fun x => -u x) Ω where
  contDiffOn := hu.contDiffOn.neg
  laplacian_eq_zero := by
    intro x hx
    simp [laplacian_neg, hu.laplacian_eq_zero x hx]

/-- The Dirichlet energy $\int_\Omega \|\nabla u(x)\|^2\, dx$ of $u$ on $\Omega$. -/
noncomputable def gradNormSquaredIntegral {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : ℝ :=
  ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2







/-- The Dirichlet energy $\int_\Omega \|\nabla w\|^2$ is nonnegative. -/
theorem gradNormSquaredIntegral_nonneg {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) :
    gradNormSquaredIntegral w Ω ≥ 0 := by
  simp only [gradNormSquaredIntegral, ge_iff_le]
  apply integral_nonneg
  intro x; positivity

/-- If the Fréchet derivative of $w$ is continuous on $\overline{\Omega}$ and $\Omega$ is bounded,
then $\|\nabla w\|^2$ is integrable on $\Omega$. -/
theorem gradNormSquared_integrableOn {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω)) :
    IntegrableOn (fun x => ‖fderiv ℝ w x‖ ^ 2) Ω := by
  have hK : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hf_cont : ContinuousOn (fun x => ‖fderiv ℝ w x‖ ^ 2) (closure Ω) :=
    (ContinuousOn.norm hcont_fderiv).pow 2
  exact (hf_cont.integrableOn_compact hK).mono_set subset_closure

/-- A $C^1$ function on an open set has continuous Fréchet derivative on that set. -/
theorem fderiv_continuousOn_of_contDiffOn {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω) :
    ContinuousOn (fun x => fderiv ℝ w x) Ω :=
  hw_c1.continuousOn_fderiv_of_isOpen hΩo le_rfl

/-- If a $C^1$ function $w$ on a bounded open set $\Omega$ has vanishing Dirichlet energy
$\int_\Omega \|\nabla w\|^2 = 0$, then $\nabla w = 0$ pointwise on $\Omega$. -/
theorem grad_zero_of_gradNormSquaredIntegral_zero {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω)
    (_hw_diff : DifferentiableOn ℝ w Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (hw : gradNormSquaredIntegral w Ω = 0) :
    ∀ x ∈ Ω, fderiv ℝ w x = 0 := by

  set g : (Fin n → ℝ) → ℝ := fun x => ‖fderiv ℝ w x‖ ^ 2 with hg_def

  have hg_int := gradNormSquared_integrableOn w Ω hΩo hΩb hcont_fderiv
  have hfderiv_cont := fderiv_continuousOn_of_contDiffOn w Ω hΩo hw_c1

  have hg_cont : ContinuousOn g Ω := (ContinuousOn.norm hfderiv_cont).pow 2

  have hg_nonneg_ae : (0 : (Fin n → ℝ) → ℝ) ≤ᵐ[MeasureTheory.MeasureSpace.volume.restrict Ω] g := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hΩo.measurableSet]
    exact ae_of_all _ (fun x _ => by positivity)
  have hg_ae : g =ᵐ[MeasureTheory.MeasureSpace.volume.restrict Ω] 0 := by
    rwa [← setIntegral_eq_zero_iff_of_nonneg_ae hg_nonneg_ae hg_int]

  have hg_zero : Set.EqOn g (fun _ => (0 : ℝ)) Ω :=
    Measure.eqOn_open_of_ae_eq hg_ae hΩo hg_cont continuousOn_const

  intro x hx
  have h := hg_zero hx
  simp [hg_def] at h
  exact h

/-- If $w$ has zero Dirichlet energy on a connected, bounded open set $\Omega$ and is
continuous up to the boundary, then $w$ is constant on $\overline{\Omega}$. -/
theorem gradNormSquared_zero_implies_constant {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hw_diff : DifferentiableOn ℝ w Ω)
    (hw_c1 : ContDiffOn ℝ 1 w Ω)
    (hw_cont : ContinuousOn w (closure Ω))
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (hw : gradNormSquaredIntegral w Ω = 0) :
    ∃ c : ℝ, ∀ x ∈ closure Ω, w x = c := by

  have h_fderiv_zero : Set.EqOn (fderiv ℝ w) 0 Ω :=
    fun x hx => grad_zero_of_gradNormSquaredIntegral_zero w Ω hΩo hw_diff hw_c1 hΩb hcont_fderiv hw x hx


  obtain ⟨c, hc_Ω⟩ := hΩo.exists_is_const_of_fderiv_eq_zero hΩc.isPreconnected hw_diff h_fderiv_zero

  have hc_closure : Set.EqOn w (fun _ => c) (closure Ω) :=
    Set.EqOn.of_subset_closure
      (fun x hx => hc_Ω x hx)
      hw_cont
      continuousOn_const
      subset_closure
      le_rfl
  exact ⟨c, fun x hx => hc_closure hx⟩

/-- For $n \geq 1$, the whole space $\mathbb{R}^n$ (modeled as `Fin n → ℝ`) is not bounded. -/
lemma not_isBounded_univ_fin_real {n : ℕ} (hn : 0 < n) :
    ¬ Bornology.IsBounded (Set.univ : Set (Fin n → ℝ)) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  push Not
  intro r
  let i₀ : Fin n := ⟨0, hn⟩
  let x : Fin n → ℝ := Function.update 0 i₀ (|r| + 1)
  intro h
  have hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) r := h (Set.mem_univ x)
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have h1 : ‖x i₀‖ ≤ ‖x‖ := norm_le_pi_norm x i₀
  have h2 : x i₀ = |r| + 1 := by simp [x, Function.update_self]
  have h3 : ‖x i₀‖ = |r| + 1 := by rw [h2]; simp; linarith [abs_nonneg r]
  have h4 : |r| + 1 ≤ r := by linarith
  linarith [abs_nonneg r, le_abs_self r]

/-- A nonempty, bounded, open, connected subset of $\mathbb{R}^n$ (with $n \geq 1$) has
nonempty topological boundary. -/
theorem frontier_nonempty_of_bounded_open_connected {n : ℕ}
    (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (_hΩo : IsOpen Ω) (_hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) :
    (frontier Ω).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h

  have hclopen : IsClopen Ω := isClopen_iff_frontier_eq_empty.mpr h

  have hΩ_univ : Ω = Set.univ := hclopen.eq_univ hΩne
  rw [hΩ_univ] at hΩb

  exact absurd hΩb (not_isBounded_univ_fin_real hn)


/-- Glue lemma: a function differentiable at every point of $\overline{\Omega}$ is differentiable
at any particular point of $\overline{\Omega}$. -/
theorem differentiableAt_of_contDiffOn_closure {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω) (_hu_reg : ContDiffOn ℝ 2 u Ω)
    (_hu_cont : ContinuousOn u (closure Ω))
    (hu_diff_closure : ∀ x ∈ closure Ω, DifferentiableAt ℝ u x)
    (x : Fin n → ℝ) (hx : x ∈ closure Ω) :
    DifferentiableAt ℝ u x :=
  hu_diff_closure x hx

/-- If $\nabla w = 0$ on an open set $\Omega$ and $\nabla w$ is continuous on $\overline{\Omega}$,
then $\nabla w = 0$ extends to the boundary $\partial \Omega$. -/
theorem fderiv_zero_on_frontier_of_zero_on_open {n : ℕ}
    (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (_hΩo : IsOpen Ω)
    (h_zero : ∀ y ∈ Ω, fderiv ℝ w y = 0)
    (hcont_fderiv : ContinuousOn (fun x => fderiv ℝ w x) (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ frontier Ω) :
    fderiv ℝ w x = 0 := by
  have hx_cl : x ∈ closure Ω := frontier_subset_closure hx
  have h_eq : Set.EqOn (fun x => fderiv ℝ w x) (fun _ => 0) (closure Ω) :=
    Set.EqOn.of_subset_closure h_zero hcont_fderiv continuousOn_const subset_closure le_rfl
  exact h_eq hx_cl








/-- The spherical mean of $u$ around the point $x$ at radius $r$: the average value of $u$ over
the sphere of radius $r$ centered at $x$, taken with respect to the $(n-1)$-dimensional Hausdorff
measure. By convention, the value at $r = 0$ is $u(x)$. -/
noncomputable def sphericalMean {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then u x
  else ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
    u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- The "spherical-average" function $r \mapsto \fint_{S^{n-1}} u(x + r\omega) \, d\sigma(\omega)$,
i.e. `sphericalMean u x r` but without the special-case branch at $r = 0$. -/
noncomputable def sphericalAvgFun {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ → ℝ :=
  fun r => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
    u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- For a harmonic function $u$ on the ball $B(x, R)$, the spherical average function
$r \mapsto \fint_{S^{n-1}} u(x + r\omega)\, d\sigma(\omega)$ is differentiable on $(0, R)$. -/
theorem sphericalAvgFun_differentiableOn_Ioo {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (hR : 0 < R) (hu : IsHarmonic u (Metric.ball x R)) :
    DifferentiableOn ℝ (sphericalAvgFun u x) (Set.Ioo 0 R) := by
  have huc := hu.contDiffOn
  set μ := (Measure.hausdorffMeasure (↑(n - 1) : ℝ) : Measure (Fin n → ℝ))
  by_cases hfin : μ (Metric.sphere (0 : Fin n → ℝ) 1) = ⊤
  ·
    have heq : sphericalAvgFun u x = fun _ => 0 := by
      ext r
      show ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1, u (x + r • ω) ∂μ = 0
      rw [setAverage_eq]
      have : (μ.real (Metric.sphere (0 : Fin n → ℝ) 1)) = 0 := by
        simp [Measure.real, hfin]
      rw [this, inv_zero, zero_smul]
    rw [heq]; exact differentiableOn_const 0
  ·
    have hfin' : μ (Metric.sphere (0 : Fin n → ℝ) 1) < ⊤ := lt_top_iff_ne_top.mpr hfin
    set ν := μ.restrict (Metric.sphere (0 : Fin n → ℝ) 1)
    haveI hν_fin : IsFiniteMeasure ν := ⟨by rwa [Measure.restrict_apply_univ]⟩
    set c : ℝ := (μ.real (Metric.sphere (0 : Fin n → ℝ) 1))⁻¹
    have heq_fn : sphericalAvgFun u x = c • (fun r => ∫ ω, u (x + r • ω) ∂ν) := by
      ext r; exact setAverage_eq μ _ _
    rw [heq_fn]
    apply DifferentiableOn.const_smul
    intro r₀ hr₀
    apply DifferentiableAt.differentiableWithinAt
    apply HasDerivAt.differentiableAt
    set s := Set.Ioo (r₀ / 2) ((r₀ + R) / 2)
    have hs_nhds : s ∈ nhds r₀ := isOpen_Ioo.mem_nhds
      ⟨by linarith [hr₀.1], by linarith [hr₀.2]⟩
    have hs_pos : ∀ r ∈ s, 0 < r := fun r hr => by linarith [hr.1, hr₀.1]
    have hs_lt_R : ∀ r ∈ s, r < R := fun r hr => by linarith [hr.2, hr₀.2]
    have hmem_ball : ∀ r ∈ s, ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        x + r • ω ∈ Metric.ball x R := by
      intro r hr ω hω
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (hs_pos r hr).le]
      have hω1 : ‖ω‖ = 1 := by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hω
      rw [hω1, mul_one]; exact hs_lt_R r hr
    have hu_diff_at : ∀ r ∈ s, ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        DifferentiableAt ℝ u (x + r • ω) := by
      intro r hr ω hω
      exact (huc.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_ball.mem_nhds (hmem_ball r hr ω hω))
    have hF_cont : ∀ r ∈ s, ContinuousOn (fun ω => u (x + r • ω))
        (Metric.sphere (0 : Fin n → ℝ) 1) := by
      intro r hr
      exact huc.continuousOn.comp
        ((continuous_const.add (continuous_const.smul continuous_id)).continuousOn)
        (fun ω hω => hmem_ball r hr ω hω)


    set K := Metric.closedBall x ((r₀ + R) / 2)
    have hK_compact : IsCompact K := isCompact_closedBall x _
    have hK_sub : K ⊆ Metric.ball x R :=
      Metric.closedBall_subset_ball (by linarith [hr₀.2])

    have hfderiv_cont : ContinuousOn (fderiv ℝ u) (Metric.ball x R) := by
      exact ((contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).mp
        (show ContDiffOn ℝ (1 + 1) u (Metric.ball x R) from by exact_mod_cast huc)).2.2.continuousOn

    have hbdd_fderiv : ∃ M : ℝ, ∀ y ∈ K, ‖fderiv ℝ u y‖ ≤ M := by
      have := hK_compact.bddAbove_image (hfderiv_cont.norm.mono hK_sub)
      obtain ⟨M, hM⟩ := this
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    obtain ⟨M, hM⟩ := hbdd_fderiv

    have hr₀s : r₀ ∈ s := ⟨by linarith [hr₀.1], by linarith [hr₀.2]⟩

    have hν_eq : ν.restrict (Metric.sphere (0 : Fin n → ℝ) 1) = ν :=
      Measure.restrict_restrict_of_subset (fun _ h => h)

    have norm_of_mem_sphere : ∀ ω ∈ Metric.sphere (0 : Fin n → ℝ) 1, ‖ω‖ = 1 :=
      fun ω hω => by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hω


    set_option maxHeartbeats 400000 in
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
      (F := fun r ω => u (x + r • ω))
      (F' := fun r ω => fderiv ℝ u (x + r • ω) ω)
      (bound := fun _ => M + 1)
      hs_nhds ?_ ?_ ?_ ?_ ?_ ?_).2

    · filter_upwards [hs_nhds] with r hr
      exact (hF_cont r hr).aestronglyMeasurable isClosed_sphere.measurableSet

    · have hint : IntegrableOn (fun ω => u (x + r₀ • ω))
          (Metric.sphere (0 : Fin n → ℝ) 1) ν :=
        (hF_cont r₀ hr₀s).integrableOn_compact (μ := ν) (isCompact_sphere _ _)
      exact hν_eq ▸ hint

    · have : ContinuousOn (fun ω => fderiv ℝ u (x + r₀ • ω) ω)
          (Metric.sphere (0 : Fin n → ℝ) 1) := by
        intro ω hω
        apply ContinuousWithinAt.clm_apply
        · exact (hfderiv_cont.comp
            ((continuous_const.add (continuous_const.smul continuous_id)).continuousOn)
            (fun ω' hω' => hmem_ball r₀ hr₀s ω' hω')).continuousWithinAt hω
        · exact continuousWithinAt_id
      exact this.aestronglyMeasurable isClosed_sphere.measurableSet

    · apply ae_restrict_of_forall_mem isClosed_sphere.measurableSet
      intro ω hω r hr
      dsimp only
      have hω1 := norm_of_mem_sphere ω hω
      have hpt : x + r • ω ∈ K := by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (hs_pos r hr).le, hω1, mul_one]
        linarith [hr.2]
      calc ‖fderiv ℝ u (x + r • ω) ω‖
          ≤ ‖fderiv ℝ u (x + r • ω)‖ * ‖ω‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * 1 := by
            rw [hω1]
            exact mul_le_mul_of_nonneg_right (hM _ hpt) zero_le_one
        _ ≤ M + 1 := by linarith

    · exact integrable_const _

    · apply ae_restrict_of_forall_mem isClosed_sphere.measurableSet
      intro ω hω r hr
      dsimp only
      have hu_da := hu_diff_at r hr ω hω
      have h_aff : HasDerivAt (fun t => x + t • ω) ω r := by
        have h1 : HasDerivAt (fun t => t • ω) ((1 : ℝ) • ω) r :=
          (hasDerivAt_id' r).smul_const ω
        have h2 : HasDerivAt (fun _ => x) 0 r := hasDerivAt_const r x
        have h3 := h2.add h1
        simp only [one_smul, zero_add] at h3; exact h3
      exact hu_da.hasFDerivAt.comp_hasDerivAt r h_aff




























/-- By definition, `sphericalMean u x 0 = u x`. -/
theorem sphericalMean_at_zero {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (R : ℝ) (_hR : 0 < R) (_hu : IsHarmonic u (Metric.ball x R)) :
    sphericalMean u x 0 = u x := by
  simp [sphericalMean]









/-- The predicate that $u$ is continuous on $\Omega$ and satisfies the volume mean-value property
on $\Omega$: for every $x \in \Omega$ and every closed ball $\overline{B(x, R)} \subseteq \Omega$,
$u(x) = \fint_{B(x, R)} u$. -/
def HasVolumeMVP {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop :=
  ContinuousOn u Ω ∧
  ∀ (x : Fin n → ℝ) (R : ℝ), x ∈ Ω → 0 < R → Metric.closedBall x R ⊆ Ω →
    u x = ⨍ y in Metric.ball x R, u y

/-- Mean-value maximum lemma: if a continuous function $u$ satisfies the volume MVP at $q$ on
$B(q, r)$, is bounded above by $M$ on $B(q, r)$, and attains the value $M$ at $q$, then $u \equiv M$
on the whole open ball $B(q, r)$. -/
theorem mvp_max_const_on_ball {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {q : Fin n → ℝ} {r : ℝ} {M : ℝ}
    (hr : 0 < r) (Ω : Set (Fin n → ℝ))
    (hball : Metric.closedBall q r ⊆ Ω)
    (hcont : ContinuousOn u Ω)
    (hmvp_q : u q = ⨍ y in Metric.ball q r, u y)
    (hle : ∀ y ∈ Metric.ball q r, u y ≤ M)
    (hqM : u q = M) :
    ∀ y ∈ Metric.ball q r, u y = M := by

  have hμ_pos : (volume (Metric.ball q r)) ≠ 0 := (measure_ball_pos volume q hr).ne'
  have hμ_fin : (volume (Metric.ball q r)) ≠ ⊤ := measure_ball_lt_top.ne
  have hreal_pos : (0 : ℝ) < volume.real (Metric.ball q r) :=
    ENNReal.toReal_pos hμ_pos hμ_fin

  have hcont_ball : ContinuousOn u (Metric.closedBall q r) := hcont.mono hball
  have hint_u : IntegrableOn u (Metric.ball q r) volume :=
    (hcont_ball.integrableOn_compact (isCompact_closedBall q r)).mono_set ball_subset_closedBall
  have hint_M : IntegrableOn (fun _ => M) (Metric.ball q r) volume := integrableOn_const

  have hle_ae : u ≤ᶠ[ae (volume.restrict (Metric.ball q r))] (fun _ => M) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hle y hy

  have havg_eq : ⨍ y in Metric.ball q r, u y = M := by linarith [hmvp_q, hqM]

  have hint_eq : ∫ y in Metric.ball q r, u y = ∫ y in Metric.ball q r, (fun _ => M) y := by
    rw [setAverage_eq] at havg_eq
    simp only [setIntegral_const, smul_eq_mul]
    have h := havg_eq
    rw [smul_eq_mul] at h
    field_simp at h ⊢
    linarith

  have hae_eq : u =ᶠ[ae (volume.restrict (Metric.ball q r))] (fun _ => M) := by
    exact (integral_eq_iff_of_ae_le hint_u hint_M hle_ae).mp hint_eq

  have hcont_u_ball : ContinuousOn u (Metric.ball q r) :=
    hcont_ball.mono ball_subset_closedBall
  have heq_on : EqOn u (fun _ => M) (Metric.ball q r) :=
    Measure.eqOn_open_of_ae_eq hae_eq isOpen_ball hcont_u_ball continuousOn_const

  intro y hy
  exact heq_on hy

/-- Strong maximum principle: if $u$ has the volume mean-value property on a connected open set
$\Omega$ and attains its supremum over $\Omega$ at an interior point $p$, then $u$ is constant on
$\Omega$. -/
theorem strong_max_principle {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω) (hmax : ∀ x ∈ Ω, u x ≤ u p) :
    ∀ x ∈ Ω, u x = u p := by
  set M := u p with hM_def
  set A := Ω ∩ u ⁻¹' {M}
  set B := Ω ∩ (u ⁻¹' {M})ᶜ
  suffices h : Ω ⊆ A by
    intro x hx; exact (h hx).2

  have hB_open : IsOpen B := by


    show IsOpen (Ω ∩ (u ⁻¹' {M})ᶜ)
    rw [show (u ⁻¹' {M})ᶜ = u ⁻¹' {M}ᶜ from rfl]
    exact hmvp.1.isOpen_inter_preimage hΩo isOpen_compl_singleton

  have hA_open : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro q ⟨hqΩ, hqM⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩo q hqΩ
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro y hy
    have hcball : Metric.closedBall q (r / 2) ⊆ Ω := by
      intro z hz
      exact hball (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr))
    constructor
    · exact hcball (Metric.ball_subset_closedBall hy)
    · have hmvp_q : u q = ⨍ z in Metric.ball q (r / 2), u z :=
        hmvp.2 q (r / 2) hqΩ (half_pos hr) hcball
      have hle : ∀ z ∈ Metric.ball q (r / 2), u z ≤ M := by
        intro z hz
        exact hmax z (hcball (Metric.ball_subset_closedBall hz))
      exact mvp_max_const_on_ball (half_pos hr) Ω hcball hmvp.1 hmvp_q hle hqM y hy

  by_contra h_not_sub
  obtain ⟨x, hx, hxnA⟩ := not_subset.mp h_not_sub
  have hxB : x ∈ B := ⟨hx, fun hxM => hxnA ⟨hx, hxM⟩⟩
  have hΩA : (Ω ∩ A).Nonempty := ⟨p, hp, hp, rfl⟩
  have hΩB : (Ω ∩ B).Nonempty := ⟨x, hx, hxB⟩
  have hcover : Ω ⊆ A ∪ B := by
    intro z hz
    by_cases h : u z = M
    · left; exact ⟨hz, h⟩
    · right; exact ⟨hz, h⟩
  have hpc : IsPreconnected Ω := hΩc.isPreconnected
  have hΩAB := hpc A B hA_open hB_open hcover hΩA hΩB
  obtain ⟨z, _, hzA, hzB⟩ := hΩAB
  exact hzB.2 hzA.2

/-- Strong minimum principle: if $u$ has the volume mean-value property on a connected open set
$\Omega$ and attains its infimum over $\Omega$ at an interior point $p$, then $u$ is constant on
$\Omega$. -/
theorem strong_min_principle {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {u : (Fin n → ℝ) → ℝ} (hmvp : HasVolumeMVP u Ω)
    {p : Fin n → ℝ} (hp : p ∈ Ω) (hmin : ∀ x ∈ Ω, u p ≤ u x) :
    ∀ x ∈ Ω, u x = u p := by
  set v := fun x => -u x
  have hmvp_neg : HasVolumeMVP v Ω := by
    constructor
    · exact hmvp.1.neg
    · intro x R hx hR hball
      have huv := hmvp.2 x R hx hR hball
      show v x = ⨍ y in Metric.ball x R, v y
      simp only [v]
      rw [show (⨍ y in Metric.ball x R, -u y) = -(⨍ y in Metric.ball x R, u y) from by
        simp [MeasureTheory.average, integral_neg]]
      linarith
  have hmax_neg : ∀ x ∈ Ω, v x ≤ v p := fun x hx => by
    simp only [v]; linarith [hmin x hx]
  have h := strong_max_principle hΩo hΩc hmvp_neg hp hmax_neg
  intro x hx
  have := h x hx
  simp only [v] at this
  linarith







end CM7
