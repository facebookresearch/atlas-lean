/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.OpenMapping
open Complex Set Filter Finset MeasureTheory Topology Metric

def ConvergesLocallyUniformlyOn (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  TendstoLocallyUniformlyOn F f atTop S

def ConvergesNormallyOn (f : ℕ → ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ M : ℕ → ℝ, Summable M ∧ ∀ n, ∀ z ∈ S, ‖f n z‖ ≤ M n

def ConvergesLocallyNormallyOn (f : ℕ → ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z₀ ∈ S, ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ConvergesNormallyOn f (U ∩ S)

theorem weierstrass_m_test_deriv_normally_convergent {f : ℕ → ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hf_holo : ∀ n, DifferentiableOn ℂ (f n) S)
    (hf_conv : ConvergesLocallyNormallyOn f S) :
    ConvergesLocallyNormallyOn (fun n z => deriv (f n) z) S := by
  intro z₀ hz₀

  obtain ⟨U, hU_open, hz₀U, M, hM_sum, hfM⟩ := hf_conv z₀ hz₀

  have hUS_open : IsOpen (U ∩ S) := hU_open.inter hS
  have hz₀US : z₀ ∈ U ∩ S := ⟨hz₀U, hz₀⟩

  obtain ⟨r, hr_pos, hr_sub⟩ := (Metric.isOpen_iff.mp hUS_open) z₀ hz₀US

  set s := r / 4 with hs_def
  have hs_pos : 0 < s := by positivity
  refine ⟨ball z₀ s, isOpen_ball, mem_ball_self hs_pos, ?_⟩

  refine ⟨fun n => M n / s, hM_sum.div_const s, ?_⟩
  intro n z hz

  have hz_ball : z ∈ ball z₀ s := hz.1
  have hcb_sub : closedBall z s ⊆ U ∩ S := by
    intro w hw
    apply hr_sub
    rw [mem_ball]
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ ≤ s + dist z z₀ := by linarith [mem_closedBall.mp hw]
      _ < s + s := by linarith [mem_ball.mp hz_ball]
      _ = r / 2 := by ring_nf; ring
      _ < r := by linarith

  have hf_dccl : DiffContOnCl ℂ (f n) (ball z s) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (ne_of_gt hs_pos)]
    exact (hf_holo n).mono (hcb_sub.trans inter_subset_right)

  have hf_sphere : ∀ w ∈ sphere z s, ‖f n w‖ ≤ M n := by
    intro w hw
    exact hfM n w (hcb_sub (sphere_subset_closedBall hw))

  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs_pos hf_dccl hf_sphere

theorem weierstrass_m_test_deriv {f : ℕ → ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hf_holo : ∀ n, DifferentiableOn ℂ (f n) S)
    (hf_conv : ConvergesLocallyNormallyOn f S) :
    ConvergesLocallyNormallyOn (fun n z => deriv (f n) z) S ∧
    ∀ z ∈ S, HasDerivAt (fun z => ∑' n, f n z) (∑' n, deriv (f n) z) z := by
  have hderiv_conv := weierstrass_m_test_deriv_normally_convergent hS hf_holo hf_conv
  refine ⟨hderiv_conv, ?_⟩
  intro z hz

  have hderiv_loc_unif : TendstoLocallyUniformlyOn
      (fun N z => ∑ k ∈ Finset.range N, deriv (f k) z)
      (fun z => ∑' n, deriv (f n) z) atTop S := by
    intro u hu x hx
    obtain ⟨U, hUo, hxU, M, hMs, hfM⟩ := hderiv_conv x hx
    have hunif := tendstoUniformlyOn_tsum_nat hMs hfM
    have hloc := hunif.tendstoLocallyUniformlyOn u hu x (Set.mem_inter hxU hx)
    obtain ⟨t, ht_mem, ht_ev⟩ := hloc
    have hU_nhds : U ∈ 𝓝[S] x := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hxU)
    rw [nhdsWithin_inter_of_mem hU_nhds] at ht_mem
    exact ⟨t, ht_mem, ht_ev⟩

  have hderiv_partial_eq : ∀ N, ∀ w ∈ S,
      deriv (fun z => ∑ k ∈ Finset.range N, f k z) w = ∑ k ∈ Finset.range N, deriv (f k) w := by
    intro N w hw
    have h1 : (fun z => ∑ k ∈ Finset.range N, f k z) = (∑ k ∈ Finset.range N, f k) := by
      ext z; simp [Finset.sum_apply]
    rw [h1]
    exact deriv_sum (fun k _ => (hf_holo k).differentiableAt (hS.mem_nhds hw))

  have hderiv_comp : TendstoLocallyUniformlyOn
      (deriv ∘ (fun N z => ∑ k ∈ Finset.range N, f k z))
      (fun z => ∑' n, deriv (f n) z) atTop S :=
    hderiv_loc_unif.congr (fun N => fun w hw => (hderiv_partial_eq N w hw).symm)

  have hpartial_holo : ∀ᶠ (N : ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∑ k ∈ Finset.range N, f k z) S := by
    apply Filter.Eventually.of_forall
    intro N
    have h1 : (fun z => ∑ k ∈ Finset.range N, f k z) = (∑ k ∈ Finset.range N, f k) := by
      ext z; simp [Finset.sum_apply]
    rw [h1]
    exact DifferentiableOn.sum (fun k _ => hf_holo k)

  have hpointwise : ∀ x ∈ S, Filter.Tendsto
      (fun N => (fun z => ∑ k ∈ Finset.range N, f k z) x) atTop
      (nhds ((fun z => ∑' n, f n z) x)) := by
    intro x hx
    simp only
    obtain ⟨U, _, hxU, M, hMs, hfM⟩ := hf_conv x hx
    have hmem : x ∈ U ∩ S := ⟨hxU, hx⟩
    have hsumm : Summable (fun n => f n x) := Summable.of_norm (Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => hfM n x hmem) hMs)
    exact hsumm.hasSum.tendsto_sum_nat

  exact hasDerivAt_of_tendsto_locally_uniformly_on' hS hderiv_comp hpartial_holo hpointwise hz


structure ParameterizedCurve where
  toFun : ℝ → ℂ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  continuous_on : ContinuousOn toFun (Set.Icc a b)

instance : CoeFun ParameterizedCurve (fun _ => ℝ → ℂ) where
  coe := ParameterizedCurve.toFun

def ParameterizedCurve.IsClosed (γ : ParameterizedCurve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

def ParameterizedCurve.IsSimple (γ : ParameterizedCurve) : Prop :=
  Set.InjOn γ.toFun (Set.Ico γ.a γ.b) ∧
  Set.InjOn γ.toFun (Set.Ioc γ.a γ.b)

noncomputable def contourIntegral (f : ℂ → ℂ) (γ : ParameterizedCurve) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

theorem contourIntegral_reparam_invariance
    (f : ℂ → ℂ) (γ₁ γ₂ : ParameterizedCurve) (φ : ℝ → ℝ) (φ' : ℝ → ℝ)

    (hcomp : ∀ t ∈ Set.Icc γ₂.a γ₂.b, γ₂.toFun t = γ₁.toFun (φ t))

    (hφa : φ γ₂.a = γ₁.a) (hφb : φ γ₂.b = γ₁.b)

    (hφ_deriv : ∀ t ∈ Set.uIcc γ₂.a γ₂.b, HasDerivAt φ (φ' t) t)

    (hφ'_cont : ContinuousOn φ' (Set.uIcc γ₂.a γ₂.b))

    (hchain : ∀ t ∈ Set.Icc γ₂.a γ₂.b,
      deriv γ₂.toFun t = (φ' t : ℂ) * deriv γ₁.toFun (φ t))

    (hg_cont : ContinuousOn (fun u => f (γ₁.toFun u) * deriv γ₁.toFun u)
      (φ '' Set.uIcc γ₂.a γ₂.b)) :
    contourIntegral f γ₂ = contourIntegral f γ₁ := by
  unfold contourIntegral

  have h_eq : Set.EqOn
      (fun t => f (γ₂.toFun t) * deriv γ₂.toFun t)
      (fun t => φ' t • ((fun u => f (γ₁.toFun u) * deriv γ₁.toFun u) ∘ φ) t)
      (Set.uIcc γ₂.a γ₂.b) := by
    intro t ht
    have ht' : t ∈ Set.Icc γ₂.a γ₂.b := by
      rwa [Set.uIcc_of_le γ₂.hab] at ht
    simp only [Function.comp, Complex.real_smul]
    rw [hcomp t ht', hchain t ht']
    ring
  rw [intervalIntegral.integral_congr h_eq]

  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (E := ℂ) (f := φ) (f' := φ')
    (g := fun u => f (γ₁.toFun u) * deriv γ₁.toFun u)
    hφ_deriv hφ'_cont hg_cont

  trans ∫ x in φ γ₂.a..φ γ₂.b, f (γ₁.toFun x) * deriv γ₁.toFun x
  · exact hsub
  · rw [hφa, hφb]

theorem locallyUniformLimit_holomorphic {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) :
    DifferentiableOn ℂ f U :=
  hf.differentiableOn hF hU

theorem locallyUniformLimit_deriv_converges {ι : Type*} {φ : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U :=
  hf.deriv hF hU

theorem locallyUniformLimit_zero_free {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U)
    (hUc : IsPreconnected U)
    (hFnz : ∀ᶠ n in φ, ∀ z ∈ U, F n z ≠ 0)
    (hfnz : ∃ z ∈ U, f z ≠ 0) :
    ∀ z ∈ U, f z ≠ 0 := by

  have hfD : DifferentiableOn ℂ f U := hf.differentiableOn hF hU
  have hfA : AnalyticOnNhd ℂ f U := hfD.analyticOnNhd hU

  intro z₀ hz₀ habs
  obtain ⟨w, hw, hfw⟩ := hfnz

  have hne : ¬ EqOn f 0 U := fun heq => hfw (heq hw)

  have hnotloczero : ¬ (∀ᶠ z in nhds z₀, f z = 0) := fun hloc =>
    hne (hfA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀ hloc)
  have hiso : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z ≠ 0 :=
    ((hfA z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnotloczero

  rw [eventually_nhdsWithin_iff] at hiso
  rw [Metric.eventually_nhds_iff] at hiso
  obtain ⟨r₂, hr₂, hball₂⟩ := hiso
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set r := min r₁ r₂ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hr_lt₁ : r < r₁ := by simp [hr_def]; linarith [min_le_left r₁ r₂]
  have hr_lt₂ : r < r₂ := by simp [hr_def]; linarith [min_le_right r₁ r₂]
  have hcball_U : closedBall z₀ r ⊆ U := fun z hz =>
    hball₁ (lt_of_le_of_lt (mem_closedBall.mp hz) hr_lt₁)
  have hfne_sphere : ∀ z ∈ sphere z₀ r, f z ≠ 0 := fun z hz =>
    hball₂ (lt_of_le_of_lt (mem_closedBall.mp (sphere_subset_closedBall hz)) hr_lt₂)
      (mem_compl_singleton_iff.mpr (fun heq => by subst heq; simp at hz; linarith))

  have hfcont : ContinuousOn f (closedBall z₀ r) := hfD.continuousOn.mono hcball_U
  have hsph_ne : (sphere z₀ r : Set ℂ).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨z_min, hz_min, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    hsph_ne
    (continuous_norm.comp_continuousOn (hfcont.mono sphere_subset_closedBall))
  set c := ‖f z_min‖ with hc_def
  have hc : 0 < c := norm_pos_iff.mpr (hfne_sphere z_min hz_min)
  have hc_bound : ∀ z ∈ sphere z₀ r, c ≤ ‖f z‖ := fun z hz => hmin hz

  have hconv : TendstoUniformlyOn F f φ (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall z₀ r)).mp (hf.mono hcball_U)

  obtain ⟨n, hn_dist, hn_nz, hn_diff⟩ :=
    ((tendstoUniformlyOn_iff.mp hconv (c/4) (by linarith)).and (hFnz.and hF)).exists
  have hn_z₀ : ‖F n z₀‖ < c / 4 := by
    have := hn_dist z₀ (mem_closedBall_self hr.le)
    rwa [habs, dist_zero_left] at this

  have hn_sphere : ∀ z ∈ sphere z₀ r, c / 2 ≤ ‖F n z - F n z₀‖ := by
    intro z hz
    have h1 : c ≤ ‖f z‖ := hc_bound z hz
    have h2 : ‖f z - F n z‖ < c / 4 := by
      rw [← dist_eq_norm]; exact hn_dist z (sphere_subset_closedBall hz)
    have h3 : c * 3 / 4 ≤ ‖F n z‖ := by linarith [norm_sub_norm_le (f z) (F n z)]
    linarith [norm_sub_norm_le (F n z) (F n z₀)]


  have hn_notconst : ∃ᶠ z in nhds z₀, F n z ≠ F n z₀ := by
    refine mt (fun h_ev => h_ev.mono fun x => not_ne_iff.mp) ?_
    intro h_eq
    have hAnF : AnalyticOnNhd ℂ (F n) U := hn_diff.analyticOnNhd hU
    have hconst_U : EqOn (F n) (fun _ => F n z₀) U :=
      hAnF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hz₀ h_eq
    obtain ⟨z₁, hz₁⟩ := hsph_ne
    have hFz₁ : F n z₁ = F n z₀ := hconst_U (hcball_U (sphere_subset_closedBall hz₁))
    linarith [hn_sphere z₁ hz₁, show ‖F n z₁ - F n z₀‖ = 0 from by rw [hFz₁, sub_self, norm_zero]]


  have hDCC : DiffContOnCl ℂ (F n) (ball z₀ r) :=
    ⟨hn_diff.mono (ball_subset_closedBall.trans hcball_U),
     (closure_ball z₀ hr.ne').symm ▸ hn_diff.continuousOn.mono hcball_U⟩
  have himage := DiffContOnCl.ball_subset_image_closedBall hDCC hr hn_sphere hn_notconst

  have h0_in : (0 : ℂ) ∈ ball (F n z₀) (c / 2 / 2) := by
    rw [mem_ball, dist_comm, dist_eq_norm, sub_zero]; linarith

  obtain ⟨ζ, hζball, hζ⟩ := himage h0_in
  exact hn_nz ζ (hcball_U hζball) hζ

theorem locallyUniformLimit_holomorphic_and_deriv_and_zeroFree {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hFnz : ∀ᶠ n in φ, ∀ z ∈ U, F n z ≠ 0)
    (hfnz : ∃ z ∈ U, f z ≠ 0) :
    DifferentiableOn ℂ f U ∧
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U ∧
    (∀ z ∈ U, f z ≠ 0) :=
  ⟨locallyUniformLimit_holomorphic hf hF hU,
   locallyUniformLimit_deriv_converges hf hF hU,
   locallyUniformLimit_zero_free hf hF hU hUc hFnz hfnz⟩

def ParameterizedCurve.image (γ : ParameterizedCurve) : Set ℂ :=
  γ.toFun '' (Set.Icc γ.a γ.b)







theorem complex_ftc_contour (γ : ParameterizedCurve) {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hγ_range : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t ∈ Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hγ_diff : ∀ t ∈ Set.uIcc γ.a γ.b, HasDerivAt γ.toFun (deriv γ.toFun t) t)
    (hint : IntervalIntegrable (fun t => deriv f (γ.toFun t) * deriv γ.toFun t)
      volume γ.a γ.b) :
    contourIntegral (deriv f) γ = f (γ.toFun γ.b) - f (γ.toFun γ.a) := by
  unfold contourIntegral

  have hchain : ∀ t ∈ Set.uIcc γ.a γ.b,
      HasDerivAt (f ∘ γ.toFun) (deriv f (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc γ.a γ.b := by rwa [Set.uIcc_of_le γ.hab] at ht
    exact (hf.differentiableAt (hΩ.mem_nhds (hγ_range t ht'))).hasDerivAt.comp t (hγ_diff t ht)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hchain hint

noncomputable def complexResidue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun R => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, R), f z)



lemma cauchy_residue_circle (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall a R)) :
    (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(a, R), (fun w => f w / (w - a)) z = f a := by
  have key : ∮ z in C(a, R), (fun w => f w / (w - a)) z =
      ∮ z in C(a, R), (z - a)⁻¹ • f z := by
    apply circleIntegral.integral_congr hR.le
    intro z _
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [key]
  have hab : a ∈ ball a R := mem_ball_self hR
  have := hf.circleIntegral_sub_inv_smul hab
  rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

theorem complexResidue_div_sub_eq
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (a : ℂ) (ha : a ∈ U) :
    complexResidue (fun w => f w / (w - a)) a = f a := by
  unfold complexResidue
  apply Filter.Tendsto.limUnder_eq
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hU a ha
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq]
  have h1 : ∀ᶠ R in nhdsWithin (0 : ℝ) (Ioi 0), R < ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hε_pos)
  have h2 : ∀ᶠ R in nhdsWithin (0 : ℝ) (Ioi 0), 0 < R :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun x hx => hx))
  exact (h1.and h2).mono fun R ⟨hRε, hR0⟩ => (cauchy_residue_circle f a R hR0
    (hf.mono (closedBall_subset_ball hRε |>.trans hε_sub))).symm

lemma meromorphicOn_div_sub
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (a : ℂ) (_ha : a ∈ U) :
    MeromorphicOn (fun w => f w / (w - a)) U := by
  intro z hz
  have hf_mero : MeromorphicAt f z :=
    (hf.analyticAt (hU.mem_nhds hz)).meromorphicAt
  have hsub_mero : MeromorphicAt (fun w => w - a) z :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact (hf_mero.mul hsub_mero.inv).congr
    (Filter.Eventually.of_forall fun w => (div_eq_mul_inv (f w) (w - a)).symm)

lemma analyticAt_div_sub
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (a z : ℂ) (hz : z ∈ U) (hza : z ≠ a) :
    AnalyticAt ℂ (fun w => f w / (w - a)) z :=
  (hf.analyticAt (hU.mem_nhds hz)).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)




theorem liouville_theorem (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) :
    ∃ c : ℂ, ∀ z : ℂ, f z = c :=
  hf.exists_const_forall_eq_of_bounded hb


theorem morera_theorem {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hf_cont : ContinuousOn f U)
    (hf_conservative : Complex.IsConservativeOn f U) :
    DifferentiableOn ℂ f U :=
  (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
    ⟨hf_conservative, hf_cont⟩
