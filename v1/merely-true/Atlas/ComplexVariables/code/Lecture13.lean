/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section

open Complex MeasureTheory Set intervalIntegral Real Filter Function Topology Metric

structure ClosedCurve where
  toFun : ℝ → ℂ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  continuous_toFun : ContinuousOn toFun (Icc a b)
  differentiable : DifferentiableOn ℝ toFun (Icc a b)
  continuous_deriv : ContinuousOn (deriv toFun) (Icc a b)
  closed : toFun a = toFun b

namespace ClosedCurve

variable (γ : ClosedCurve)

def range : Set ℂ := γ.toFun '' Icc γ.a γ.b

def LiesIn (Ω : Set ℂ) : Prop := γ.range ⊆ Ω

def windingNumber (w : ℂ) : ℂ :=
  (2 * ↑π * I)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t

def IsHomologousToZero (Ω : Set ℂ) : Prop :=
  γ.LiesIn Ω ∧ ∀ a : ℂ, a ∉ Ω → γ.windingNumber a = 0

def contourIntegral (f : ℂ → ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

lemma range_nonempty : γ.range.Nonempty :=
  ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr γ.hab, rfl⟩

lemma liesIn_nonempty {Ω : Set ℂ} (h : γ.LiesIn Ω) : Ω.Nonempty :=
  γ.range_nonempty.mono h

lemma isCompact_range : IsCompact γ.range :=
  isCompact_Icc.image_of_continuousOn γ.continuous_toFun

lemma isClosed_range : IsClosed γ.range :=
  γ.isCompact_range.isClosed

end ClosedCurve

theorem ClosedCurve.continuous_windingNumber_restrict (γ : ClosedCurve) :
    Continuous (γ.rangeᶜ.restrict γ.windingNumber) := by
  rw [← continuousOn_iff_continuous_restrict]
  intro w₀ hw₀
  apply ContinuousAt.continuousWithinAt

  unfold ClosedCurve.windingNumber
  apply ContinuousAt.const_mul


  set δ := infDist w₀ γ.range with hδ_def
  have hδ : 0 < δ :=
    (γ.isClosed_range.notMem_iff_infDist_pos γ.range_nonempty).mp hw₀
  refine continuousAt_of_dominated_interval
    (bound := fun t => (δ / 2)⁻¹ * ‖deriv γ.toFun t‖) ?_ ?_ ?_ ?_
  ·
    have hopen : IsOpen γ.rangeᶜ := γ.isClosed_range.isOpen_compl
    filter_upwards [hopen.mem_nhds hw₀] with w hw
    have hco : ContinuousOn (fun t => (γ.toFun t - w)⁻¹ * deriv γ.toFun t) (Icc γ.a γ.b) :=
      (ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
        (fun t ht => sub_ne_zero.mpr (fun h => hw ⟨t, ht, h⟩))).mul γ.continuous_deriv
    exact (hco.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono (uIoc_subset_uIcc.trans (by rw [uIcc_of_le γ.hab])) le_rfl)
  ·
    filter_upwards [ball_mem_nhds w₀ (half_pos hδ)] with w hw
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le γ.hab] at ht
    have ht' : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
    have hmem : γ.toFun t ∈ γ.range := ⟨t, ht', rfl⟩
    have hdist_t : δ ≤ dist w₀ (γ.toFun t) := infDist_le_dist_of_mem hmem
    have hdist_w : dist w w₀ < δ / 2 := mem_ball.mp hw
    have hge : δ / 2 ≤ ‖γ.toFun t - w‖ := by
      rw [← dist_eq_norm]
      linarith [dist_triangle (γ.toFun t) w w₀, dist_comm w₀ (γ.toFun t)]
    rw [norm_mul, norm_inv]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (half_pos hδ) hge) (norm_nonneg _)
  ·
    exact (γ.continuous_deriv.norm.intervalIntegrable_of_Icc γ.hab).const_mul _
  ·
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le γ.hab] at ht
    have ht' : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
    have hne : γ.toFun t - w₀ ≠ 0 :=
      sub_ne_zero.mpr (fun h => hw₀ ⟨t, ht', h⟩)
    exact (ContinuousAt.inv₀ (continuousAt_const.sub continuousAt_id) hne).mul
      continuousAt_const

set_option maxHeartbeats 800000 in
theorem ClosedCurve.windingNumber_intValued (γ : ClosedCurve) (z : ℂ) (hz : z ∉ γ.range) :
    ∃ n : ℤ, γ.windingNumber z = ↑n := by
  set h : ℝ → ℂ := fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t with hh_def
  set g : ℝ → ℂ := fun t => ∫ s in γ.a..t, h s with hg_def
  have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t - z ≠ 0 := by
    intro t ht hsub; exact hz ⟨t, ht, sub_eq_zero.mp hsub⟩
  have hh_cont : ContinuousOn h (Icc γ.a γ.b) :=
    ((γ.continuous_toFun.sub continuousOn_const).inv₀ hne).mul γ.continuous_deriv
  have hg_cont : ContinuousOn g (Icc γ.a γ.b) := by
    have hint : IntegrableOn h (uIcc γ.a γ.b) volume := by
      rw [uIcc_of_le γ.hab]; exact hh_cont.integrableOn_compact isCompact_Icc
    have := continuousOn_primitive_interval hint; rwa [uIcc_of_le γ.hab] at this
  set F : ℝ → ℂ := fun t => cexp (-g t) * (γ.toFun t - z) with hF_def
  have hF_cont : ContinuousOn F (Icc γ.a γ.b) :=
    (continuous_exp.comp_continuousOn (hg_cont.neg)).mul (γ.continuous_toFun.sub continuousOn_const)
  have hF_deriv : ∀ t ∈ Ioo γ.a γ.b, HasDerivAt F 0 t := by
    intro t ht
    have ht_mem := Ioo_subset_Icc_self ht
    have hh_int : IntervalIntegrable h volume γ.a t :=
      (hh_cont.mono (by rw [uIcc_of_le ht.1.le]; exact Icc_subset_Icc_right ht.2.le)).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter h (nhds t) volume :=
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun x hx => hh_cont.continuousAt (Icc_mem_nhds hx.1 hx.2)) t ht
    have hca : ContinuousAt h t := hh_cont.continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hg_deriv : HasDerivAt g (h t) t := integral_hasDerivAt_right hh_int hmeas hca
    have hγ_deriv : HasDerivAt γ.toFun (deriv γ.toFun t) t :=
      (γ.differentiable.differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
    have hexp_deriv : HasDerivAt (fun t => cexp (-g t)) (cexp (-g t) * (-(h t))) t :=
      (hasDerivAt_exp (-g t)).comp t hg_deriv.neg
    have hsub_deriv : HasDerivAt (fun t => γ.toFun t - z) (deriv γ.toFun t) t := by
      have h1 := hγ_deriv.sub (hasDerivAt_const t z); simp only [sub_zero] at h1; exact h1
    have hprod := hexp_deriv.mul hsub_deriv
    suffices cexp (-g t) * -(h t) * (γ.toFun t - z) + cexp (-g t) * deriv γ.toFun t = 0 by
      rwa [this] at hprod
    simp only [hh_def]; field_simp [hne t ht_mem]; ring
  have hFba : F γ.b = F γ.a := by
    have key := integral_eq_sub_of_hasDerivAt_of_le γ.hab hF_cont hF_deriv intervalIntegrable_const
    simp only [intervalIntegral.integral_const, smul_zero] at key
    exact sub_eq_zero.mp key.symm
  have hga : g γ.a = 0 := by simp [hg_def, integral_same]
  have hne_a : γ.toFun γ.a - z ≠ 0 := hne γ.a (left_mem_Icc.mpr γ.hab)
  have hexp_eq : cexp (-(g γ.b)) = 1 := by
    have hFa : F γ.a = γ.toFun γ.a - z := by simp [hF_def, hga]
    have hFb : F γ.b = cexp (-(g γ.b)) * (γ.toFun γ.a - z) := by simp [hF_def, γ.closed]
    have : cexp (-(g γ.b)) * (γ.toFun γ.a - z) = γ.toFun γ.a - z := by
      rw [← hFb, hFba, hFa]
    exact mul_right_cancel₀ hne_a (by rwa [one_mul])
  obtain ⟨n, hn⟩ := exp_eq_one_iff.mp hexp_eq
  refine ⟨-n, ?_⟩
  show γ.windingNumber z = ↑(-n)
  unfold ClosedCurve.windingNumber
  change (2 * ↑π * I)⁻¹ * ∫ t in γ.a..γ.b, h t = ↑(-n)
  rw [show (∫ t in γ.a..γ.b, h t) = g γ.b from rfl]
  have hgb : g γ.b = -(↑n * (2 * ↑π * I)) := neg_eq_iff_eq_neg.mp hn
  rw [hgb]; push_cast; field_simp

lemma isLocallyConstant_of_continuous_intValued {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} (hf_cont : Continuous f)
    (hf_int : ∀ x, ∃ n : ℤ, f x = ↑n) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro c
  by_cases hc : ∃ n : ℤ, c = ↑n
  · obtain ⟨n, rfl⟩ := hc
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    simp only [mem_preimage, mem_singleton_iff] at hx
    refine ⟨f ⁻¹' Metric.ball (↑n : ℂ) 1, ?_, ?_, ?_⟩
    · intro y hy
      simp only [mem_preimage, mem_singleton_iff, Metric.mem_ball] at hy ⊢
      obtain ⟨m, hm⟩ := hf_int y
      rw [hm] at hy ⊢
      have key : (m : ℂ) - n = ↑(m - n : ℤ) := by push_cast; ring
      rw [dist_eq_norm, key, Complex.norm_intCast] at hy
      have : (m - n : ℤ) = 0 := by
        by_contra h3
        exact absurd hy (not_lt.mpr
          (by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h3))
      have : m = n := by omega
      simp [this]
    · exact hf_cont.isOpen_preimage _ Metric.isOpen_ball
    · simp only [mem_preimage, Metric.mem_ball]
      rw [hx, dist_self]; exact one_pos
  · convert isOpen_empty using 1
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro heq
    exact hc (hf_int x |>.imp fun n hn => by rw [← heq, hn])

theorem ClosedCurve.isLocallyConstant_windingNumber_restrict (γ : ClosedCurve) :
    IsLocallyConstant (γ.rangeᶜ.restrict γ.windingNumber) :=
  isLocallyConstant_of_continuous_intValued
    γ.continuous_windingNumber_restrict
    (fun ⟨z, hz⟩ => γ.windingNumber_intValued z hz)

namespace ClosedCurve
variable (γ : ClosedCurve)

lemma contourIntegral_cancel_sub_inv {f : ℂ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ∉ γ.range) :
    γ.contourIntegral (fun ζ => (ζ - z₀) * f ζ * (ζ - z₀)⁻¹) = γ.contourIntegral f := by
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le γ.hab] at ht
  have hne : γ.toFun t - z₀ ≠ 0 :=
    sub_ne_zero.mpr (fun h => hz₀ (h ▸ ⟨t, ht, rfl⟩))
  simp only []
  field_simp

end ClosedCurve

def dividedDiff (f : ℂ → ℂ) : ℂ × ℂ → ℂ := fun p => dslope f p.1 p.2

theorem dividedDiff_symm (f : ℂ → ℂ) (z ζ : ℂ) :
    dividedDiff f (z, ζ) = dividedDiff f (ζ, z) := by
  simp only [dividedDiff]
  rcases eq_or_ne z ζ with rfl | hne
  · simp
  · simp only [dslope_of_ne f hne.symm, dslope_of_ne f hne, slope_comm]

lemma dslope_sub_deriv_norm_le {f : ℂ → ℂ} {s : Set ℂ} {z ζ z₀ : ℂ} {C : ℝ}
    (hf : ∀ w ∈ s, DifferentiableAt ℂ f w)
    (hC : ∀ w ∈ s, ‖deriv f w - deriv f z₀‖ ≤ C)
    (hs : Convex ℝ s) (hz : z ∈ s) (hζ : ζ ∈ s) :
    ‖dslope f z ζ - deriv f z₀‖ ≤ C := by
  rcases eq_or_ne ζ z with heq | hne
  · subst heq; simp only [dslope_same]; exact hC _ hz
  · rw [dslope_of_ne _ hne]
    set h := fun w => f w - deriv f z₀ * w
    have hh_diff : ∀ w ∈ s, DifferentiableAt ℂ h w := fun w hw =>
      (hf w hw).sub ((differentiableAt_const _).mul differentiableAt_id)
    have hh_deriv : ∀ w ∈ s, deriv h w = deriv f w - deriv f z₀ := fun w hw =>
      ((hf w hw).hasDerivAt.sub
        (by simpa using (hasDerivAt_id w).const_mul (deriv f z₀))).deriv
    have hh_bound : ∀ w ∈ s, ‖deriv h w‖ ≤ C := fun w hw => by
      rw [hh_deriv w hw]; exact hC w hw
    have mvt := hs.norm_image_sub_le_of_norm_deriv_le hh_diff hh_bound hz hζ
    have hh_sub : h ζ - h z = (f ζ - f z) - deriv f z₀ * (ζ - z) := by simp [h]; ring
    rw [hh_sub] at mvt
    rw [show slope f z ζ - deriv f z₀ =
        (ζ - z)⁻¹ * ((f ζ - f z) - deriv f z₀ * (ζ - z)) from by
      rw [slope_def_module]; simp only [smul_eq_mul]
      field_simp [sub_ne_zero.mpr hne], norm_mul, norm_inv]
    calc ‖ζ - z‖⁻¹ * ‖(f ζ - f z) - deriv f z₀ * (ζ - z)‖
        ≤ ‖ζ - z‖⁻¹ * (C * ‖ζ - z‖) :=
          mul_le_mul_of_nonneg_left mvt (inv_nonneg.mpr (norm_nonneg _))
      _ = C := by field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)]

theorem continuousOn_dividedDiff {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    ContinuousOn (dividedDiff f) (Ω ×ˢ Ω) := by
  apply (hΩ.prod hΩ).continuousOn_iff.mpr
  intro ⟨z₀, ζ₀⟩ ⟨hz₀, hζ₀⟩
  simp only at hz₀ hζ₀
  rcases eq_or_ne z₀ ζ₀ with rfl | hne
  ·
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hf' : ContinuousAt (deriv f) z₀ :=
      (hf.deriv hΩ).continuousOn.continuousAt (hΩ.mem_nhds hz₀)
    rw [Metric.continuousAt_iff] at hf'
    obtain ⟨δ₁, hδ₁, hδ₁_bound⟩ := hf' (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, hball⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
    set δ := min δ₁ δ₂
    refine ⟨δ, lt_min hδ₁ hδ₂, fun ⟨z, ζ⟩ hdist => ?_⟩
    rw [Prod.dist_eq] at hdist; simp only at hdist
    have hz : dist z z₀ < δ := lt_of_le_of_lt (le_max_left _ _) hdist
    have hζ : dist ζ z₀ < δ := lt_of_le_of_lt (le_max_right _ _) hdist
    show dist (dslope f z ζ) (dslope f z₀ z₀) < ε
    rw [dslope_same, dist_comm, dist_eq_norm, norm_sub_rev]
    have hfδ : ∀ w ∈ ball z₀ δ, DifferentiableAt ℂ f w := fun w hw =>
      hf.differentiableAt (hΩ.mem_nhds (hball (ball_subset_ball (min_le_right _ _) hw)))
    have hCδ : ∀ w ∈ ball z₀ δ, ‖deriv f w - deriv f z₀‖ ≤ ε / 2 := fun w hw => by
      rw [← dist_eq_norm]
      exact le_of_lt (hδ₁_bound (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)))
    calc ‖dslope f z ζ - deriv f z₀‖
        ≤ ε / 2 := dslope_sub_deriv_norm_le hfδ hCδ (convex_ball z₀ δ)
            (mem_ball.mpr hz) (mem_ball.mpr hζ)
      _ < ε := half_lt_self hε
  ·
    set g : ℂ × ℂ → ℂ := fun p => (f p.2 - f p.1) / (p.2 - p.1)
    have hf_cont : ContinuousOn f Ω := hf.continuousOn
    have h1 : ContinuousAt f z₀ := hf_cont.continuousAt (hΩ.mem_nhds hz₀)
    have h2 : ContinuousAt f ζ₀ := hf_cont.continuousAt (hΩ.mem_nhds hζ₀)
    have hg_cont : ContinuousAt g (z₀, ζ₀) :=
      ((h2.comp continuousAt_snd).sub (h1.comp continuousAt_fst)).div
        (continuousAt_snd.sub continuousAt_fst) (sub_ne_zero.mpr (Ne.symm hne))
    exact hg_cont.congr <| by
      filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds
        (show (z₀, ζ₀) ∈ {p : ℂ × ℂ | p.1 ≠ p.2} from hne)]
      rintro ⟨z, ζ⟩ (hzζ : z ≠ ζ)
      simp only [dividedDiff, g]
      rw [dslope_of_ne _ hzζ.symm, slope_def_module, smul_eq_mul, div_eq_inv_mul]

theorem differentiableOn_dividedDiff_snd {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) :
    DifferentiableOn ℂ (fun ζ => dividedDiff f (z₀, ζ)) Ω := by
  simp only [dividedDiff]
  exact (Complex.differentiableOn_dslope (hΩ.mem_nhds hz₀)).mpr hf

theorem differentiableOn_dividedDiff_fst {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (ζ₀ : ℂ) (hζ₀ : ζ₀ ∈ Ω) :
    DifferentiableOn ℂ (fun z => dividedDiff f (z, ζ₀)) Ω := by
  have h : (fun z => dividedDiff f (z, ζ₀)) = (fun z => dividedDiff f (ζ₀, z)) := by
    ext z; exact dividedDiff_symm f z ζ₀
  rw [h]
  exact differentiableOn_dividedDiff_snd hΩ hf ζ₀ hζ₀

open scoped Classical in
def ClosedCurve.complementDomain (γ : ClosedCurve) : Set ℂ :=
  {z : ℂ | z ∉ γ.range ∧ γ.windingNumber z = 0}

open scoped Classical in
def cauchyPiecewise (Ω : Set ℂ) (f : ℂ → ℂ) (γ : ClosedCurve) (z : ℂ) : ℂ :=
  if z ∈ Ω then
    (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => dividedDiff f (z, ζ))
  else
    (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹)

lemma cauchyPiecewise_eq_on_omega {Ω : Set ℂ} {f : ℂ → ℂ} {γ : ClosedCurve}
    {z : ℂ} (hz : z ∈ Ω) :
    cauchyPiecewise Ω f γ z =
      (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => dividedDiff f (z, ζ)) := by
  simp [cauchyPiecewise, hz]

lemma cauchyPiecewise_eq_off_omega {Ω : Set ℂ} {f : ℂ → ℂ} {γ : ClosedCurve}
    {z : ℂ} (hz : z ∉ Ω) :
    cauchyPiecewise Ω f γ z =
      (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹) := by
  simp [cauchyPiecewise, hz]

lemma union_complementDomain_eq_univ {Ω : Set ℂ} {γ : ClosedCurve}
    (hγ : γ.IsHomologousToZero Ω) :
    Ω ∪ γ.complementDomain = Set.univ := by
  ext z
  simp only [mem_union, ClosedCurve.complementDomain, mem_setOf_eq, mem_univ, iff_true]
  by_cases hz : z ∈ Ω
  · exact Or.inl hz
  · right; exact ⟨fun habs => hz (hγ.1 habs), hγ.2 z hz⟩

theorem isOpen_complementDomain (γ : ClosedCurve) : IsOpen γ.complementDomain := by

  have hcompact : IsCompact γ.range :=
    IsCompact.image_of_continuousOn isCompact_Icc γ.continuous_toFun

  have hopen : IsOpen γ.rangeᶜ := hcompact.isClosed.isOpen_compl


  have hfiber : IsOpen {x : ↥(γ.rangeᶜ) | γ.windingNumber x.val = 0} :=
    γ.isLocallyConstant_windingNumber_restrict.isOpen_fiber 0

  have heq : γ.complementDomain =
      Subtype.val '' {x : ↥(γ.rangeᶜ) | γ.windingNumber x.val = 0} := by
    ext z
    simp only [ClosedCurve.complementDomain, mem_setOf_eq, mem_image, Subtype.exists]
    constructor
    · intro ⟨hz_not_range, hz_winding⟩
      exact ⟨z, hz_not_range, hz_winding, rfl⟩
    · rintro ⟨w, hw_not_range, hw_winding, rfl⟩
      exact ⟨hw_not_range, hw_winding⟩

  rw [heq]
  exact hfiber.trans hopen

noncomputable def cauchyTypeIntegral (f : ℂ → ℂ) (γ : ClosedCurve) (z : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹)

theorem differentiableOn_cauchyTypeIntegral (f : ℂ → ℂ) (γ : ClosedCurve)
    (hf_cont : ContinuousOn f γ.range) :
    DifferentiableOn ℂ (cauchyTypeIntegral f γ) (γ.range)ᶜ := by
  intro z₀ hz₀
  rw [Set.mem_compl_iff] at hz₀
  have hK : IsCompact γ.range := γ.isCompact_range
  have hd_pos : 0 < infDist z₀ γ.range :=
    (hK.isClosed.notMem_iff_infDist_pos γ.range_nonempty).mp hz₀
  set r := infDist z₀ γ.range / 2
  have hr_pos : 0 < r := by positivity
  have huIoc_sub : Set.uIoc γ.a γ.b ⊆ Icc γ.a γ.b := by
    rw [uIoc_of_le γ.hab]; exact Ioc_subset_Icc_self

  have hdist : ∀ t ∈ Icc γ.a γ.b, ∀ z ∈ ball z₀ r, r ≤ ‖γ.toFun t - z‖ := by
    intro t ht z hz
    rw [← dist_eq_norm]
    have h1 : infDist z₀ γ.range ≤ dist z₀ (γ.toFun t) :=
      infDist_le_dist_of_mem ⟨t, ht, rfl⟩
    have h2 : dist z z₀ < r := mem_ball.mp hz
    have h3 : dist (γ.toFun t) z₀ ≤ dist (γ.toFun t) z + dist z z₀ :=
      dist_triangle (γ.toFun t) z z₀
    rw [dist_comm] at h1
    have hr_eq : r = infDist z₀ γ.range / 2 := rfl
    linarith
  have hne_sub : ∀ t ∈ Icc γ.a γ.b, ∀ z ∈ ball z₀ r, γ.toFun t - z ≠ 0 := fun t ht z hz h0 =>
    absurd (hdist t ht z hz) (by rw [h0, norm_zero]; push_neg; exact hr_pos)

  have hfγ : ContinuousOn (f ∘ γ.toFun) (Icc γ.a γ.b) :=
    hf_cont.comp γ.continuous_toFun (mapsTo_image _ _)

  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn hf_cont
  obtain ⟨Cγ, hCγ⟩ := isCompact_Icc.exists_bound_of_continuousOn γ.continuous_deriv

  have hF_cont : ∀ z ∈ ball z₀ r, ContinuousOn
      (fun t => f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t) (Icc γ.a γ.b) := by
    intro z hz
    exact (hfγ.mul ((γ.continuous_toFun.sub continuousOn_const).inv₀
      (fun t ht => hne_sub t ht z hz))).mul γ.continuous_deriv

  have hF'_cont : ContinuousOn
      (fun t => f (γ.toFun t) * ((γ.toFun t - z₀) ^ 2)⁻¹ * deriv γ.toFun t) (Icc γ.a γ.b) := by
    exact (hfγ.mul (((γ.continuous_toFun.sub continuousOn_const).pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (hne_sub t ht z₀ (mem_ball_self hr_pos))))).mul
      γ.continuous_deriv

  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t)
    (F' := fun z t => f (γ.toFun t) * ((γ.toFun t - z) ^ 2)⁻¹ * deriv γ.toFun t)
    (x₀ := z₀) (s := ball z₀ r) (bound := fun _ => Cf * (r ^ 2)⁻¹ * Cγ) (μ := volume)
    (ball_mem_nhds z₀ hr_pos)

    (by filter_upwards [ball_mem_nhds z₀ hr_pos] with z hz
        exact ((hF_cont z hz).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc)

    ((hF_cont z₀ (mem_ball_self hr_pos)).intervalIntegrable_of_Icc γ.hab)

    ((hF'_cont.mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc)

    (by apply Filter.Eventually.of_forall; intro t ht z hz
        have ht' := huIoc_sub ht
        have hζ_mem : γ.toFun t ∈ γ.range := ⟨t, ht', rfl⟩
        calc ‖f (γ.toFun t) * ((γ.toFun t - z) ^ 2)⁻¹ * deriv γ.toFun t‖
            = ‖f (γ.toFun t)‖ * ‖((γ.toFun t - z) ^ 2)⁻¹‖ * ‖deriv γ.toFun t‖ := by
              simp [norm_mul]
          _ ≤ Cf * (r ^ 2)⁻¹ * Cγ := by
              have hinv : ‖((γ.toFun t - z) ^ 2)⁻¹‖ ≤ (r ^ 2)⁻¹ := by
                rw [norm_inv, norm_pow]
                exact inv_anti₀ (by positivity)
                  (pow_le_pow_left₀ (by positivity) (hdist t ht' z hz) 2)
              exact mul_le_mul (mul_le_mul (hCf _ hζ_mem) hinv (norm_nonneg _)
                  (le_trans (norm_nonneg _) (hCf _ hζ_mem))) (hCγ _ ht')
                  (norm_nonneg _) (mul_nonneg (le_trans (norm_nonneg _) (hCf _ hζ_mem)) (inv_nonneg.mpr (sq_nonneg _))))

    (intervalIntegrable_const)

    (by apply Filter.Eventually.of_forall; intro t ht z hz
        have hζz : γ.toFun t - z ≠ 0 := hne_sub t (huIoc_sub ht) z hz
        have hd : HasDerivAt (fun w => (γ.toFun t - w)⁻¹) ((γ.toFun t - z) ^ 2)⁻¹ z := by
          simpa using ((hasDerivAt_const z (γ.toFun t)).sub (hasDerivAt_id z)).inv hζz
        exact (hd.const_mul _).mul_const _)


  have heq : cauchyTypeIntegral f γ =
      fun z => (2 * ↑π * I)⁻¹ *
        ∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t := by
    ext z; simp only [cauchyTypeIntegral, ClosedCurve.contourIntegral]
  rw [heq]
  exact (key.2.const_mul _).differentiableAt.differentiableWithinAt

namespace ClosedCurve

variable (γ : ClosedCurve)

theorem differentiableOn_dslope_contourIntegral_complement
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω) :
    DifferentiableOn ℂ (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) γ.rangeᶜ := by
  have hopen : IsOpen γ.rangeᶜ := γ.isClosed_range.isOpen_compl
  have hf_cont : ContinuousOn f γ.range := hf.continuousOn.mono hγ.1

  have hCauchy : DifferentiableOn ℂ (cauchyTypeIntegral f γ) γ.rangeᶜ :=
    differentiableOn_cauchyTypeIntegral f γ hf_cont

  have hCauchy1 : DifferentiableOn ℂ (cauchyTypeIntegral (fun _ => 1) γ) γ.rangeᶜ :=
    differentiableOn_cauchyTypeIntegral _ γ continuousOn_const


  have hsplit : ∀ z, z ∉ γ.range →
      γ.contourIntegral (fun ζ => dslope f z ζ) =
        γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹) -
          f z * γ.contourIntegral (fun ζ => (ζ - z)⁻¹) := by
    intro z hz
    have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z := fun t ht heq => hz ⟨t, ht, heq⟩
    simp only [ClosedCurve.contourIntegral]

    have hstep : ∀ t ∈ Set.uIcc γ.a γ.b,
        dslope f z (γ.toFun t) * deriv γ.toFun t =
          (f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t) -
          (f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t)) := by
      intro t ht
      have ht' : t ∈ Icc γ.a γ.b := by rwa [uIcc_of_le γ.hab] at ht
      have hne_t := hne t ht'
      rw [dslope_of_ne f hne_t, slope_def_field]
      field_simp

    rw [intervalIntegral.integral_congr hstep]


    have huIoc_sub : Set.uIoc γ.a γ.b ⊆ Icc γ.a γ.b := by
      rw [uIoc_of_le γ.hab]; exact Ioc_subset_Icc_self
    have hint1 : IntervalIntegrable
        (fun t => f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t) volume γ.a γ.b := by
      apply ContinuousOn.intervalIntegrable_of_Icc γ.hab
      exact ((hf_cont.comp γ.continuous_toFun (mapsTo_image _ _)).mul
        ((γ.continuous_toFun.sub continuousOn_const).inv₀
          (fun t ht => sub_ne_zero.mpr (hne t ht)))).mul γ.continuous_deriv
    have hint2 : IntervalIntegrable
        (fun t => f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t)) volume γ.a γ.b := by
      apply ContinuousOn.intervalIntegrable_of_Icc γ.hab
      exact continuousOn_const.mul (((γ.continuous_toFun.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht))).mul γ.continuous_deriv)
    rw [intervalIntegral.integral_sub hint1 hint2]
    have hconst : (∫ t in γ.a..γ.b, f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t)) =
        f z * ∫ t in γ.a..γ.b, (γ.toFun t - z)⁻¹ * deriv γ.toFun t :=
      intervalIntegral.integral_const_mul _ _
    rw [hconst]


  have h2piI_ne : (2 * ↑π * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero _ _) I_ne_zero
    · exact two_ne_zero
    · exact ofReal_ne_zero.mpr pi_ne_zero
  have hwind_eq : ∀ z, z ∉ γ.range →
      γ.contourIntegral (fun ζ => (ζ - z)⁻¹) = 2 * ↑π * I * γ.windingNumber z := by
    intro z hz
    simp only [ClosedCurve.contourIntegral, ClosedCurve.windingNumber]
    rw [mul_inv_cancel_left₀ h2piI_ne]

  intro z₀ hz₀

  have hlc := γ.isLocallyConstant_windingNumber_restrict

  have hconst : ∀ᶠ z in 𝓝[(γ.rangeᶜ)] z₀, γ.windingNumber z = γ.windingNumber z₀ := by
    rw [nhdsWithin_eq_map_subtype_coe hz₀, Filter.eventually_map]
    exact hlc.eventually_eq ⟨z₀, hz₀⟩
  set c := γ.windingNumber z₀

  by_cases hz₀Ω : z₀ ∈ Ω
  ·


    have hF_eq : ∀ᶠ z in 𝓝[(γ.rangeᶜ)] z₀,
        γ.contourIntegral (fun ζ => dslope f z ζ) =
          γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹) - f z * (2 * ↑π * I * c) := by
      apply Filter.Eventually.mono (Filter.inter_mem
        (nhdsWithin_le_nhds (hopen.mem_nhds hz₀)) hconst)
      intro z ⟨hzc, hzw⟩
      rw [hsplit z hzc, hwind_eq z hzc, hzw]

    have h1 : DifferentiableWithinAt ℂ
        (fun z => γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹)) γ.rangeᶜ z₀ := by
      have : DifferentiableWithinAt ℂ (fun z => (2 * ↑π * I) * cauchyTypeIntegral f γ z) γ.rangeᶜ z₀ :=
        (hCauchy z₀ hz₀).const_mul _
      apply this.congr_of_eventuallyEq_of_mem _ hz₀
      apply Filter.Eventually.mono (nhdsWithin_le_nhds (hopen.mem_nhds hz₀))
      intro z hz
      simp only [cauchyTypeIntegral]
      rw [mul_inv_cancel_left₀ h2piI_ne]

    have h2 : DifferentiableWithinAt ℂ
        (fun z => f z * (2 * ↑π * I * c)) γ.rangeᶜ z₀ := by
      exact (hf.differentiableAt (hΩ.mem_nhds hz₀Ω)).differentiableWithinAt.mul_const _

    apply (h1.sub h2).congr_of_eventuallyEq_of_mem hF_eq hz₀
  ·
    have hc_zero : c = 0 := hγ.2 z₀ hz₀Ω

    have hF_eq : ∀ᶠ z in 𝓝[(γ.rangeᶜ)] z₀,
        γ.contourIntegral (fun ζ => dslope f z ζ) =
          γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹) := by
      apply Filter.Eventually.mono (Filter.inter_mem
        (nhdsWithin_le_nhds (hopen.mem_nhds hz₀)) hconst)
      intro z ⟨hzc, hzw⟩
      rw [hsplit z hzc, hwind_eq z hzc, hzw, hc_zero, mul_zero, mul_zero, sub_zero]

    have h1 : DifferentiableWithinAt ℂ
        (fun z => γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹)) γ.rangeᶜ z₀ := by
      have : DifferentiableWithinAt ℂ (fun z => (2 * ↑π * I) * cauchyTypeIntegral f γ z) γ.rangeᶜ z₀ :=
        (hCauchy z₀ hz₀).const_mul _
      apply this.congr_of_eventuallyEq_of_mem _ hz₀
      apply Filter.Eventually.mono (nhdsWithin_le_nhds (hopen.mem_nhds hz₀))
      intro z hz
      simp only [cauchyTypeIntegral]
      rw [mul_inv_cancel_left₀ h2piI_ne]
    apply h1.congr_of_eventuallyEq_of_mem hF_eq hz₀

set_option maxHeartbeats 800000 in
theorem differentiableOn_dslope_contourIntegral_omega_morera
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω) (z₀ : ℂ)
    (hz₀ : z₀ ∈ Ω) :
    DifferentiableWithinAt ℂ (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) Ω z₀ := by

  apply DifferentiableAt.differentiableWithinAt

  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀

  have hγΩ : γ.LiesIn Ω := hγ.1

  have hF_eq : (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) =
      (fun z => ∫ t in γ.a..γ.b, dividedDiff f (z, γ.toFun t) * deriv γ.toFun t) := by
    ext z; simp only [ClosedCurve.contourIntegral, dividedDiff]
  rw [hF_eq]

  set r' := r / 4 with hr'_def
  have hr'_pos : 0 < r' := by positivity
  have h2r'_pos : 0 < 2 * r' := by positivity
  have h2r'_lt_r : 2 * r' < r := by linarith
  have hball_sub : ball z₀ r ⊆ Ω := hr_sub

  have h3r'_lt_r : 3 * r' < r := by linarith
  have hcball3_sub : closedBall z₀ (3 * r') ⊆ Ω := by
    intro w hw
    exact hball_sub (lt_of_le_of_lt (mem_closedBall.mp hw) h3r'_lt_r |> mem_ball.mpr)

  have hcball2_sub : closedBall z₀ (2 * r') ⊆ closedBall z₀ (3 * r') :=
    closedBall_subset_closedBall (by linarith)

  have huIoc_sub : Set.uIoc γ.a γ.b ⊆ Icc γ.a γ.b := by
    rw [uIoc_of_le γ.hab]; exact Ioc_subset_Icc_self

  have hγt_mem : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ Ω := fun t ht =>
    hγΩ ⟨t, ht, rfl⟩


  have hdd_cont := continuousOn_dividedDiff hΩ hf
  have hF_cont : ∀ z ∈ ball z₀ (2 * r'), ContinuousOn
      (fun t => dividedDiff f (z, γ.toFun t) * deriv γ.toFun t) (Icc γ.a γ.b) := by
    intro z hz
    have hz_mem : z ∈ Ω := hcball3_sub (hcball2_sub (le_of_lt (mem_ball.mp hz) |> mem_closedBall.mpr))
    apply ContinuousOn.mul _ γ.continuous_deriv
    exact (hdd_cont.comp (continuousOn_const.prodMk γ.continuous_toFun)
      (fun t ht => ⟨hz_mem, hγt_mem t ht⟩))


  have hcball2_compact : IsCompact (closedBall z₀ (2 * r')) := isCompact_closedBall z₀ (2 * r')
  have hγrange_compact : IsCompact γ.range := γ.isCompact_range
  have hprod_compact : IsCompact (closedBall z₀ (2 * r') ×ˢ γ.range) :=
    hcball2_compact.prod hγrange_compact
  have hprod_sub : closedBall z₀ (2 * r') ×ˢ γ.range ⊆ Ω ×ˢ Ω := by
    apply Set.prod_mono
    · exact fun w hw => hcball3_sub (hcball2_sub hw)
    · exact hγΩ
  obtain ⟨Cdd, hCdd⟩ := hprod_compact.exists_bound_of_continuousOn (hdd_cont.mono hprod_sub)
  obtain ⟨Cγ, hCγ⟩ := isCompact_Icc.exists_bound_of_continuousOn γ.continuous_deriv

  have hDiffContOnCl : ∀ t ∈ Icc γ.a γ.b, ∀ z ∈ ball z₀ r',
      DiffContOnCl ℂ (fun w => dividedDiff f (w, γ.toFun t)) (ball z r') := by
    intro t ht z hz
    have hζ_mem : γ.toFun t ∈ Ω := hγt_mem t ht

    have hcb_sub : closedBall z r' ⊆ Ω := by
      intro w hw
      apply hcball3_sub; apply hcball2_sub
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
        _ ≤ r' + r' := add_le_add (mem_closedBall.mp hw) (le_of_lt (mem_ball.mp hz))
        _ = 2 * r' := by ring
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (ne_of_gt hr'_pos)]
    exact (differentiableOn_dividedDiff_fst hΩ hf (γ.toFun t) hζ_mem).mono hcb_sub

  have hderiv_bound : ∀ t ∈ Icc γ.a γ.b, ∀ z ∈ ball z₀ r',
      ‖deriv (fun w => dividedDiff f (w, γ.toFun t)) z‖ ≤ Cdd / r' := by
    intro t ht z hz
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr'_pos (hDiffContOnCl t ht z hz)
    intro w hw


    have hw_mem : w ∈ closedBall z₀ (2 * r') := by
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
        _ = r' + dist z z₀ := by rw [mem_sphere.mp hw]
        _ ≤ r' + r' := by linarith [le_of_lt (mem_ball.mp hz)]
        _ = 2 * r' := by ring
    have hζ_mem : γ.toFun t ∈ γ.range := ⟨t, ht, rfl⟩
    exact hCdd (w, γ.toFun t) ⟨hw_mem, hζ_mem⟩


  have hF_deriv : ∀ t ∈ Set.uIoc γ.a γ.b, ∀ z ∈ ball z₀ r',
      HasDerivAt (fun w => dividedDiff f (w, γ.toFun t) * deriv γ.toFun t)
        (deriv (fun w => dividedDiff f (w, γ.toFun t)) z * deriv γ.toFun t) z := by
    intro t ht z hz
    have ht' := huIoc_sub ht
    have hζ_mem : γ.toFun t ∈ Ω := hγt_mem t ht'
    have hz_mem : z ∈ Ω := hball_sub (ball_subset_ball (by linarith : r' ≤ r) hz)
    have hda := (differentiableOn_dividedDiff_fst hΩ hf (γ.toFun t) hζ_mem).differentiableAt
      (hΩ.mem_nhds hz_mem) |>.hasDerivAt
    exact hda.mul_const _

  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => dividedDiff f (z, γ.toFun t) * deriv γ.toFun t)
    (F' := fun z t => deriv (fun w => dividedDiff f (w, γ.toFun t)) z * deriv γ.toFun t)
    (x₀ := z₀) (s := ball z₀ r') (bound := fun _ => Cdd / r' * Cγ) (μ := volume)
    (ball_mem_nhds z₀ hr'_pos)

    (by filter_upwards [ball_mem_nhds z₀ h2r'_pos] with z hz
        exact ((hF_cont z (ball_subset_ball (by linarith : 2 * r' ≤ 2 * r') hz)).mono
          huIoc_sub).aestronglyMeasurable measurableSet_uIoc)

    ((hF_cont z₀ (mem_ball_self h2r'_pos)).intervalIntegrable_of_Icc γ.hab)

    (by


      let h_seq : ℕ → ℂ := fun n => (r' : ℂ) * ((↑(n + 1) : ℂ))⁻¹

      have h_seq_ne : ∀ n, h_seq n ≠ 0 := fun n =>
        mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr'_pos))
          (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega)))

      have h_seq_in_ball : ∀ n, z₀ + h_seq n ∈ ball z₀ (2 * r') := fun n => by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        show ‖(r' : ℂ) * ((↑(n + 1) : ℂ))⁻¹‖ < 2 * r'
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr'_pos.le, norm_inv,
            Complex.norm_natCast]
        calc r' * (↑(n + 1) : ℝ)⁻¹ ≤ r' * 1 := by
              apply mul_le_mul_of_nonneg_left _ hr'_pos.le
              exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
          _ = r' := mul_one r'
          _ < 2 * r' := by linarith

      have h_seq_tend : Tendsto h_seq atTop (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        ·
          have h1 : Tendsto (fun n : ℕ => ((↑(n + 1) : ℂ))⁻¹) atTop (𝓝 0) :=
            (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp (tendsto_add_atTop_nat 1)
          have h2 : Tendsto (fun n : ℕ => (r' : ℂ) * ((↑(n + 1) : ℂ))⁻¹) atTop (𝓝 0) := by
            simpa only [mul_zero] using tendsto_const_nhds.mul h1
          exact h2
        · exact Filter.Eventually.of_forall (fun n => h_seq_ne n)


      set F_main := fun (z : ℂ) (t : ℝ) => dividedDiff f (z, γ.toFun t) * deriv γ.toFun t
      set F'_z₀ := fun (t : ℝ) =>
        deriv (fun w => dividedDiff f (w, γ.toFun t)) z₀ * deriv γ.toFun t
      let G : ℕ → ℝ → ℂ := fun n t =>
        (h_seq n)⁻¹ • (F_main (z₀ + h_seq n) t - F_main z₀ t)

      have hG_meas : ∀ n : ℕ, AEStronglyMeasurable (G n)
          (volume.restrict (Set.uIoc γ.a γ.b)) := by
        intro n
        have hcont_n : ContinuousOn (G n) (Icc γ.a γ.b) :=
          ((hF_cont _ (h_seq_in_ball n)).sub (hF_cont z₀ (mem_ball_self h2r'_pos))).const_smul _
        exact (hcont_n.mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc

      have hG_lim : ∀ᵐ t ∂(volume.restrict (Set.uIoc γ.a γ.b)),
          Tendsto (fun n => G n t) atTop (𝓝 (F'_z₀ t)) := by
        rw [ae_restrict_iff' measurableSet_uIoc]
        apply Filter.Eventually.of_forall
        intro t ht
        have ht' := huIoc_sub ht
        have hζ_mem : γ.toFun t ∈ Ω := hγt_mem t ht'
        have hda := (differentiableOn_dividedDiff_fst hΩ hf (γ.toFun t) hζ_mem).differentiableAt
          (hΩ.mem_nhds hz₀) |>.hasDerivAt
        have hda_F : HasDerivAt (fun w => F_main w t) (F'_z₀ t) z₀ := hda.mul_const _
        exact hda_F.tendsto_slope_zero.comp h_seq_tend
      exact aestronglyMeasurable_of_tendsto_ae atTop hG_meas hG_lim)

    (by apply Filter.Eventually.of_forall; intro t ht z hz
        have ht' := huIoc_sub ht
        calc ‖deriv (fun w => dividedDiff f (w, γ.toFun t)) z * deriv γ.toFun t‖
            = ‖deriv (fun w => dividedDiff f (w, γ.toFun t)) z‖ * ‖deriv γ.toFun t‖ := norm_mul ..
          _ ≤ Cdd / r' * Cγ := by
              have hCdd_nn : 0 ≤ Cdd := by
                have hmem : (z₀, γ.toFun γ.a) ∈ closedBall z₀ (2 * r') ×ˢ γ.range :=
                  ⟨mem_closedBall_self (by linarith), ⟨γ.a, left_mem_Icc.mpr γ.hab, rfl⟩⟩
                exact le_trans (norm_nonneg _) (hCdd _ hmem)
              exact mul_le_mul (hderiv_bound t ht' z hz) (hCγ _ ht') (norm_nonneg _)
                (div_nonneg hCdd_nn hr'_pos.le))

    (intervalIntegrable_const)

    (by apply Filter.Eventually.of_forall; intro t ht z hz
        exact hF_deriv t ht z hz)
  exact key.2.differentiableAt

theorem differentiableOn_dslope_contourIntegral_omega
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω) :
    DifferentiableOn ℂ (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) Ω := by
  intro z₀ hz₀
  by_cases hzγ : z₀ ∈ γ.range
  ·
    exact γ.differentiableOn_dslope_contourIntegral_omega_morera hΩ hf hγ z₀ hz₀
  ·
    have hcomp := γ.differentiableOn_dslope_contourIntegral_complement hΩ hf hγ
    have hopen : IsOpen γ.rangeᶜ := γ.isCompact_range.isClosed.isOpen_compl
    exact (hcomp.differentiableAt (hopen.mem_nhds hzγ)).differentiableWithinAt

theorem contourIntegral_dslope_differentiable
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω) :
    Differentiable ℂ (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) := by


  have hF_Ω := γ.differentiableOn_dslope_contourIntegral_omega hΩ hf hγ
  have hF_comp := γ.differentiableOn_dslope_contourIntegral_complement hΩ hf hγ


  have hrange_compact : IsCompact γ.range :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun

  have hrange_open : IsOpen γ.rangeᶜ := hrange_compact.isClosed.isOpen_compl

  have h_cover : Ω ∪ γ.rangeᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro z
    by_cases hz : z ∈ Ω
    · exact Set.mem_union_left _ hz
    · exact Set.mem_union_right _ (fun hc => hz (hγ.1 hc))

  rw [← differentiableOn_univ, ← h_cover]
  exact DifferentiableOn.union_of_isOpen hF_Ω hF_comp hΩ hrange_open

set_option maxHeartbeats 800000 in
theorem contourIntegral_dslope_tendsto_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω) :
    Tendsto (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) (cocompact ℂ) (𝓝 0) := by

  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn γ.continuous_toFun
  obtain ⟨Cd, hCd⟩ := isCompact_Icc.exists_bound_of_continuousOn γ.continuous_deriv
  have hCg_nn : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg γ.a (left_mem_Icc.mpr γ.hab))
  have hCd_nn : 0 ≤ Cd := le_trans (norm_nonneg _) (hCd γ.a (left_mem_Icc.mpr γ.hab))
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf.continuousOn.comp γ.continuous_toFun (fun t ht => hγ.1 ⟨t, ht, rfl⟩)
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont
  have hCf_nn : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf γ.a (left_mem_Icc.mpr γ.hab))

  have wn_int : ∀ z : ℂ, z ∉ γ.range → ∃ n : ℤ, γ.windingNumber z = ↑n := by
    intro z hz
    set h : ℝ → ℂ := fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t with hh_def
    set g : ℝ → ℂ := fun t => ∫ s in γ.a..t, h s with hg_def
    have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t - z ≠ 0 := by
      intro t ht hsub; exact hz ⟨t, ht, sub_eq_zero.mp hsub⟩
    have hh_cont : ContinuousOn h (Icc γ.a γ.b) :=
      ((γ.continuous_toFun.sub continuousOn_const).inv₀ hne).mul γ.continuous_deriv
    have hg_cont : ContinuousOn g (Icc γ.a γ.b) := by
      have hint : IntegrableOn h (uIcc γ.a γ.b) volume := by
        rw [uIcc_of_le γ.hab]; exact hh_cont.integrableOn_compact isCompact_Icc
      have := continuousOn_primitive_interval hint; rwa [uIcc_of_le γ.hab] at this
    set F : ℝ → ℂ := fun t => cexp (-g t) * (γ.toFun t - z) with hF_def
    have hF_cont : ContinuousOn F (Icc γ.a γ.b) :=
      (continuous_exp.comp_continuousOn (hg_cont.neg)).mul
        (γ.continuous_toFun.sub continuousOn_const)
    have hF_deriv : ∀ t ∈ Ioo γ.a γ.b, HasDerivAt F 0 t := by
      intro t ht
      have ht_mem := Ioo_subset_Icc_self ht
      have hh_int : IntervalIntegrable h volume γ.a t :=
        (hh_cont.mono (by rw [uIcc_of_le ht.1.le]; exact Icc_subset_Icc_right ht.2.le)).intervalIntegrable

      have hmeas : StronglyMeasurableAtFilter h (nhds t) volume :=
        ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun x hx => hh_cont.continuousAt (Icc_mem_nhds hx.1 hx.2)) t ht
      have hca : ContinuousAt h t := hh_cont.continuousAt (Icc_mem_nhds ht.1 ht.2)
      have hg_deriv : HasDerivAt g (h t) t := integral_hasDerivAt_right hh_int hmeas hca
      have hγ_deriv : HasDerivAt γ.toFun (deriv γ.toFun t) t :=
        (γ.differentiable.differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
      have hexp_deriv : HasDerivAt (fun t => cexp (-g t)) (cexp (-g t) * (-(h t))) t :=
        (hasDerivAt_exp (-g t)).comp t hg_deriv.neg
      have hsub_deriv : HasDerivAt (fun t => γ.toFun t - z) (deriv γ.toFun t) t := by
        have h1 := hγ_deriv.sub (hasDerivAt_const t z); simp only [sub_zero] at h1; exact h1
      have hprod := hexp_deriv.mul hsub_deriv
      suffices cexp (-g t) * -(h t) * (γ.toFun t - z) + cexp (-g t) * deriv γ.toFun t = 0 by
        rwa [this] at hprod
      simp only [hh_def]; field_simp [hne t ht_mem]; ring
    have hFba : F γ.b = F γ.a := by
      have key := integral_eq_sub_of_hasDerivAt_of_le γ.hab hF_cont hF_deriv
        intervalIntegrable_const
      simp only [intervalIntegral.integral_const, smul_zero] at key
      exact sub_eq_zero.mp key.symm
    have hga : g γ.a = 0 := by simp [hg_def, integral_same]
    have hne_a : γ.toFun γ.a - z ≠ 0 := hne γ.a (left_mem_Icc.mpr γ.hab)
    have hexp_eq : cexp (-(g γ.b)) = 1 := by
      have hFa : F γ.a = γ.toFun γ.a - z := by simp [hF_def, hga]
      have hFb : F γ.b = cexp (-(g γ.b)) * (γ.toFun γ.a - z) := by simp [hF_def, γ.closed]
      have : cexp (-(g γ.b)) * (γ.toFun γ.a - z) = γ.toFun γ.a - z := by
        rw [← hFb, hFba, hFa]
      exact mul_right_cancel₀ hne_a (by rwa [one_mul])
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp_eq
    refine ⟨-n, ?_⟩
    show γ.windingNumber z = ↑(-n)
    unfold ClosedCurve.windingNumber
    change (2 * ↑π * I)⁻¹ * ∫ t in γ.a..γ.b, h t = ↑(-n)
    rw [show (∫ t in γ.a..γ.b, h t) = g γ.b from rfl]
    have hgb : g γ.b = -(↑n * (2 * ↑π * I)) := neg_eq_iff_eq_neg.mp hn
    rw [hgb]; push_cast; field_simp

  have wn_zero_large : ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ → w ∉ γ.range →
      γ.windingNumber w = 0 := by
    use Cg + (2 * Real.pi)⁻¹ * Cd * |γ.b - γ.a| + 1
    intro w hw hw_range
    obtain ⟨n, hn⟩ := wn_int w hw_range
    have hw_sub_pos : 0 < ‖w‖ - Cg := by
      have : 0 ≤ (2 * Real.pi)⁻¹ * Cd * |γ.b - γ.a| :=
        mul_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity)) hCd_nn) (abs_nonneg _)
      linarith
    have hlt : ‖γ.windingNumber w‖ < 1 := by
      unfold windingNumber
      have norm_2piI : ‖(2 * ↑Real.pi * I : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      calc ‖(2 * ↑Real.pi * I)⁻¹ *
              ∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
          ≤ ‖(2 * ↑Real.pi * I)⁻¹‖ *
            ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖ := norm_mul_le _ _
        _ ≤ ‖(2 * ↑Real.pi * I)⁻¹‖ * (Cd / (‖w‖ - Cg) * |γ.b - γ.a|) := by
            gcongr
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro t ht
            rw [uIoc_of_le γ.hab] at ht
            have ht' : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
            have h_norm_sub : ‖w‖ - Cg ≤ ‖γ.toFun t - w‖ := by
              have := norm_sub_norm_le w (γ.toFun t)
              rw [norm_sub_rev] at this; linarith [hCg t ht']
            calc ‖(γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
                = ‖γ.toFun t - w‖⁻¹ * ‖deriv γ.toFun t‖ := by rw [norm_mul, norm_inv]
              _ ≤ (‖w‖ - Cg)⁻¹ * Cd := by
                  apply mul_le_mul (inv_anti₀ hw_sub_pos h_norm_sub) (hCd t ht')
                    (norm_nonneg _) (inv_nonneg.mpr hw_sub_pos.le)
              _ = Cd / (‖w‖ - Cg) := by rw [mul_comm, div_eq_mul_inv]
        _ = (2 * Real.pi)⁻¹ * Cd * |γ.b - γ.a| / (‖w‖ - Cg) := by
            rw [norm_inv, norm_2piI]; ring
        _ < 1 := by rw [div_lt_one hw_sub_pos]; linarith
    rw [hn] at hlt ⊢
    rw [Complex.norm_intCast] at hlt
    have h0 : n = 0 := by
      by_contra hne
      linarith [show (1 : ℝ) ≤ |(↑n : ℝ)| from by exact_mod_cast Int.one_le_abs hne]
    simp [h0]

  obtain ⟨Rw, hRw⟩ := wn_zero_large
  rw [Metric.tendsto_nhds]
  intro ε hε


  set K := Cf * Cd * |γ.b - γ.a| with hK_def
  have hK_nn : 0 ≤ K := mul_nonneg (mul_nonneg hCf_nn hCd_nn) (abs_nonneg _)

  set R := max (Cg + 1) (max (Rw + 1) (Cg + K / ε + 1)) with hR_def

  have hR_gt_Cg : Cg < R := by linarith [le_max_left (Cg + 1) (max (Rw + 1) (Cg + K / ε + 1))]
  have hR_gt_Rw : Rw < R := by
    linarith [le_max_left (Rw + 1) (Cg + K / ε + 1) |>.trans
              (le_max_right (Cg + 1) (max (Rw + 1) (Cg + K / ε + 1)))]


  apply Filter.Eventually.mono
  show ∀ᶠ z : ℂ in cocompact ℂ, R < ‖z‖
  · have : {z : ℂ | ‖z‖ ≤ R} ⊆ Metric.closedBall 0 R := by
      intro z hz; simp [Metric.mem_closedBall, dist_zero_right]; exact hz
    exact Filter.Eventually.mono
      (IsCompact.compl_mem_cocompact
        (IsCompact.of_isClosed_subset (isCompact_closedBall 0 R)
          (isClosed_le continuous_norm continuous_const) this))
      (fun z hz => by simp at hz; exact hz)
  · intro z hz_norm

    have hz_range : z ∉ γ.range := by
      intro ⟨t, ht, htf⟩
      have : ‖z‖ ≤ Cg := by rw [← htf]; exact hCg t ht
      linarith

    have hz_wn : γ.windingNumber z = 0 := hRw z (by linarith) hz_range


    simp only [dist_zero_right]


    have hne_t : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z := by
      intro t ht heq; exact hz_range ⟨t, ht, heq⟩

    have h_eq : γ.contourIntegral (fun ζ => dslope f z ζ) =
        (∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t)
        - f z * (∫ t in γ.a..γ.b, (γ.toFun t - z)⁻¹ * deriv γ.toFun t) := by
      unfold contourIntegral
      have h_integrand : ∀ t ∈ Icc γ.a γ.b,
          dslope f z (γ.toFun t) * deriv γ.toFun t =
            f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t
            - f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t) := by
        intro t ht
        have hne' : γ.toFun t ≠ z := hne_t t ht
        rw [dslope_of_ne _ hne', slope_def_module, smul_eq_mul]; ring
      rw [show (∫ t in γ.a..γ.b, dslope f z (γ.toFun t) * deriv γ.toFun t) =
            ∫ t in γ.a..γ.b, (f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t
            - f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t)) from
            intervalIntegral.integral_congr (fun t ht => by
              rw [uIcc_of_le γ.hab] at ht
              exact h_integrand t ht)]
      rw [intervalIntegral.integral_sub]
      · congr 1
        exact intervalIntegral.integral_const_mul (f z) _
      · exact ((hfγ_cont.mul ((γ.continuous_toFun.sub continuousOn_const).inv₀
            (fun t ht => sub_ne_zero.mpr (hne_t t ht)))).mul γ.continuous_deriv).intervalIntegrable_of_Icc γ.hab
      · exact (continuousOn_const.mul
            (((γ.continuous_toFun.sub continuousOn_const).inv₀
            (fun t ht => sub_ne_zero.mpr (hne_t t ht))).mul γ.continuous_deriv)).intervalIntegrable_of_Icc γ.hab

    have h_wn_integral : ∫ t in γ.a..γ.b, (γ.toFun t - z)⁻¹ * deriv γ.toFun t =
        2 * ↑π * I * γ.windingNumber z := by
      unfold windingNumber
      have h2pi : (2 : ℂ) * ↑π * I ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (mod_cast Real.pi_ne_zero)) I_ne_zero
      field_simp
    rw [h_eq, h_wn_integral, hz_wn, mul_zero, mul_zero, sub_zero]

    have hz_sub_pos : 0 < ‖z‖ - Cg := by linarith
    calc ‖∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t‖
        ≤ Cf * Cd / (‖z‖ - Cg) * |γ.b - γ.a| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro t ht
          rw [uIoc_of_le γ.hab] at ht
          have ht' : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
          have h_norm_sub : ‖z‖ - Cg ≤ ‖γ.toFun t - z‖ := by
            have := norm_sub_norm_le z (γ.toFun t)
            rw [norm_sub_rev] at this; linarith [hCg t ht']
          calc ‖f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t‖
              = ‖f (γ.toFun t)‖ * ‖γ.toFun t - z‖⁻¹ * ‖deriv γ.toFun t‖ := by
                rw [norm_mul, norm_mul, norm_inv]
            _ ≤ Cf * (‖z‖ - Cg)⁻¹ * Cd := by
                apply mul_le_mul
                · apply mul_le_mul (hCf t ht') (inv_anti₀ hz_sub_pos h_norm_sub)
                    (inv_nonneg.mpr (norm_nonneg _)) (le_trans (norm_nonneg _) (hCf t ht'))
                · exact hCd t ht'
                · exact norm_nonneg _
                · exact mul_nonneg (le_trans (norm_nonneg _) (hCf t ht'))
                    (inv_nonneg.mpr hz_sub_pos.le)
            _ = Cf * Cd / (‖z‖ - Cg) := by ring
      _ = K / (‖z‖ - Cg) := by rw [hK_def]; ring
      _ < ε := by
          rw [div_lt_iff₀ hz_sub_pos]
          have hR_bound : Cg + K / ε + 1 ≤ R := le_max_right _ _ |>.trans (le_max_right _ _)
          have hKe : K / ε < ‖z‖ - Cg := by linarith
          calc K = K / ε * ε := (div_mul_cancel₀ K hε.ne').symm
            _ < (‖z‖ - Cg) * ε := by nlinarith
            _ = ε * (‖z‖ - Cg) := by ring

theorem contourIntegral_dslope_eq_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω)
    {z : ℂ} (_hz : z ∈ Ω) :
    γ.contourIntegral (fun ζ => dslope f z ζ) = 0 := by

  have h_diff := γ.contourIntegral_dslope_differentiable hΩ hf hγ

  have h_tend := γ.contourIntegral_dslope_tendsto_zero hΩ hf hγ

  exact _root_.Differentiable.apply_eq_of_tendsto_cocompact h_diff z h_tend

lemma h_vanishes
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω)
    {z : ℂ} (hz : z ∈ Ω) (hzγ : z ∉ γ.range) :
    γ.contourIntegral (fun ζ => (f ζ - f z) * (ζ - z)⁻¹) = 0 := by

  have key := γ.contourIntegral_dslope_eq_zero hΩ hf hγ hz


  suffices γ.contourIntegral (fun ζ => (f ζ - f z) * (ζ - z)⁻¹) =
      γ.contourIntegral (fun ζ => dslope f z ζ) from this ▸ key
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le γ.hab] at ht
  have hne : γ.toFun t ≠ z := fun h => hzγ ⟨t, ht, h⟩
  simp only []
  congr 1
  rw [dslope_of_ne _ hne, slope_def_module, smul_eq_mul]
  ring

lemma contourIntegrable_cauchy_kernel
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsHomologousToZero Ω)
    {z : ℂ} (hz : z ∈ Ω) (hzγ : z ∉ γ.range) :
    IntervalIntegrable
      (fun t => f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t)
      MeasureSpace.volume γ.a γ.b ∧
    IntervalIntegrable
      (fun t => f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t))
      MeasureSpace.volume γ.a γ.b := by

  have hder : IntervalIntegrable (deriv γ.toFun) MeasureSpace.volume γ.a γ.b :=
    ContinuousOn.intervalIntegrable_of_Icc γ.hab γ.continuous_deriv
  have hγΩ : γ.LiesIn Ω := hγ.1

  have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t - z ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (fun h => hzγ (h ▸ ⟨t, ht, rfl⟩))

  have hfg_cont : ContinuousOn (fun t => f (γ.toFun t) * (γ.toFun t - z)⁻¹) (Icc γ.a γ.b) :=
    (ContinuousOn.comp hf.continuousOn γ.continuous_toFun
      (fun t ht => hγΩ ⟨t, ht, rfl⟩)).mul
      ((γ.continuous_toFun.sub continuousOn_const).inv₀ hne)

  have hinv_cont : ContinuousOn (fun t => (γ.toFun t - z)⁻¹) (Icc γ.a γ.b) :=
    (γ.continuous_toFun.sub continuousOn_const).inv₀ hne
  refine ⟨?_, ?_⟩
  ·
    convert hder.continuousOn_mul (uIcc_of_le γ.hab ▸ hfg_cont) using 1
  ·
    have h1 : IntervalIntegrable (fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t)
        MeasureSpace.volume γ.a γ.b :=
      hder.continuousOn_mul (uIcc_of_le γ.hab ▸ hinv_cont)
    convert h1.const_mul (f z) using 1

theorem cauchy_integral_formula (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω)
    (z : ℂ) (hz : z ∈ Ω) (hzγ : z ∉ γ.range) :
    γ.windingNumber z * f z =
      (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹) := by

  have hv := γ.h_vanishes hΩ hf hγ hz hzγ
  have hI := γ.contourIntegrable_cauchy_kernel hΩ hf hγ hz hzγ

  simp only [contourIntegral] at hv ⊢
  simp only [windingNumber]


  have hv' : ∫ t in γ.a..γ.b, (f (γ.toFun t) * (γ.toFun t - z)⁻¹ * deriv γ.toFun t -
      f z * ((γ.toFun t - z)⁻¹ * deriv γ.toFun t)) = 0 := by
    convert hv using 1; congr 1; ext t; ring

  rw [intervalIntegral.integral_sub hI.1 hI.2] at hv'

  have hconst : ∫ (x : ℝ) in γ.a..γ.b, f z * ((γ.toFun x - z)⁻¹ * deriv γ.toFun x) =
      f z * ∫ (x : ℝ) in γ.a..γ.b, (γ.toFun x - z)⁻¹ * deriv γ.toFun x :=
    intervalIntegral.integral_const_mul _ _
  rw [hconst] at hv'

  rw [sub_eq_zero.mp hv']
  ring

theorem exists_point_in_open_not_on_curve (Ω : Set ℂ) (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty)
    (γ : ClosedCurve) (hγ : γ.LiesIn Ω) :
    ∃ z₀ : ℂ, z₀ ∈ Ω ∧ z₀ ∉ γ.range := by
  by_contra h
  push Not at h

  have hΩeq : Ω = γ.range := Subset.antisymm (fun z hz => h z hz) hγ

  have hK : IsCompact γ.range := isCompact_Icc.image_of_continuousOn γ.continuous_toFun

  rw [hΩeq] at hΩ hΩne
  have hcl : IsClopen γ.range := ⟨hK.isClosed, hΩ⟩

  exact noncompact_univ ℂ (hcl.eq_univ hΩne ▸ hK)

theorem cauchy_theorem (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω) :
    γ.contourIntegral f = 0 := by

  obtain ⟨z₀, hz₀Ω, hz₀γ⟩ := exists_point_in_open_not_on_curve Ω hΩ
    (γ.liesIn_nonempty hγ.1) γ hγ.1

  have hF : DifferentiableOn ℂ (fun ζ => (ζ - z₀) * f ζ) Ω :=
    (differentiableOn_id.sub (differentiableOn_const z₀)).mul hf

  have hCIF := cauchy_integral_formula Ω hΩ (fun ζ => (ζ - z₀) * f ζ) hF γ hγ z₀ hz₀Ω hz₀γ

  simp only [sub_self, zero_mul, mul_zero] at hCIF

  rw [γ.contourIntegral_cancel_sub_inv hz₀γ] at hCIF

  have h2pi : (2 : ℂ) * ↑π * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (mod_cast Real.pi_ne_zero)) I_ne_zero
  rwa [eq_comm, mul_eq_zero, inv_eq_zero, or_iff_right h2pi] at hCIF

end ClosedCurve

theorem differentiableOn_cauchyPiecewise_omega (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω) :
    DifferentiableOn ℂ (cauchyPiecewise Ω f γ) Ω := by

  set F : ℂ → ℂ := fun z => (2 * ↑π * I)⁻¹ *
    γ.contourIntegral (fun ζ => dslope f z ζ) with hF_def

  have hF_diff : Differentiable ℂ F :=
    (γ.contourIntegral_dslope_differentiable hΩ hf hγ).const_mul _

  have h_eq : ∀ z ∈ Ω, cauchyPiecewise Ω f γ z = F z := by
    intro z hz
    simp only [cauchyPiecewise, if_pos hz, dividedDiff, hF_def]


  exact hF_diff.differentiableOn.congr (fun z hz => (h_eq z hz))

theorem cauchyPiecewise_eq_cauchyTypeIntegral_on_complementDomain
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω) :
    ∀ z ∈ γ.complementDomain, cauchyPiecewise Ω f γ z = cauchyTypeIntegral f γ z := by
  intro z ⟨hzγ, hwz⟩
  by_cases hz : z ∈ Ω
  ·

    have lhs : cauchyPiecewise Ω f γ z = 0 := by
      rw [cauchyPiecewise_eq_on_omega hz]
      have : γ.contourIntegral (fun ζ => dividedDiff f (z, ζ)) = 0 := by
        have h := γ.contourIntegral_dslope_eq_zero hΩ hf hγ hz
        convert h using 1
      rw [this, mul_zero]

    have rhs : cauchyTypeIntegral f γ z = 0 := by
      have hcif := ClosedCurve.cauchy_integral_formula Ω hΩ f hf γ hγ z hz hzγ
      rw [hwz, zero_mul] at hcif
      simp only [cauchyTypeIntegral]
      exact hcif.symm
    rw [lhs, rhs]
  ·
    simp only [cauchyPiecewise_eq_off_omega hz, cauchyTypeIntegral]

theorem differentiableOn_cauchyPiecewise_complement (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω) :
    DifferentiableOn ℂ (cauchyPiecewise Ω f γ) γ.complementDomain := by
  have h_eq := cauchyPiecewise_eq_cauchyTypeIntegral_on_complementDomain Ω hΩ f hf γ hγ
  have h_cont : ContinuousOn f γ.range :=
    hf.continuousOn.mono (fun z hz => hγ.1 hz)
  have h_diff := differentiableOn_cauchyTypeIntegral f γ h_cont
  have h_sub : γ.complementDomain ⊆ (γ.range)ᶜ := fun z hz => hz.1
  exact (h_diff.mono h_sub).congr (fun z hz => (h_eq z hz))

theorem cauchyPiecewise_differentiable (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω) :
    Differentiable ℂ (cauchyPiecewise Ω f γ) := by
  rw [← differentiableOn_univ, ← union_complementDomain_eq_univ hγ]
  exact DifferentiableOn.union_of_isOpen
    (differentiableOn_cauchyPiecewise_omega Ω hΩ f hf γ hγ)
    (differentiableOn_cauchyPiecewise_complement Ω hΩ f hf γ hγ)
    hΩ (isOpen_complementDomain γ)

theorem cauchyPiecewise_tendsto_zero_cocompact (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω) :
    Filter.Tendsto (cauchyPiecewise Ω f γ) (Filter.cocompact ℂ) (nhds 0) := by

  set F := fun z => (2 * ↑π * I)⁻¹ *
    γ.contourIntegral (fun ζ => dslope f z ζ) with hF_def

  have hF_diff : Differentiable ℂ F :=
    (γ.contourIntegral_dslope_differentiable hΩ hf hγ).const_mul _

  have hG_diff := cauchyPiecewise_differentiable Ω hΩ f hf γ hγ

  have agree_on_Ω : ∀ z ∈ Ω, cauchyPiecewise Ω f γ z = F z := by
    intro z hz
    simp only [cauchyPiecewise, if_pos hz, dividedDiff, hF_def]

  obtain ⟨z₀, hz₀⟩ := γ.range_nonempty.mono hγ.1

  have heq_nhds : cauchyPiecewise Ω f γ =ᶠ[nhds z₀] F :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, hΩ.mem_nhds hz₀, agree_on_Ω⟩

  have heq : cauchyPiecewise Ω f γ = F :=
    AnalyticOnNhd.eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG_diff)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF_diff)
      heq_nhds

  have hF_tends : Filter.Tendsto F (Filter.cocompact ℂ) (nhds 0) := by
    rw [hF_def]
    have : (fun z => (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => dslope f z ζ)) =
           ((· * ·) ((2 * ↑π * I)⁻¹)) ∘
             (fun z => γ.contourIntegral (fun ζ => dslope f z ζ)) := by
      ext; simp
    rw [this]
    conv_rhs => rw [show (0 : ℂ) = (2 * ↑π * I)⁻¹ * 0 from by ring]
    exact (γ.contourIntegral_dslope_tendsto_zero hΩ hf hγ).const_mul _

  rw [heq]
  exact hF_tends

theorem cauchyPiecewise_eq_zero (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (γ : ClosedCurve) (hγ : γ.IsHomologousToZero Ω)
    (z : ℂ) :
    cauchyPiecewise Ω f γ z = 0 := by
  have h_entire := cauchyPiecewise_differentiable Ω hΩ f hf γ hγ
  have h_tendsto := cauchyPiecewise_tendsto_zero_cocompact Ω hΩ f hf γ hγ
  exact Differentiable.apply_eq_of_tendsto_cocompact h_entire z h_tendsto

end

open Topology OnePoint

abbrev RiemannSphere := OnePoint ℂ

def Set.toRiemannSphere (Ω : Set ℂ) : Set RiemannSphere :=
  OnePoint.some '' Ω

def Complex.IsSimplyConnected (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ IsConnected (Ω.toRiemannSphere)ᶜ

lemma Complex.IsSimplyConnected.isOpen {Ω : Set ℂ} (h : Complex.IsSimplyConnected Ω) :
    IsOpen Ω :=
  h.1

lemma Complex.IsSimplyConnected.isConnected {Ω : Set ℂ} (h : Complex.IsSimplyConnected Ω) :
    IsConnected Ω :=
  h.2.1
