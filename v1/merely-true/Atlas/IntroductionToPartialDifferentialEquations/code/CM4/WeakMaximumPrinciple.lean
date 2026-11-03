/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Basic

open Set

noncomputable section

namespace WeakMaximumPrinciple

/-- The open spacetime cylinder $Q_T = (0,T) \times (a,b) \subseteq \mathbb{R}^2$,
the spatial-temporal domain on which the heat equation is posed. -/
def SpacetimeCylinder (T a b : ℝ) : Set (ℝ × ℝ) :=
  Ioo 0 T ×ˢ Ioo a b

/-- The closed spacetime cylinder $\overline{Q_T} = [0,T] \times [a,b]$,
the closure of the spacetime cylinder where the solution is required to be continuous. -/
def ClosedCylinder (T a b : ℝ) : Set (ℝ × ℝ) :=
  Icc 0 T ×ˢ Icc a b

/-- The parabolic boundary $\partial_p Q_T = (\{0\} \times [a,b]) \cup ((0,T] \times \{a,b\})$,
i.e. the bottom of the cylinder together with its lateral sides (but not the top). -/
def ParabolicBoundary (T a b : ℝ) : Set (ℝ × ℝ) :=
  ({0} ×ˢ Icc a b) ∪ (Ioc 0 T ×ˢ {a, b})

/-- The parabolic boundary is contained in the closed cylinder. -/
lemma ParabolicBoundary_subset_ClosedCylinder {T a b : ℝ} (hT : 0 < T) (hab : a ≤ b) :
    ParabolicBoundary T a b ⊆ ClosedCylinder T a b := by
  intro ⟨t, x⟩ htx
  simp only [ParabolicBoundary, ClosedCylinder, mem_union, mem_prod, mem_singleton_iff,
    mem_Icc, mem_Ioc, mem_insert_iff] at htx ⊢
  rcases htx with ⟨rfl, hx⟩ | ⟨ht, hx⟩
  · exact ⟨⟨le_refl _, hT.le⟩, hx⟩
  · rcases hx with rfl | rfl
    · exact ⟨⟨ht.1.le, ht.2⟩, ⟨le_refl _, hab⟩⟩
    · exact ⟨⟨ht.1.le, ht.2⟩, ⟨hab, le_refl _⟩⟩

/-- The closed cylinder is nonempty whenever $T \ge 0$ and $a \le b$. -/
lemma ClosedCylinder_nonempty {T a b : ℝ} (hT : 0 ≤ T) (hab : a ≤ b) :
    (ClosedCylinder T a b).Nonempty :=
  ⟨(0, a), by simp [ClosedCylinder, mem_Icc, hT, hab]⟩

/-- The parabolic boundary is nonempty whenever $a \le b$ (it contains $(0, a)$). -/
lemma ParabolicBoundary_nonempty {T a b : ℝ} (hab : a ≤ b) :
    (ParabolicBoundary T a b).Nonempty :=
  ⟨(0, a), by simp [ParabolicBoundary, mem_union, mem_prod, mem_Icc, hab]⟩

/-- The closed cylinder $[0,T] \times [a,b]$ is compact, as a product of compact intervals. -/
lemma ClosedCylinder_isCompact {T a b : ℝ} :
    IsCompact (ClosedCylinder T a b) :=
  isCompact_Icc.prod isCompact_Icc

/-- The heat operator $L_D u = u_t - D \, u_{xx}$ acting on a function $u : \mathbb{R}^2 \to \mathbb{R}$
at a point $p = (t, x)$, with diffusion constant $D$. -/
def HeatOp (u : ℝ × ℝ → ℝ) (D : ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun t => u (t, p.2)) p.1 1 -
    D * fderiv ℝ (fun x => fderiv ℝ (fun x' => u (p.1, x')) x 1) p.2 1

/-- Subtracting a constant does not change the Fréchet derivative:
$\frac{d}{dx}(f(x) - c) = \frac{d}{dx} f(x)$. -/
lemma HeatOp_fderiv_sub_const_eq (f : ℝ → ℝ) (c : ℝ) (x : ℝ) :
    fderiv ℝ (fun t => f t - c) x = fderiv ℝ f x := by
  by_cases hd : DifferentiableAt ℝ f x
  · rw [show (fun t => f t - c) = f - fun _ => c from rfl,
        fderiv_sub hd (differentiableAt_const c)]
    simp
  · have : ¬ DifferentiableAt ℝ (fun t => f t - c) x := by
      intro h; apply hd
      convert h.add (differentiableAt_const c) using 1; ext t; simp [sub_add_cancel]
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt this]

/-- At an interior maximum point $(t_0, x_0)$ of $u$ in the closed cylinder
(with $t_0 > 0$ and $a < x_0 < b$), the time derivative satisfies $u_t(t_0, x_0) \ge 0$,
since $u$ does not increase as $t$ decreases away from the maximum. -/
theorem time_deriv_nonneg_at_interior_max
    {T a b : ℝ} (hT : 0 < T) (hab : a < b)
    (u : ℝ × ℝ → ℝ)
    (hu_cont : ContinuousOn u (ClosedCylinder T a b))
    (t₀ x₀ : ℝ)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hx₀a : a < x₀) (hx₀b : x₀ < b)
    (hmax : ∀ q ∈ ClosedCylinder T a b, u q ≤ u (t₀, x₀)) :
    fderiv ℝ (fun t => u (t, x₀)) t₀ (1 : ℝ) ≥ 0 := by

  show deriv (fun t => u (t, x₀)) t₀ ≥ 0
  set g := fun t => u (t, x₀) with hg_def

  have hg_le : ∀ t ∈ Icc 0 t₀, g t ≤ g t₀ := by
    intro t ⟨h0t, htt₀⟩
    apply hmax
    exact ⟨⟨h0t, le_trans htt₀ ht₀T⟩, ⟨hx₀a.le, hx₀b.le⟩⟩
  by_cases hd : DifferentiableAt ℝ g t₀
  ·
    by_contra h_neg
    push Not at h_neg
    have hda := hd.hasDerivAt
    have hslope := hda.tendsto_slope_zero_left

    have hev_neg : ∀ᶠ h in nhdsWithin (0:ℝ) (Iio 0), h⁻¹ • (g (t₀ + h) - g t₀) < 0 :=
      hslope.eventually (gt_mem_nhds (by linarith : (0:ℝ) > deriv g t₀))
    have hev_h_neg : ∀ᶠ h in nhdsWithin (0:ℝ) (Iio 0), h < 0 :=
      eventually_nhdsWithin_of_forall (fun x hx => hx)

    have hev_h_bound : ∀ᶠ h in nhdsWithin (0:ℝ) (Iio 0), -t₀ < h := by
      apply nhdsWithin_le_nhds
      exact Ioi_mem_nhds (by linarith)
    obtain ⟨h, hslope_neg, hh_neg, hh_bound⟩ := (hev_neg.and (hev_h_neg.and hev_h_bound)).exists

    have h_mem : t₀ + h ∈ Icc 0 t₀ := by constructor <;> linarith
    have h_le : g (t₀ + h) ≤ g t₀ := hg_le _ h_mem

    have : h⁻¹ • (g (t₀ + h) - g t₀) ≥ 0 := by
      simp only [smul_eq_mul]
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt (inv_lt_zero.mpr hh_neg)) (by linarith)
    linarith
  ·
    rw [deriv_zero_of_not_differentiableAt hd]

/-- At an interior maximum point $(t_0, x_0)$ of $u$ (with $a < x_0 < b$), the second spatial
derivative satisfies $u_{xx}(t_0, x_0) \le 0$, by the standard one-variable second derivative test. -/
theorem spatial_second_deriv_nonpos_at_interior_max
    {T a b : ℝ} (hT : 0 < T) (hab : a < b)
    (u : ℝ × ℝ → ℝ)
    (hu_cont : ContinuousOn u (ClosedCylinder T a b))
    (t₀ x₀ : ℝ)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hx₀a : a < x₀) (hx₀b : x₀ < b)
    (hmax : ∀ q ∈ ClosedCylinder T a b, u q ≤ u (t₀, x₀)) :
    fderiv ℝ (fun x => fderiv ℝ (fun x' => u (t₀, x')) x (1 : ℝ)) x₀ (1 : ℝ) ≤ 0 := by

  show deriv (fun x => deriv (fun x' => u (t₀, x')) x) x₀ ≤ 0
  set f := fun x => u (t₀, x) with hf_def

  have hf_max_on : ∀ x ∈ Icc a b, f x ≤ f x₀ := by
    intro x ⟨hax, hxb⟩
    exact hmax (t₀, x) ⟨⟨ht₀.le, ht₀T⟩, ⟨hax, hxb⟩⟩
  have hlocal_max : IsLocalMax f x₀ := by
    apply IsMaxOn.isLocalMax (s := Icc a b) (hs := Icc_mem_nhds hx₀a hx₀b)
    exact hf_max_on

  have hcont_f : ContinuousAt f x₀ := by
    have h_maps : MapsTo (fun x => (t₀, x)) (Icc a b) (ClosedCylinder T a b) := by
      intro x ⟨hax, hxb⟩
      exact ⟨⟨ht₀.le, ht₀T⟩, ⟨hax, hxb⟩⟩
    have : ContinuousOn f (Icc a b) := hu_cont.comp (by fun_prop) h_maps
    exact this.continuousAt (Icc_mem_nhds hx₀a hx₀b)


  by_contra h_pos
  push Not at h_pos
  have hd0 : deriv f x₀ = 0 := hlocal_max.deriv_eq_zero
  have hlocal_min : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos h_pos hd0 hcont_f

  have heq : ∀ᶠ x in nhds x₀, f x = f x₀ := by
    filter_upwards [hlocal_max, hlocal_min] with x hmax' hmin
    exact le_antisymm hmax' hmin
  rw [Filter.eventually_iff_exists_mem] at heq
  obtain ⟨s, hs_nhds, hs_eq⟩ := heq
  rw [mem_nhds_iff] at hs_nhds
  obtain ⟨t, hts, ht_open, hx₀t⟩ := hs_nhds

  have hderiv_zero : ∀ x ∈ t, deriv f x = 0 := by
    intro x hx
    have : f =ᶠ[nhds x] fun _ => f x₀ := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨t, ht_open.mem_nhds hx, fun y hy => hs_eq y (hts hy)⟩
    rw [this.deriv_eq]
    exact deriv_const x (f x₀)

  have hderiv_eq : deriv f =ᶠ[nhds x₀] fun _ => (0 : ℝ) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨t, ht_open.mem_nhds hx₀t, hderiv_zero⟩
  have : deriv (deriv f) x₀ = 0 := by
    rw [hderiv_eq.deriv_eq]
    exact deriv_const x₀ (0 : ℝ)
  linarith

/-- Combining the time and spatial derivative tests: at an interior maximum point of $u$, the
heat operator is nonnegative, $L_D u(t_0, x_0) = u_t - D u_{xx} \ge 0$ (when $D > 0$). -/
theorem interior_max_HeatOp_nonneg
    {T a b D : ℝ} (hT : 0 < T) (hab : a < b) (hD : 0 < D)
    (u : ℝ × ℝ → ℝ)
    (hu_cont : ContinuousOn u (ClosedCylinder T a b))
    (t₀ x₀ : ℝ)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hx₀a : a < x₀) (hx₀b : x₀ < b)
    (hmax : ∀ q ∈ ClosedCylinder T a b, u q ≤ u (t₀, x₀)) :
    HeatOp u D (t₀, x₀) ≥ 0 := by
  unfold HeatOp
  have h_ut := time_deriv_nonneg_at_interior_max hT hab u hu_cont t₀ x₀ ht₀ ht₀T hx₀a hx₀b hmax
  have h_uxx := spatial_second_deriv_nonpos_at_interior_max hT hab u hu_cont t₀ x₀ ht₀ ht₀T hx₀a hx₀b hmax
  linarith [mul_nonneg hD.le (neg_nonneg.mpr h_uxx)]

/-- The perturbation identity: $L_D(w - \varepsilon t) = L_D w - \varepsilon$, used to convert a
non-strict inequality $L_D w \le 0$ into a strict one for the perturbed function. -/
theorem HeatOp_sub_eps_time
    (w : ℝ × ℝ → ℝ) (D ε : ℝ) (p : ℝ × ℝ)
    (hw_t : DifferentiableAt ℝ (fun t => w (t, p.2)) p.1) :
    HeatOp (fun q => w q - ε * q.1) D p = HeatOp w D p - ε := by
  unfold HeatOp
  have hεt : DifferentiableAt ℝ (fun t => ε * t) p.1 := by fun_prop
  conv_lhs =>
    rw [show (fun t => (fun q => w q - ε * q.1) (t, p.2)) =
        (fun t => w (t, p.2)) - (fun t => ε * t) from by ext; simp]
  rw [fderiv_sub hw_t hεt, ContinuousLinearMap.sub_apply]
  have h_deriv_εt : (fderiv ℝ (fun t => ε * t) p.1) (1 : ℝ) = ε := by
    change deriv (fun t => ε * t) p.1 = ε
    rw [show (fun t => ε * t) = (· * ε) from by ext; ring]
    simp
  rw [h_deriv_εt]
  have h_space : (fun x => fderiv ℝ (fun x' => (fun q => w q - ε * q.1) (p.1, x')) x (1 : ℝ)) =
      (fun x => fderiv ℝ (fun x' => w (p.1, x')) x (1 : ℝ)) := by
    ext x; congr 1
    exact HeatOp_fderiv_sub_const_eq (fun x' => w (p.1, x')) (ε * p.1) x
  rw [h_space]
  ring

/-- Linearity of the heat operator under subtraction: $L_D(w - v) = L_D w - L_D v$ for $C^2$
functions $w$ and $v$. -/
theorem HeatOp_sub
    (w v : ℝ × ℝ → ℝ) (hw : ContDiff ℝ 2 w) (hv : ContDiff ℝ 2 v)
    (D : ℝ) (p : ℝ × ℝ) :
    HeatOp (fun q => w q - v q) D p = HeatOp w D p - HeatOp v D p := by
  unfold HeatOp
  have hw_t : DifferentiableAt ℝ (fun t => w (t, p.2)) p.1 :=
    (hw.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt
  have hv_t : DifferentiableAt ℝ (fun t => v (t, p.2)) p.1 :=
    (hv.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt
  have hw_x : ∀ x, DifferentiableAt ℝ (fun x' => w (p.1, x')) x :=
    fun x => (hw.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt
  have hv_x : ∀ x, DifferentiableAt ℝ (fun x' => v (p.1, x')) x :=
    fun x => (hv.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt
  have hw_xx : DifferentiableAt ℝ (fun x => fderiv ℝ (fun x' => w (p.1, x')) x (1 : ℝ)) p.2 := by
    have h1 : ContDiff ℝ 2 (fun x' : ℝ => w (p.1, x')) := hw.comp (by fun_prop)
    have h2 : ContDiff ℝ 1 (fun x => fderiv ℝ (fun x' => w (p.1, x')) x) :=
      h1.fderiv_right (by norm_cast : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((h2.clm_apply contDiff_const).differentiable (by decide)).differentiableAt
  have hv_xx : DifferentiableAt ℝ (fun x => fderiv ℝ (fun x' => v (p.1, x')) x (1 : ℝ)) p.2 := by
    have h1 : ContDiff ℝ 2 (fun x' : ℝ => v (p.1, x')) := hv.comp (by fun_prop)
    have h2 : ContDiff ℝ 1 (fun x => fderiv ℝ (fun x' => v (p.1, x')) x) :=
      h1.fderiv_right (by norm_cast : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((h2.clm_apply contDiff_const).differentiable (by decide)).differentiableAt
  conv_lhs =>
    rw [show (fun t => (fun q => w q - v q) (t, p.2)) = (fun t => w (t, p.2)) - (fun t => v (t, p.2)) from by ext; simp]
  rw [fderiv_sub hw_t hv_t]
  simp only [ContinuousLinearMap.sub_apply]
  have h_inner : ∀ x, fderiv ℝ (fun x' => w (p.1, x') - v (p.1, x')) x =
      fderiv ℝ (fun x' => w (p.1, x')) x - fderiv ℝ (fun x' => v (p.1, x')) x := by
    intro x
    rw [show (fun x' => w (p.1, x') - v (p.1, x')) = (fun x' => w (p.1, x')) - (fun x' => v (p.1, x')) from by ext; simp]
    exact fderiv_sub (hw_x x) (hv_x x)
  have h_inner_applied : (fun x => fderiv ℝ (fun x' => (fun q => w q - v q) (p.1, x')) x (1 : ℝ)) =
      (fun x => fderiv ℝ (fun x' => w (p.1, x')) x 1 - fderiv ℝ (fun x' => v (p.1, x')) x 1) := by
    ext x; simp [h_inner x, ContinuousLinearMap.sub_apply]
  rw [h_inner_applied]
  rw [show (fun x => fderiv ℝ (fun x' => w (p.1, x')) x (1 : ℝ) - fderiv ℝ (fun x' => v (p.1, x')) x (1 : ℝ)) =
      (fun x => fderiv ℝ (fun x' => w (p.1, x')) x 1) - (fun x => fderiv ℝ (fun x' => v (p.1, x')) x 1) from by ext; simp]
  rw [fderiv_sub hw_xx hv_xx]
  simp [ContinuousLinearMap.sub_apply]
  ring

/-- Perturbation by a linear-in-time term: $L_D(u - tM) = L_D u - M$, used in the stability
estimate proof. -/
theorem HeatOp_sub_time_const
    (u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 2 u) (D M : ℝ) (p : ℝ × ℝ) :
    HeatOp (fun q => u q - q.1 * M) D p = HeatOp u D p - M := by
  unfold HeatOp
  have hu_t : DifferentiableAt ℝ (fun t => u (t, p.2)) p.1 :=
    (hu.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt
  have hM : DifferentiableAt ℝ (fun t => t * M) p.1 := by fun_prop
  conv_lhs =>
    rw [show (fun t => (fun q => u q - q.1 * M) (t, p.2)) =
        (fun t => u (t, p.2)) - (fun t => t * M) from by ext; simp]
  rw [fderiv_sub hu_t hM, ContinuousLinearMap.sub_apply]
  have h_deriv_tM : (fderiv ℝ (fun t => t * M) p.1) (1 : ℝ) = M := by
    change deriv (fun t => t * M) p.1 = M
    simp
  rw [h_deriv_tM]
  have h_space : (fun x => fderiv ℝ (fun x' => (fun q => u q - q.1 * M) (p.1, x')) x (1 : ℝ)) =
      (fun x => fderiv ℝ (fun x' => u (p.1, x')) x (1 : ℝ)) := by
    ext x; congr 1
    exact HeatOp_fderiv_sub_const_eq (fun x' => u (p.1, x')) (p.1 * M) x
  rw [h_space]
  ring

/-- Strict version of the weak maximum principle: if $L_D u < 0$ strictly throughout the interior
of $Q_T$, then $u$ attains its maximum on the closed cylinder on the parabolic boundary
$\partial_p Q_T$. -/
lemma strict_max_on_ParabolicBoundary
    {T a b D : ℝ} (hT : 0 < T) (hab : a < b) (hD : 0 < D)
    (u : ℝ × ℝ → ℝ)
    (hu_cont : ContinuousOn u (ClosedCylinder T a b))
    (hL_neg : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp u D (t, x) < 0) :
    ∀ p ∈ ClosedCylinder T a b,
      u p ≤ sSup (u '' ParabolicBoundary T a b) := by
  have hne : (ClosedCylinder T a b).Nonempty := ClosedCylinder_nonempty hT.le hab.le
  obtain ⟨p₀, hp₀_mem, hp₀_max⟩ := ClosedCylinder_isCompact.exists_isMaxOn hne hu_cont
  have hp₀_le : ∀ q ∈ ClosedCylinder T a b, u q ≤ u p₀ := fun q hq => hp₀_max hq
  obtain ⟨t₀, x₀⟩ := p₀
  simp only [ClosedCylinder, mem_prod, mem_Icc] at hp₀_mem
  obtain ⟨⟨h0t₀, ht₀T⟩, ⟨hax₀, hx₀b⟩⟩ := hp₀_mem
  have hbdd : BddAbove (u '' ParabolicBoundary T a b) :=
    (ClosedCylinder_isCompact.image_of_continuousOn hu_cont).bddAbove.mono
      (image_mono (ParabolicBoundary_subset_ClosedCylinder hT hab.le))
  suffices hp₀_pb : (t₀, x₀) ∈ ParabolicBoundary T a b by
    intro p hp
    calc u p ≤ u (t₀, x₀) := hp₀_le p hp
    _ ≤ sSup (u '' ParabolicBoundary T a b) :=
        le_csSup hbdd (mem_image_of_mem u hp₀_pb)

  by_contra h_not_pb
  have ht₀_ne : t₀ ≠ 0 := by
    intro ht0; apply h_not_pb; left; exact ⟨ht0, hax₀, hx₀b⟩
  have ht₀_pos : 0 < t₀ := lt_of_le_of_ne h0t₀ (Ne.symm ht₀_ne)
  have hx₀_ne_a : x₀ ≠ a := by
    intro hxa; apply h_not_pb; right; exact ⟨⟨ht₀_pos, ht₀T⟩, Or.inl hxa⟩
  have hx₀_ne_b : x₀ ≠ b := by
    intro hxb; apply h_not_pb; right; exact ⟨⟨ht₀_pos, ht₀T⟩, Or.inr hxb⟩
  have hx₀a : a < x₀ := lt_of_le_of_ne hax₀ (Ne.symm hx₀_ne_a)
  have hx₀b' : x₀ < b := lt_of_le_of_ne hx₀b hx₀_ne_b

  have hge : HeatOp u D (t₀, x₀) ≥ 0 :=
    interior_max_HeatOp_nonneg hT hab hD u hu_cont t₀ x₀ ht₀_pos ht₀T hx₀a hx₀b' hp₀_le

  exact absurd hge (not_le.mpr (hL_neg t₀ x₀ ht₀_pos ht₀T hx₀a hx₀b'))

/-- **Theorem 1.1 (Weak Maximum Principle).** Let $w \in C^2(Q_T) \cap C(\overline{Q_T})$ be a
solution to the heat equation $w_t - D \Delta w = f$ with $f \le 0$. Then $w$ attains its
maximum on $\overline{Q_T}$ on the parabolic boundary $\partial_p Q_T$, i.e.
$w(p) \le \sup_{\partial_p Q_T} w$ for every $p \in \overline{Q_T}$. -/
theorem weak_maximum_principle
    {T a b D : ℝ} (hT : 0 < T) (hab : a < b) (hD : 0 < D)
    (w : ℝ × ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w (SpacetimeCylinder T a b))
    (hw_cont : ContinuousOn w (ClosedCylinder T a b))
    (hL : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp w D (t, x) ≤ 0)
    (hw_diff_t : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      DifferentiableAt ℝ (fun t' => w (t', x)) t) :
    ∀ p ∈ ClosedCylinder T a b,
      w p ≤ sSup (w '' ParabolicBoundary T a b) := by
  intro p hp

  suffices h : ∀ ε > (0 : ℝ), w p ≤ sSup (w '' ParabolicBoundary T a b) + ε * T by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < w p - sSup (w '' ParabolicBoundary T a b) := sub_pos.mpr hlt
    have := h ((w p - sSup (w '' ParabolicBoundary T a b)) / (2 * T))
      (div_pos hpos (mul_pos two_pos hT))
    have hineq : (w p - sSup (w '' ParabolicBoundary T a b)) / (2 * T) * T =
        (w p - sSup (w '' ParabolicBoundary T a b)) / 2 := by field_simp
    linarith
  intro ε hε
  set u := fun q : ℝ × ℝ => w q - ε * q.1 with hu_def
  have hu_cont : ContinuousOn u (ClosedCylinder T a b) :=
    hw_cont.sub (continuousOn_const.mul continuous_fst.continuousOn)

  have hL_u_neg : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp u D (t, x) < 0 := by
    intro t' x' ht' ht'T hx'a hx'b
    rw [hu_def, HeatOp_sub_eps_time w D ε (t', x') (hw_diff_t t' x' ht' ht'T hx'a hx'b)]
    linarith [hL t' x' ht' ht'T hx'a hx'b]

  have h_strict := strict_max_on_ParabolicBoundary hT hab hD u hu_cont hL_u_neg
  have hu_p := h_strict p hp

  have hw_eq : w p = u p + ε * p.1 := by simp [hu_def]

  have hp1 : p.1 ≤ T := by
    simp only [ClosedCylinder, mem_prod, mem_Icc] at hp; exact hp.1.2

  have hbdd_w : BddAbove (w '' ParabolicBoundary T a b) :=
    (ClosedCylinder_isCompact.image_of_continuousOn hw_cont).bddAbove.mono
      (image_mono (ParabolicBoundary_subset_ClosedCylinder hT hab.le))
  have hu_le_w : sSup (u '' ParabolicBoundary T a b) ≤
      sSup (w '' ParabolicBoundary T a b) := by
    apply csSup_le
    · exact (ParabolicBoundary_nonempty hab.le).image u
    · intro y hy
      obtain ⟨q, hq_mem, rfl⟩ := hy
      simp only [hu_def]
      have hq1_nonneg : (0 : ℝ) ≤ q.1 := by
        have := ParabolicBoundary_subset_ClosedCylinder hT hab.le hq_mem
        simp only [ClosedCylinder, mem_prod, mem_Icc] at this
        exact this.1.1
      have : 0 ≤ ε * q.1 := mul_nonneg hε.le hq1_nonneg
      linarith [le_csSup hbdd_w (mem_image_of_mem w hq_mem)]

  calc w p = u p + ε * p.1 := hw_eq
  _ ≤ sSup (u '' ParabolicBoundary T a b) + ε * T := by
      have : ε * p.1 ≤ ε * T := mul_le_mul_of_nonneg_left hp1 hε.le
      linarith [hu_p]
  _ ≤ sSup (w '' ParabolicBoundary T a b) + ε * T := by linarith [hu_le_w]

/-- **Comparison principle.** If $v, w$ are $C^2$ functions on the closed cylinder with
$L_D v \ge L_D w$ in the interior and $v \ge w$ on the parabolic boundary, then $v \ge w$
on all of $\overline{Q_T}$. -/
theorem comparison_principle
    {T a b D : ℝ} (hT : 0 < T) (hab : a < b) (hD : 0 < D)
    (v w : ℝ × ℝ → ℝ)
    (hv_smooth : ContDiff ℝ 2 v)
    (hw_smooth : ContDiff ℝ 2 w)
    (hv_cont : ContinuousOn v (ClosedCylinder T a b))
    (hw_cont : ContinuousOn w (ClosedCylinder T a b))

    (hfg : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp v D (t, x) ≥ HeatOp w D (t, x))

    (hbdry : ∀ p ∈ ParabolicBoundary T a b, v p ≥ w p) :
    ∀ p ∈ ClosedCylinder T a b, v p ≥ w p := by

  set u := fun p : ℝ × ℝ => w p - v p with hu_def
  have hu_smooth : ContDiff ℝ 2 u := hw_smooth.sub hv_smooth
  have hu_cont : ContinuousOn u (ClosedCylinder T a b) := hw_cont.sub hv_cont

  have hL_u : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp u D (t, x) ≤ 0 := by
    intro t x ht htT hxa hxb
    rw [hu_def, HeatOp_sub w v hw_smooth hv_smooth]
    linarith [hfg t x ht htT hxa hxb]

  have h_wmp := weak_maximum_principle hT hab hD u (hu_smooth.contDiffOn) hu_cont hL_u
    (fun t x ht htT hxa hxb => (hu_smooth.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt)

  have h_sup_le : sSup (u '' ParabolicBoundary T a b) ≤ 0 := by
    apply csSup_le
    · exact (ParabolicBoundary_nonempty hab.le).image u
    · intro y hy
      obtain ⟨q, hq_mem, rfl⟩ := hy
      simp only [hu_def]
      linarith [hbdry q hq_mem]

  intro p hp
  have := h_wmp p hp
  simp only [hu_def] at this
  linarith

/-- **Stability estimate.** If $|L_D w - L_D v| \le M$ on $\overline{Q_T}$, then
$\max_{\overline{Q_T}} |v - w| \le \max_{\partial_p Q_T} |v - w| + T \cdot M$,
giving stability of the solution with respect to the right-hand side. -/
theorem stability_estimate
    {T a b D : ℝ} (hT : 0 < T) (hab : a < b) (hD : 0 < D)
    (v w : ℝ × ℝ → ℝ)
    (hv_smooth : ContDiff ℝ 2 v)
    (hw_smooth : ContDiff ℝ 2 w)
    (hv_cont : ContinuousOn v (ClosedCylinder T a b))
    (hw_cont : ContinuousOn w (ClosedCylinder T a b))
    (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ p ∈ ClosedCylinder T a b,
      |HeatOp w D p - HeatOp v D p| ≤ M) :
    ∀ p ∈ ClosedCylinder T a b,
      |v p - w p| ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) + T * M := by

  have hq1_nonneg : ∀ q ∈ ParabolicBoundary T a b, (0 : ℝ) ≤ q.1 := by
    intro q hq
    simp only [ParabolicBoundary, mem_union, mem_prod, mem_singleton_iff,
      mem_Icc, mem_Ioc] at hq
    rcases hq with ⟨h1, _⟩ | ⟨ht, _⟩
    · linarith
    · linarith

  have hbdd_abs : BddAbove ((fun q => |v q - w q|) '' ParabolicBoundary T a b) := by
    exact (ClosedCylinder_isCompact.image_of_continuousOn
      (ContinuousOn.abs (hv_cont.sub hw_cont))).bddAbove.mono
      (image_mono (ParabolicBoundary_subset_ClosedCylinder hT hab.le))
  intro p hp
  have hp1 : p.1 ≤ T := by
    simp only [ClosedCylinder, mem_prod, mem_Icc] at hp; exact hp.1.2

  set u₁ := fun q : ℝ × ℝ => w q - v q - q.1 * M with hu₁_def
  have hu₁_smooth : ContDiff ℝ 2 u₁ := (hw_smooth.sub hv_smooth).sub (by fun_prop)
  have hu₁_cont : ContinuousOn u₁ (ClosedCylinder T a b) :=
    (hw_cont.sub hv_cont).sub (continuous_fst.continuousOn.mul continuousOn_const)
  have hL_u₁ : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp u₁ D (t, x) ≤ 0 := by
    intro t' x' ht' ht'T hx'a hx'b
    have hmem : (t', x') ∈ ClosedCylinder T a b := by
      simp [ClosedCylinder, mem_Icc, ht'.le, ht'T, hx'a.le, hx'b.le]
    rw [hu₁_def, show (fun q : ℝ × ℝ => w q - v q - q.1 * M) =
      (fun q => (fun q => w q - v q) q - q.1 * M) from rfl,
      HeatOp_sub_time_const _ (hw_smooth.sub hv_smooth),
      HeatOp_sub w v hw_smooth hv_smooth]
    have := hM (t', x') hmem
    rw [abs_le] at this; linarith
  have h1 := weak_maximum_principle hT hab hD u₁ (hu₁_smooth.contDiffOn) hu₁_cont hL_u₁
    (fun t x ht htT hxa hxb => (hu₁_smooth.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt) p hp
  have h1_le : sSup (u₁ '' ParabolicBoundary T a b) ≤
      sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) := by
    apply csSup_le ((ParabolicBoundary_nonempty hab.le).image u₁)
    intro y hy
    obtain ⟨q, hq_mem, rfl⟩ := hy
    simp only [hu₁_def]
    have hq1 : (0 : ℝ) ≤ q.1 := hq1_nonneg q hq_mem
    have : w q - v q - q.1 * M ≤ |w q - v q| := by
      linarith [le_abs_self (w q - v q), mul_nonneg hq1 hM_nonneg]
    calc w q - v q - q.1 * M ≤ |w q - v q| := this
    _ = |v q - w q| := abs_sub_comm _ _
    _ ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) :=
        le_csSup hbdd_abs (mem_image_of_mem _ hq_mem)
  have h_wv : w p - v p ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) + T * M := by
    have h_u1_bound : u₁ p ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) :=
      le_trans h1 h1_le
    simp only [hu₁_def] at h_u1_bound
    linarith [mul_le_mul_of_nonneg_right hp1 hM_nonneg]

  set u₂ := fun q : ℝ × ℝ => v q - w q - q.1 * M with hu₂_def
  have hu₂_smooth : ContDiff ℝ 2 u₂ := (hv_smooth.sub hw_smooth).sub (by fun_prop)
  have hu₂_cont : ContinuousOn u₂ (ClosedCylinder T a b) :=
    (hv_cont.sub hw_cont).sub (continuous_fst.continuousOn.mul continuousOn_const)
  have hL_u₂ : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp u₂ D (t, x) ≤ 0 := by
    intro t' x' ht' ht'T hx'a hx'b
    have hmem : (t', x') ∈ ClosedCylinder T a b := by
      simp [ClosedCylinder, mem_Icc, ht'.le, ht'T, hx'a.le, hx'b.le]
    rw [hu₂_def, show (fun q : ℝ × ℝ => v q - w q - q.1 * M) =
      (fun q => (fun q => v q - w q) q - q.1 * M) from rfl,
      HeatOp_sub_time_const _ (hv_smooth.sub hw_smooth),
      HeatOp_sub v w hv_smooth hw_smooth]
    have := hM (t', x') hmem
    rw [abs_le] at this; linarith
  have h2 := weak_maximum_principle hT hab hD u₂ (hu₂_smooth.contDiffOn) hu₂_cont hL_u₂
    (fun t x ht htT hxa hxb => (hu₂_smooth.comp (by fun_prop)).differentiable (by decide) |>.differentiableAt) p hp
  have h2_le : sSup (u₂ '' ParabolicBoundary T a b) ≤
      sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) := by
    apply csSup_le ((ParabolicBoundary_nonempty hab.le).image u₂)
    intro y hy
    obtain ⟨q, hq_mem, rfl⟩ := hy
    simp only [hu₂_def]
    have hq1 : (0 : ℝ) ≤ q.1 := hq1_nonneg q hq_mem
    calc v q - w q - q.1 * M
        ≤ |v q - w q| := by linarith [le_abs_self (v q - w q), mul_nonneg hq1 hM_nonneg]
    _ ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) :=
        le_csSup hbdd_abs (mem_image_of_mem _ hq_mem)
  have h_vw : v p - w p ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) + T * M := by
    have h_u2_bound : u₂ p ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) :=
      le_trans h2 h2_le
    simp only [hu₂_def] at h_u2_bound
    linarith [mul_le_mul_of_nonneg_right hp1 hM_nonneg]

  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Corollary 1.0.1 (Comparison Principle and Stability).** Combines the comparison principle
and the stability estimate: under appropriate $C^2$ regularity hypotheses, if $L_D v \ge L_D w$
and $v \ge w$ on $\partial_p Q_T$, then $v \ge w$ throughout $\overline{Q_T}$; and if
$|L_D w - L_D v| \le M$ on $\overline{Q_T}$, then
$\max_{\overline{Q_T}} |v - w| \le \max_{\partial_p Q_T} |v - w| + T \cdot M$. -/
theorem corollary_1_0_1
    {T a b D : ℝ} (hT : 0 < T) (hab : a < b) (hD : 0 < D)
    (v w : ℝ × ℝ → ℝ)
    (hv_smooth : ContDiff ℝ 2 v)
    (hw_smooth : ContDiff ℝ 2 w)
    (hv_cont : ContinuousOn v (ClosedCylinder T a b))
    (hw_cont : ContinuousOn w (ClosedCylinder T a b))

    (hfg : ∀ t x, 0 < t → t ≤ T → a < x → x < b →
      HeatOp v D (t, x) ≥ HeatOp w D (t, x))
    (hbdry : ∀ p ∈ ParabolicBoundary T a b, v p ≥ w p)

    (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ p ∈ ClosedCylinder T a b,
      |HeatOp w D p - HeatOp v D p| ≤ M) :
    (∀ p ∈ ClosedCylinder T a b, v p ≥ w p) ∧
    (∀ p ∈ ClosedCylinder T a b,
      |v p - w p| ≤ sSup ((fun q => |v q - w q|) '' ParabolicBoundary T a b) + T * M) :=
  ⟨comparison_principle hT hab hD v w hv_smooth hw_smooth hv_cont hw_cont hfg hbdry,
   stability_estimate hT hab hD v w hv_smooth hw_smooth hv_cont hw_cont M hM_nonneg hM⟩

end WeakMaximumPrinciple
