/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory intervalIntegral Real

namespace DegreeTheory

noncomputable def det2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

def OnUnitCircle (f : ℝ → Fin 2 → ℝ) : Prop := ∀ t, (f t 0) ^ 2 + (f t 1) ^ 2 = 1

noncomputable def angularVelocity (f : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ := det2 (f t) (deriv f t)

def IsAngleFunction (f : ℝ → Fin 2 → ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ θ ∧ ∀ t, f t 0 = cos (θ t) ∧ f t 1 = sin (θ t)

theorem exists_angle_of_unit_circle (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ₀ : ℝ, a = cos θ₀ ∧ b = sin θ₀ := by
  have habs : a ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> nlinarith [sq_nonneg b]
  have hsin_nn : 0 ≤ sin (arccos a) :=
    sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg a) (arccos_le_pi a)
  have hsin_sq : sin (arccos a) ^ 2 = b ^ 2 := by
    have := sin_sq (arccos a); rw [cos_arccos habs.1 habs.2] at this; linarith
  by_cases hb : b ≥ 0
  · exact ⟨arccos a, (cos_arccos habs.1 habs.2).symm,
      by nlinarith [sq_nonneg (sin (arccos a) - b)]⟩
  · exact ⟨-(arccos a), by rw [cos_neg]; exact (cos_arccos habs.1 habs.2).symm,
      by rw [sin_neg]; nlinarith [sq_nonneg (sin (arccos a) + b), not_le.mp hb]⟩

theorem smooth_angular_velocity (f : ℝ → Fin 2 → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (angularVelocity f) := by
  have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp hf
  have hfi' : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => deriv (fun s => f s i) t) := by
    intro i; apply AnalyticOn.contDiff; intro x _
    exact ((hfi i).contDiffAt (x := x)).analyticAt.deriv.analyticWithinAt
  have heq : angularVelocity f = fun t =>
      (fun t => f t 0) t * (fun t => deriv (fun s => f s 1) t) t -
      (fun t => f t 1) t * (fun t => deriv (fun s => f s 0) t) t := by
    ext t; simp only [angularVelocity, det2]
    have hd := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
    congr 1 <;> congr 1 <;> exact congr_fun hd _
  rw [heq]
  exact ((hfi 0).mul (hfi' 1)).sub ((hfi 1).mul (hfi' 0))



theorem ode_uniqueness (f : ℝ → Fin 2 → ℝ) (θ : ℝ → ℝ)
    (hf : ContDiff ℝ ⊤ f) (hcirc : OnUnitCircle f) (hθ : ContDiff ℝ ⊤ θ)
    (hderiv : ∀ t, HasDerivAt θ (angularVelocity f t) t)
    (hinit0 : f 0 0 = cos (θ 0)) (hinit1 : f 0 1 = sin (θ 0)) :
    ∀ t, f t 0 = cos (θ t) ∧ f t 1 = sin (θ t) := by
  set g : ℝ → ℝ := fun t => f t 0 * cos (θ t) + f t 1 * sin (θ t)
  have hf0 : ContDiff ℝ ⊤ (fun t => f t 0) := (contDiff_apply ℝ ℝ 0).comp hf
  have hf1 : ContDiff ℝ ⊤ (fun t => f t 1) := (contDiff_apply ℝ ℝ 1).comp hf
  have g_diff : Differentiable ℝ g :=
    (hf0.differentiable (by norm_num)).mul (hθ.cos.differentiable (by norm_num)) |>.add
      ((hf1.differentiable (by norm_num)).mul (hθ.sin.differentiable (by norm_num)))
  have hcirc_deriv : ∀ t, f t 0 * deriv (fun s => f s 0) t +
      f t 1 * deriv (fun s => f s 1) t = 0 := by
    intro t
    have hd : HasDerivAt (fun s => (f s 0) ^ 2 + (f s 1) ^ 2) 0 t := by
      have : (fun s => (f s 0) ^ 2 + (f s 1) ^ 2) = fun _ => (1 : ℝ) := by ext s; exact hcirc s
      rw [this]; exact hasDerivAt_const t 1
    have hd2 : HasDerivAt (fun s => (f s 0) ^ 2 + (f s 1) ^ 2)
      (2 * f t 0 * deriv (fun s => f s 0) t + 2 * f t 1 * deriv (fun s => f s 1) t) t := by
      have h0 := ((hf0.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
      have h1 := ((hf1.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
      convert (h0.pow 2).add (h1.pow 2) using 1; ring
    linarith [hd.unique hd2]
  have g_deriv_zero : ∀ t, deriv g t = 0 := by
    intro t
    have ha := ((hf0.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
    have hb := ((hf1.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
    have hθt := hderiv t
    have hg_deriv : HasDerivAt g
      (deriv (fun s => f s 0) t * cos (θ t) - f t 0 * sin (θ t) * angularVelocity f t +
       deriv (fun s => f s 1) t * sin (θ t) + f t 1 * cos (θ t) * angularVelocity f t) t := by
      convert ha.mul hθt.cos |>.add (hb.mul hθt.sin) using 1; ring
    rw [hg_deriv.deriv]
    have hd_eq : ∀ i : Fin 2, deriv f t i = deriv (fun s => f s i) t :=
      fun i => congr_fun (deriv_pi (fun i => ((contDiff_apply ℝ ℝ i).comp hf |>.differentiable
        (by norm_num)).differentiableAt (x := t))) i
    have hω : angularVelocity f t = f t 0 * deriv (fun s => f s 1) t -
        f t 1 * deriv (fun s => f s 0) t := by
      simp only [angularVelocity, det2]; rw [hd_eq 0, hd_eq 1]
    rw [hω]
    have hunit := hcirc_deriv t
    have huc := hcirc t
    have key : deriv (fun s => f s 0) t * cos (θ t) -
        f t 0 * sin (θ t) * (f t 0 * deriv (fun s => f s 1) t -
          f t 1 * deriv (fun s => f s 0) t) +
        deriv (fun s => f s 1) t * sin (θ t) +
        f t 1 * cos (θ t) * (f t 0 * deriv (fun s => f s 1) t -
          f t 1 * deriv (fun s => f s 0) t) =
      (f t 0 * deriv (fun s => f s 0) t + f t 1 * deriv (fun s => f s 1) t) *
        (f t 0 * cos (θ t) + f t 1 * sin (θ t)) +
      (deriv (fun s => f s 0) t * cos (θ t) + deriv (fun s => f s 1) t * sin (θ t)) *
        (1 - (f t 0)^2 - (f t 1)^2) := by ring
    linarith [key, mul_eq_zero_of_left hunit (f t 0 * cos (θ t) + f t 1 * sin (θ t)),
              mul_eq_zero_of_right
                (deriv (fun s => f s 0) t * cos (θ t) + deriv (fun s => f s 1) t * sin (θ t))
                (show (1 - (f t 0)^2 - (f t 1)^2) = 0 by linarith)]
  have g_const : ∀ t, g t = g 0 :=
    fun t => is_const_of_deriv_eq_zero g_diff g_deriv_zero 0 t |>.symm
  have g_init : g 0 = 1 := by
    simp only [g]; rw [hinit0, hinit1]
    nlinarith [sin_sq_add_cos_sq (θ 0)]
  intro t
  have hgt : f t 0 * cos (θ t) + f t 1 * sin (θ t) = 1 := by
    have := g_const t; simp only [g] at this; linarith [g_init]
  have huc := hcirc t
  have hcs : cos (θ t) ^ 2 + sin (θ t) ^ 2 = 1 := by linarith [sin_sq_add_cos_sq (θ t)]
  have h : (f t 0 - cos (θ t)) ^ 2 + (f t 1 - sin (θ t)) ^ 2 = 0 := by nlinarith
  exact ⟨by nlinarith [sq_nonneg (f t 0 - cos (θ t)), sq_nonneg (f t 1 - sin (θ t))],
         by nlinarith [sq_nonneg (f t 0 - cos (θ t)), sq_nonneg (f t 1 - sin (θ t))]⟩


theorem angle_function_unique (f : ℝ → Fin 2 → ℝ) (θ₁ θ₂ : ℝ → ℝ)
    (h1 : IsAngleFunction f θ₁) (h2 : IsAngleFunction f θ₂) :
    ∃ k : ℤ, ∀ t, θ₂ t - θ₁ t = 2 * π * k := by

  obtain ⟨hθ1_smooth, hθ1_eq⟩ := h1
  obtain ⟨hθ2_smooth, hθ2_eq⟩ := h2

  have hdiff_smooth : ContDiff ℝ ⊤ (fun t => θ₂ t - θ₁ t) := hθ2_smooth.sub hθ1_smooth

  have hcos_eq_one : ∀ t, cos (θ₂ t - θ₁ t) = 1 := by
    intro t
    rw [cos_sub]
    have ⟨h1a, h1b⟩ := hθ1_eq t
    have ⟨h2a, h2b⟩ := hθ2_eq t
    rw [← h1a, ← h1b, ← h2a, ← h2b]
    have hcs := sin_sq_add_cos_sq (θ₁ t)
    have : f t 0 * f t 0 + f t 1 * f t 1 = sin (θ₁ t) ^ 2 + cos (θ₁ t) ^ 2 := by
      rw [← h1a, ← h1b]; ring
    linarith

  have hint : ∀ t, ∃ k : ℤ, (θ₂ t - θ₁ t) = ↑k * (2 * π) := by
    intro t
    obtain ⟨k, hk⟩ := (cos_eq_one_iff (θ₂ t - θ₁ t)).mp (hcos_eq_one t)
    exact ⟨k, hk.symm⟩


  have hderiv_eq : ∀ t, deriv (fun s => θ₂ s - θ₁ s) t = 0 := by
    intro t

    have hθ1_diff : DifferentiableAt ℝ θ₁ t :=
      (hθ1_smooth.differentiable (by norm_num)).differentiableAt
    have hθ2_diff : DifferentiableAt ℝ θ₂ t :=
      (hθ2_smooth.differentiable (by norm_num)).differentiableAt
    have : deriv (fun s => θ₂ s - θ₁ s) t = deriv θ₂ t - deriv θ₁ t :=
      deriv_sub hθ2_diff hθ1_diff
    rw [this]


    have hf0_eq1 : (fun s => f s 0) = (fun s => cos (θ₁ s)) := funext (fun s => (hθ1_eq s).1)
    have hf1_eq1 : (fun s => f s 1) = (fun s => sin (θ₁ s)) := funext (fun s => (hθ1_eq s).2)
    have hd_θ1 := hθ1_diff.hasDerivAt
    have hd0_1 : HasDerivAt (fun s => f s 0) (-sin (θ₁ t) * deriv θ₁ t) t := by
      rw [hf0_eq1]; exact hd_θ1.cos
    have hd1_1 : HasDerivAt (fun s => f s 1) (cos (θ₁ t) * deriv θ₁ t) t := by
      rw [hf1_eq1]; exact hd_θ1.sin
    have hf0_eq2 : (fun s => f s 0) = (fun s => cos (θ₂ s)) := funext (fun s => (hθ2_eq s).1)
    have hf1_eq2 : (fun s => f s 1) = (fun s => sin (θ₂ s)) := funext (fun s => (hθ2_eq s).2)
    have hd_θ2 := hθ2_diff.hasDerivAt
    have hd0_2 : HasDerivAt (fun s => f s 0) (-sin (θ₂ t) * deriv θ₂ t) t := by
      rw [hf0_eq2]; exact hd_θ2.cos
    have hd1_2 : HasDerivAt (fun s => f s 1) (cos (θ₂ t) * deriv θ₂ t) t := by
      rw [hf1_eq2]; exact hd_θ2.sin

    have heq0 : -sin (θ₁ t) * deriv θ₁ t = -sin (θ₂ t) * deriv θ₂ t :=
      hd0_1.unique hd0_2

    have heq1 : cos (θ₁ t) * deriv θ₁ t = cos (θ₂ t) * deriv θ₂ t :=
      hd1_1.unique hd1_2

    have hceq : cos (θ₁ t) = cos (θ₂ t) := by
      rw [← (hθ1_eq t).1, ← (hθ2_eq t).1]
    have hseq : sin (θ₁ t) = sin (θ₂ t) := by
      rw [← (hθ1_eq t).2, ← (hθ2_eq t).2]


    have h_eq_deriv : deriv θ₂ t = deriv θ₁ t := by
      have h1 : cos (θ₁ t) * deriv θ₁ t = cos (θ₁ t) * deriv θ₂ t := by
        rw [heq1, hceq]
      have h2 : sin (θ₁ t) * deriv θ₁ t = sin (θ₁ t) * deriv θ₂ t := by
        have heq0' := heq0
        rw [← hseq] at heq0'
        linarith
      have hc : cos (θ₁ t) * (deriv θ₁ t - deriv θ₂ t) = 0 := by linarith
      have hs : sin (θ₁ t) * (deriv θ₁ t - deriv θ₂ t) = 0 := by linarith
      have hkey : (deriv θ₁ t - deriv θ₂ t) = 0 := by
        have hsum : cos (θ₁ t) ^ 2 + sin (θ₁ t) ^ 2 = 1 := by
          linarith [sin_sq_add_cos_sq (θ₁ t)]
        nlinarith [sq_abs (cos (θ₁ t)), sq_abs (sin (θ₁ t)),
                   sq_abs (deriv θ₁ t - deriv θ₂ t),
                   mul_self_nonneg (cos (θ₁ t) * (deriv θ₁ t - deriv θ₂ t)),
                   mul_self_nonneg (sin (θ₁ t) * (deriv θ₁ t - deriv θ₂ t)),
                   hc, hs, hsum]
      linarith
    linarith

  have hconst : ∀ t, (θ₂ t - θ₁ t) = (θ₂ 0 - θ₁ 0) := by
    intro t
    exact is_const_of_deriv_eq_zero (hdiff_smooth.differentiable (by norm_num)) hderiv_eq 0 t |>.symm

  obtain ⟨k, hk⟩ := hint 0
  refine ⟨k, fun t => ?_⟩
  rw [hconst t, hk]; ring


noncomputable def degreeReal (f : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..T, det2 (f t) (deriv f t)







end DegreeTheory
