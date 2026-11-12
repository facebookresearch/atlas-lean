/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace PlaneCurves

def det2 (v w : EuclideanSpace ℝ (Fin 2)) : ℝ := v 0 * w 1 - v 1 * w 0

theorem det2_antisymm (v w : EuclideanSpace ℝ (Fin 2)) : det2 v w = -det2 w v := by
  simp only [det2]; ring

theorem det2_self (v : EuclideanSpace ℝ (Fin 2)) : det2 v v = 0 := by
  simp only [det2]; ring

structure IsRegularCurve (c : ℝ → EuclideanSpace ℝ (Fin 2)) (S : Set ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  deriv_ne_zero : ∀ t ∈ S, deriv c t ≠ 0

def curvature (c : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  det2 (deriv c t) (deriv (deriv c) t) / ‖deriv c t‖ ^ 3

def J (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![- v 1, v 0]

@[simp]
lemma J_apply_zero (v : EuclideanSpace ℝ (Fin 2)) : J v 0 = - v 1 := by
  simp [J, EuclideanSpace.equiv]

@[simp]
lemma J_apply_one (v : EuclideanSpace ℝ (Fin 2)) : J v 1 = v 0 := by
  simp [J, EuclideanSpace.equiv]

lemma inner_eq_coord (v w : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ v w = v 0 * w 0 + v 1 * w 1 := by
  simp only [Fin.sum_univ_two, inner, Inner.inner,
    RCLike.re_to_real, starRingEnd_apply, star_trivial, mul_comm]

theorem deriv_eq_det2_smul_J_of_norm_eq_one (f : ℝ → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ⊤ f)
    (hunit : ∀ t, ‖f t‖ = 1) (t : ℝ) :
    deriv f t = det2 (f t) (deriv f t) • J (f t) := by

  have horth : @inner ℝ _ _ (f t) (deriv f t) = 0 := by
    have hconst : (fun s => ‖f s‖ ^ 2) = (fun _ => (1 : ℝ)) := by
      ext s; rw [hunit s]; norm_num
    have hdiff := (hf.differentiable (by simp)).differentiableAt (x := t)
    have hd := hdiff.hasDerivAt.norm_sq
    have hd2 : HasDerivAt (fun s => ‖f s‖ ^ 2) 0 t := by
      rw [hconst]; exact hasDerivAt_const t 1
    linarith [hd.unique hd2]

  have hinner : f t 0 * (deriv f t) 0 + f t 1 * (deriv f t) 1 = 0 := by
    rw [← inner_eq_coord]; exact horth
  have hnorm : (f t 0) ^ 2 + (f t 1) ^ 2 = 1 := by
    have := EuclideanSpace.real_norm_sq_eq (f t)
    rw [Fin.sum_univ_two] at this
    nlinarith [sq_nonneg (f t 0), sq_nonneg (f t 1), hunit t]

  ext i; fin_cases i
  ·
    show (deriv f t) 0 = (f t 0 * (deriv f t) 1 - f t 1 * (deriv f t) 0) * (- f t 1)
    have key : f t 0 * (f t 0 * (deriv f t) 0 + f t 1 * (deriv f t) 1) =
      (deriv f t) 0 * (f t 0) ^ 2 + f t 0 * f t 1 * (deriv f t) 1 := by ring
    rw [hinner, mul_zero] at key
    have h3 : (deriv f t) 0 * ((f t 0) ^ 2 + (f t 1) ^ 2) = (deriv f t) 0 := by
      rw [hnorm]; ring
    linarith
  ·
    show (deriv f t) 1 = (f t 0 * (deriv f t) 1 - f t 1 * (deriv f t) 0) * f t 0
    have key : f t 1 * (f t 0 * (deriv f t) 0 + f t 1 * (deriv f t) 1) =
      f t 0 * f t 1 * (deriv f t) 0 + (deriv f t) 1 * (f t 1) ^ 2 := by ring
    rw [hinner, mul_zero] at key
    have h3 : (deriv f t) 1 * ((f t 0) ^ 2 + (f t 1) ^ 2) = (deriv f t) 1 := by
      rw [hnorm]; ring
    linarith

lemma J_smul (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : J (a • v) = a • J v := by
  ext i; fin_cases i <;> simp [smul_eq_mul]

lemma det2_smul_left (a : ℝ) (v w : EuclideanSpace ℝ (Fin 2)) :
    det2 (a • v) w = a * det2 v w := by
  simp [det2, smul_eq_mul]; ring

lemma det2_add_right (v w₁ w₂ : EuclideanSpace ℝ (Fin 2)) :
    det2 v (w₁ + w₂) = det2 v w₁ + det2 v w₂ := by
  simp [det2]; ring

lemma det2_smul_right (a : ℝ) (v w : EuclideanSpace ℝ (Fin 2)) :
    det2 v (a • w) = a * det2 v w := by
  simp [det2, smul_eq_mul]; ring

lemma det2_unit_tangent_deriv (v w : EuclideanSpace ℝ (Fin 2)) (α : ℝ) (hv : ‖v‖ ≠ 0) :
    det2 (‖v‖⁻¹ • v) (‖v‖⁻¹ • w + α • v) * ‖v‖⁻¹ = det2 v w / ‖v‖ ^ 3 := by
  rw [det2_smul_left, det2_add_right, det2_smul_right, det2_smul_right, det2_self,
    mul_zero, add_zero]
  field_simp

theorem frenet_equation (c : ℝ → EuclideanSpace ℝ (Fin 2)) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0) (t : ℝ) :
    deriv (fun s => (‖deriv c s‖⁻¹) • deriv c s) t =
    curvature c t • J (deriv c t) := by

  have hdc : ContDiff ℝ ⊤ (deriv c) := by
    have : ContDiff ℝ (⊤ + 1) c := by simp [WithTop.top_add]; exact hc
    exact this.deriv'
  have hnorm_ne : ∀ s, ‖deriv c s‖ ≠ 0 := fun s => norm_ne_zero_iff.mpr (hreg s)

  have hT : ContDiff ℝ ⊤ (fun s => (‖deriv c s‖⁻¹) • deriv c s) :=
    ((ContDiff.norm (𝕜 := ℝ) hdc (fun s => hreg s)).inv hnorm_ne).smul hdc

  have hTunit : ∀ s, ‖(‖deriv c s‖⁻¹) • deriv c s‖ = 1 := by
    intro s; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hnorm_ne s)]

  have hlemma := deriv_eq_det2_smul_J_of_norm_eq_one
    (fun s => (‖deriv c s‖⁻¹) • deriv c s) hT hTunit t

  rw [hlemma, J_smul, smul_smul]

  congr 1


  have hdiff_inv : DifferentiableAt ℝ (fun s => (‖deriv c s‖⁻¹ : ℝ)) t :=
    ((ContDiff.norm (𝕜 := ℝ) hdc (fun s => hreg s)).inv hnorm_ne).differentiable
      WithTop.top_ne_zero |>.differentiableAt
  have hdiff_dc : DifferentiableAt ℝ (deriv c) t :=
    (hdc.differentiable WithTop.top_ne_zero).differentiableAt
  have hderiv_T : deriv (fun s => (‖deriv c s‖⁻¹) • deriv c s) t =
    (‖deriv c t‖⁻¹) • deriv (deriv c) t +
    deriv (fun s => ‖deriv c s‖⁻¹) t • deriv c t :=
    deriv_smul hdiff_inv hdiff_dc

  rw [hderiv_T]
  exact det2_unit_tangent_deriv (deriv c t) (deriv (deriv c) t)
    (deriv (fun s => ‖deriv c s‖⁻¹) t) (hnorm_ne t)

lemma J_J (v : EuclideanSpace ℝ (Fin 2)) : J (J v) = -v := by
  ext i; fin_cases i <;> simp

lemma norm_J (v : EuclideanSpace ℝ (Fin 2)) : ‖J v‖ = ‖v‖ := by
  have hJv : ‖J v‖ ^ 2 = (J v 0) ^ 2 + (J v 1) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq (J v); rw [Fin.sum_univ_two] at h; exact h
  have hv : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq v; rw [Fin.sum_univ_two] at h; exact h
  have heq : ‖J v‖ ^ 2 = ‖v‖ ^ 2 := by rw [hJv, hv]; simp; ring
  nlinarith [norm_nonneg (J v), norm_nonneg v]

lemma J_add (v w : EuclideanSpace ℝ (Fin 2)) : J (v + w) = J v + J w := by
  ext i; fin_cases i <;> simp; ring

def JLinearMap : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := J
  map_add' := J_add
  map_smul' := J_smul

def JContinuous : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap JLinearMap

lemma J_hasDerivAt (f : ℝ → EuclideanSpace ℝ (Fin 2)) (f' : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (hf : HasDerivAt f f' t) : HasDerivAt (fun s => J (f s)) (J f') t :=
  JContinuous.hasFDerivAt.comp_hasDerivAt t hf

theorem constant_curvature_is_circle (c : ℝ → EuclideanSpace ℝ (Fin 2)) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0) (R : ℝ) (hR : R ≠ 0)
    (hκ : ∀ t, curvature c t = R⁻¹) :
    ∃ (center : EuclideanSpace ℝ (Fin 2)), ∀ t, ‖c t - center‖ = |R| := by

  set T : ℝ → EuclideanSpace ℝ (Fin 2) := fun s => (‖deriv c s‖⁻¹) • deriv c s

  set m : ℝ → EuclideanSpace ℝ (Fin 2) := fun s => c s + R • J (T s)

  have hdc : ContDiff ℝ ⊤ (deriv c) := by
    have h : ContDiff ℝ (⊤ + 1) c := by simp [WithTop.top_add]; exact hc
    exact h.deriv'
  have hnorm_ne : ∀ s, ‖deriv c s‖ ≠ 0 := fun s => norm_ne_zero_iff.mpr (hreg s)
  have hT_smooth : ContDiff ℝ ⊤ T :=
    ((ContDiff.norm (𝕜 := ℝ) hdc (fun s => hreg s)).inv hnorm_ne).smul hdc
  have hTunit : ∀ s, ‖T s‖ = 1 := by
    intro s; show ‖(‖deriv c s‖⁻¹) • deriv c s‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hnorm_ne s)]
  have hJT_smooth : ContDiff ℝ ⊤ (fun s => J (T s)) := JContinuous.contDiff.comp hT_smooth
  have hm_smooth : ContDiff ℝ ⊤ m := hc.add (ContDiff.const_smul R hJT_smooth)
  have hm_diff : Differentiable ℝ m := hm_smooth.differentiable WithTop.top_ne_zero

  have hm_deriv_zero : ∀ s, deriv m s = 0 := by
    intro s
    have hT_diff : DifferentiableAt ℝ T s :=
      hT_smooth.differentiable WithTop.top_ne_zero |>.differentiableAt
    have hc_hd : HasDerivAt c (deriv c s) s :=
      (hc.differentiable WithTop.top_ne_zero).differentiableAt.hasDerivAt
    have hJT_hd : HasDerivAt (fun u => J (T u)) (J (deriv T s)) s :=
      J_hasDerivAt T (deriv T s) s hT_diff.hasDerivAt
    have hRJT_hd : HasDerivAt (fun u => R • J (T u)) (R • J (deriv T s)) s :=
      hJT_hd.const_smul R
    have hm_hd : HasDerivAt m (deriv c s + R • J (deriv T s)) s :=
      hc_hd.add hRJT_hd
    rw [hm_hd.deriv]

    have hFrenet_s : deriv T s = curvature c s • J (deriv c s) :=
      frenet_equation c hc hreg s

    rw [hFrenet_s, hκ s, J_smul, J_J]
    simp only [smul_neg, smul_smul, mul_inv_cancel₀ hR, one_smul, add_neg_cancel]

  have hm_const : ∀ s, m s = m 0 := fun s =>
    is_const_of_deriv_eq_zero hm_diff hm_deriv_zero s 0

  refine ⟨m 0, fun t => ?_⟩
  have heq : c t - m 0 = -(R • J (T t)) := by
    have h2 : c t + R • J (T t) = m 0 := hm_const t
    have h3 : c t - m 0 = c t - (c t + R • J (T t)) := by rw [h2]
    rw [h3]; abel
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, norm_J, hTunit, mul_one]

open scoped Gradient

abbrev R2 := EuclideanSpace ℝ (Fin 2)

def hessianVec (F : R2 → ℝ) (x v : R2) : R2 :=
  fderiv ℝ (fun y => gradient F y) x v

lemma det2_J_eq_neg_inner (v w : EuclideanSpace ℝ (Fin 2)) :
    det2 (J v) w = -@inner ℝ _ _ v w := by
  simp only [det2, J_apply_zero, J_apply_one, inner_eq_coord]
  ring

lemma inner_J_eq_det2 (v w : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (J v) w = det2 v w := by
  simp only [inner_eq_coord, J_apply_zero, J_apply_one, det2]
  ring

theorem orthog_proportional_J (v w : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (horthog : @inner ℝ _ _ v w = 0) :
    w = (det2 v w / ‖v‖ ^ 2) • J v := by
  have hinner : v 0 * w 0 + v 1 * w 1 = 0 := by rw [← inner_eq_coord]; exact horthog
  have hnorm_sq : v 0 ^ 2 + v 1 ^ 2 = ‖v‖ ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    rw [Fin.sum_univ_two] at h; linarith [sq_abs (v 0), sq_abs (v 1)]
  have hne : (‖v‖ : ℝ) ^ 2 ≠ 0 := by
    rw [← hnorm_sq]
    intro h
    have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hv; ext i; fin_cases i <;> simp_all
  ext i; fin_cases i
  · show w 0 = (det2 v w / ‖v‖ ^ 2) • J v 0
    simp only [J_apply_zero, det2, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hne, ← hnorm_sq]
    have key : v 0 * (v 0 * w 0 + v 1 * w 1) = 0 := by rw [hinner]; ring
    linarith [key]
  · show w 1 = (det2 v w / ‖v‖ ^ 2) • J v 1
    simp only [J_apply_one, det2, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hne, ← hnorm_sq]
    have key : v 1 * (v 0 * w 0 + v 1 * w 1) = 0 := by rw [hinner]; ring
    linarith [key]

theorem level_set_orthogonality (F : R2 → ℝ) (c : ℝ → R2) (a : ℝ)
    (hF : ContDiff ℝ ⊤ F) (hc : ContDiff ℝ ⊤ c)
    (hlevel : ∀ t, F (c t) = a) (t : ℝ) :
    fderiv ℝ F (c t) (deriv c t) = 0 := by
  have hFc : (fun t => F (c t)) = fun _ => a := funext hlevel
  have hd_Fc : HasDerivAt (fun t => F (c t)) 0 t := by
    rw [hFc]; exact hasDerivAt_const t a
  have hFd := HasFDerivAt.comp_hasDerivAt t
    (hF.differentiable WithTop.top_ne_zero).differentiableAt.hasFDerivAt
    (hc.differentiable WithTop.top_ne_zero).differentiableAt.hasDerivAt
  linarith [hd_Fc.unique hFd]

theorem level_set_gradient_orthogonality (F : R2 → ℝ) (c : ℝ → R2) (a : ℝ)
    (hF : ContDiff ℝ ⊤ F) (hc : ContDiff ℝ ⊤ c)
    (hlevel : ∀ t, F (c t) = a) (t : ℝ) :
    @inner ℝ _ _ (gradient F (c t)) (deriv c t) = 0 := by
  rw [inner_gradient_left (hF.differentiable WithTop.top_ne_zero).differentiableAt]
  exact level_set_orthogonality F c a hF hc hlevel t

theorem second_diff_level_set (F : R2 → ℝ) (c : ℝ → R2) (a : ℝ)
    (hF : ContDiff ℝ ⊤ F) (hc : ContDiff ℝ ⊤ c)
    (hlevel : ∀ t, F (c t) = a) (t : ℝ) :
    @inner ℝ _ _ (hessianVec F (c t) (deriv c t)) (deriv c t) +
    @inner ℝ _ _ (gradient F (c t)) (deriv (deriv c) t) = 0 := by
  have hgradF : Differentiable ℝ (fun y => gradient F y) := by
    have hfderiv : ContDiff ℝ ⊤ (fderiv ℝ F) := hF.fderiv_right (by simp [WithTop.top_add])
    have heq : (fun y => gradient F y) =
        (fun y => (InnerProductSpace.toDual ℝ R2).symm (fderiv ℝ F y)) := by
      ext y; simp [gradient]
    rw [heq]
    exact ((InnerProductSpace.toDual ℝ R2).symm.toContinuousLinearEquiv.contDiff.comp
      hfderiv).differentiable WithTop.top_ne_zero
  have hdc : ContDiff ℝ ⊤ (deriv c) := by
    have : ContDiff ℝ (⊤ + 1) c := by simp [WithTop.top_add]; exact hc
    exact this.deriv'
  have hgrad_deriv : HasDerivAt (fun s => gradient F (c s))
      (hessianVec F (c t) (deriv c t)) t :=
    HasFDerivAt.comp_hasDerivAt t
      (hgradF.differentiableAt.hasFDerivAt)
      ((hc.differentiable WithTop.top_ne_zero).differentiableAt.hasDerivAt)
  have hdc_deriv : HasDerivAt (deriv c) (deriv (deriv c) t) t :=
    (hdc.differentiable WithTop.top_ne_zero).differentiableAt.hasDerivAt
  have hprod := HasDerivAt.inner (𝕜 := ℝ) hgrad_deriv hdc_deriv
  have hzero : (fun s => @inner ℝ _ _ (gradient F (c s)) (deriv c s)) = fun _ => (0 : ℝ) := by
    ext s
    rw [inner_gradient_left (hF.differentiable WithTop.top_ne_zero).differentiableAt]
    have hFc : (fun t => F (c t)) = fun _ => a := funext hlevel
    have hd_Fc : HasDerivAt (fun t => F (c t)) 0 s := by
      rw [hFc]; exact hasDerivAt_const s a
    have hFd := HasFDerivAt.comp_hasDerivAt s
      (hF.differentiable WithTop.top_ne_zero).differentiableAt.hasFDerivAt
      (hc.differentiable WithTop.top_ne_zero).differentiableAt.hasDerivAt
    linarith [hd_Fc.unique hFd]
  have hconst : HasDerivAt (fun s => @inner ℝ _ _ (gradient F (c s)) (deriv c s)) 0 t := by
    rw [hzero]; exact hasDerivAt_const t 0
  have heq := hconst.unique hprod
  linarith

theorem curvature_level_set (F : R2 → ℝ) (c : ℝ → R2) (a : ℝ) (t : ℝ)
    (hF : ContDiff ℝ ⊤ F) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0) (hlevel : ∀ t, F (c t) = a)
    (hgrad : gradient F (c t) ≠ 0)
    (hpos : det2 (gradient F (c t)) (deriv c t) > 0) :
    curvature c t = @inner ℝ _ _ (J (gradient F (c t)))
      (hessianVec F (c t) (J (gradient F (c t)))) / ‖gradient F (c t)‖ ^ 3 := by
  set g := gradient F (c t)
  set c' := deriv c t
  set c'' := deriv (deriv c) t
  set lam := det2 g c' / ‖g‖ ^ 2

  have horth : @inner ℝ _ _ g c' = 0 :=
    level_set_gradient_orthogonality F c a hF hc hlevel t
  have hprop : c' = lam • J g := orthog_proportional_J g c' hgrad horth

  have hgnorm_ne : (‖g‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hgrad
  have hgnorm_sq_ne : (‖g‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hgnorm_ne
  have hdet2_g_Jg : det2 g (J g) = ‖g‖ ^ 2 := by
    rw [← inner_J_eq_det2]
    rw [real_inner_comm]
    simp only [inner_eq_coord, J_apply_zero, J_apply_one]
    have h := EuclideanSpace.real_norm_sq_eq g
    rw [Fin.sum_univ_two] at h
    linarith [sq_abs (g 0), sq_abs (g 1)]
  have hlam_pos : lam > 0 := by
    show det2 g c' / ‖g‖ ^ 2 > 0
    exact div_pos hpos (by positivity)

  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos

  have hnorm_c' : ‖c'‖ = lam * ‖g‖ := by
    rw [hprop, norm_smul, norm_J, Real.norm_of_nonneg (le_of_lt hlam_pos)]

  have hsecond := second_diff_level_set F c a hF hc hlevel t


  have hg_c'' : @inner ℝ _ _ g c'' = -@inner ℝ _ _ (hessianVec F (c t) c') c' := by
    linarith


  have hdet_expand : det2 c' c'' = lam * det2 (J g) c'' := by
    rw [hprop, det2_smul_left]

  have hdet_J : det2 (J g) c'' = -@inner ℝ _ _ g c'' := det2_J_eq_neg_inner g c''


  have hhess_expand : @inner ℝ _ _ (hessianVec F (c t) c') c' =
      lam ^ 2 * @inner ℝ _ _ (hessianVec F (c t) (J g)) (J g) := by
    rw [hprop]
    simp only [hessianVec]
    rw [show fderiv ℝ (fun y => gradient F y) (c t) (lam • J g) =
      lam • fderiv ℝ (fun y => gradient F y) (c t) (J g) from
      (fderiv ℝ (fun y => gradient F y) (c t)).map_smul lam (J g)]
    rw [inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]; ring


  have hdet_final : det2 c' c'' =
      lam ^ 3 * @inner ℝ _ _ (J g) (hessianVec F (c t) (J g)) := by
    rw [hdet_expand, hdet_J, hg_c'', hhess_expand]
    rw [real_inner_comm (hessianVec F (c t) (J g)) (J g)]
    ring

  have hnorm_cube : ‖c'‖ ^ 3 = lam ^ 3 * ‖g‖ ^ 3 := by
    rw [hnorm_c']; ring

  unfold curvature
  rw [hdet_final, hnorm_cube]
  have hlam_cube_ne : lam ^ 3 ≠ 0 := pow_ne_zero _ hlam_ne
  field_simp

theorem curvature_level_set_neg (F : R2 → ℝ) (c : ℝ → R2) (a : ℝ) (t : ℝ)
    (hF : ContDiff ℝ ⊤ F) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0) (hlevel : ∀ t, F (c t) = a)
    (hgrad : gradient F (c t) ≠ 0)
    (h_neg : det2 (gradient F (c t)) (deriv c t) < 0) :
    -curvature c t = @inner ℝ _ _ (J (gradient F (c t)))
      (hessianVec F (c t) (J (gradient F (c t)))) / ‖gradient F (c t)‖ ^ 3 := by
  set g := gradient F (c t)
  set c' := deriv c t
  set c'' := deriv (deriv c) t
  set lam := det2 g c' / ‖g‖ ^ 2

  have horth : @inner ℝ _ _ g c' = 0 :=
    level_set_gradient_orthogonality F c a hF hc hlevel t
  have hprop : c' = lam • J g := orthog_proportional_J g c' hgrad horth

  have hgnorm_ne : (‖g‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hgrad
  have hgnorm_sq_ne : (‖g‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hgnorm_ne
  have hlam_neg : lam < 0 := by
    show det2 g c' / ‖g‖ ^ 2 < 0
    exact div_neg_of_neg_of_pos h_neg (by positivity)
  have hlam_ne : lam ≠ 0 := ne_of_lt hlam_neg

  have hnorm_c' : ‖c'‖ = -lam * ‖g‖ := by
    rw [hprop, norm_smul, norm_J, Real.norm_eq_abs, abs_of_neg hlam_neg]

  have hsecond := second_diff_level_set F c a hF hc hlevel t
  have hg_c'' : @inner ℝ _ _ g c'' = -@inner ℝ _ _ (hessianVec F (c t) c') c' := by
    linarith

  have hdet_expand : det2 c' c'' = lam * det2 (J g) c'' := by
    rw [hprop, det2_smul_left]
  have hdet_J : det2 (J g) c'' = -@inner ℝ _ _ g c'' := det2_J_eq_neg_inner g c''
  have hhess_expand : @inner ℝ _ _ (hessianVec F (c t) c') c' =
      lam ^ 2 * @inner ℝ _ _ (hessianVec F (c t) (J g)) (J g) := by
    rw [hprop]
    simp only [hessianVec]
    rw [show fderiv ℝ (fun y => gradient F y) (c t) (lam • J g) =
      lam • fderiv ℝ (fun y => gradient F y) (c t) (J g) from
      (fderiv ℝ (fun y => gradient F y) (c t)).map_smul lam (J g)]
    rw [inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]; ring
  have hdet_final : det2 c' c'' =
      lam ^ 3 * @inner ℝ _ _ (J g) (hessianVec F (c t) (J g)) := by
    rw [hdet_expand, hdet_J, hg_c'', hhess_expand]
    rw [real_inner_comm (hessianVec F (c t) (J g)) (J g)]
    ring

  have hnorm_cube : ‖c'‖ ^ 3 = (-lam) ^ 3 * ‖g‖ ^ 3 := by
    rw [hnorm_c']; ring


  unfold curvature
  rw [hdet_final, hnorm_cube]
  have hlam_cube_ne : lam ^ 3 ≠ 0 := pow_ne_zero _ hlam_ne
  have hgnorm_cube_ne : ‖g‖ ^ 3 ≠ 0 := pow_ne_zero _ hgnorm_ne
  field_simp

theorem curvature_level_set_full (F : R2 → ℝ) (c : ℝ → R2) (a : ℝ) (t : ℝ)
    (hF : ContDiff ℝ ⊤ F) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0) (hlevel : ∀ t, F (c t) = a)
    (hgrad : gradient F (c t) ≠ 0)
    (hdet_ne : det2 (gradient F (c t)) (deriv c t) ≠ 0) :
    curvature c t * ‖gradient F (c t)‖ ^ 3 * |det2 (gradient F (c t)) (deriv c t)| =
    det2 (gradient F (c t)) (deriv c t) *
      @inner ℝ _ _ (J (gradient F (c t)))
        (hessianVec F (c t) (J (gradient F (c t)))) := by
  have hgnorm_ne : (‖gradient F (c t)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hgrad
  have hgnorm_cube_ne : ‖gradient F (c t)‖ ^ 3 ≠ 0 := pow_ne_zero _ hgnorm_ne
  rcases lt_or_gt_of_ne hdet_ne with h_neg | h_pos
  · have hcurv := curvature_level_set_neg F c a t hF hc hreg hlevel hgrad h_neg
    have hκ : curvature c t * ‖gradient F (c t)‖ ^ 3 =
        -@inner ℝ _ _ (J (gradient F (c t)))
          (hessianVec F (c t) (J (gradient F (c t)))) := by
      have h := congr_arg (- · * ‖gradient F (c t)‖ ^ 3) hcurv
      simp only [neg_neg, neg_mul] at h
      rw [div_mul_cancel₀ _ hgnorm_cube_ne] at h
      linarith
    rw [abs_of_neg h_neg]
    nlinarith [hκ]
  · have hcurv := curvature_level_set F c a t hF hc hreg hlevel hgrad h_pos
    have hκ : curvature c t * ‖gradient F (c t)‖ ^ 3 =
        @inner ℝ _ _ (J (gradient F (c t)))
          (hessianVec F (c t) (J (gradient F (c t)))) := by
      have h := congr_arg (· * ‖gradient F (c t)‖ ^ 3) hcurv
      simp only at h
      rw [div_mul_cancel₀ _ hgnorm_cube_ne] at h
      linarith
    rw [abs_of_pos h_pos]
    nlinarith [hκ]

theorem curvature_reparametrization (c : ℝ → EuclideanSpace ℝ (Fin 2)) (ψ : ℝ → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hψ : ContDiff ℝ ⊤ ψ)
    (hreg : ∀ t, deriv c (ψ t) ≠ 0) (hψ' : ∀ t, deriv ψ t > 0) (t : ℝ) :
    curvature (c ∘ ψ) t = curvature c (ψ t) := by
  open scoped ContDiff in
  have hc_diff : Differentiable ℝ c := hc.differentiable (by exact WithTop.top_ne_zero)
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by exact WithTop.top_ne_zero)
  open scoped ContDiff in
  have hc'_smooth : ContDiff ℝ ⊤ (deriv c) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (⊤ + 1) c from by
      rwa [show (⊤ : WithTop ℕ∞) + 1 = ⊤ from by simp])).2.2
  open scoped ContDiff in
  have hψ'_smooth : ContDiff ℝ ⊤ (deriv ψ) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (⊤ + 1) ψ from by
      rwa [show (⊤ : WithTop ℕ∞) + 1 = ⊤ from by simp])).2.2
  have hc'_diff : Differentiable ℝ (deriv c) :=
    hc'_smooth.differentiable (by exact WithTop.top_ne_zero)
  have hψ'_diff : Differentiable ℝ (deriv ψ) :=
    hψ'_smooth.differentiable (by exact WithTop.top_ne_zero)
  have hψ'_ne : ∀ s, deriv ψ s ≠ 0 := fun s => ne_of_gt (hψ' s)
  have hderiv1 : ∀ s, deriv (c ∘ ψ) s = deriv ψ s • deriv c (ψ s) :=
    fun s => deriv.scomp s (hc_diff.differentiableAt) (hψ_diff.differentiableAt)
  have hderiv1_eq : deriv (c ∘ ψ) = fun s => deriv ψ s • deriv c (ψ s) :=
    funext hderiv1
  have hcomp_c' : Differentiable ℝ (fun u => deriv c (ψ u)) :=
    hc'_diff.comp hψ_diff
  have hderiv_c'_comp : ∀ s, deriv (fun u => deriv c (ψ u)) s =
      deriv ψ s • deriv (deriv c) (ψ s) :=
    fun s => deriv.scomp s (hc'_diff.differentiableAt) (hψ_diff.differentiableAt)
  have hderiv2 : deriv (deriv (c ∘ ψ)) t =
      deriv ψ t • (deriv ψ t • deriv (deriv c) (ψ t)) +
      deriv (deriv ψ) t • deriv c (ψ t) := by
    have heq : deriv (c ∘ ψ) = fun s => deriv ψ s • deriv c (ψ s) := hderiv1_eq
    conv_lhs => rw [heq]
    have : deriv (fun s => deriv ψ s • deriv c (ψ s)) t =
        deriv ψ t • deriv (fun u => deriv c (ψ u)) t + deriv (deriv ψ) t • deriv c (ψ t) :=
      deriv_fun_smul (hψ'_diff.differentiableAt) (hcomp_c'.differentiableAt)
    rw [this, hderiv_c'_comp t]
  unfold curvature
  rw [hderiv1 t, hderiv2]
  rw [det2_smul_left, det2_add_right, det2_smul_right, det2_smul_right, det2_smul_right,
    det2_self, mul_zero, add_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hψ' t)]
  have ha : deriv ψ t ≠ 0 := hψ'_ne t
  have hv : deriv c (ψ t) ≠ 0 := hreg t
  have hnv : ‖deriv c (ψ t)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  field_simp

lemma exists_smul_of_det2_eq_zero (u v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hdet : det2 u v = 0) : ∃ s : ℝ, u = s • v := by
  simp only [det2] at hdet
  have hv_or : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hv
    ext i; fin_cases i <;> simp [h.1, h.2]
  rcases hv_or with hv0 | hv1
  · refine ⟨u 0 / v 0, ?_⟩
    ext i; fin_cases i
    · simp [smul_eq_mul, div_mul_cancel₀ (u 0) hv0]
    · have h1 : u 0 * v 1 = u 1 * v 0 := by linarith
      show u 1 = u 0 / v 0 * v 1
      field_simp
      linarith
  · refine ⟨u 1 / v 1, ?_⟩
    ext i; fin_cases i
    · have h1 : u 0 * v 1 = u 1 * v 0 := by linarith
      show u 0 = u 1 / v 1 * v 0
      field_simp
      linarith
    · simp [smul_eq_mul, div_mul_cancel₀ (u 1) hv1]

lemma det2_sub_left (v₁ v₂ w : EuclideanSpace ℝ (Fin 2)) :
    det2 (v₁ - v₂) w = det2 v₁ w - det2 v₂ w := by
  simp [det2]; ring
theorem zero_curvature_is_line (c : ℝ → EuclideanSpace ℝ (Fin 2)) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0)
    (hzero : ∀ t, curvature c t = 0) :
    ∃ (p v : EuclideanSpace ℝ (Fin 2)), ∀ t, ∃ s : ℝ, c t = p + s • v := by

  have hdc : ContDiff ℝ ⊤ (deriv c) := by
    have : ContDiff ℝ (⊤ + 1) c := by simp [WithTop.top_add]; exact hc
    exact this.deriv'
  have hnorm_ne : ∀ s, ‖deriv c s‖ ≠ 0 := fun s => norm_ne_zero_iff.mpr (hreg s)

  have hT_deriv_zero : ∀ t, deriv (fun s => (‖deriv c s‖⁻¹) • deriv c s) t = 0 := by
    intro t
    have hfr := frenet_equation c hc hreg t
    rw [hfr, hzero t, zero_smul]

  have hT_diff : Differentiable ℝ (fun s => (‖deriv c s‖⁻¹) • deriv c s) :=
    (((ContDiff.norm (𝕜 := ℝ) hdc (fun s => hreg s)).inv hnorm_ne).smul hdc).differentiable
      WithTop.top_ne_zero

  have hT_const : ∀ t₁ t₂, (‖deriv c t₁‖⁻¹) • deriv c t₁ = (‖deriv c t₂‖⁻¹) • deriv c t₂ :=
    is_const_of_deriv_eq_zero hT_diff hT_deriv_zero

  have hprop : ∀ t, deriv c t = (‖deriv c t‖ * ‖deriv c 0‖⁻¹) • deriv c 0 := by
    intro t
    have h1 : (‖deriv c t‖⁻¹) • deriv c t = (‖deriv c 0‖⁻¹) • deriv c 0 := hT_const t 0
    calc deriv c t
        = ‖deriv c t‖ • ((‖deriv c t‖⁻¹) • deriv c t) := by
          rw [smul_smul, mul_inv_cancel₀ (hnorm_ne t), one_smul]
      _ = ‖deriv c t‖ • ((‖deriv c 0‖⁻¹) • deriv c 0) := by rw [h1]
      _ = (‖deriv c t‖ * ‖deriv c 0‖⁻¹) • deriv c 0 := by rw [smul_smul]
  have hdet_deriv : ∀ t, det2 (deriv c t) (deriv c 0) = 0 := by
    intro t; rw [hprop t, det2_smul_left, det2_self, mul_zero]


  set v₀ := deriv c 0


  have hc_diff : Differentiable ℝ c := hc.differentiable WithTop.top_ne_zero

  have hcomp_hasDerivAt : ∀ t (i : Fin 2),
      HasDerivAt (fun s => c s i) ((deriv c t) i) t := by
    intro t i
    have hct := hc_diff.differentiableAt.hasDerivAt (x := t)

    have hequiv : HasDerivAt (fun s => (EuclideanSpace.equiv (Fin 2) ℝ) (c s))
        ((EuclideanSpace.equiv (Fin 2) ℝ) (deriv c t)) t :=
      (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hct
    exact hasDerivAt_pi.mp hequiv i
  have hg_hasDerivAt : ∀ t, HasDerivAt (fun s => det2 (c s) v₀) (det2 (deriv c t) v₀) t := by
    intro t
    show HasDerivAt (fun s => (c s) 0 * v₀ 1 - (c s) 1 * v₀ 0)
      ((deriv c t) 0 * v₀ 1 - (deriv c t) 1 * v₀ 0) t
    exact ((hcomp_hasDerivAt t 0).mul_const (v₀ 1)).sub
      ((hcomp_hasDerivAt t 1).mul_const (v₀ 0))
  have hg_diff : Differentiable ℝ (fun s => det2 (c s) v₀) :=
    fun t => (hg_hasDerivAt t).differentiableAt
  have hg_deriv_zero : ∀ t, deriv (fun s => det2 (c s) v₀) t = 0 := by
    intro t
    rw [(hg_hasDerivAt t).deriv]
    exact hdet_deriv t
  have hg_const : ∀ t₁ t₂, det2 (c t₁) v₀ = det2 (c t₂) v₀ :=
    is_const_of_deriv_eq_zero hg_diff hg_deriv_zero
  have hg_zero : ∀ t, det2 (c t - c 0) v₀ = 0 := by
    intro t
    rw [det2_sub_left, sub_eq_zero]
    exact hg_const t 0

  exact ⟨c 0, v₀, fun t => by
    obtain ⟨s, hs⟩ := exists_smul_of_det2_eq_zero (c t - c 0) v₀ (hreg 0) (hg_zero t)
    exact ⟨s, by rw [show c t = s • v₀ + c 0 from sub_eq_iff_eq_add.mp hs, add_comm]⟩⟩


theorem deriv_toLp_comp {f : ℝ → Fin 2 → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => (WithLp.toLp 2 (f s) : EuclideanSpace ℝ (Fin 2))) t =
    WithLp.toLp 2 (deriv f t) := by
  have heq : (fun s => (WithLp.toLp 2 (f s) : EuclideanSpace ℝ (Fin 2))) =
      (↑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap) ∘ f := rfl
  rw [heq]
  have hL : HasFDerivAt
      (↑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap : (Fin 2 → ℝ) → _)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap (f t) :=
    ContinuousLinearMap.hasFDerivAt _
  have hda := hL.comp_hasDerivAt t hf.hasDerivAt
  rw [hda.deriv]
  rfl

theorem deriv_graph_curve (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) (t : ℝ) :
    deriv (fun s => (!₂[s, f s] : EuclideanSpace ℝ (Fin 2))) t =
    (!₂[(1 : ℝ), deriv f t] : EuclideanSpace ℝ (Fin 2)) := by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hdiff : DifferentiableAt ℝ (fun s => (![s, f s] : Fin 2 → ℝ)) t := by
    apply differentiableAt_pi.mpr
    intro i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hf_diff.differentiableAt]
  rw [show (fun s => (!₂[s, f s] : EuclideanSpace ℝ (Fin 2))) =
      (fun s => WithLp.toLp 2 (![s, f s])) from rfl]
  rw [deriv_toLp_comp hdiff]
  congr 1
  have hd : ∀ i : Fin 2, DifferentiableAt ℝ (fun s => (![s, f s] : Fin 2 → ℝ) i) t := by
    intro i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hf_diff.differentiableAt]
  rw [show (fun s => (![s, f s] : Fin 2 → ℝ)) = (fun s i => (![s, f s] : Fin 2 → ℝ) i) from rfl]
  rw [deriv_pi hd]
  ext i; fin_cases i
  · simp [Matrix.cons_val_zero]
  · simp [Matrix.cons_val_one, Matrix.cons_val_fin_one]

theorem deriv2_graph_curve (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) (t : ℝ) :
    deriv (deriv (fun s => (!₂[s, f s] : EuclideanSpace ℝ (Fin 2)))) t =
    (!₂[(0 : ℝ), deriv (deriv f) t] : EuclideanSpace ℝ (Fin 2)) := by
  have hf_deriv_smooth : ContDiff ℝ ⊤ (deriv f) := by
    have : ContDiff ℝ (⊤ + 1) f := hf.of_le le_top
    exact (contDiff_succ_iff_deriv.mp this).2.2
  have hfunext : deriv (fun s => (!₂[s, f s] : EuclideanSpace ℝ (Fin 2))) =
      (fun s => (!₂[(1 : ℝ), deriv f s] : EuclideanSpace ℝ (Fin 2))) := by
    funext s; exact deriv_graph_curve f hf s
  rw [hfunext]
  have hf'_diff : Differentiable ℝ (deriv f) := hf_deriv_smooth.differentiable (by simp)
  have hdiff2 : DifferentiableAt ℝ (fun s => (![(1 : ℝ), deriv f s] : Fin 2 → ℝ)) t := by
    apply differentiableAt_pi.mpr
    intro i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, differentiableAt_const, hf'_diff.differentiableAt]
  rw [show (fun s => (!₂[(1 : ℝ), deriv f s] : EuclideanSpace ℝ (Fin 2))) =
      (fun s => WithLp.toLp 2 (![(1 : ℝ), deriv f s])) from rfl]
  rw [deriv_toLp_comp hdiff2]
  congr 1
  have hd2 : ∀ i : Fin 2, DifferentiableAt ℝ (fun s => (![(1 : ℝ), deriv f s] : Fin 2 → ℝ) i) t := by
    intro i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, differentiableAt_const, hf'_diff.differentiableAt]
  rw [show (fun s => (![(1 : ℝ), deriv f s] : Fin 2 → ℝ)) =
      (fun s i => (![(1 : ℝ), deriv f s] : Fin 2 → ℝ) i) from rfl]
  rw [deriv_pi hd2]
  ext i; fin_cases i
  · simp [Matrix.cons_val_zero, deriv_const]
  · simp [Matrix.cons_val_one, Matrix.cons_val_fin_one]

theorem curvature_graph (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) (t : ℝ) :
    curvature (fun t => !₂[t, f t]) t =
    deriv (deriv f) t / (1 + deriv f t ^ 2) ^ ((3 : ℝ) / 2) := by
  simp only [curvature]
  rw [deriv_graph_curve f hf t, deriv2_graph_curve f hf t]
  have hdet : det2 (!₂[(1 : ℝ), deriv f t]) (!₂[(0 : ℝ), deriv (deriv f) t]) =
      deriv (deriv f) t := by
    simp [det2]
  have hnorm3 : (‖(!₂[(1 : ℝ), deriv f t] : EuclideanSpace ℝ (Fin 2))‖ ^ 3 : ℝ) =
      (1 + deriv f t ^ 2) ^ ((3 : ℝ) / 2) := by
    have hpos : (0 : ℝ) < 1 + deriv f t ^ 2 := by positivity
    rw [show ‖(!₂[(1 : ℝ), deriv f t] : EuclideanSpace ℝ (Fin 2))‖ =
        Real.sqrt (1 + deriv f t ^ 2) from by
      rw [EuclideanSpace.norm_eq]
      congr 1
      simp [Fin.sum_univ_two]]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast ((1 + deriv f t ^ 2) ^ ((1 : ℝ) / 2)) 3,
        ← Real.rpow_mul (le_of_lt hpos)]
    norm_num
  rw [hdet, hnorm3]

theorem curvature_unit_speed (c : ℝ → EuclideanSpace ℝ (Fin 2)) (_hc : ContDiff ℝ ⊤ c)
    (hunit : ∀ t, ‖deriv c t‖ = 1) (t : ℝ) :
    curvature c t = det2 (deriv c t) (deriv (deriv c) t) := by
  simp only [curvature, hunit t, one_pow, div_one]

theorem unit_speed_second_deriv (c : ℝ → EuclideanSpace ℝ (Fin 2)) (hc : ContDiff ℝ ⊤ c)
    (hunit : ∀ t, ‖deriv c t‖ = 1) (t : ℝ) :
    deriv (deriv c) t = curvature c t • J (deriv c t) := by

  have hreg : ∀ s, deriv c s ≠ 0 := by
    intro s h
    have := hunit s
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm

  have hfrenet := frenet_equation c hc hreg t

  have hsimp : ∀ s, (‖deriv c s‖⁻¹) • deriv c s = deriv c s := by
    intro s
    rw [hunit s, inv_one, one_smul]

  have hderiv_eq : deriv (fun s => (‖deriv c s‖⁻¹) • deriv c s) t = deriv (deriv c) t := by
    congr 1
    funext s
    exact hsimp s
  rw [hderiv_eq] at hfrenet
  exact hfrenet

theorem curvature_abs_eq_norm_second_deriv (c : ℝ → EuclideanSpace ℝ (Fin 2)) (hc : ContDiff ℝ ⊤ c)
    (hunit : ∀ t, ‖deriv c t‖ = 1) (t : ℝ) :
    |curvature c t| = ‖deriv (deriv c) t‖ := by
  rw [unit_speed_second_deriv c hc hunit t, norm_smul, norm_J, hunit t, mul_one, Real.norm_eq_abs]

theorem curvature_unit_speed_characterization (c : ℝ → EuclideanSpace ℝ (Fin 2))
    (hc : ContDiff ℝ ⊤ c) (hunit : ∀ t, ‖deriv c t‖ = 1) (t : ℝ) :
    curvature c t = det2 (deriv c t) (deriv (deriv c) t) ∧
    deriv (deriv c) t = curvature c t • J (deriv c t) ∧
    |curvature c t| = ‖deriv (deriv c) t‖ :=
  ⟨curvature_unit_speed c hc hunit t,
   unit_speed_second_deriv c hc hunit t,
   curvature_abs_eq_norm_second_deriv c hc hunit t⟩





lemma hasDerivAt_euclidean_pair {f g : ℝ → ℝ} {f' g' : ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![f s, g s])
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![f', g']) t := by
  have hpi : HasDerivAt (fun s => (![f s, g s] : Fin 2 → ℝ)) (![f', g'] : Fin 2 → ℝ) t := by
    rw [hasDerivAt_pi]; intro i; fin_cases i
    · simpa [Matrix.cons_val_zero] using hf
    · simpa [Matrix.cons_val_one, Matrix.cons_val_fin_one] using hg
  exact (ContinuousLinearMap.hasFDerivAt
    (↑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap)).comp_hasDerivAt t hpi





theorem osculating_circle (c : ℝ → EuclideanSpace ℝ (Fin 2)) (_hc : ContDiff ℝ ⊤ c)
    (hunit : ∀ t, ‖deriv c t‖ = 1) (t₀ : ℝ) (hκ : curvature c t₀ ≠ 0) :
    let center := c t₀ + (curvature c t₀)⁻¹ • J (deriv c t₀)
    let R := |(curvature c t₀)⁻¹|

    (R > 0) ∧
    (‖c t₀ - center‖ = R) ∧
    (@inner ℝ _ _ (c t₀ - center) (deriv c t₀) = 0) ∧
    (R⁻¹ = |curvature c t₀|) ∧


    (∀ (center' : EuclideanSpace ℝ (Fin 2)) (R' : ℝ),
      R' > 0 →
      ‖c t₀ - center'‖ = R' →
      @inner ℝ _ _ (c t₀ - center') (deriv c t₀) = 0 →
      R'⁻¹ = |curvature c t₀| →
      @inner ℝ _ _ (center' - c t₀) (J (deriv c t₀)) * curvature c t₀ > 0 →
      center' = center ∧ R' = R) := by
  set κ := curvature c t₀
  set T := deriv c t₀
  have hκ_ne : κ ≠ 0 := hκ
  have hT_norm : ‖T‖ = 1 := hunit t₀
  have hT_ne : T ≠ 0 := by
    intro h; rw [h, norm_zero] at hT_norm; exact one_ne_zero hT_norm.symm

  have hJT_sq : @inner ℝ _ _ (J T) (J T) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, norm_J, hT_norm, one_pow]
  refine ⟨abs_pos.mpr (inv_ne_zero hκ_ne), ?_, ?_, ?_, ?_⟩

  · show ‖c t₀ - (c t₀ + κ⁻¹ • J T)‖ = |κ⁻¹|
    have h1 : c t₀ - (c t₀ + κ⁻¹ • J T) = -(κ⁻¹ • J T) := by abel
    rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, norm_J, hT_norm, mul_one]

  · show @inner ℝ _ _ (c t₀ - (c t₀ + κ⁻¹ • J T)) T = 0
    have h1 : c t₀ - (c t₀ + κ⁻¹ • J T) = -(κ⁻¹ • J T) := by abel
    rw [h1, inner_neg_left, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    rw [inner_J_eq_det2, det2_antisymm, det2_self, neg_zero, mul_zero, neg_zero]

  · show |κ⁻¹|⁻¹ = |κ|
    rw [abs_inv, inv_inv]

  · intro center' R' hR'_pos hpass htang hcurv hside
    have hR'_ne : R' ≠ 0 := ne_of_gt hR'_pos

    have hR'_eq : R' = |κ⁻¹| := by
      rw [← inv_inv R', hcurv, ← abs_inv]


    have htang' : @inner ℝ _ _ T (c t₀ - center') = 0 := by rw [real_inner_comm]; exact htang
    have horth := orthog_proportional_J T (c t₀ - center') hT_ne htang'

    rw [hT_norm, one_pow, div_one] at horth
    set lam := det2 T (c t₀ - center') with hlam_def

    have hlam_abs : |lam| = |κ⁻¹| := by
      have h1 : ‖c t₀ - center'‖ = |lam| * ‖J T‖ := by
        conv_lhs => rw [horth]
        rw [norm_smul, Real.norm_eq_abs]
      rw [norm_J, hT_norm, mul_one] at h1
      have hpass2 : ‖c t₀ - center'‖ = |κ⁻¹| := by rw [hpass, hR'_eq]
      linarith [hpass2]


    have hside_simpl : -lam * κ > 0 := by
      have heq : center' - c t₀ = (-lam) • J T := by
        have : center' - c t₀ = -(c t₀ - center') := by abel
        rw [this, horth]; simp only [neg_smul]
      rw [heq, inner_smul_left, starRingEnd_apply, star_trivial, hJT_sq, mul_one] at hside
      exact hside

    have hlam_eq : lam = -κ⁻¹ := by
      have hsq : lam ^ 2 = κ⁻¹ ^ 2 := by
        nlinarith [sq_abs lam, sq_abs κ⁻¹]

      have hfactor : (lam - κ⁻¹) * (lam + κ⁻¹) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hfactor with heq | heq
      ·
        exfalso
        have hlam_val : lam = κ⁻¹ := by linarith
        have : -lam * κ = -(κ⁻¹ * κ) := by rw [hlam_val]; ring
        rw [inv_mul_cancel₀ hκ_ne] at this
        linarith
      ·
        linarith

    constructor
    ·
      have h1 : c t₀ - center' = -(κ⁻¹ • J T) := by
        have h := horth
        rw [hlam_eq] at h
        rw [h, neg_smul]

      have h2 : center' = c t₀ + κ⁻¹ • J T := by
        have h3 : center' + -(κ⁻¹ • J T) = c t₀ := by
          have := (sub_eq_iff_eq_add.mp h1).symm
          rwa [add_comm] at this

        have h4 : center' = c t₀ - -(κ⁻¹ • J T) := eq_sub_of_add_eq h3
        rwa [sub_neg_eq_add] at h4

      exact h2
    · exact hR'_eq

end PlaneCurves

end
