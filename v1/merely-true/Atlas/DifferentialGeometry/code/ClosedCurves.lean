/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.PlaneCurves
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fin.VecNotation
import Atlas.DifferentialGeometry.code.DegreeTheory

noncomputable section

open Finset BigOperators MeasureTheory

namespace ClosedCurves

structure IsClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  period_pos : T > 0
  periodic : ∀ t, c (t + T) = c t
  regular : ∀ t, deriv c t ≠ 0

def IsSimpleClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  IsClosedCurve c T ∧ ∀ s t, 0 ≤ s → s < t → t < T → c s ≠ c t

def IsConvexCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  IsSimpleClosedCurve c T ∧
  ∀ (a : Fin 2 → ℝ) (b : ℝ) (t₀ : ℝ),

    (∑ i, a i * c t₀ i) = b →

    (∑ i, a i * deriv c t₀ i) = 0 →

    (∀ t, (∑ i, a i * c t i) ≤ b) ∨ (∀ t, (∑ i, a i * c t i) ≥ b)

def toEuclidean (c : ℝ → Fin 2 → ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c t)

def curvature (c : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  PlaneCurves.curvature (toEuclidean c) t

def totalCurvature (c : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, curvature c t * ‖deriv (toEuclidean c) t‖

lemma deriv_periodic_of_closed (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) : ∀ t, deriv c (t + T) = deriv c t := by
  intro t
  have heq : (fun s => c (s + T)) = c := by
    funext s; exact hc.periodic s
  have hcdiff : Differentiable ℝ c := hc.smooth.differentiable (by simp)
  have h1 : deriv (fun s => c (s + T)) t = deriv c (t + T) := by
    have hd : HasDerivAt (fun s => c (s + T)) (deriv c (t + T)) t := by
      have hc_at : HasDerivAt c (deriv c (t + T)) (t + T) := hcdiff.differentiableAt.hasDerivAt
      have hadd : HasDerivAt (· + T) 1 t := (hasDerivAt_id t).add_const T
      have hcomp := hc_at.scomp t hadd
      simpa [Function.comp] using hcomp
    exact hd.deriv
  rw [← h1, heq]

lemma norm_deriv_periodic_of_closed (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) : ∀ t, ‖deriv c (t + T)‖ = ‖deriv c t‖ := by
  intro t; rw [deriv_periodic_of_closed c T hc t]

def unitTangent (c : ℝ → Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  (‖deriv (toEuclidean c) t‖⁻¹) • deriv c t

def rotationNumber (c : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  totalCurvature c T / (2 * Real.pi)

theorem curvature_speed_eq_det2_unitTangent (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0) :
    curvature c t * ‖deriv (toEuclidean c) t‖ =
    DegreeTheory.det2 (unitTangent c t) (deriv (unitTangent c) t) := by

  have hce_smooth : ContDiff ℝ ⊤ (toEuclidean c) := by
    unfold toEuclidean
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.contDiff.comp hsmooth

  set L : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv : (Fin 2 → ℝ) ≃L[ℝ] _).toContinuousLinearMap

  have hL : ∀ s, deriv (toEuclidean c) s = L (deriv c s) := by
    intro s; unfold toEuclidean
    exact (L.hasFDerivAt.comp_hasDerivAt s
      ((hsmooth.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv

  have hce_ne : deriv (toEuclidean c) t ≠ 0 := by
    rw [hL t]; intro h
    apply hc'

    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.injective h

  have hnorm_ne : ‖deriv (toEuclidean c) t‖ ≠ 0 := norm_ne_zero_iff.mpr hce_ne

  have hdc_E : ContDiff ℝ ⊤ (deriv (toEuclidean c)) := by
    have : ContDiff ℝ (⊤ + 1) (toEuclidean c) := by
      simp [WithTop.top_add]; exact hce_smooth
    exact this.deriv'

  have hdiff_dc_E : DifferentiableAt ℝ (deriv (toEuclidean c)) t :=
    (hdc_E.differentiable (by simp)).differentiableAt
  have hdiff_inv : DifferentiableAt ℝ (fun s => (‖deriv (toEuclidean c) s‖⁻¹ : ℝ)) t := by
    apply DifferentiableAt.inv
    · exact hdiff_dc_E.norm (𝕜 := ℝ) hce_ne
    · exact hnorm_ne

  have hT_eq_L : ∀ s,
      (‖deriv (toEuclidean c) s‖⁻¹ : ℝ) • deriv (toEuclidean c) s = L (unitTangent c s) := by
    intro s; unfold unitTangent; rw [map_smul, hL s]

  have hdc : ContDiff ℝ ⊤ (deriv c) := by
    have : ContDiff ℝ (⊤ + 1) c := by simp [WithTop.top_add]; exact hsmooth
    exact this.deriv'
  have hdiff_dc : DifferentiableAt ℝ (deriv c) t :=
    (hdc.differentiable (by simp)).differentiableAt

  have hU_diff : DifferentiableAt ℝ (unitTangent c) t := by
    unfold unitTangent
    exact hdiff_inv.smul hdiff_dc

  set T_E : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun s => (‖deriv (toEuclidean c) s‖⁻¹) • deriv (toEuclidean c) s
  have hT_diff : DifferentiableAt ℝ T_E t := hdiff_inv.smul hdiff_dc_E

  have hT_fun_eq : T_E = L ∘ (unitTangent c) := by
    funext s; exact hT_eq_L s

  have hderiv_T_eq : deriv T_E t = L (deriv (unitTangent c) t) := by
    rw [hT_fun_eq]
    exact (L.hasFDerivAt.comp_hasDerivAt t hU_diff.hasDerivAt).deriv

  have hdet2_eq : PlaneCurves.det2 (T_E t) (deriv T_E t) =
      DegreeTheory.det2 (unitTangent c t) (deriv (unitTangent c) t) := by
    rw [show T_E t = L (unitTangent c t) from hT_eq_L t, hderiv_T_eq]
    simp only [PlaneCurves.det2, DegreeTheory.det2]

    rfl

  rw [← hdet2_eq]

  have hderiv_T : deriv T_E t =
    (‖deriv (toEuclidean c) t‖⁻¹) • deriv (deriv (toEuclidean c)) t +
    deriv (fun s => ‖deriv (toEuclidean c) s‖⁻¹) t • deriv (toEuclidean c) t :=
    deriv_smul hdiff_inv hdiff_dc_E
  rw [hderiv_T]
  have key := PlaneCurves.det2_unit_tangent_deriv (deriv (toEuclidean c) t)
    (deriv (deriv (toEuclidean c)) t)
    (deriv (fun s => ‖deriv (toEuclidean c) s‖⁻¹) t) hnorm_ne

  unfold curvature PlaneCurves.curvature

  have hN_ne : (‖deriv (toEuclidean c) t‖ : ℝ) ≠ 0 := hnorm_ne

  have key' : PlaneCurves.det2 (‖deriv (toEuclidean c) t‖⁻¹ • deriv (toEuclidean c) t)
    (‖deriv (toEuclidean c) t‖⁻¹ • deriv (deriv (toEuclidean c)) t +
     deriv (fun s => ‖deriv (toEuclidean c) s‖⁻¹) t • deriv (toEuclidean c) t) =
    PlaneCurves.det2 (deriv (toEuclidean c) t) (deriv (deriv (toEuclidean c)) t) /
      ‖deriv (toEuclidean c) t‖ ^ 3 * ‖deriv (toEuclidean c) t‖ := by
    have := key
    field_simp at this ⊢
    linarith
  linarith [key']

theorem total_curvature_eq_two_pi_degree (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    totalCurvature c T = 2 * Real.pi * DegreeTheory.degreeReal (unitTangent c) T := by
  suffices h : totalCurvature c T =
      ∫ t in (0 : ℝ)..T, DegreeTheory.det2 (unitTangent c t) (deriv (unitTangent c) t) by
    rw [h]
    unfold DegreeTheory.degreeReal
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  unfold totalCurvature
  congr 1
  ext t
  exact curvature_speed_eq_det2_unitTangent c t hc.smooth (hc.regular t)

theorem rotationNumber_eq_degree (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    rotationNumber c T = DegreeTheory.degreeReal (unitTangent c) T := by
  unfold rotationNumber
  rw [total_curvature_eq_two_pi_degree c T hc]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma unitTangent_on_unit_circle (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    DegreeTheory.OnUnitCircle (unitTangent c) := by
  intro t
  unfold unitTangent toEuclidean
  set v := deriv c t
  have hreg : v ≠ 0 := hc.regular t

  have hderiv_toE : deriv (fun s => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c s)) t =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm v := by
    have hcdiff : DifferentiableAt ℝ c t :=
      (hc.smooth.differentiable (by simp)).differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hL : HasFDerivAt (fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm x) L (c t) :=
      L.hasFDerivAt
    have hf : HasDerivAt c (deriv c t) t := hcdiff.hasDerivAt
    have hcomp := hL.comp_hasDerivAt t hf
    exact hcomp.deriv

  rw [hderiv_toE]
  set r := ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm v‖
  have hr_pos : r > 0 := by
    simp only [r]
    refine norm_pos_iff.mpr ?_
    intro h
    have : (EuclideanSpace.equiv (Fin 2) ℝ) ((EuclideanSpace.equiv (Fin 2) ℝ).symm v) =
      (EuclideanSpace.equiv (Fin 2) ℝ) 0 := congr_arg _ h
    simp at this
    exact hreg this
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos

  simp only [Pi.smul_apply, smul_eq_mul]

  have hrsq : (v 0) ^ 2 + (v 1) ^ 2 = r ^ 2 := by
    simp only [r, EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp [Fin.sum_univ_two]
  rw [mul_pow, mul_pow, ← mul_add, hrsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr_ne)]

lemma unitTangent_periodic (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    ∀ t, unitTangent c (t + T) = unitTangent c t := by
  intro t
  unfold unitTangent
  have hderiv_per := deriv_periodic_of_closed c T hc t

  conv_lhs => rw [hderiv_per]

  congr 1

  unfold toEuclidean
  have hcdiff : Differentiable ℝ c := hc.smooth.differentiable (by simp)
  have hderiv_toE : ∀ s, deriv (fun u => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c u)) s =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (deriv c s) := by
    intro s
    have hcs : DifferentiableAt ℝ c s := hcdiff.differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hL : HasFDerivAt (fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm x) L (c s) :=
      L.hasFDerivAt
    have hf : HasDerivAt c (deriv c s) s := hcs.hasDerivAt
    exact (hL.comp_hasDerivAt s hf).deriv
  rw [hderiv_toE (t + T), hderiv_toE t, hderiv_per]

lemma det2_unitTangent_deriv_eq_curvature_speed (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (p : Fin 2 → ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0)
    (hfp : unitTangent c t = p) :
    DegreeTheory.det2 p (deriv (unitTangent c) t) =
    curvature c t * ‖deriv (toEuclidean c) t‖ := by
  rw [← hfp]
  exact (curvature_speed_eq_det2_unitTangent c t hsmooth hc').symm

lemma norm_deriv_toEuclidean_pos (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0) :
    ‖deriv (toEuclidean c) t‖ > 0 := by
  have hderiv_eq : deriv (toEuclidean c) t = (EuclideanSpace.equiv (Fin 2) ℝ).symm (deriv c t) := by
    unfold toEuclidean
    have hcdiff : DifferentiableAt ℝ c t :=
      (hsmooth.differentiable (by simp)).differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact (L.hasFDerivAt.comp_hasDerivAt t hcdiff.hasDerivAt).deriv
  rw [hderiv_eq]
  exact norm_pos_iff.mpr (by
    intro h
    have : (EuclideanSpace.equiv (Fin 2) ℝ) ((EuclideanSpace.equiv (Fin 2) ℝ).symm (deriv c t)) =
      (EuclideanSpace.equiv (Fin 2) ℝ) 0 := congr_arg _ h
    simp at this
    exact hc' this)

lemma sign_det2_unitTangent_eq_sign_curvature (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (p : Fin 2 → ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0)
    (hfp : unitTangent c t = p) :
    Real.sign (DegreeTheory.det2 p (deriv (unitTangent c) t)) =
    Real.sign (curvature c t) := by
  rw [det2_unitTangent_deriv_eq_curvature_speed c t p hsmooth hc' hfp]

  have hnorm_pos : ‖deriv (toEuclidean c) t‖ > 0 := norm_deriv_toEuclidean_pos c t hsmooth hc'

  rcases lt_trichotomy (curvature c t) 0 with hk | hk | hk
  · rw [Real.sign_of_neg hk, Real.sign_of_neg (mul_neg_of_neg_of_pos hk hnorm_pos)]
  · simp [hk, Real.sign_zero]
  · rw [Real.sign_of_pos hk, Real.sign_of_pos (mul_pos hk hnorm_pos)]

lemma unitTangent_eq_e1_iff (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0) :
    unitTangent c t = (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ↔
    ((deriv c t) 1 = 0 ∧ (deriv c t) 0 > 0) := by
  unfold unitTangent
  set v := deriv c t
  have hr_pos : ‖deriv (toEuclidean c) t‖ > 0 := norm_deriv_toEuclidean_pos c t hsmooth hc'
  set r := ‖deriv (toEuclidean c) t‖
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hderiv_eq : deriv (toEuclidean c) t = (EuclideanSpace.equiv (Fin 2) ℝ).symm v := by
    unfold toEuclidean
    have hcdiff : DifferentiableAt ℝ c t :=
      (hsmooth.differentiable (by simp)).differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact (L.hasFDerivAt.comp_hasDerivAt t hcdiff.hasDerivAt).deriv

  have hr_eq_norm : r = Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) := by
    simp only [r, hderiv_eq]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, sq_abs]

  constructor
  · intro h

    have h0 : r⁻¹ * v 0 = 1 := by
      have := congr_fun h ⟨0, by omega⟩; simpa [Pi.smul_apply, smul_eq_mul] using this
    have h1 : r⁻¹ * v 1 = 0 := by
      have := congr_fun h ⟨1, by omega⟩; simpa [Pi.smul_apply, smul_eq_mul] using this
    constructor
    · exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hr_ne)
    · have hv0_eq : v 0 = r := by field_simp at h0; linarith
      linarith
  · intro ⟨hv1, hv0⟩

    have hr_eq_v0 : r = v 0 := by
      rw [hr_eq_norm, hv1]; simp; rw [Real.sqrt_sq (le_of_lt hv0)]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = 0
    · simp only [hi, ite_true]
      rw [hr_eq_v0, inv_mul_cancel₀ (ne_of_gt hv0)]
    · simp only [hi, ite_false]
      have : i = 1 := by omega
      rw [this, hv1, mul_zero]

def det2 (a b : Fin 2 → ℝ) : ℝ := DegreeTheory.det2 a b

lemma periodic_global_min_of_minOn {f : ℝ → ℝ} {T t₀ : ℝ}
    (hT : 0 < T) (hper : Function.Periodic f T)
    (hmin : IsMinOn f (Set.Icc 0 T) t₀) :
    ∀ s, f t₀ ≤ f s := by
  intro s

  obtain ⟨y, hy_mem, hy_eq⟩ := hper.exists_mem_Ico₀ hT s
  rw [hy_eq]

  exact hmin (Set.Ico_subset_Icc_self hy_mem)

end ClosedCurves

end
