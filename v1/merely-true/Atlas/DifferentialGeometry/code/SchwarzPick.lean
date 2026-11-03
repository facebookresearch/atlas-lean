/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Complex Metric Set Function Filter

open scoped Topology ComplexConjugate

namespace SchwarzPick

noncomputable def mobiusMap (a : ℂ) (w : ℂ) : ℂ :=
  (w - a) / (1 - conj a * w)

noncomputable def mobiusInv (a : ℂ) (w : ℂ) : ℂ :=
  (w + a) / (1 + conj a * w)

lemma mobiusMap_self (a : ℂ) : mobiusMap a a = 0 := by
  simp [mobiusMap, sub_self]

lemma mobiusInv_zero (a : ℂ) : mobiusInv a 0 = a := by
  simp [mobiusInv]

lemma norm_conj_mul_lt_one {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖conj a * w‖ < 1 := by
  rw [norm_mul, RCLike.norm_conj]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha hw.le

lemma one_sub_conj_mul_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 - conj a * w ≠ 0 := by
  intro heq
  have h1 : conj a * w = 1 := by linear_combination -heq
  have h2 : ‖conj a * w‖ = 1 := by rw [h1, norm_one]
  exact absurd h2 (ne_of_lt (norm_conj_mul_lt_one ha hw))

lemma norm_sq_lt_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖z‖ ^ 2 < 1 := by
  have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  nlinarith [mul_lt_one_of_nonneg_of_lt_one_left h0 hz (le_of_lt hz)]

lemma one_sub_norm_sq_pos {z : ℂ} (hz : ‖z‖ < 1) : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by
  linarith [norm_sq_lt_one_of_norm_lt_one hz]

lemma mobiusMap_mem_ball {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    mobiusMap a w ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  have hne : (1 : ℂ) - conj a * w ≠ 0 := one_sub_conj_mul_ne_zero ha hw
  simp only [mobiusMap]
  rw [norm_div]
  rw [div_lt_one (by positivity)]


  rw [show ‖w - a‖ < ‖(1 : ℂ) - conj a * w‖ ↔
      ‖w - a‖ ^ 2 < ‖(1 : ℂ) - conj a * w‖ ^ 2 from
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).symm]

  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]

  have key : (Complex.normSq ((1 : ℂ) - conj a * w) : ℝ) - Complex.normSq (w - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq w) := by
    have h1 : (w * conj a).re = (conj a * w).re := by rw [mul_comm]
    have h2 : (conj (conj a * w)).re = (conj a * w).re := Complex.conj_re _
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (w.re - a.re), sq_nonneg (w.im - a.im),
      sq_nonneg (w.re * a.im - w.im * a.re)]
  have h1 : (0 : ℝ) < 1 - Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq]; exact one_sub_norm_sq_pos ha
  have h2 : (0 : ℝ) < 1 - Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]; exact one_sub_norm_sq_pos hw
  linarith [mul_pos h1 h2]

lemma mobiusInv_mem_ball {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    mobiusInv a w ∈ ball (0 : ℂ) 1 := by
  have : mobiusInv a w = mobiusMap (-a) w := by
    simp [mobiusInv, mobiusMap, map_neg, neg_mul, sub_neg_eq_add]
  rw [this]
  exact mobiusMap_mem_ball (by rwa [norm_neg]) hw

lemma differentiableOn_mobiusMap {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (mobiusMap a) (ball 0 1) := by
  intro w hw
  have hw_norm : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact differentiableAt_id.sub (differentiableAt_const a)
  · exact (differentiableAt_const 1).sub ((differentiableAt_const (conj a)).mul differentiableAt_id)
  · exact one_sub_conj_mul_ne_zero ha hw_norm

lemma differentiableOn_mobiusInv {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (mobiusInv a) (ball 0 1) := by
  have heq : mobiusInv a = mobiusMap (-a) := by
    ext w; simp [mobiusInv, mobiusMap, map_neg, neg_mul, sub_neg_eq_add]
  rw [heq]
  exact differentiableOn_mobiusMap (by rwa [norm_neg])

theorem schwarz_pick (h : ℂ → ℂ)
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (h_maps : MapsTo h (ball 0 1) (ball 0 1))
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv h z‖ ≤ (1 - ‖h z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
  have hz_norm : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hhz : h z ∈ ball (0 : ℂ) 1 := h_maps hz
  have hhz_norm : ‖h z‖ < 1 := mem_ball_zero_iff.mp hhz
  have h1z : (0 : ℝ) < 1 - ‖z‖ ^ 2 := one_sub_norm_sq_pos hz_norm
  have h1hz : (0 : ℝ) < 1 - ‖h z‖ ^ 2 := one_sub_norm_sq_pos hhz_norm

  set g := mobiusMap (h z) ∘ h ∘ mobiusInv z with hg_def

  have hg_maps : MapsTo g (ball 0 1) (ball 0 1) := by
    intro w hw
    simp only [g, comp_apply]
    apply mobiusMap_mem_ball hhz_norm
    exact mem_ball_zero_iff.mp (h_maps (mobiusInv_mem_ball hz_norm (mem_ball_zero_iff.mp hw)))

  have hg_diff : DifferentiableOn ℂ g (ball 0 1) := by
    apply DifferentiableOn.comp (differentiableOn_mobiusMap hhz_norm)
    · apply DifferentiableOn.comp hd (differentiableOn_mobiusInv hz_norm)
      exact fun w hw => mobiusInv_mem_ball hz_norm (mem_ball_zero_iff.mp hw)
    · intro w hw
      exact h_maps (mobiusInv_mem_ball hz_norm (mem_ball_zero_iff.mp hw))

  have hg_zero : g 0 = 0 := by
    simp only [g, comp_apply, mobiusInv_zero, mobiusMap_self]

  have hg_schwarz : ‖deriv g 0‖ ≤ 1 := by
    have hg_maps' : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
      rw [hg_zero]
      exact fun w hw => mem_closedBall_zero_iff.mpr (le_of_lt (mem_ball_zero_iff.mp (hg_maps hw)))
    exact Complex.norm_deriv_le_one_of_mapsTo_ball hg_diff hg_maps' one_pos


  suffices h_chain : ‖deriv h z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖h z‖ ^ 2) ≤ ‖deriv g 0‖ by
    calc ‖deriv h z‖
      = ‖deriv h z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖h z‖ ^ 2) *
        ((1 - ‖h z‖ ^ 2) / (1 - ‖z‖ ^ 2)) := by field_simp
      _ ≤ ‖deriv g 0‖ * ((1 - ‖h z‖ ^ 2) / (1 - ‖z‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_right h_chain (div_nonneg h1hz.le h1z.le)
      _ ≤ 1 * ((1 - ‖h z‖ ^ 2) / (1 - ‖z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right hg_schwarz (div_nonneg h1hz.le h1z.le)
      _ = (1 - ‖h z‖ ^ 2) / (1 - ‖z‖ ^ 2) := one_mul _

  have hd_inv : HasDerivAt (mobiusInv z) (1 - conj z * z) 0 := by
    have hnum : HasDerivAt (fun w : ℂ => w + z) 1 0 := by
      have h := (hasDerivAt_id (0 : ℂ)).add (hasDerivAt_const 0 z)
      simp only [add_zero] at h; exact h
    have hden : HasDerivAt (fun w : ℂ => 1 + conj z * w) (conj z) 0 := by
      have h := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
        ((hasDerivAt_const (0 : ℂ) (conj z)).mul (hasDerivAt_id 0))
      simp only [zero_add, zero_mul, mul_one] at h; exact h
    have hne : (1 : ℂ) + conj z * (0 : ℂ) ≠ 0 := by simp
    have hdiv := hnum.div hden hne
    simp only [zero_add, mul_zero, add_zero, one_pow, mul_one] at hdiv
    convert hdiv using 1
    ring

  have hd_map : HasDerivAt (mobiusMap (h z)) (1 / (1 - conj (h z) * h z)) (h z) := by
    have hne : (1 : ℂ) - conj (h z) * h z ≠ 0 := one_sub_conj_mul_ne_zero hhz_norm hhz_norm
    have hnum : HasDerivAt (fun w : ℂ => w - h z) 1 (h z) := by
      have h := (hasDerivAt_id (h z)).sub (hasDerivAt_const (h z) (h z))
      simp only [sub_zero] at h; exact h
    have hden : HasDerivAt (fun w : ℂ => 1 - conj (h z) * w) (-conj (h z)) (h z) := by
      have h := (hasDerivAt_const (h z) (1 : ℂ)).sub
        ((hasDerivAt_const (h z) (conj (h z))).mul (hasDerivAt_id (h z)))
      simp only [zero_sub, zero_mul, mul_one, zero_add] at h
      exact h
    have hdiv := hnum.div hden hne
    simp only [sub_self, zero_mul, sub_zero, one_mul] at hdiv
    convert hdiv using 1
    rw [one_div, sq]
    field_simp [hne]

  have hd_at_z : DifferentiableAt ℂ h z := hd.differentiableAt (isOpen_ball.mem_nhds hz)
  have h_at_inv : HasDerivAt (h ∘ mobiusInv z) (deriv h z * (1 - conj z * z)) 0 := by
    have hd_h_z : HasDerivAt h (deriv h z) (mobiusInv z 0) := by
      rw [mobiusInv_zero]; exact hd_at_z.hasDerivAt
    exact hd_h_z.comp 0 hd_inv
  have hd_comp : HasDerivAt g
      (1 / (1 - conj (h z) * h z) * (deriv h z * (1 - conj z * z))) 0 := by
    have hd_map' : HasDerivAt (mobiusMap (h z)) (1 / (1 - conj (h z) * h z))
        ((h ∘ mobiusInv z) 0) := by
      simp only [comp_apply, mobiusInv_zero]
      exact hd_map
    exact hd_map'.comp 0 h_at_inv
  have hderiv_eq : deriv g 0 = 1 / (1 - conj (h z) * h z) * (deriv h z * (1 - conj z * z)) :=
    hd_comp.deriv

  have hnorm_inv : ‖(1 : ℂ) - conj z * z‖ = 1 - ‖z‖ ^ 2 := by
    have heq : (1 : ℂ) - conj z * z = ↑((1 : ℝ) - ‖z‖ ^ 2) := by
      have h0 : conj z * z = ↑(Complex.normSq z) := by
        rw [mul_comm]; exact Complex.mul_conj z
      rw [h0, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [heq]; exact_mod_cast abs_of_pos h1z
  have hnorm_map : ‖(1 : ℂ) - conj (h z) * h z‖ = 1 - ‖h z‖ ^ 2 := by
    have heq : (1 : ℂ) - conj (h z) * h z = ↑((1 : ℝ) - ‖h z‖ ^ 2) := by
      have h0 : conj (h z) * h z = ↑(Complex.normSq (h z)) := by
        rw [mul_comm]; exact Complex.mul_conj (h z)
      rw [h0, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [heq]; exact_mod_cast abs_of_pos h1hz

  rw [hderiv_eq, norm_mul, norm_mul, norm_div, norm_one, hnorm_map, hnorm_inv]
  rw [one_div, div_eq_mul_inv, mul_comm]

noncomputable def hyperbolicDist (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : ℝ :=
  2 * Real.artanh (‖z - w‖ / ‖starRingEnd ℂ w * z - 1‖)

theorem hyperbolic_dist_formula (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hyperbolicDist z w hz hw =
      2 * Real.artanh (‖z - w‖ / ‖starRingEnd ℂ w * z - 1‖) := by
  rfl

noncomputable def poincareConformalFactor (z : ℂ) : ℝ :=
  2 / (1 - ‖z‖ ^ 2)

end SchwarzPick
